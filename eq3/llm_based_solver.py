"""LLM-backed Lean proof search via OpenRouter."""
from __future__ import annotations

import os
import re
import time
from pathlib import Path
from typing import Any

import requests
from dotenv import load_dotenv

from eq3.composite_solver import Solution
from eq3.lean_utils import check_solution_with_lean, solution_to_code, spec_to_code


OPENROUTER_URL = "https://openrouter.ai/api/v1/chat/completions"
DEFAULT_MODEL = "anthropic/claude-3.5-sonnet"


def _extract_lean_block(text: str) -> tuple[str | None, str | None]:
    """Return (proof, polarity_hint) from a response containing a Lean fence."""
    polarity_hint = None
    polarity_matches = list(re.finditer(r"\b(POSITIVE|NEGATIVE)\b", text, flags=re.IGNORECASE))
    if polarity_matches:
        polarity_hint = polarity_matches[-1].group(1).lower()

    matches = list(re.finditer(r"```lean[^\S\r\n]*(?:\r?\n)?(.*?)```", text, flags=re.DOTALL | re.IGNORECASE))
    if not matches:
        matches = list(re.finditer(r"```[^\S\r\n]*(?:\r?\n)?(.*?)```", text, flags=re.DOTALL))
    if not matches:
        return None, polarity_hint
    proof = re.sub(r"\r?\n[ \t]*$", "", matches[-1].group(1))
    return proof if proof.strip() else None, polarity_hint


class LLMBasedSolver:
    """Ask an OpenRouter model for a positive or negative Lean proof and verify it."""

    def __init__(
        self,
        *,
        model: str | None = None,
        proofs_dir: str | os.PathLike[str] = "proofs/llm",
        failed_dir: str | os.PathLike[str] = "proofs/llm_failed",
        lean_workdir: str | os.PathLike[str] = "proofs",
        max_attempts: int = 1,
        timeout: int = 120,
        temperature: float = 0.2,
        env_path: str | os.PathLike[str] = ".env",
    ) -> None:
        load_dotenv(env_path)
        self.api_key = os.environ.get("OPENROUTER_API_KEY")
        self.model = model or os.environ.get("OPENROUTER_MODEL", DEFAULT_MODEL)
        self.proofs_dir = Path(proofs_dir)
        self.failed_dir = Path(failed_dir)
        self.lean_workdir = Path(lean_workdir)
        self.max_attempts = max_attempts
        self.timeout = timeout
        self.temperature = temperature
        self.stats: dict[str, int | float] = {
            "calls": 0,
            "verified_positive": 0,
            "verified_negative": 0,
            "failed": 0,
            "prompt_tokens": 0,
            "completion_tokens": 0,
            "total_tokens": 0,
            "cost_usd": 0.0,
        }

    def try_solve(self, spec: Solution, return_all: bool = False) -> Solution | None:
        if return_all:
            result = self.try_solve(spec, return_all=False)
            return {"solutions": [result]} if result else {}
        if not self.api_key:
            return None

        self.proofs_dir.mkdir(parents=True, exist_ok=True)
        self.failed_dir.mkdir(parents=True, exist_ok=True)
        problem_id = self._problem_id(spec)
        previous_error = ""

        for attempt in range(1, self.max_attempts + 1):
            content = self._call_model(spec, previous_error)
            if content is None:
                self.stats["failed"] = int(self.stats["failed"]) + 1
                return None
            proof, polarity_hint = _extract_lean_block(content)
            if proof is None:
                previous_error = "The response did not contain a ```lean fenced proof block."
                self._save_text(self.failed_dir / f"{problem_id}_attempt{attempt}.txt", content)
                continue
            if re.search(r"\b(sorry|admit)\b", proof):
                previous_error = "The Lean proof block used sorry or admit."
                self._save_text(self.failed_dir / f"{problem_id}_attempt{attempt}.lean", proof)
                continue

            failures = []
            for suffix, result in self._candidate_solutions(proof, polarity_hint):
                lean_code = solution_to_code({**spec, **result})
                ok, lean_output = check_solution_with_lean(lean_code, workdir=str(self.lean_workdir))
                if ok:
                    self._save_text(self.proofs_dir / f"{problem_id}_{suffix}.lean", lean_code)
                    key = f"verified_{suffix}"
                    self.stats[key] = int(self.stats[key]) + 1
                    return result
                failures.append(f"{suffix}: {lean_output}")
                self._save_text(self.failed_dir / f"{problem_id}_attempt{attempt}_{suffix}.lean", lean_code)
                self._save_text(self.failed_dir / f"{problem_id}_attempt{attempt}_{suffix}.out", lean_output)

            previous_error = "Lean rejected the proof:\n" + "\n\n".join(failures)

        self.stats["failed"] = int(self.stats["failed"]) + 1
        return None

    def _call_model(self, spec: Solution, previous_error: str) -> str | None:
        headers = {
            "Authorization": f"Bearer {self.api_key}",
            "Content-Type": "application/json",
            "HTTP-Referer": os.environ.get("OPENROUTER_SITE_URL", "https://github.com/R-Peleg/pyMagmaProver"),
            "X-Title": os.environ.get("OPENROUTER_APP_NAME", "pyMagmaProver"),
        }
        messages = [
            {
                "role": "system",
                "content": (
                    "You are an expert Lean 4/mathlib prover. Return either POSITIVE or NEGATIVE, "
                    "then exactly one fenced Lean code block containing only the proof fragment that goes after := by. "
                    "Do not use JSON, commentary, sorry, admit, or unsound axioms. Example response:\n"
                    "POSITIVE\n"
                    "```lean\n"
                    "  intro x y\n"
                    "  exact hX x y\n"
                    "```"
                ),
            },
            {"role": "user", "content": self._prompt(spec, previous_error)},
        ]
        payload = {
            "model": self.model,
            "messages": messages,
            "temperature": self.temperature,
            "max_tokens": 10_000,
        }
        self.stats["calls"] = int(self.stats["calls"]) + 1
        try:
            response = requests.post(OPENROUTER_URL, headers=headers, json=payload, timeout=self.timeout)
        except requests.RequestException:
            return None
        if response.status_code >= 400:
            return None
        try:
            data = response.json()
        except ValueError:
            return None
        self._record_usage(data)
        choices = data.get("choices") or []
        if not choices:
            return None
        message = choices[0].get("message") or {}
        content = message.get("content")
        return content if isinstance(content, str) else None

    def _prompt(self, spec: Solution, previous_error: str) -> str:
        equations = "\n".join(f"- {equation.string}" for equation in spec.get("equations", []))
        target = getattr(spec.get("target"), "string", "")
        retry = f"\nPrevious Lean/error feedback:\n{previous_error}\n" if previous_error else ""
        return (
            "Find either a positive proof or a negative counterexample proof for this magma problem.\n"
            f"Assumptions:\n{equations}\nTarget: {target}\n\n"
            "Return POSITIVE or NEGATIVE followed by exactly one ```lean fenced block. "
            "The block must contain only the proof fragment inserted after one of these theorem statements. "
            "It must compile in Lean 4 with Mathlib and must not use sorry, admit, or unsound axioms.\n\n"
            f"Full template with both goals:\n```lean\n{spec_to_code(spec)}\n```"
            f"{retry}"
        )

    def _record_usage(self, data: dict[str, Any]) -> None:
        usage = data.get("usage") or {}
        for src, dst in (
            ("prompt_tokens", "prompt_tokens"),
            ("completion_tokens", "completion_tokens"),
            ("total_tokens", "total_tokens"),
        ):
            value = usage.get(src)
            if isinstance(value, int):
                self.stats[dst] = int(self.stats[dst]) + value
        cost = usage.get("cost") or usage.get("total_cost") or data.get("total_cost")
        if isinstance(cost, str):
            try:
                cost = float(cost)
            except ValueError:
                cost = None
        if isinstance(cost, (int, float)):
            self.stats["cost_usd"] = float(self.stats["cost_usd"]) + float(cost)
        if not usage.get("total_tokens"):
            self.stats["total_tokens"] = int(self.stats["prompt_tokens"]) + int(self.stats["completion_tokens"])

    @staticmethod
    def _candidate_solutions(proof: str, polarity_hint: str | None) -> list[tuple[str, Solution]]:
        positive: tuple[str, Solution] = ("positive", {"vc-proof-positive": proof})
        negative: tuple[str, Solution] = ("negative", {"vc-proof-negative": proof, "counterexample": "llm"})
        if polarity_hint == "positive":
            return [positive]
        if polarity_hint == "negative":
            return [negative]
        return [positive, negative]

    @staticmethod
    def _problem_id(spec: Solution) -> str:
        spec_positive = spec.get("vc-spec-positive", "")
        match = re.search(r"theorem\s+([A-Za-z0-9_']+)", spec_positive)
        if match:
            return match.group(1)
        return f"llm_{int(time.time() * 1000)}"

    @staticmethod
    def _save_text(path: Path, text: str) -> None:
        path.write_text(text)

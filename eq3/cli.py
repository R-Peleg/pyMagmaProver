"""Command line interface for eq3."""
from __future__ import annotations

import argparse
import json
from collections.abc import Sequence
from typing import Any

from eq3.composite_solver import CompositeSolver
from eq3.equation_path import EquationPathSolver
from eq3.equation_utils import Equation, Expression, all_expressions, parse_equation
from eq3.lean_utils import cli_lean_spec, solution_to_plain_code
from eq3.symbolic import BinaryOpSolver, FalseOpSolver, TakeSided


def _load_config(path: str | None) -> dict[str, Any]:
    if not path:
        return {}
    with open(path, encoding="utf-8") as f:
        return json.load(f)


def _parse_equations(values: Sequence[str], prefix: str) -> list[Equation]:
    return [parse_equation(value.replace('*', '◇'), f"{prefix}{i}") for i, value in enumerate(values)]


def _solution_result(solution: dict[str, Any] | None) -> dict[str, Any] | None:
    if not solution:
        return None
    if "vc-proof-positive" in solution:
        return {"result": "proved", "proof": solution["vc-proof-positive"]}
    if "vc-proof-negative" in solution:
        return {
            "result": "disproved",
            "counterexample": solution.get("counterexample", "unknown"),
            "proof": solution["vc-proof-negative"],
        }
    return None


def _with_lean_code(
    result: dict[str, Any] | None,
    equations: list[Equation],
    target: Equation,
    solution: dict[str, Any] | None,
) -> dict[str, Any] | None:
    if result is None or solution is None:
        return result
    if result["result"] not in {"proved", "disproved"}:
        return result
    lean_spec = cli_lean_spec(equations, target)
    return {**result, "lean": solution_to_plain_code({**lean_spec, **solution})}


def solve(
    axioms: Sequence[str],
    target: str,
    *,
    mode: str = "both",
    max_degree: int = 4,
) -> dict[str, Any]:
    parsed_axioms = _parse_equations(axioms, "hA")
    parsed_target = parse_equation(target, "target")
    spec = {"equations": parsed_axioms, "target": parsed_target}

    if mode in {"prove", "both"}:
        proof = EquationPathSolver(max_degree=max_degree).try_solve(spec, return_all=False)
        result = _solution_result(proof)
        if result is not None:
            return _with_lean_code(result, parsed_axioms, parsed_target, proof) or result

    if mode in {"disprove", "both"}:
        disproof = CompositeSolver([TakeSided, BinaryOpSolver, FalseOpSolver]).try_solve(spec, return_all=False)
        result = _solution_result(disproof)
        if result is not None:
            return _with_lean_code(result, parsed_axioms, parsed_target, disproof) or result

    return {"result": "unknown"}


def infer(
    axioms: Sequence[str],
    *,
    variables: Sequence[str] = (),
    max_depth: int = 1,
    max_degree: int = 4,
) -> dict[str, Any]:
    parsed_axioms = _parse_equations(axioms, "hA")
    variable_names = sorted({v for axiom in parsed_axioms for v in axiom.variables} | set(variables))
    targets = [expr for expr in all_expressions(variable_names, max_depth) if expr.degree <= max_degree]
    assignment_options: list[Expression] = targets
    seen: set[str] = set()
    equations: list[dict[str, str]] = []

    for axiom in parsed_axioms:
        for lhs in targets:
            for rhs, proof in axiom.infer_equalities(lhs, assignment_options):
                if rhs.degree > max_degree or lhs == rhs:
                    continue
                equation = f"{lhs} = {rhs}"
                if equation in seen:
                    continue
                seen.add(equation)
                equations.append({"equation": equation, "reason": str(axiom), "proof": proof})

    return {"result": "inferred", "equations": equations}


def _print_result(result: dict[str, Any], output_format: str) -> None:
    if output_format == "json":
        print(json.dumps(result, indent=2, ensure_ascii=False))
        return

    if result["result"] in {"proved", "disproved"} and "lean" in result:
        print(result["lean"])
        return
    print(result["result"])
    if result["result"] == "disproved":
        print(f"counterexample: {result['counterexample']}")
    if result["result"] == "inferred":
        for item in result["equations"]:
            print(item["equation"])


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Prove, disprove, or infer equations for one binary magma operation.")
    parser.add_argument("--config", help="JSON configuration file")
    parser.add_argument("--axiom", action="append", default=[], help="Axiom equation. Can be repeated.")
    parser.add_argument("--target", help="Target equation for prove/disprove mode")
    parser.add_argument("--mode", choices=["prove", "disprove", "both"], default=None, help="Solver mode")
    mode_flags = parser.add_mutually_exclusive_group()
    mode_flags.add_argument("--prove", action="store_true", help="Alias for --mode prove")
    mode_flags.add_argument("--disprove", action="store_true", help="Alias for --mode disprove")
    mode_flags.add_argument("--both", action="store_true", help="Alias for --mode both")
    parser.add_argument("--infer", action="store_true", help="List equations inferred in one rewrite step from generated expressions")
    parser.add_argument("--variable", action="append", default=[], help="Extra variable to use for inference. Can be repeated.")
    parser.add_argument("--max-depth", type=int, default=None, help="Maximum generated expression depth for inference")
    parser.add_argument("--max-degree", type=int, default=None, help="Maximum expression degree for proof search/inference")
    parser.add_argument("--format", choices=["text", "json"], default=None, help="Output format")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    config = _load_config(args.config)

    axioms = list(config.get("axioms", [])) + list(args.axiom)
    if not axioms:
        raise SystemExit("At least one --axiom or config axiom is required")

    output_format = args.format or config.get("format", "text")
    max_depth = args.max_depth if args.max_depth is not None else int(config.get("max_depth", 1))
    max_degree = args.max_degree if args.max_degree is not None else int(config.get("max_degree", 4))

    if args.infer or config.get("infer", False):
        variables = list(config.get("variables", [])) + list(args.variable)
        result = infer(axioms, variables=variables, max_depth=max_depth, max_degree=max_degree)
    else:
        target = args.target or config.get("target")
        if not target:
            raise SystemExit("--target or config target is required unless --infer is used")
        mode = args.mode or config.get("mode", "both")
        if args.prove:
            mode = "prove"
        elif args.disprove:
            mode = "disprove"
        elif args.both:
            mode = "both"
        if mode not in {"prove", "disprove", "both"}:
            raise SystemExit("mode must be one of: prove, disprove, both")
        result = solve(axioms, target, mode=mode, max_degree=max_degree)

    _print_result(result, output_format)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

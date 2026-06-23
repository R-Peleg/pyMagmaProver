from __future__ import annotations

import shutil
import unittest
from pathlib import Path
from typing import Any

from eq3.equation_utils import parse_equation
from eq3.lean_utils import check_solution_with_lean, eq3_lean_spec, solution_to_code
from eq3.symbolic import AffineModSolver


PROOFS_DIR = Path(__file__).resolve().parents[2] / "proofs"


def _lean_available() -> bool:
    return shutil.which("lake") is not None and PROOFS_DIR.joinpath("lakefile.lean").exists()


def _spec() -> dict[str, Any]:
    entry = {
        "X": "idempotent",
        "X_eq": parse_equation("x ◇ x = x", "hX"),
        "Y": "commutativity",
        "Y_eq": parse_equation("x ◇ y = y ◇ x", "hY"),
        "Z": "singleton",
        "Z_eq": parse_equation("x = y", "target"),
    }
    return {
        **eq3_lean_spec(entry),
        "equations": [entry["X_eq"], entry["Y_eq"]],
        "target": entry["Z_eq"],
    }


class AffineModSolverTests(unittest.TestCase):
    def test_finds_affine_mod_counterexample(self) -> None:
        solution = AffineModSolver(3).try_solve(_spec(), return_all=False)

        self.assertIn("vc-proof-negative", solution)
        self.assertEqual(solution["counterexample"], "affine-mod-3-a2-b2-c0")

    @unittest.skipUnless(_lean_available(), "Lean/Lake toolchain is required for Lean regression tests")
    def test_generated_counterexample_verifies_in_lean(self) -> None:
        spec = _spec()
        solution = AffineModSolver(3).try_solve(spec, return_all=False)
        code = solution_to_code({**spec, **solution})

        ok, output = check_solution_with_lean(code, workdir=str(PROOFS_DIR))

        self.assertTrue(ok, output)


if __name__ == "__main__":
    unittest.main()

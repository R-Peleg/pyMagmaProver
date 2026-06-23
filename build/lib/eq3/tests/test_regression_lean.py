from __future__ import annotations

import shutil
import unittest
from pathlib import Path
from typing import Any

from eq3.equation_path import EquationPathSolver
from eq3.equation_utils import parse_equation
from eq3.lean_utils import check_solution_with_lean, eq3_lean_spec, solution_to_code
from eq3.symbolic import BinaryOpSolver


PROOFS_DIR = Path(__file__).resolve().parents[2] / "proofs"


def _lean_available() -> bool:
    return shutil.which("lake") is not None and PROOFS_DIR.joinpath("lakefile.lean").exists()


@unittest.skipUnless(_lean_available(), "Lean/Lake toolchain is required for Lean regression tests")
class LeanRegressionTests(unittest.TestCase):
    def _assert_lean_verifies(self, spec: dict[str, Any], solution: dict[str, Any] | None) -> None:
        self.assertIsNotNone(solution)
        assert solution is not None
        code = solution_to_code({**spec, **solution})
        ok, output = check_solution_with_lean(code, workdir=str(PROOFS_DIR))
        self.assertTrue(ok, output)

    def test_commutativity_and_absorption_proves_singleton(self) -> None:
        entry = {
            "X": "EquationX",
            "X_eq": parse_equation("x = x ◇ (x ◇ y)", "hX"),
            "Y": "commutativity",
            "Y_eq": parse_equation("x ◇ y = y ◇ x", "hY"),
            "Z": "singleton",
            "Z_eq": parse_equation("x = y", "target"),
        }
        spec = {
            **eq3_lean_spec(entry),
            "equations": [entry["X_eq"], entry["Y_eq"]],
            "target": entry["Z_eq"],
        }

        solution = EquationPathSolver(max_degree=4).try_solve(spec, return_all=False)

        self.assertIn("vc-proof-positive", solution or {})
        self._assert_lean_verifies(spec, solution)

    def test_commutativity_does_not_prove_singleton(self) -> None:
        entry = {
            "X": "commutativity",
            "X_eq": parse_equation("x ◇ y = y ◇ x", "hX"),
            "Y": "reflexive",
            "Y_eq": parse_equation("x = x", "hY"),
            "Z": "singleton",
            "Z_eq": parse_equation("x = y", "target"),
        }
        spec = {
            **eq3_lean_spec(entry),
            "equations": [entry["X_eq"], entry["Y_eq"]],
            "target": entry["Z_eq"],
        }

        solution = BinaryOpSolver.try_solve(spec, return_all=False)

        self.assertEqual((solution or {}).get("counterexample"), "xor")
        self.assertIn("vc-proof-negative", solution or {})
        self._assert_lean_verifies(spec, solution)


if __name__ == "__main__":
    unittest.main()

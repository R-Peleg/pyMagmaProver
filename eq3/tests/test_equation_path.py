import unittest

from eq3.equation_path import EquationPathSolver
from eq3.equation_utils import parse_equation


class EquationPathSolverTests(unittest.TestCase):
    def test_equation4_classic_proof_uses_hypothesis_names(self) -> None:
        spec = {
            "equations": [
                parse_equation("x = x ◇ y", "hX"),
                parse_equation("x ◇ y = y ◇ x", "hY"),
            ],
            "target": parse_equation("x = y", "target"),
        }

        solution = EquationPathSolver(max_degree=4).try_solve(spec)

        self.assertIsNotNone(solution)
        assert solution is not None
        proof = solution["vc-proof-positive"]
        self.assertNotIn("None", proof)
        self.assertIn("_ = x ◇ y := hX x y", proof)
        self.assertIn("_ = y ◇ x := hY x y", proof)
        self.assertIn("_ = y := (hX y x).symm", proof)

    def test_unnamed_equation_does_not_emit_none_proof(self) -> None:
        spec = {
            "equations": [
                parse_equation("x = x ◇ y"),
                parse_equation("x ◇ y = y ◇ x", "hY"),
            ],
            "target": parse_equation("x = y", "target"),
        }

        with self.assertRaisesRegex(ValueError, "no hypothesis name"):
            EquationPathSolver(max_degree=4).try_solve(spec)


if __name__ == "__main__":
    unittest.main()

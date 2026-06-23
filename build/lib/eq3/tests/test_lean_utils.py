import unittest

from eq3.equation_utils import parse_equation
from eq3.lean_utils import eq3_lean_spec


class LeanUtilsTests(unittest.TestCase):
    def test_eq3_lean_spec_uses_equation_objects(self) -> None:
        spec = eq3_lean_spec(
            {
                "X": "EquationX",
                "X_eq": parse_equation("x = (x ◇ (x ◇ y)) ◇ x", "TEST"),
                "Y": "commutativity",
                "Y_eq": parse_equation("x ◇ y = y ◇ x", "TEST"),
                "Z": "singleton",
                "Z_eq": parse_equation("x = y", "TEST"),
            }
        )

        self.assertIn(
            "abbrev EquationX (G : Type _) [Magma G] := ∀ x y : G, x = (x ◇ (x ◇ y)) ◇ x",
            spec["vc-preamble"],
        )
        self.assertIn(
            "abbrev commutativity (G : Type _) [Magma G] := ∀ x y : G, x ◇ y = y ◇ x",
            spec["vc-preamble"],
        )
        self.assertIn(
            "theorem EquationX_and_commutativity_implies_singleton",
            spec["vc-spec-positive"],
        )


if __name__ == "__main__":
    unittest.main()

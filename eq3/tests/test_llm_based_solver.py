import unittest

from eq3.llm_based_solver import _extract_lean_block


class LLMBasedSolverTests(unittest.TestCase):
    def test_extract_lean_block_preserves_proof_indentation(self) -> None:
        proof, polarity = _extract_lean_block(
            """POSITIVE
```lean
  intro x y
  have hx := hX x y
  have hy := hX y x
  aesop
```"""
        )

        self.assertEqual(polarity, "positive")
        self.assertEqual(
            proof,
            "  intro x y\n  have hx := hX x y\n  have hy := hX y x\n  aesop",
        )

    def test_extract_lean_block_takes_last_solution(self) -> None:
        proof, polarity = _extract_lean_block(
            """NEGATIVE
```lean
  exact first_attempt
```

Actually, use this one.

POSITIVE
```lean
  intro x y
  exact hX x y
```"""
        )

        self.assertEqual(polarity, "positive")
        self.assertEqual(proof, "  intro x y\n  exact hX x y")


if __name__ == "__main__":
    unittest.main()

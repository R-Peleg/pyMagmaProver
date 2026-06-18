from __future__ import annotations

import io
import unittest
from contextlib import redirect_stdout

from eq3.cli import main


class CliTests(unittest.TestCase):
    def _run_cli(self, args: list[str]) -> str:
        stdout = io.StringIO()
        with redirect_stdout(stdout):
            self.assertEqual(main(args), 0)
        return stdout.getvalue()

    def test_text_format_emits_positive_lean_solution(self) -> None:
        output = self._run_cli([
            "--axiom", "x * y = y * x",
            "--axiom", "x = x * (x * y)",
            "--target", "x = y",
            "--format", "text",
        ])

        self.assertTrue(output.startswith("\nimport Mathlib.Tactic"))
        self.assertIn("theorem eq3_positive", output)
        self.assertIn("  calc", output)
        self.assertNotIn("vc-", output)
        self.assertNotIn("\nproved\n", output)

    def test_text_format_emits_negative_lean_solution(self) -> None:
        output = self._run_cli([
            "--axiom", "x * y = y * x",
            "--axiom", "x = x * (x * x)",
            "--target", "x = y",
            "--format", "text",
        ])

        self.assertTrue(output.startswith("\nimport Mathlib.Tactic"))
        self.assertIn("theorem eq3_negative", output)
        self.assertIn("refine ⟨Bool", output)
        self.assertNotIn("vc-", output)
        self.assertNotIn("counterexample:", output)


if __name__ == "__main__":
    unittest.main()

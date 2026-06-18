import unittest
from dataclasses import FrozenInstanceError

from eq3.equation_utils import (
    Equation,
    Expression,
    equation_to_string,
    parse_equation,
)


class EquationUtilsTests(unittest.TestCase):
    def test_parse_equation_returns_immutable_equation_object(self) -> None:
        equation = parse_equation("x = (x ◇ (x ◇ y)) ◇ x", "TEST")

        self.assertIsInstance(equation, Equation)
        self.assertEqual(equation.data, "equation")
        self.assertEqual(equation.string, "x = (x ◇ (x ◇ y)) ◇ x")
        self.assertEqual(equation.string_representation, "x = (x ◇ (x ◇ y)) ◇ x")
        self.assertEqual(equation.degree, 3)
        self.assertEqual(equation.variables, ["x", "y"])

        with self.assertRaises(FrozenInstanceError):
            equation.string = "changed"  # type: ignore[misc]

    def test_expression_saves_tree_string_and_degree(self) -> None:
        equation = parse_equation("x = (x ◇ (x ◇ y)) ◇ x", 'TEST')
        expression = equation.rhs

        self.assertIsInstance(expression, Expression)
        self.assertEqual(expression.data, "binop")
        self.assertEqual(expression.string, "(x ◇ (x ◇ y)) ◇ x")
        self.assertEqual(expression.string_representation, "(x ◇ (x ◇ y)) ◇ x")
        self.assertEqual(equation_to_string(expression), "(x ◇ (x ◇ y)) ◇ x")
        self.assertEqual(expression.degree, 3)
        self.assertEqual(expression.variables, ["x", "y"])

    def test_assignment_returns_new_equation_without_mutating_original(self) -> None:
        equation = parse_equation("x ◇ y = z")
        replacement = parse_equation("a ◇ b = unused").lhs

        assigned = equation.assign({"x": replacement})

        self.assertEqual(equation.string, "x ◇ y = z")
        self.assertEqual(assigned.string, "(a ◇ b) ◇ y = z")
        self.assertEqual(assigned.degree, 2)

    def test_infer_equalities_rewrites_matching_subexpressions(self) -> None:
        equation = parse_equation("y ◇ x = x ◇ y")
        expression = parse_equation("x ◇ (x ◇ y) = unused").lhs

        results = equation.infer_equalities(expression)

        self.assertEqual(
            [result.string for result, _ in results],
            ["x ◇ (y ◇ x)", "(x ◇ y) ◇ x"],
        )

    def test_infer_equalities_rewrites_top_level_and_subexpressions(self) -> None:
        equation = parse_equation("x = x ◇ x")
        expression = parse_equation("x ◇ y = unused").lhs

        results = equation.infer_equalities(expression)

        self.assertEqual(
            [result.string for result, _ in results],
            ["(x ◇ x) ◇ y", "x ◇ (y ◇ y)"],
        )

    def test_infer_equalities_uses_supplied_variables_for_replacement(self) -> None:
        equation = parse_equation("x = x ◇ (x ◇ y)")
        expression = parse_equation("x = unused").lhs
        replacement_y = parse_equation("z = unused").lhs

        results = equation.infer_equalities(expression, [replacement_y])

        self.assertEqual([result.string for result, _ in results], ["x ◇ (x ◇ z)"])

    def test_infer_equalities_tries_each_assignment_for_each_free_variable(self) -> None:
        equation = parse_equation("x = x ◇ (y ◇ z)")
        expression = parse_equation("x = unused").lhs
        assignments = [parse_equation("a = unused").lhs, parse_equation("b = unused").lhs]

        results = equation.infer_equalities(expression, assignments)

        self.assertEqual(
            [result.string for result, _ in results],
            ["x ◇ (a ◇ a)", "x ◇ (a ◇ b)", "x ◇ (b ◇ a)", "x ◇ (b ◇ b)"],
        )

    def test_infer_equalities_rewrites_whole_expression_with_free_assignments(self) -> None:
        equation = parse_equation("x = x ◇ (x ◇ y)")
        expression = parse_equation("x ◇ y = unused").lhs
        assignments = [parse_equation("x = unused").lhs, parse_equation("y = unused").lhs]

        results = equation.infer_equalities(expression, assignments)

        self.assertEqual(
            [result.string for result, _ in results],
            [
                "(x ◇ (x ◇ x)) ◇ y",
                "(x ◇ (x ◇ y)) ◇ y",
                "x ◇ (y ◇ (y ◇ x))",
                "x ◇ (y ◇ (y ◇ y))",
                "(x ◇ y) ◇ ((x ◇ y) ◇ x)",
                "(x ◇ y) ◇ ((x ◇ y) ◇ y)",
            ],
        )

if __name__ == "__main__":
    unittest.main()

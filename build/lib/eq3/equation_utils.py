"""
Immutable equation and expression utilities.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from itertools import product
from typing import Any, Mapping, Optional, cast

import lark


grammar = r"""
?start: equation

equation: expr "=" expr

?expr: expr "◇" term  -> binop
     | term

?term: CNAME          -> var
     | "(" expr ")"

%import common.CNAME
%import common.WS
%ignore WS
"""

parser = lark.Lark(grammar, start="start", parser="lalr")


TreeLike = Any


@dataclass(frozen=True)
class Expression:
    """Immutable expression with no dependency on the parser's tree type."""

    data: str
    value: str | None = None
    children: tuple["Expression", ...] = ()
    string: str = field(init=False)
    string_representation: str = field(init=False)
    degree: int = field(init=False)
    variables: list[str] = field(init=False)

    def __post_init__(self) -> None:
        if self.data == "var":
            if self.value is None or self.children:
                raise ValueError("Variable expressions require a value and no children")
            string = self.value
            object.__setattr__(self, "string", string)
            object.__setattr__(self, "string_representation", string)
            object.__setattr__(self, "degree", 0)
            object.__setattr__(self, "variables", [string])
            return

        if self.data != "binop" or self.value is not None or len(self.children) != 2:
            raise ValueError("Binary expressions require exactly two children and no value")

        left, right = self.children
        string = _expression_to_string(self)
        object.__setattr__(self, "string", string)
        object.__setattr__(self, "string_representation", string)
        object.__setattr__(self, "degree", 1 + left.degree + right.degree)
        object.__setattr__(self, "variables", sorted(set(left.variables) | set(right.variables)))

    @classmethod
    def var(cls, name: str) -> "Expression":
        return cls("var", name)

    @classmethod
    def binop(cls, left: "Expression", right: "Expression") -> "Expression":
        return cls("binop", None, (left, right))

    @property
    def variable(self) -> str:
        if self.data != "var":
            raise ValueError("Only variable expressions have a variable name")
        if self.value is None:
            raise ValueError("Variable expressions require a value")
        return self.value

    def assign(self, assignments: Mapping[str, TreeLike]) -> "Expression":
        """Return a new expression with variables substituted."""
        if self.data == "var":
            return _as_expression(assignments.get(self.variable, self))

        left, right = self.children
        return Expression.binop(left.assign(assignments), right.assign(assignments))

    @staticmethod
    def from_str(expr_str: str) -> Expression:
        return parse_equation(f'{expr_str} = unused').lhs

    def __repr__(self) -> str:
        return f'Expression.from_str("{self.string}")'

    def __str__(self) -> str:
        return self.string

    def __hash__(self) -> int:
        return hash((self.data, self.string))


@dataclass(frozen=True)
class Equation:
    """Immutable equation with string form, degree, and variable metadata."""

    lhs: Expression
    rhs: Expression
    lean_name: Optional[str]
    string: str = field(init=False)
    string_representation: str = field(init=False)
    degree: int = field(init=False)
    variables: list[str] = field(init=False)
    data: str = field(init=False, default="equation")

    def __post_init__(self) -> None:
        string = f"{self.lhs} = {self.rhs}"
        object.__setattr__(self, "data", "equation")
        object.__setattr__(self, "string", string)
        object.__setattr__(self, "string_representation", string)
        object.__setattr__(self, "degree", self.lhs.degree + self.rhs.degree)
        object.__setattr__(self, "variables", sorted(set(self.lhs.variables) | set(self.rhs.variables)))

    def assign(self, assignments: Mapping[str, TreeLike]) -> "Equation":
        """Return a new equation with variables substituted."""
        return Equation(self.lhs.assign(assignments), self.rhs.assign(assignments), None)

    def infer_direct_equality(self, expression: Expression) -> Optional[Expression]:
        """
        Give an equivalent expression, or None if not found
        """
        if expression == self.lhs:
            return self.rhs
        elif expression == self.rhs:
            return self.lhs
        return None
    
    def infer_equalities(
            self,
            expression: Expression,
            free_variable_assignments: Optional[list[TreeLike]] = None
        ) -> list[tuple[Expression, str]]:
        """
        Give a list of expressions equal to parameter.
        For example, if the equation is y ◇ x = x ◇ y, and expression is x ◇ (x ◇ y), the results will be:
        * x ◇ (y ◇ x)
        * (x ◇ y) ◇ x
        For example, if the equation is x = x ◇ x, and expression is x ◇ y, the result is
        * (x ◇ x) ◇ y)
        * (x ◇ (y ◇ y)
        Returns a list of expression, and proof as LEAN string
        """

        def match(pattern: Expression, target: Expression, bindings: dict[str, Expression]) -> Optional[dict[str, Expression]]:
            if pattern.data == "var":
                bound = bindings.get(pattern.variable)
                if bound is not None:
                    return bindings if bound == target else None
                return {**bindings, pattern.variable: target}

            if target.data != "binop":
                return None

            left_match = match(pattern.children[0], target.children[0], bindings)
            if left_match is None:
                return None
            return match(pattern.children[1], target.children[1], left_match)

        assignment_options = tuple(_as_expression(value) for value in (free_variable_assignments or []))

        def instantiate(pattern: Expression, bindings: Mapping[str, Expression]) -> Expression:
            if pattern.data == "var":
                return bindings[pattern.variable]
            left, right = pattern.children
            return Expression.binop(instantiate(left, bindings), instantiate(right, bindings))

        def instantiate_all(pattern: Expression, bindings: Mapping[str, Expression]) -> list[tuple[Expression, str]]:
            free_variables = [variable for variable in pattern.variables if variable not in bindings]
            if not free_variables:
                binding_var_str = [bindings[k].string for k in sorted(bindings)]
                binding_var_str = [v if len(v) == 1 else f'({v})' for v in binding_var_str]
                binding_str = ' '.join(binding_var_str)
                return [(instantiate(pattern, bindings), f'{self.lean_name} {binding_str}')]
            if not assignment_options:
                return []

            instances: list[tuple[Expression, str]] = []
            for assignment_values in product(assignment_options, repeat=len(free_variables)):
                all_bindings = {**bindings, **dict(zip(free_variables, assignment_values))}
                binding_var_str = [all_bindings[k].string for k in sorted(all_bindings)]
                binding_var_str = [v if len(v) == 1 else f'({v})' for v in binding_var_str]
                binding_str = ' '.join(binding_var_str)
                instances.append((instantiate(pattern, all_bindings), f'{self.lean_name} {binding_str}'))
            return instances

        def add_result(results: list[tuple[Expression, str]], seen: set[Expression], result: tuple[Expression, str]) -> None:
            if result[0] not in seen:
                results.append(result)
                seen.add(result[0])

        def replacements_for(target: Expression, allow_variable_pattern: bool) -> list[tuple[Expression, str]]:
            replacements: list[tuple[Expression, str]] = []
            seen: set[Expression] = set()

            for pattern, replacement in ((self.lhs, self.rhs), (self.rhs, self.lhs)):
                if pattern.data == "var" and not allow_variable_pattern:
                    continue
                bindings = match(pattern, target, {})
                if bindings is not None:
                    for instance, proof in instantiate_all(replacement, bindings):
                        if pattern == self.rhs:
                            # Reverse assignment, use symmetry
                            proof = f'({proof}).symm'
                        add_result(replacements, seen, (instance, proof))

            return replacements

        def rewrite_once(target: Expression) -> list[tuple[Expression, str]]:
            results: list[tuple[Expression, str]] = []
            seen: set[Expression] = set()

            if target.data == "binop":
                left, right = target.children
                for replacement, lean_str in rewrite_once(left):
                    result_expr = Expression.binop(replacement, right)
                    proof = f'congrArg (fun t => t ◇ ({right.string})) ({lean_str})'
                    add_result(results, seen, (result_expr, proof))
                for replacement, lean_str in rewrite_once(right):
                    result_expr = Expression.binop(left, replacement)
                    proof = f'congrArg (fun t => ({left.string}) ◇ t) ({lean_str})'
                    add_result(results, seen, (result_expr, proof))

            for replacement, lean_str in replacements_for(target, target.data == "var" or bool(assignment_options)):
                add_result(results, seen, (replacement, lean_str))

            return results

        return rewrite_once(expression)

    @staticmethod
    def from_str(eq_str: str) -> Equation:
        return parse_equation(eq_str)

    def __repr__(self) -> str:
        return f'Equation.from_str("{self.string}")'

    def __str__(self) -> str:
        return self.string

    def __hash__(self) -> int:
        return hash((self.data, self.string))


def _as_expression(value: TreeLike) -> Expression:
    if isinstance(value, Expression):
        return value
    raise ValueError(f"Expected expression, got {type(value).__name__}")


def _expression_to_string(expression: Expression, toplevel: bool = True) -> str:
    if expression.data == "var":
        return expression.variable
    if expression.data == "binop":
        binop_str = f"{_expression_to_string(expression.children[0], False)} ◇ {_expression_to_string(expression.children[1], False)}"
        return binop_str if toplevel else f"({binop_str})"
    raise ValueError(f"Unknown node type: {expression.data}")


def parse_equation(equation_str: str, lean_name: Optional[str] = None) -> Equation:
    def convert_expr(tree: lark.Tree) -> Expression:
        if tree.data == "var":
            return Expression.var(str(tree.children[0]))
        if tree.data == "binop":
            return Expression.binop(
                convert_expr(cast(lark.Tree, tree.children[0])),
                convert_expr(cast(lark.Tree, tree.children[1])),
            )
        raise ValueError(f"Invalid expression tree: {tree.data}")

    tree = parser.parse(equation_str)
    if tree.data != "equation" or len(tree.children) != 2:
        raise ValueError("Invalid equation tree")
    return Equation(
        convert_expr(cast(lark.Tree, tree.children[0])),
        convert_expr(cast(lark.Tree, tree.children[1])),
        lean_name,
    )


def all_expressions(variables: list[str], max_depth: int) -> list[Expression]:
    """
    Generate all possible expressions using the given variables and the binary operator ◇, up to a certain depth.
    """
    if max_depth < 0:
        return []

    unique_vars = list(dict.fromkeys(variables))

    def make_var(name: str) -> Expression:
        return Expression.var(name)

    by_depth: list[list[Expression]] = [[make_var(v) for v in unique_vars]]
    results: list[Expression] = list(by_depth[0])

    for depth in range(1, max_depth + 1):
        current: list[Expression] = []
        for left_depth in range(depth):
            right_depth = depth - 1 - left_depth

            current.extend(
                Expression.binop(left, right)
                for left in by_depth[left_depth]
                for right in by_depth[right_depth]
            )

        by_depth.append(current)
        results.extend(current)

    return results


def equation_to_string(equation: TreeLike, toplevel: bool = True) -> str:
    if isinstance(equation, Equation):
        return equation.string
    if isinstance(equation, Expression):
        return _expression_to_string(equation, toplevel)
    raise ValueError(f"Unknown node type: {type(equation).__name__}")


if __name__ == "__main__":
    equation = parse_equation("x ◇ y = z")
    print(equation)
    equation2 = equation.assign(
        {
            "x": parse_equation("a ◇ b = z").lhs,
            "y": parse_equation("c ◇ d = z").lhs,
            "z": parse_equation("e ◇ f = z").lhs,
        }
    )
    print(equation2)

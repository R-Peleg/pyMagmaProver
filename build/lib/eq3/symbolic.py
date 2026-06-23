"""
Functions for symbolic solving of proofs and counterexamples
"""
from __future__ import annotations

from collections.abc import Callable
from itertools import product
from typing import Any

import z3  # type: ignore[import-untyped]

from eq3.composite_solver import CompositeSolver, Solution
from eq3.equation_utils import Expression, parse_equation


ExprLike = Expression
BoolOp = Callable[[int, int], int]
AffineCoefficients = tuple[int, int, int]
AffineTerms = tuple[Any, Any, Any]


class TakeSided:
    """
    Checks both left and right Magma evaluation, returning all successful
    attempts (or just the first if return_all=False).
    """

    LEAN_OPS = {0: "fun x _ => x", 1: "fun _ x => x"}
    LABELS = {0: 'take-left', 1: 'take-right'}

    @staticmethod
    def _evaluate(expression: Expression, side: int) -> str:
        while True:
            if expression.data == 'binop':
                expression = expression.children[side]
            else:
                return expression.variable

    @staticmethod
    def _compliant(equation: Any, side: int) -> bool:
        if equation.data != 'equation':
            raise ValueError('invalid equation tree ' + str(equation))
        return TakeSided._evaluate(equation.lhs, side) == TakeSided._evaluate(equation.rhs, side)

    @staticmethod
    def try_solve(spec: Solution, return_all: bool = True) -> Solution:
        assumed_equations = spec['equations']
        target_equation = spec['target']
        results = []
        for side in (0, 1):
            valid = True
            for pos in assumed_equations:
                if not TakeSided._compliant(pos, side):
                    valid = False
                    break
            if not valid:
                continue
            if TakeSided._compliant(target_equation, side):
                continue
            axiom_proofs = ["fun _ _ => rfl" for _ in assumed_equations]
            lean_proof = "exact ⟨Bool, ⟨{}⟩, {}⟩".format(
                TakeSided.LEAN_OPS[side],
                ", ".join([*axiom_proofs, "fun h => Bool.noConfusion (h true false)"]),
            )
            result = {'vc-proof-negative': lean_proof, 'counterexample': TakeSided.LABELS[side]}
            if return_all:
                results.append(result)
            else:
                return result
        if return_all:
            if results:
                return {'solutions': results}
            return {}
        return {}


class BinaryOpSolver:
    """
    Interprets each variable as a bit and ◇ as a binary Boolean operation
    (XOR, AND, OR).  For each operation, checks whether all positive equations
    are identities and the negative equation is not.
    """

    _OPS = [
        ('xor', lambda a, b: a ^ b, 'Bool.xor'),
        ('and', lambda a, b: a & b, 'fun x y => x && y'),
        ('or',  lambda a, b: a | b, 'fun x y => x || y'),
    ]

    @staticmethod
    def _eval(expr: ExprLike, var_to_bit: dict[str, int], op: BoolOp) -> int:
        while True:
            if expr.data == 'binop':
                return op(BinaryOpSolver._eval(expr.children[0], var_to_bit, op),
                          BinaryOpSolver._eval(expr.children[1], var_to_bit, op))
            return var_to_bit.get(expr.variable, 0)

    @staticmethod
    def _is_identity(equation: Any, var_to_bit: dict[str, int], op: BoolOp) -> bool:
        if equation.data != 'equation':
            raise ValueError('invalid equation tree')
        return BinaryOpSolver._eval(equation.lhs, var_to_bit, op) == BinaryOpSolver._eval(equation.rhs, var_to_bit, op)

    @staticmethod
    def try_solve(spec: Solution, return_all: bool = True) -> Solution:
        assumed_equations = spec['equations']
        target_equation = spec['target']
        # TODO: fix
        var_list: list[str] = list(target_equation.variables)
        var_to_bit = {v: 1 << i for i, v in enumerate(var_list)}

        results = []
        for name, op, lean_op in BinaryOpSolver._OPS:
            ok = True
            for pos in assumed_equations:
                if not BinaryOpSolver._is_identity(pos, var_to_bit, op):
                    ok = False
                    break
            if not ok:
                continue
            if BinaryOpSolver._is_identity(target_equation, var_to_bit, op):
                continue

            holes = ', '.join('?_' for _ in range(len(assumed_equations) + 1))
            proof_steps = '\n'.join('· native_decide' for _ in range(len(assumed_equations) + 1))
            lean_proof = f'refine ⟨Bool, ⟨{lean_op}⟩, {holes}⟩\n{proof_steps}'
            result = {'vc-proof-negative': lean_proof, 'counterexample': name}
            if return_all:
                results.append(result)
            else:
                return result

        if return_all:
            if results:
                return {'solutions': results}
            return {}
        return {}


class FalseOpSolver:
    """
    Interprets ◇ as the constant-false operation: x ◇ y = false for all x, y.
    Any expression containing ◇ evaluates to false.
    """

    LABEL = 'false-op'

    _FALSE = 'False'

    @staticmethod
    def _eval(expr: ExprLike) -> str:
        while True:
            if expr.data == 'binop':
                return FalseOpSolver._FALSE
            return expr.variable

    @staticmethod
    def _compliant(equation: Any) -> bool:
        if equation.data != 'equation':
            raise ValueError('invalid equation tree')
        return FalseOpSolver._eval(equation.lhs) == FalseOpSolver._eval(equation.rhs)

    @staticmethod
    def try_solve(spec: Solution, return_all: bool = True) -> Solution:
        assumed_equations = spec['equations']
        target_equation = spec['target']
        for pos in assumed_equations:
            if not FalseOpSolver._compliant(pos):
                return {} if return_all else {}

        if FalseOpSolver._compliant(target_equation):
            return {} if return_all else {}

        holes = ', '.join('?_' for _ in range(len(assumed_equations) + 1))
        proof_steps = '\n'.join('· native_decide' for _ in range(len(assumed_equations) + 1))
        lean_proof = f'refine ⟨Bool, ⟨fun _ _ => false⟩, {holes}⟩\n{proof_steps}'
        result = {'vc-proof-negative': lean_proof, 'counterexample': FalseOpSolver.LABEL}
        if return_all:
            return {'solutions': [result]}
        return result


class AffineModSolver:
    """
    Searches affine magmas on Fin n of the form x ◇ y = a*x + b*y + c mod n.

    Z3 solves for coefficients satisfying all finite positive assignments and
    one target assignment witnessing failure.
    """

    def __init__(self, n: int) -> None:
        if n < 2:
            raise ValueError("AffineModSolver requires n >= 2")
        self.n = n

    def _z3_eval(self, expr: ExprLike, assignment: dict[str, Any], coefficients: AffineTerms) -> Any:
        if expr.data == 'binop':
            a, b, c = coefficients
            left = self._z3_eval(expr.children[0], assignment, coefficients)
            right = self._z3_eval(expr.children[1], assignment, coefficients)
            return (a * left + b * right + c) % self.n
        return assignment[expr.variable]

    def _add_identity_constraints(self, solver: z3.Solver, equation: Any, coefficients: AffineTerms) -> None:
        if equation.data != 'equation':
            raise ValueError('invalid equation tree')
        for values in product(range(self.n), repeat=len(equation.variables)):
            assignment = dict(zip(equation.variables, values))
            solver.add(
                self._z3_eval(equation.lhs, assignment, coefficients)
                == self._z3_eval(equation.rhs, assignment, coefficients)
            )

    def _add_target_violation(self, solver: z3.Solver, equation: Any, coefficients: AffineTerms) -> None:
        if equation.data != 'equation':
            raise ValueError('invalid equation tree')
        assignment = {variable: z3.Int(f'target_{variable}') for variable in equation.variables}
        for variable in assignment.values():
            solver.add(variable >= 0, variable < self.n)
        solver.add(self._z3_eval(equation.lhs, assignment, coefficients) != self._z3_eval(equation.rhs, assignment, coefficients))

    def _base_solver(self, assumed_equations: list[Any], target_equation: Any) -> tuple[z3.Solver, AffineTerms]:
        solver = z3.Solver()
        coefficients = (z3.Int('a'), z3.Int('b'), z3.Int('c'))
        for coefficient in coefficients:
            solver.add(coefficient >= 0, coefficient < self.n)
        for equation in assumed_equations:
            self._add_identity_constraints(solver, equation, coefficients)
        self._add_target_violation(solver, target_equation, coefficients)
        return solver, coefficients

    def _model_coefficients(self, model: z3.ModelRef, coefficients: AffineTerms) -> AffineCoefficients:
        values = tuple(model.evaluate(coefficient, model_completion=True).as_long() % self.n for coefficient in coefficients)
        return (values[0], values[1], values[2])

    def _lean_proof(self, assumptions_count: int, coefficients: AffineCoefficients) -> str:
        a, b, c = coefficients
        holes = ', '.join('?_' for _ in range(assumptions_count + 1))
        proof_steps = '\n'.join('· native_decide' for _ in range(assumptions_count + 1))
        lean_op = (
            f'fun x y => ⟨({a} * x.val + {b} * y.val + {c}) % {self.n}, '
            'Nat.mod_lt _ (by native_decide)⟩'
        )
        return f'refine ⟨Fin {self.n}, ⟨{lean_op}⟩, {holes}⟩\n{proof_steps}'

    def try_solve(self, spec: Solution, return_all: bool = True) -> Solution:
        assumed_equations = spec['equations']
        target_equation = spec['target']
        results = []
        solver, symbolic_coefficients = self._base_solver(assumed_equations, target_equation)

        while solver.check() == z3.sat:
            coefficients = self._model_coefficients(solver.model(), symbolic_coefficients)
            a, b, c = coefficients
            result = {
                'vc-proof-negative': self._lean_proof(len(assumed_equations), coefficients),
                'counterexample': f'affine-mod-{self.n}-a{a}-b{b}-c{c}',
            }
            if return_all:
                results.append(result)
            else:
                return result
            solver.add(z3.Or(
                symbolic_coefficients[0] != a,
                symbolic_coefficients[1] != b,
                symbolic_coefficients[2] != c,
            ))

        if return_all:
            if results:
                return {'solutions': results}
            return {}
        return {}


main_solver = CompositeSolver([TakeSided, BinaryOpSolver, FalseOpSolver, AffineModSolver(3)])

if __name__ == '__main__':
    t1 = parse_equation("x = (x ◇ (y ◇ (x ◇ z))) ◇ x")
    t2 = parse_equation("x = x ◇ (y ◇ ((z ◇ z) ◇ y))")
    t3 = parse_equation("x = y")
    spec = {'equations': [t1, t2], 'target': t3}
    print(TakeSided.try_solve(dict(spec), return_all=True))
    print(TakeSided.try_solve(dict(spec), return_all=False))
    print()
    print("BinaryOpSolver:")
    print(BinaryOpSolver.try_solve(dict(spec), return_all=True))
    print()
    print("FalseOpSolver:")
    print(FalseOpSolver.try_solve(dict(spec), return_all=True))
    print()
    print("CompositeSolver:")
    print(main_solver.try_solve(dict(spec), return_all=False))

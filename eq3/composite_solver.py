"""
Composite solver that delegates to a configurable list of solvers.
"""
from __future__ import annotations

from typing import Any


Solution = dict[str, Any]


class CompositeSolver:
    """Tries each solver in order and returns all counterexamples found."""

    def __init__(self, solvers: list[Any]) -> None:
        self.solvers = list(solvers)

    def try_solve(self, spec: Solution, return_all: bool = False) -> Solution | None:
        if return_all:
            all_solutions: list[Solution] = []
            for solver in self.solvers:
                result = solver.try_solve(spec, return_all=True)
                if result:
                    all_solutions.extend(result.get('solutions', []))
            return {'solutions': all_solutions} if all_solutions else {}
        else:
            for solver in self.solvers:
                result = solver.try_solve(spec, return_all=False)
                if result:
                    return result
            return None

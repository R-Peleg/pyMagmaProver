"""
Prove an equality by using path of equations.
"""
from __future__ import annotations

import itertools
from typing import Any

import networkx as nx

from eq3.composite_solver import Solution
from eq3.equation_utils import Equation, Expression


class EquationPathSolver:
    def __init__(self, max_degree: int = 3):
        self.max_degree = max_degree
        self.max_depth = 12

    def try_solve(self,
                  spec: Solution,
                  return_all: bool = False) -> Solution | None:
        if return_all:
            raise NotImplementedError("Finding all paths is not implemented yet.")

        assumed_equations: list[Equation] = spec['equations']
        target_equation = spec['target']
        all_variables = target_equation.variables
        all_variable_expr = [Expression.from_str(v) for v in all_variables]
        # Construct equation graph
        expression_graph: nx.DiGraph[Expression] = nx.DiGraph()
        # Start with LHS of the target equation
        # TODO: Flip equation if needed, or take sub-components.
        # For our case with x = y as target we're good
        current_bfs = [target_equation.lhs]
        next_bfs = []
        found = False
        for bfs_iteration in range(self.max_depth):
            for eq in assumed_equations:
                for lhs in current_bfs:
                    if lhs.degree > self.max_degree:
                        continue
                    for rhs, lean_string in eq.infer_equalities(lhs, all_variable_expr):
                        # Prevent self-loops
                        if lhs == rhs:
                            continue
                        # Limit degree
                        if rhs.degree > self.max_degree:
                            continue
                        # Prevent duplicated edges
                        if expression_graph.has_edge(lhs, rhs):
                            continue
                        # Experimental: prevent dual route
                        if rhs in expression_graph.nodes:
                            continue
                        # Prevent cycles
                        if expression_graph.has_edge(rhs, lhs):
                            continue
                        expression_graph.add_edge(lhs, rhs, equation=lean_string)
                        if rhs == target_equation.rhs:
                            found = True
                            break
                        next_bfs.append(rhs)
                    if found:
                        break
                if found:
                    break
            if found:
                break
            current_bfs = next_bfs
            next_bfs = []
        # Find paths from target_lhs to target_rhs
        if not found:
            return None
        path = nx.shortest_path(expression_graph, source=target_equation.lhs,
                                target=target_equation.rhs)

        lean_lines = [
            f'  intro {" ".join(all_variables)}',
            f'  calc'
        ]
        for currrent, next_expr in zip(path[:-1], path[1:]):
            edge_data: dict[str, Any] = expression_graph.get_edge_data(currrent, next_expr)
            lean_lines.append(f'   _ = {next_expr.string} := {edge_data["equation"]}')
        return {'vc-proof-positive': "\n".join(lean_lines)}


if __name__ == "__main__":
    from eq3.equation_utils import parse_equation
    solver = EquationPathSolver(max_degree=4)
    spec = {
        # 'equations': [('hX', parse_equation('x = y ◇ x')), ('hY', parse_equation('x ◇ y = y ◇ x'))],
        # Harder case
        'equations': [ parse_equation('x = x ◇ (x ◇ y)', 'hX'), parse_equation('x ◇ y = y ◇ x', 'hY')],
        'target': parse_equation('x = y'),
    }
    result = solver.try_solve(spec, return_all=False)
    assert result is not None
    print(result)
    print(result['vc-proof-positive'])

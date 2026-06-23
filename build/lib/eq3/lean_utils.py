import os
import subprocess
import tempfile
from typing import Any

from eq3.equation_utils import Equation


LeanSpec = dict[str, Any]


PREFIX = \
"""
class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op
"""

def eq_abbrev(entry: str, equation: Equation) -> str:
    vars_str = ' '.join(equation.variables)
    if vars_str:
        return f"abbrev {entry} (G : Type _) [Magma G] := ∀ {vars_str} : G, {equation.string}"
    return f"abbrev {entry} (G : Type _) [Magma G] := {equation.string}"


def equation_prop(equation: Equation, type_name: str = "G") -> str:
    vars_str = ' '.join(equation.variables)
    if vars_str:
        return f"∀ {vars_str} : {type_name}, {equation.string}"
    return equation.string


def cli_lean_spec(equations: list[Equation], target: Equation) -> LeanSpec:
    hypotheses = ' '.join(
        f"({equation.lean_name}: {equation_prop(equation)})"
        for equation in equations
    )
    positive_stmt = f"theorem eq3_positive (G: Type _) [Magma G] {hypotheses} : {equation_prop(target)} := by\n"
    negative_props = [equation_prop(equation) for equation in equations]
    negative_props.append(f"¬ {equation_prop(target)}")
    negative_body = ' ∧ '.join(f"({prop})" for prop in negative_props)
    negative_stmt = (
        "theorem eq3_negative "
        f": ∃ (G: Type) (_: Magma G), {negative_body} := by\n"
    )
    return {
        'vc-preamble': PREFIX + '\n',
        'vc-helpers': '',
        'vc-spec-positive': positive_stmt,
        'vc-spec-negative': negative_stmt,
        'vc-postamble': '',
    }

def eq3_lean_spec(entry: LeanSpec) -> LeanSpec:
    x_abbrev = eq_abbrev(entry['X'], entry['X_eq'])
    y_abbrev = eq_abbrev(entry['Y'], entry['Y_eq'])
    z_abbrev = eq_abbrev(entry['Z'], entry['Z_eq'])
    theorem_stmt = (
        f"theorem {entry['X']}_and_{entry['Y']}_implies_{entry['Z']} "
        f"(G: Type _) [Magma G] (hX: {entry['X']} G) (hY: {entry['Y']} G) : {entry['Z']} G := by\n"
    )
    counterexample_stmt = (
        f"theorem {entry['X']}_and_{entry['Y']}_not_implies_{entry['Z']} "
        f": ∃ (G: Type) (_: Magma G), {entry['X']} G ∧ {entry['Y']} G ∧ ¬ {entry['Z']} G := by\n"
    )
    return {
      'vc-helpers': '',
      'vc-preamble': f'{PREFIX}\n{x_abbrev}\n{y_abbrev}\n{z_abbrev}\n',
      'vc-spec-positive': theorem_stmt,
      'vc-spec-negative': counterexample_stmt,
      'vc-postamble': ''
    }


def spec_to_code(spec: LeanSpec) -> str:
    return (
        '-- <vc-preamble>\n' +
        spec['vc-preamble'] +
        '-- </vc-preamble>\n\n' +
        '-- <vc-helpers>\n' +
        spec['vc-helpers'] +
        '-- </vc-helpers>\n\n' +
        '-- <vc-spec-positive>\n' +
        spec['vc-spec-positive'] +
        '-- </vc-spec-positive>\n' +
        '-- <vc-proof-positive>\n' +
        '   sorry\n' +
        '-- </vc-proof-positive>\n\n' +
        '-- <vc-spec-negative>\n' +
        spec['vc-spec-negative'] +
        '-- </vc-spec-negative>\n' +
        '-- <vc-proof-negative>\n' +
        '   sorry\n' +
        '-- </vc-proof-negative>' +
        spec['vc-postamble']
    )

def solution_to_code(entry: LeanSpec) -> str:
    has_positive_solution = bool(entry.get('vc-proof-positive'))
    has_negative_solution = bool(entry.get('vc-proof-negative'))
    if not has_positive_solution and not has_negative_solution:
        raise ValueError('No solution at all found')
    if has_positive_solution and has_negative_solution:
        raise ValueError('Cannot have both positive and negative solution')
    if has_positive_solution:
        proof_part = (
            '-- <vc-spec-positive>\n' +
            entry['vc-spec-positive'] +
            '-- </vc-spec-positive>\n' +
            '-- <vc-proof-positive>\n' +
            entry['vc-proof-positive'] + '\n' +
            '-- </vc-proof-positive>\n\n'
        )
    else:
        proof_part = (
            '-- <vc-spec-negative>\n' +
            entry['vc-spec-negative'] +
            '-- </vc-spec-negative>\n' +
            '-- <vc-proof-negative>\n' +
            entry['vc-proof-negative'] + '\n' +
            '-- </vc-proof-negative>\n\n'
        )

    return (
        '-- <vc-preamble>\n' +
        entry['vc-preamble'] +
        '-- </vc-preamble>\n\n' +
        '-- <vc-helpers>\n' +
        entry['vc-helpers'] +
        '-- </vc-helpers>\n\n' +
        proof_part +
        entry['vc-postamble']
    )


def solution_to_plain_code(entry: LeanSpec) -> str:
    has_positive_solution = bool(entry.get('vc-proof-positive'))
    has_negative_solution = bool(entry.get('vc-proof-negative'))
    if not has_positive_solution and not has_negative_solution:
        raise ValueError('No solution at all found')
    if has_positive_solution and has_negative_solution:
        raise ValueError('Cannot have both positive and negative solution')

    if has_positive_solution:
        proof_part = entry['vc-spec-positive'] + entry['vc-proof-positive'] + '\n'
    else:
        proof_part = entry['vc-spec-negative'] + entry['vc-proof-negative'] + '\n'

    return entry['vc-preamble'] + entry['vc-helpers'] + proof_part + entry['vc-postamble']


def check_solution_with_lean(code: str, *, workdir: str | None = None) -> tuple[bool, str]:
    """Run Lean on a generated solution file and return (ok, output)."""
    lean_bin = os.environ.get('LEAN', 'lean')
    with tempfile.NamedTemporaryFile('w', suffix='.lean', dir=workdir, delete=False) as f:
        f.write(code)
        path = f.name
    try:
        cmd = [lean_bin, path]
        if workdir and os.path.exists(os.path.join(workdir, 'lakefile.lean')):
            cmd = ['lake', 'env', lean_bin, path]
        proc = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            check=False,
            cwd=workdir
        )
        output = (proc.stdout or '') + (proc.stderr or '')
        return proc.returncode == 0, output.strip()
    finally:
        try:
            os.unlink(path)
        except FileNotFoundError:
            pass

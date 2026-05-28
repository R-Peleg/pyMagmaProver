# pyMagmaProver

`pyMagmaProver` searches for simple proofs and counterexamples for equations over a magma with one binary operation, written as `◇`.

It can be used as a Python package or through the installed `eq3` command.

## Install

```bash
pip install .
```

For development:

```bash
pip install -e '.[dev]'
```

The optional dataset demo also needs HTTP/progress dependencies:

```bash
pip install -e '.[demo]'
```

## Equation Syntax

Equations use variables, parentheses, and the binary operator `◇`:

```text
x ◇ y = y ◇ x
x = x ◇ (x ◇ y)
```

Variable names use Python/Lark-style identifiers such as `x`, `y`, `foo`.

## CLI Usage

Prove or disprove whether axioms imply a target:

```bash
eq3 --axiom 'x ◇ y = y ◇ x' --axiom 'x = x ◇ (x ◇ y)' --target 'x = y' --mode both
```

For convenience, it is possible to use '*' instead of '◇'

Modes:

```text
prove      only try proof search
disprove   only try counterexample search
both       try proof search, then counterexample search
```

You can select a mode with `--mode prove`, `--mode disprove`, `--mode both`, or the shortcut flags `--prove`, `--disprove`, and `--both`.

Results are one of:

```text
proved
disproved
unknown
```

JSON output:

```bash
eq3 --axiom 'x ◇ y = y ◇ x' --target 'x = y' --mode disprove --format json
```

Use a JSON config file:

```json
{
  "axioms": ["x ◇ y = y ◇ x", "x = x ◇ (x ◇ y)"],
  "target": "x = y",
  "mode": "both",
  "max_degree": 4,
  "format": "json"
}
```

```bash
eq3 --config config.json
```

Command-line options override or extend config values. Repeated `--axiom` values are added to config axioms.

## Inference Mode

List all one-step equations inferred from the axioms over generated expressions:

```bash
eq3 --infer --axiom 'x ◇ y = y ◇ x' --max-depth 1 --format json
```

Useful options:

```text
--variable NAME   add an inference variable not present in the axioms
--max-depth N     generate expressions up to depth N
--max-degree N    ignore expressions above degree N
```

## Python API

```python
from eq3.cli import solve, infer

print(solve(["x ◇ y = y ◇ x"], "x = y", mode="disprove"))
print(infer(["x ◇ y = y ◇ x"], max_depth=1))
```

Lower-level immutable objects are available from `eq3.equation_utils`:

```python
from eq3.equation_utils import parse_equation

equation = parse_equation("x ◇ y = y ◇ x")
print(equation.lhs)
print(equation.rhs)
```

Parsing uses Lark internally only when initializing equations and expressions. Stored equations and expressions are native immutable Python dataclasses.

## Demo

The previous commutativity dataset experiment lives in:

```bash
python demo/find_trivial_with_commutativity.py
```

It downloads external data and can generate Lean proof files under `proofs/`.

## Lean

Some utilities can emit Lean proof fragments. To check generated Lean files, install Lean 4 with `elan` and use the existing Lake project under `proofs/`.

## Tests

```bash
.venv/bin/python -m pytest
```

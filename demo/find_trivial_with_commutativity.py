"""
A script to search for equations that satisfy: Equation and commutativity -> Singleton

Builds the implication graph, then iteratively tests each equation using the
two-sided projection method to determine if it (together with commutativity)
implies the singleton magma (Equation2: x = y). Results are propagated through
the implication graph.
"""
from __future__ import annotations

import json
import gzip
import os
import shutil
import time
from typing import Any

import networkx as nx
import requests
from tqdm import tqdm

from eq3.equation_utils import parse_equation
from eq3.symbolic import TakeSided, BinaryOpSolver, FalseOpSolver
from eq3.equation_path import EquationPathSolver
from eq3.composite_solver import CompositeSolver
from eq3.lean_utils import (
    spec_to_code, solution_to_code, check_solution_with_lean,
    eq3_lean_spec, PREFIX
)

DATASET_URL = "https://teorth.github.io/equational_theories/raw_data/general.json.gz"
LOCAL_PATH = "data/general.json.gz"
EXTRACT_PATH = LOCAL_PATH.replace(".gz", "")
EQUATIONS_URL = 'https://raw.githubusercontent.com/teorth/equational_theories/refs/heads/main/data/equations.txt'
LOCAL_EQUATIONS_FILE = 'equations.txt'
RUN_LEAN = False

main_solver = CompositeSolver([
    TakeSided, BinaryOpSolver, FalseOpSolver, EquationPathSolver(max_degree=4)])

PROOFS_DIR = "proofs"


def download_if_needed() -> None:
    if not os.path.exists(LOCAL_PATH):
        print(f"Downloading dataset from {DATASET_URL}...")
        response = requests.get(DATASET_URL)
        with open(LOCAL_PATH, "wb") as f:
            f.write(response.content)
        print("Download complete.")
        extract_dataset()
    else:
        print("Dataset already exists locally.")
    if not os.path.exists(LOCAL_EQUATIONS_FILE):
        print(f"Downloading equations file from {EQUATIONS_URL}...")
        response = requests.get(EQUATIONS_URL)
        with open(LOCAL_EQUATIONS_FILE, "wb") as f:
            f.write(response.content)
        print("Equations file downloaded.")
    else:
        print("Equations file already exists locally.")


def extract_dataset() -> None:
    print(f"Extracting {LOCAL_PATH}...")
    with gzip.open(LOCAL_PATH, "rb") as f_in:
        with open(EXTRACT_PATH, "wb") as f_out:
            shutil.copyfileobj(f_in, f_out)
    print(f"Extraction complete. File saved to {EXTRACT_PATH}.")


def eq_number(eq_id: str) -> int:
    return int(eq_id[len('Equation'):])

def trivial_commutativity_spec(eq_id: str, eq_str: str) -> dict[str, Any]:
    """Create a spec dict for the problem: equation + commutativity -> singleton."""
    eq_obj = parse_equation(eq_str)
    comm_obj = parse_equation('x ◇ y = y ◇ x')
    singleton = parse_equation('x = y')
    entry = {
        'X': eq_id,
        'X_str': eq_str,
        'X_eq': eq_obj,
        'Y': 'commutativity',
        'Y_str': 'x ◇ y = y ◇ x',
        'Y_eq': comm_obj,
        'Z': 'singleton',
        'Z_str': 'x = y',
        'Z_eq': singleton,
    }
    lean_spec = eq3_lean_spec(entry)
    return {
        'vc-preamble': lean_spec['vc-preamble'],
        'vc-helpers': '',
        'vc-spec-positive': lean_spec['vc-spec-positive'],
        'vc-spec-negative': lean_spec['vc-spec-negative'],
        'vc-postamble': '',
        'equations': [eq_obj, comm_obj],
        'target': singleton,
    }


def main() -> tuple[dict[str, Any], dict[str, str], dict[str, str], list[str], list[str], list[str]]:
    t_start = time.time()
    download_if_needed()

    data = json.load(open(EXTRACT_PATH))

    G: nx.DiGraph[str] = nx.DiGraph()
    for imp in data['implications']:
        G.add_edge(imp['lhs'], imp['rhs'])

    with open(LOCAL_EQUATIONS_FILE, 'r') as f:
        equations = [line.strip() for line in f]

    def eq_string(eq_id: str) -> str:
        idx = eq_number(eq_id)
        if 0 < idx <= len(equations):
            return equations[idx - 1]
        return f"(equation {idx})"

    status: dict[str, Any] = {node: 'not_tried' for node in G.nodes}
    reason: dict[str, str] = {}
    counterexample: dict[str, str] = {}

    status['Equation2'] = True
    reason['Equation2'] = 'initial_true'
    for pred in nx.ancestors(G, 'Equation2'):
        if status[pred] == 'not_tried':
            status[pred] = True
            reason[pred] = 'propagate_true'

    parsed: dict[str, Any] = {}
    def get_parsed(eq_id: str) -> Any:
        if eq_id not in parsed:
            try:
                parsed[eq_id] = parse_equation(eq_string(eq_id))
            except Exception:
                parsed[eq_id] = None
        return parsed[eq_id]

    os.makedirs(PROOFS_DIR, exist_ok=True)
    with tqdm(total=len(G.nodes), desc="Testing equations") as pbar:
        while True:
            not_tried = [n for n in G.nodes if status[n] == 'not_tried']
            if not not_tried:
                break

            parsable = [n for n in not_tried if get_parsed(n) is not None]
            if not parsable:
                break

            parsable.sort(key=eq_number)
            eq_id = parsable[0]

            spec = trivial_commutativity_spec(eq_id, eq_string(eq_id))
            solution = main_solver.try_solve(spec, return_all=False)
            if solution is None:
                status[eq_id] = 'UNKNOWN'
                reason[eq_id] = 'unknown'
                pbar.update(1)
                continue

            if 'vc-proof-negative' in solution:
                status[eq_id] = False
                cex_label = solution['counterexample']
                counterexample[eq_id] = cex_label
                reason[eq_id] = 'test_counterexample'
                for succ in nx.descendants(G, eq_id):
                    if status[succ] == 'not_tried':
                        status[succ] = False
                        counterexample[succ] = cex_label
                        reason[succ] = 'propagate_false'
                        pbar.update(1)
            elif 'vc-proof-positive' in solution:
                solution_full_dict = {
                    **spec,
                    "vc-proof-positive": solution['vc-proof-positive']
                }
                lean_code = solution_to_code(solution_full_dict)
                if RUN_LEAN:
                    ok, lean_output = check_solution_with_lean(lean_code, workdir=PROOFS_DIR)
                else:
                    ok, lean_output = True, ''
                if not ok:
                    raise RuntimeError(f"Lean verification failed for {eq_id}:\n{lean_output}")
                with open(os.path.join(PROOFS_DIR, f"{eq_id}.lean"), 'w') as f:
                    f.write(lean_code)
                status[eq_id] = True
                reason[eq_id] = 'test_proof'
                pbar.update(1)
                for pred in nx.ancestors(G, eq_id):
                    if status[pred] in ('UNKNOWN', 'not_tried'):
                        status[pred] = True
                        reason[pred] = 'propagate_true'
                        if status[pred] == 'not_tried':
                            pbar.update(1)
            else:
                status[eq_id] = 'UNKNOWN'
                reason[eq_id] = 'unknown'

            pbar.update(1)

    # Anything still not_tried is unparseable
    for n in G.nodes:
        if status[n] == 'not_tried':
            status[n] = 'UNKNOWN'
            reason[n] = 'unparseable'

    t_elapsed = time.time() - t_start

    # Collect statistics by reason
    true_from_test = sum(1 for r in reason.values() if r == 'test_proof')
    true_from_prop = sum(1 for r in reason.values() if r == 'propagate_true')
    false_from_test = sum(1 for r in reason.values() if r == 'test_counterexample')
    false_from_prop = sum(1 for r in reason.values() if r == 'propagate_false')
    unknown_count = sum(1 for r in reason.values() if r in ('unparseable', 'unknown'))

    true_eqs = sorted([n for n in status if status[n] is True and n != 'Equation2'], key=eq_number)
    false_eqs = sorted([n for n in status if status[n] is False], key=eq_number)
    unknown_eqs = sorted([n for n in status if status[n] == 'UNKNOWN'], key=eq_number)

    m, s = divmod(t_elapsed, 60)
    h, m = divmod(m, 60)

    print(f"Timing: {int(h)}h {int(m)}m {s:.1f}s")
    print()
    print(f"Total equations in graph: {len(G.nodes)}")
    print(f"  True:  {len(true_eqs) + 1} total  ({true_from_test} by direct proof, {true_from_prop} by True propagation)")
    print(f"  False: {len(false_eqs)} total  ({false_from_test} by counterexample, {false_from_prop} by False propagation)")
    print(f"  UNKNOWN: {unknown_count}")
    print()

    if true_eqs:
        print("True equations (first 30):")
        for eid in true_eqs[:30]:
            tag = '  test' if reason.get(eid) == 'test_proof' else '  prop'
            print(f"  {eid}: {eq_string(eid)}  [{tag}]")
        if len(true_eqs) > 30:
            print(f"  ... and {len(true_eqs) - 30} more")
        print()

    if false_eqs:
        print("False equations (first 30):")
        for eid in false_eqs[:30]:
            tag = '  test' if reason.get(eid) == 'test_counterexample' else '  prop'
            cex = counterexample.get(eid, '?')
            print(f"  {eid}: {eq_string(eid)}  [{tag}]  cex={cex}")
        if len(false_eqs) > 30:
            print(f"  ... and {len(false_eqs) - 30} more")
        print()

    if unknown_eqs:
        print("UNKNOWN equations (first 30):")
        for eid in unknown_eqs[:30]:
            print(f"  {eid}: {eq_string(eid)}")
        if len(unknown_eqs) > 30:
            print(f"  ... and {len(unknown_eqs) - 30} more")
        print()

    return status, reason, counterexample, true_eqs, false_eqs, unknown_eqs


if __name__ == "__main__":
    main()

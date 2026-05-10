#!/usr/bin/env python3
"""
Pit the **HQIV geometric pipeline** (prime encode → Ω → moiré patch → BST on cumulative |ΔS|)
against **ground truth**:

* **3-CNF suite:** every entry in :data:`hqiv_geometric_3sat_demo.ALL_SAT_BENCHMARKS` — SAT label via
  brute force (small ``n_vars``).
* **General CNF:** DIMACS parse → :class:`FormulaCNF` — same geometry; SAT label via brute force if
  ``n_vars ≤ 22`` else optional **pycosat** when installed.

The third column is **``sat_at_bst_j_first``**: :func:`~hqiv_geometric_3sat_demo.eval_sat_at_patch_index`
at the BST crossing index — a **real** clause check, not the old ``cum_total >= 1`` toy
(``legacy_cum_total_guess_sat``).

This script **does not** claim early/late fraction rules or the BST assignment are sound SAT solvers;
it reports **match rates** so you can see the gap (cf. ``test_hqiv_geometric_3sat_heuristics.py``).

Examples::

  python3 scripts/hqiv_geometric_ksat_benchmark.py --suite
  python3 scripts/hqiv_geometric_ksat_benchmark.py --cnf scripts/who_owns_the_zebra.cnf
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import sys
from pathlib import Path
from typing import Any

_scripts = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("hqiv_geometric_3sat_demo", _scripts / "hqiv_geometric_3sat_demo.py")
_g3 = importlib.util.module_from_spec(_spec)
assert _spec.loader is not None
sys.modules["hqiv_geometric_3sat_demo"] = _g3
_spec.loader.exec_module(_g3)


def parse_dimacs_cnf(path: Path) -> _g3.FormulaCNF:
    """Parse DIMACS CNF; clauses may have any positive length (multi-line clauses allowed)."""

    nvars = 0
    clauses: list[tuple[_g3.Literal, ...]] = []
    cur: list[_g3.Literal] = []
    for raw in path.read_text().splitlines():
        line = raw.strip()
        if not line or line.startswith("c"):
            continue
        if line.startswith("p"):
            parts = line.split()
            if len(parts) < 4 or parts[1] != "cnf":
                raise ValueError(f"bad preamble: {line!r}")
            nvars = int(parts[2])
            continue
        for x in line.split():
            v = int(x)
            if v == 0:
                clauses.append(tuple(cur))
                cur = []
            else:
                var = abs(v) - 1
                if var < 0 or var >= nvars:
                    raise ValueError(f"literal {v} out of range for nvars={nvars}")
                cur.append(_g3.Literal(var, neg=(v < 0)))
    if cur:
        raise ValueError(f"{path}: unfinished clause")
    if nvars < 1:
        raise ValueError("no problem line or nvars < 1")
    return _g3.FormulaCNF(num_vars=nvars, clauses=tuple(clauses))


def _try_pycosat_satisfiable(clauses: list[list[int]]) -> bool | None:
    try:
        import pycosat  # type: ignore[import-not-found]
    except ImportError:
        return None
    sol = pycosat.solve(clauses)
    return sol != "UNSAT"


def dimacs_clauses_for_pycosat(path: Path) -> list[list[int]]:
    """Clauses as lists of non-zero DIMACS integers (pycosat format)."""

    out: list[list[int]] = []
    cur: list[int] = []
    for raw in path.read_text().splitlines():
        line = raw.strip()
        if not line or line.startswith("c") or line.startswith("p"):
            continue
        for x in line.split():
            v = int(x)
            if v == 0:
                out.append(cur)
                cur = []
            else:
                cur.append(v)
    if cur:
        raise ValueError("unfinished clause")
    return out


def run_one(
    name: str,
    formula: _g3.Formula3SAT | _g3.FormulaCNF,
    *,
    sat_ref: bool | None,
) -> dict[str, Any]:
    pipe = _g3.run_geometric_cnf_pipeline(formula, include_moire_checker=False)
    gh = pipe["geometry_heuristics"]
    row: dict[str, Any] = {
        "name": name,
        "n_vars": pipe["n_vars"],
        "n_clauses": pipe["n_clauses"],
        "M_bit_length": pipe["M_bit_length"],
        "omega_literal_sum": pipe["omega_literal_sum"],
        "sat_ref": sat_ref,
        "sat_bruteforce": pipe["sat_bruteforce"],
        "frac_j_first": gh.get("frac_j_first"),
        "guess_early_cross_sat": gh["guess_early_cross_sat"],
        "guess_late_cross_sat": gh["guess_late_cross_sat"],
        "sat_at_bst_j_first": gh["sat_at_bst_j_first"],
        "legacy_cum_total_guess_sat": gh["legacy_cum_total_guess_sat"],
    }
    truth = sat_ref if sat_ref is not None else pipe["sat_bruteforce"]
    if truth is not None:
        for key in ("guess_early_cross_sat", "guess_late_cross_sat", "sat_at_bst_j_first"):
            row[f"match_{key}"] = bool(row[key]) == truth
    return row


def suite_rows() -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for name, fm, exp_sat, _wit, _note in _g3.ALL_SAT_BENCHMARKS:
        out.append(run_one(name, fm, sat_ref=exp_sat))
    return out


def summarize(rows: list[dict[str, Any]]) -> dict[str, Any]:
    keys = ("guess_early_cross_sat", "guess_late_cross_sat", "sat_at_bst_j_first")
    mk = [f"match_{k}" for k in keys]
    summary: dict[str, Any] = {"n": len(rows), "heuristics": {}}
    for mkey in mk:
        vals = [r[mkey] for r in rows if mkey in r]
        if not vals:
            continue
        summary["heuristics"][mkey] = {"correct": sum(1 for v in vals if v), "total": len(vals)}
    return summary


def main() -> None:
    p = argparse.ArgumentParser(description="Geometry vs SAT labels (suite + DIMACS CNF)")
    p.add_argument("--suite", action="store_true", help="run ALL_SAT_BENCHMARKS (3-CNF)")
    p.add_argument("--cnf", type=Path, help="general CNF file (e.g. zebra)")
    p.add_argument("--json", action="store_true")
    args = p.parse_args()

    rows: list[dict[str, Any]] = []

    if args.suite:
        rows.extend(suite_rows())

    if args.cnf:
        path = args.cnf
        if not path.is_file():
            p.error(f"not a file: {path}")
        fm = parse_dimacs_cnf(path)
        sat_ref: bool | None = None
        if fm.num_vars <= 22:
            sat_ref, _ = _g3.is_satisfiable_bruteforce(fm)
        else:
            sat_ref = _try_pycosat_satisfiable(dimacs_clauses_for_pycosat(path))
        rec = run_one(path.name, fm, sat_ref=sat_ref)
        rec["cnf_path"] = str(path)
        rec["sat_ref_source"] = "bruteforce" if fm.num_vars <= 22 else "pycosat"
        rows.append(rec)

    if not rows:
        p.error("need --suite and/or --cnf")

    summ = summarize(rows)
    if args.json:
        print(json.dumps({"summary": summ, "rows": rows}, indent=2))
    else:
        print("HQIV geometric pipeline vs SAT labels\n")
        print(json.dumps(summ, indent=2))
        for r in rows:
            print(
                f"{r.get('name', r.get('cnf_path'))}: sat_ref={r.get('sat_ref')}  "
                f"early={r['guess_early_cross_sat']} late={r['guess_late_cross_sat']} "
                f"sat@bst={r['sat_at_bst_j_first']}  frac_j_first={r.get('frac_j_first')}"
            )


if __name__ == "__main__":
    main()

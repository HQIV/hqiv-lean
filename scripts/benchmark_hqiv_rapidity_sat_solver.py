#!/usr/bin/env python3
"""
**Legacy / regression:** random k-SAT timing for ``hqiv_rapidity_frontier_sat_solver`` backends.

For **candidate encodings** that target the open Lean interfaces (``RibbonCoverCollapseData``,
plane bridge, ``SATSharedManifold`` dimensions, Ω(M) pegs, etc.), use
``scripts/hqiv_lean_encoding_pegs.py`` instead — this file is **not** the main HQIV encoding
experiment harness.

**Default backend is PySAT** (MiniSat-class CDCL): the instrumented DPLL in the solver script
is intended for small instances and certificate metrics; random k-SAT at large ``n`` requires a
modern CDCL engine.

**Random 3-SAT hardness:** at the critical clause/variable ratio (about **4.26** for large ``n``),
individual instances can take orders of magnitude longer than the same ``n`` at ratio **3–3.5**.
For "large but finishes quickly" smoke tests, prefer ``--ratio 3`` or ``--ratio 3.5``; use the
default clause count (~``4.26 * n``) when you intentionally want hard random instances.

Examples::

  # Quick random 3-SAT (PySAT), 50 variables, 200 clauses × 30 samples
  python3 scripts/benchmark_hqiv_rapidity_sat_solver.py --n-vars 50 --clauses 200 --samples 30

  # Larger run (tens of thousands of clauses)
  python3 scripts/benchmark_hqiv_rapidity_sat_solver.py --n-vars 2000 --clauses 8000 --samples 5 --seed 1

  # Stress: many variables (adjust clauses to stay ~4.26 * n for hard-ish random 3-SAT)
  python3 scripts/benchmark_hqiv_rapidity_sat_solver.py --n-vars 8000 --ratio 4.26 --samples 3

  # Compare DPLL vs PySAT on *small* CNFs only (DPLL will be slow / use --max-nodes)
  python3 scripts/benchmark_hqiv_rapidity_sat_solver.py --n-vars 18 --clauses 80 --samples 50 --backend both

  python3 scripts/benchmark_hqiv_rapidity_sat_solver.py --json
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import random
import statistics
import sys
import time
from pathlib import Path
from typing import Any


def _load_solver():
    scripts = Path(__file__).resolve().parent
    spec = importlib.util.spec_from_file_location(
        "hqiv_rapidity_frontier_sat_solver", scripts / "hqiv_rapidity_frontier_sat_solver.py"
    )
    mod = importlib.util.module_from_spec(spec)
    sys.modules["hqiv_rapidity_frontier_sat_solver"] = mod
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod


def random_ksat(n_vars: int, n_clauses: int, k: int, rng: random.Random) -> list[list[int]]:
    if n_vars < k:
        raise ValueError(f"need n_vars >= k for sampling without replacement, got n_vars={n_vars}, k={k}")
    clauses: list[list[int]] = []
    for _ in range(n_clauses):
        vs = rng.sample(range(1, n_vars + 1), k)
        lits = [v if rng.random() < 0.5 else -v for v in vs]
        clauses.append(lits)
    return clauses


def bench_pysat(clauses: list[list[int]], solver_name: str) -> tuple[bool, float]:
    from pysat.solvers import Solver

    t0 = time.perf_counter()
    with Solver(name=solver_name) as slv:
        for c in clauses:
            slv.add_clause(c)
        ok = slv.solve()
    return ok, time.perf_counter() - t0


def bench_dpll(mod, clauses: list[list[int]], n_vars: int, max_nodes: int | None) -> tuple[bool | None, float]:
    st = mod.DPLLStats()
    t0 = time.perf_counter()
    r = mod.dpll_satisfiable([c[:] for c in clauses], n_vars, st, max_nodes=max_nodes)
    return r, time.perf_counter() - t0


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description="Benchmark HQIV rapidity-frontier SAT backends")
    p.add_argument("--n-vars", type=int, default=100, help="number of variables")
    p.add_argument(
        "--clauses",
        type=int,
        default=None,
        help="number of clauses (if omitted, use --ratio * n_vars)",
    )
    p.add_argument(
        "--ratio",
        type=float,
        default=None,
        help="clause count = floor(ratio * n_vars); default 4.26 if neither --clauses nor --ratio set",
    )
    p.add_argument("--k", type=int, default=3, help="literals per clause (k-SAT)")
    p.add_argument("--samples", type=int, default=20, help="number of random formulas")
    p.add_argument("--seed", type=int, default=0)
    p.add_argument(
        "--backend",
        choices=("pysat", "dpll", "both"),
        default="pysat",
        help="pysat = CDCL (default); dpll = instrumented solver; both = compare on same CNFs (small n only)",
    )
    p.add_argument(
        "--pysat-solver",
        default="m22",
        help="PySAT solver name (e.g. m22, g4, cd)",
    )
    p.add_argument(
        "--dpll-max-nodes",
        type=int,
        default=None,
        help="abort DPLL after this many nodes (UNKNOWN counts separately)",
    )
    p.add_argument("--warmup", type=int, default=1, help="extra PySAT solves to JIT-warm (discarded)")
    p.add_argument("--json", action="store_true")
    args = p.parse_args(argv)

    n = args.n_vars
    if args.clauses is not None:
        m = args.clauses
    elif args.ratio is not None:
        m = max(1, int(args.ratio * n))
    else:
        m = max(1, int(4.26 * n))

    if n < args.k:
        print(f"benchmark: need n_vars >= k, got n={n}, k={args.k}", file=sys.stderr)
        return 2

    mod = _load_solver()
    rng = random.Random(args.seed)

    for _ in range(max(0, args.warmup)):
        cw = random_ksat(n, m, args.k, rng)
        if args.backend in ("pysat", "both"):
            bench_pysat(cw, args.pysat_solver)

    times_py: list[float] = []
    times_dp: list[float] = []
    sat_py = unsat_py = unk_dp = 0
    ok_py_list: list[bool] = []
    ok_dp_list: list[bool | None] = []

    wall = time.perf_counter()
    for i in range(args.samples):
        clauses = random_ksat(n, m, args.k, rng)
        if args.backend in ("pysat", "both"):
            ok, elapsed = bench_pysat(clauses, args.pysat_solver)
            ok_py_list.append(ok)
            times_py.append(elapsed)
            if ok:
                sat_py += 1
            else:
                unsat_py += 1
        if args.backend in ("dpll", "both"):
            okd, eld = bench_dpll(mod, clauses, n, args.dpll_max_nodes)
            ok_dp_list.append(okd)
            times_dp.append(eld)
            if okd is True:
                pass
            elif okd is False:
                pass
            else:
                unk_dp += 1
    wall_total = time.perf_counter() - wall

    report: dict[str, Any] = {
        "n_vars": n,
        "n_clauses": m,
        "k": args.k,
        "samples": args.samples,
        "seed": args.seed,
        "wall_seconds": wall_total,
        "backend": args.backend,
        "pysat_solver": args.pysat_solver if args.backend in ("pysat", "both") else None,
    }

    if times_py:
        report["pysat"] = {
            "sat_count": sat_py,
            "unsat_count": unsat_py,
            "time_seconds_total": sum(times_py),
            "time_ms_mean": statistics.mean(times_py) * 1000,
            "time_ms_median": statistics.median(times_py) * 1000,
            "time_ms_max": max(times_py) * 1000,
            "seconds_per_million_literals": (sum(times_py) / (args.samples * m * args.k)) * 1e6
            if m and args.k
            else None,
        }
    if times_dp:
        agree = None
        if ok_py_list and len(ok_py_list) == len(ok_dp_list):
            agree = sum(1 for a, b in zip(ok_py_list, ok_dp_list) if b is not None and a == b)
        report["dpll"] = {
            "unknown_count": unk_dp,
            "time_seconds_total": sum(times_dp),
            "time_ms_mean": statistics.mean(times_dp) * 1000,
            "time_ms_median": statistics.median(times_dp) * 1000,
            "time_ms_max": max(times_dp) * 1000,
            "agree_with_pysat_when_defined": agree,
        }

    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print(f"Benchmark: n={n} m={m} k={args.k} samples={args.samples} seed={args.seed}")
        print(f"Wall clock (generation + solve): {wall_total:.3f} s")
        if times_py:
            pp = report["pysat"]
            print(
                f"  PySAT ({args.pysat_solver}): SAT={sat_py} UNSAT={unsat_py}  "
                f"mean {pp['time_ms_mean']:.2f} ms/instance  max {pp['time_ms_max']:.2f} ms"
            )
            if pp["seconds_per_million_literals"] is not None:
                print(
                    f"    (~{pp['seconds_per_million_literals']:.3f} s per 10^6 literal occurrences)"
                )
        if times_dp:
            pd = report["dpll"]
            print(
                f"  DPLL: UNKNOWN={unk_dp}  mean {pd['time_ms_mean']:.2f} ms/instance  "
                f"max {pd['time_ms_max']:.2f} ms"
            )
            if pd["agree_with_pysat_when_defined"] is not None:
                print(f"    agree with PySAT on {pd['agree_with_pysat_when_defined']}/{args.samples} instances")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())

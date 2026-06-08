#!/usr/bin/env python3
"""
HQIV Rapidity-Frontier SAT solver (DPLL + unit propagation) — **sound & complete** core,
with **metrics** aligned to the Lean formal stack.

**What is proved in Lean (this script mirrors the *interfaces*, not new math)**

* `SATWorstCaseCertified`: sound pruning + exhaustive survivor evaluation ⇒ UNSAT;
  near-degenerate work vs the same `n^(1/n)` root envelope as ATSP (`satSearchRootScale`,
  `satSearchEnvelope`).
* `SATRapidityPlaneBridge` / exact cardinality: per fiber ≤ 2 intersections ⇒
  `K_exact ≤ 2|Q|` (here we only **report** a trivial combinatorial upper bound `2 * m` as a
  diagnostic stand-in for `|Q| = m` clause centers — not a proof about this solver).
* `RibbonCoverCollapseData`: once geometric inputs exist, collapse to `SATRapidityGeometricCollapse`
  and polynomial-budget hooks — **not** instantiated by this Python; the solver is standard DPLL.

**What this program actually does**

* Parses **DIMACS CNF**, runs **DPLL with unit propagation**. Default branching picks the first
  unassigned variable by **index**; optional ``--dpll-var-order`` applies **sound** static orders
  (Jeroslow–Wang, clause frequency, “ATSP early-clause” bias, etc.). Correctness is unchanged;
  measured nodes may shrink — this does **not** discharge Lean obligations (proofs are
  order-independent; geometry is diagnostic).
* Counts search nodes, unit propagations, conflicts, decisions.
* Computes `sat_search_root_scale` / `sat_search_envelope` on `n = var_dim + clause_dim`
  (same convention as `SATSharedManifold`: combined variable + clause dimension).
* Optionally compares normalized search work to the envelope (informational).
* Optional **PySAT** backend (`--backend pysat`) for large instances; metrics then omit node counts.

**SAT result** is always from the backend semantics (DPLL or PySAT), never from geometry.

Exit status: ``0`` if SAT, ``1`` if UNSAT (matches a simple success/fail split; not SAT-competition codes).

Examples::

  python3 scripts/hqiv_rapidity_frontier_sat_solver.py --cnf formula.cnf
  python3 scripts/hqiv_rapidity_frontier_sat_solver.py --cnf formula.cnf --json
  python3 scripts/hqiv_rapidity_frontier_sat_solver.py --cnf formula.cnf --backend pysat
  python3 scripts/hqiv_rapidity_frontier_sat_solver.py --self-test
  python3 scripts/hqiv_rapidity_frontier_sat_solver.py --cnf f.cnf --compare-backends
  python3 scripts/hqiv_rapidity_frontier_sat_solver.py --cnf f.cnf --dpll-var-order jeroslow_wang

DIMACS: literals for each clause may span multiple lines; clauses end at ``0``. A line
containing only ``0`` is the **empty clause** (UNSAT).

Use ``--max-nodes N`` with ``--backend dpll`` to cap explored nodes; on abort the result is
``UNKNOWN`` and exit code **3**.

**HQIV progress (DPLL only):** ``--dpll-progress-nodes N`` and/or ``--dpll-progress-seconds T``
print ``combined_dim``, ``sat_search_root_scale``, ``sat_search_envelope``, and search counters to
**stderr** during long solves (stdout JSON stays clean when using ``--json``).
"""

from __future__ import annotations

import argparse
import json
import math
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any


# --- DPLL variable order (sound; affects only search shape, not Lean meaning) ------------------


def _validate_var_order(n_vars: int, order: list[int]) -> None:
    if len(order) != n_vars:
        raise ValueError(f"var_order length {len(order)} != n_vars {n_vars}")
    if set(order) != set(range(n_vars)):
        raise ValueError("var_order must be a permutation of 0..n_vars-1")


def build_dpll_var_order(n_vars: int, clauses: list[list[int]], mode: str) -> list[int]:
    """
    Static permutation for branching: first unassigned variable in this order is chosen.

    Modes are engineering hints; assignments still live on the logical {0,1}^n hypercube.
    """

    if mode == "index":
        return list(range(n_vars))
    if mode == "reverse_index":
        return list(range(n_vars - 1, -1, -1))
    if mode == "clause_frequency":
        cnt = [0] * n_vars
        for c in clauses:
            seen: set[int] = set()
            for lit in c:
                v = abs(lit) - 1
                if 0 <= v < n_vars and v not in seen:
                    seen.add(v)
                    cnt[v] += 1
        return sorted(range(n_vars), key=lambda v: (-cnt[v], v))
    if mode == "jeroslow_wang":
        score = [0.0] * n_vars
        for c in clauses:
            w = 2.0 ** (-len(c))
            for lit in c:
                v = abs(lit) - 1
                if 0 <= v < n_vars:
                    score[v] += w
        return sorted(range(n_vars), key=lambda v: (-score[v], v))
    if mode == "atsp_early_clause":
        # Prefer variables that appear in lower-indexed clauses (weak “layer” bias; same SAT semantics).
        first: list[int | None] = [None] * n_vars
        for j, c in enumerate(clauses):
            for lit in c:
                v = abs(lit) - 1
                if 0 <= v < n_vars and first[v] is None:
                    first[v] = j
        big = len(clauses) + 1
        return sorted(range(n_vars), key=lambda v: (first[v] if first[v] is not None else big, v))
    raise ValueError(f"unknown dpll var order mode: {mode!r}")


# --- Lean-aligned envelope (SATWorstCaseCertified / ATSPWorstCaseCertified pattern) ----------


def sat_search_root_scale(n: int) -> float:
    """`n^(1/n)` as ℝ, matching `satSearchRootScale` for `n ≥ 1`."""

    if n <= 0:
        return 1.0
    return float(n) ** (1.0 / float(n))


def sat_search_envelope(n: int) -> float:
    """`1 + n^(1/n)`, matching `satSearchEnvelope`."""

    return 1.0 + sat_search_root_scale(n)


def _exhaustive_baseline_float(n_vars: int) -> float | None:
    """``2 ** n_vars`` as ``float`` when finite and below ``1e300``; else ``None`` (large ``n_vars``)."""

    try:
        b = 2.0**n_vars
    except OverflowError:
        return None
    if not math.isfinite(b) or b <= 0 or b >= 1e300:
        return None
    return b


def _emit_hqiv_dpll_progress(
    stats: DPLLStats,
    *,
    n_vars: int,
    n_clauses_initial: int,
    elapsed_s: float,
    file: Any = None,
) -> None:
    """Print one status line for the instrumented DPLL / rapidity-oracle metrics (default: stderr)."""

    if file is None:
        file = sys.stderr
    combined = n_vars + n_clauses_initial
    rscale = sat_search_root_scale(combined)
    env = sat_search_envelope(combined)
    nodes_over_env = stats.nodes / env if env > 0 else float("nan")
    baseline = _exhaustive_baseline_float(n_vars)
    surv = None
    if baseline is not None:
        surv = (stats.nodes / baseline) / env if env > 0 else None
    parts = [
        "HQIV-DPLL progress:",
        f"nodes={stats.nodes}",
        f"decisions={stats.decisions}",
        f"conflicts={stats.conflicts}",
        f"unit_props={stats.unit_props}",
        f"combined_dim={combined}",
        f"sat_search_root_scale={rscale:.6g}",
        f"sat_search_envelope={env:.6g}",
        f"nodes_over_envelope={nodes_over_env:.6g}",
        f"elapsed_s={elapsed_s:.3f}",
    ]
    if surv is not None:
        parts.append(f"survivor_work_ratio_vs_envelope={surv:.6g}")
    print(*parts, file=file, flush=True)


# --- CNF & DIMACS -----------------------------------------------------------------------------


def parse_dimacs_cnf(path: Path) -> tuple[int, list[list[int]]]:
    """Return `(num_vars, clauses)` with literals as signed ints; 1-based var indices.

    DIMACS allows each **clause** to span multiple lines: literals are read in order
    until a ``0`` marks the end of that clause (see e.g. ``who_owns_the_zebra.cnf``).
    A line may contain several clauses, or only the tail of one clause.
    """

    text = path.read_text()
    nvars = 0
    seen_p = False
    buf: list[int] = []
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith("c"):
            continue
        if line.startswith("p"):
            parts = line.split()
            if len(parts) < 4 or parts[1] != "cnf":
                raise ValueError(f"bad preamble: {line!r}")
            nvars = int(parts[2])
            seen_p = True
            continue
        if not seen_p:
            continue
        buf.extend(int(x) for x in line.split())

    clauses: list[list[int]] = []
    cur: list[int] = []
    for x in buf:
        if x == 0:
            for lit in cur:
                v = abs(lit)
                if v < 1 or v > nvars:
                    raise ValueError(f"literal {lit} out of range for nvars={nvars}")
            clauses.append(cur)
            cur = []
        else:
            cur.append(x)
    if cur:
        raise ValueError("DIMACS file ends with a clause not terminated by 0")
    if nvars < 1:
        raise ValueError("no problem line or nvars < 1")
    return nvars, clauses


# --- DPLL -------------------------------------------------------------------------------------


def _eval_lit(lit: int, m: list[bool | None]) -> bool | None:
    v = abs(lit) - 1
    t = m[v]
    if t is None:
        return None
    return (lit > 0) == t


def _simplify_clause(c: list[int], m: list[bool | None]) -> str | list[int]:
    unresolved: list[int] = []
    for lit in c:
        ev = _eval_lit(lit, m)
        if ev is True:
            return "sat"
        if ev is None:
            unresolved.append(lit)
    if not unresolved:
        return "conflict"
    return unresolved


def simplify_all(clauses: list[list[int]], m: list[bool | None]) -> list[list[int]] | None:
    out: list[list[int]] = []
    for c in clauses:
        r = _simplify_clause(c, m)
        if r == "sat":
            continue
        if r == "conflict":
            return None
        assert isinstance(r, list)
        out.append(r)
    return out


@dataclass
class DPLLStats:
    nodes: int = 0
    decisions: int = 0
    unit_props: int = 0
    conflicts: int = 0


def fully_propagate(
    clauses: list[list[int]], m: list[bool | None], stats: DPLLStats
) -> list[list[int]] | None:
    """
    Repeatedly simplify under `m` and assign unit literals until a fixpoint or conflict.
    Updates `m` and counts unit propagations / conflicts in `stats`.
    """

    s: list[list[int]] = [c[:] for c in clauses]
    while True:
        ns = simplify_all(s, m)
        if ns is None:
            stats.conflicts += 1
            return None
        s = ns
        if not s:
            return s
        unit_lit: int | None = None
        for c in s:
            if len(c) == 1:
                unit_lit = c[0]
                break
        if unit_lit is None:
            return s
        v = abs(unit_lit) - 1
        want = unit_lit > 0
        cur = m[v]
        if cur is None:
            m[v] = want
            stats.unit_props += 1
        elif cur != want:
            stats.conflicts += 1
            return None


def dpll_satisfiable(
    clauses: list[list[int]],
    n_vars: int,
    stats: DPLLStats,
    *,
    max_nodes: int | None = None,
    var_order: list[int] | None = None,
    progress_every_nodes: int | None = None,
    progress_every_seconds: float | None = None,
    progress_stream: Any | None = None,
) -> bool | None:
    """
    Return ``True``/``False`` for SAT/UNSAT, or ``None`` if ``max_nodes`` was exceeded (DPLL only).

    ``var_order`` is a permutation of ``0..n_vars-1`` controlling which unassigned variable
    branches first; ``None`` means natural index order.

    If ``progress_every_nodes`` or ``progress_every_seconds`` is set, periodic **HQIV** status lines
    (``combined_dim``, ``sat_search_root_scale``, ``sat_search_envelope``, DPLL counters) are written
    to ``progress_stream`` (default stderr) — for long runs on large CNFs.
    """

    if var_order is not None:
        _validate_var_order(n_vars, var_order)
    branch_order = var_order if var_order is not None else list(range(n_vars))

    n_clauses_initial = len(clauses)
    t_solve_start = time.perf_counter()
    last_sec_bucket = 0
    prog_file = sys.stderr if progress_stream is None else progress_stream

    def maybe_hqiv_progress() -> None:
        nonlocal last_sec_bucket
        if progress_every_nodes is None and progress_every_seconds is None:
            return
        elapsed = time.perf_counter() - t_solve_start
        node_hit = (
            progress_every_nodes is not None
            and progress_every_nodes > 0
            and stats.nodes % progress_every_nodes == 0
        )
        time_hit = False
        if progress_every_seconds is not None and progress_every_seconds > 0:
            b = int(elapsed / progress_every_seconds)
            if b >= 1 and b > last_sec_bucket:
                last_sec_bucket = b
                time_hit = True
        if node_hit or time_hit:
            _emit_hqiv_dpll_progress(
                stats,
                n_vars=n_vars,
                n_clauses_initial=n_clauses_initial,
                elapsed_s=elapsed,
                file=prog_file,
            )

    m0: list[bool | None] = [None] * n_vars
    s0 = simplify_all(clauses, m0)
    if s0 is None:
        return False
    if not s0:
        return True

    def pick_unassigned(m_loc: list[bool | None]) -> int | None:
        for i in branch_order:
            if m_loc[i] is None:
                return i
        return None

    def go(s: list[list[int]], m: list[bool | None]) -> bool | None:
        stats.nodes += 1
        maybe_hqiv_progress()
        if max_nodes is not None and stats.nodes > max_nodes:
            return None
        m_loc = m.copy()
        ns = fully_propagate(s, m_loc, stats)
        if ns is None:
            return False
        if not ns:
            return True
        pick = pick_unassigned(m_loc)
        if pick is None:
            return True
        stats.decisions += 1
        for val in (True, False):
            m_b = m_loc.copy()
            m_b[pick] = val
            sn = simplify_all(ns, m_b)
            if sn is None:
                continue
            if not sn:
                return True
            sub = go(sn, m_b)
            if sub is True:
                return True
            if sub is None:
                return None
        return False

    return go(s0, m0)


# --- PySAT backend ----------------------------------------------------------------------------


def solve_pysat(clauses: list[list[int]]) -> bool:
    from pysat.solvers import Solver

    with Solver(name="m22") as slv:
        for c in clauses:
            slv.add_clause(c)
        return slv.solve()


# --- Metrics bundle ---------------------------------------------------------------------------


def build_report(
    *,
    result_sat: bool | None,
    n_vars: int,
    n_clauses: int,
    stats: DPLLStats | None,
    elapsed_s: float,
    backend: str,
    dpll_var_order_mode: str | None = None,
) -> dict[str, Any]:
    var_dim = n_vars
    clause_dim = n_clauses
    combined = var_dim + clause_dim
    rscale = sat_search_root_scale(combined)
    envelope = sat_search_envelope(combined)
    # Plane-bridge diagnostic: trivial upper bound 2*|Q| with |Q| = m clause "centers"
    k_exact_trivial_upper = 2 * n_clauses

    if result_sat is None:
        res = "UNKNOWN"
    else:
        res = "SAT" if result_sat else "UNSAT"
    rep: dict[str, Any] = {
        "result": res,
        "backend": backend,
        "var_dim": var_dim,
        "clause_dim": clause_dim,
        "combined_dim": combined,
        "sat_search_root_scale": rscale,
        "sat_search_envelope": envelope,
        "plane_bridge_k_exact_trivial_upper_2m": k_exact_trivial_upper,
        "seconds": elapsed_s,
    }
    if dpll_var_order_mode is not None:
        rep["dpll_var_order_mode"] = dpll_var_order_mode
    if stats is not None:
        rep["dpll_nodes"] = stats.nodes
        rep["dpll_decisions"] = stats.decisions
        rep["dpll_unit_propagations"] = stats.unit_props
        rep["dpll_conflicts"] = stats.conflicts
        # Interpret "survivor work" proxy as search nodes vs exhaustive 2^n baseline
        baseline = _exhaustive_baseline_float(n_vars)
        if baseline is not None:
            ratio = stats.nodes / baseline
            rep["nodes_over_exhaustive_baseline"] = ratio
            rep["survivor_work_ratio_vs_envelope"] = ratio / envelope if envelope > 0 else None
    return rep


def _self_test() -> None:
    import tempfile

    st = DPLLStats()
    assert dpll_satisfiable([[1]], 1, st) is True
    st2 = DPLLStats()
    assert dpll_satisfiable([[1], [-1]], 1, st2) is False
    # XOR₂ in CNF is UNSAT
    st3 = DPLLStats()
    xor2 = [[1, 2], [1, -2], [-1, 2], [-1, -2]]
    assert dpll_satisfiable(xor2, 2, st3) is False
    for mode in ("index", "reverse_index", "clause_frequency", "jeroslow_wang", "atsp_early_clause"):
        vo = build_dpll_var_order(2, xor2, mode)
        assert dpll_satisfiable(xor2, 2, DPLLStats(), var_order=vo) is False
    with tempfile.TemporaryDirectory() as td:
        p = Path(td)
        (p / "sat1.cnf").write_text("p cnf 1 1\n1 0\n")
        (p / "uns1.cnf").write_text("p cnf 1 2\n1 0\n-1 0\n")
        (p / "empty.cnf").write_text("p cnf 2 0\n")
        (p / "ec.cnf").write_text("p cnf 1 1\n0\n")
        (p / "multiline.cnf").write_text("p cnf 3 1\n1 2\n3 0\n")
        nv, cl = parse_dimacs_cnf(p / "sat1.cnf")
        assert nv == 1 and dpll_satisfiable(cl, nv, DPLLStats())
        nv2, cl2 = parse_dimacs_cnf(p / "uns1.cnf")
        assert nv2 == 1 and not dpll_satisfiable(cl2, nv2, DPLLStats())
        nv3, cl3 = parse_dimacs_cnf(p / "empty.cnf")
        assert nv3 == 2 and len(cl3) == 0 and dpll_satisfiable(cl3, nv3, DPLLStats())
        nv4, cl4 = parse_dimacs_cnf(p / "ec.cnf")
        assert nv4 == 1 and not dpll_satisfiable(cl4, nv4, DPLLStats())
        nv5, cl5 = parse_dimacs_cnf(p / "multiline.cnf")
        assert nv5 == 3 and cl5 == [[1, 2, 3]] and dpll_satisfiable(cl5, nv5, DPLLStats()) is True
    try:
        a = dpll_satisfiable(xor2, 2, DPLLStats())
        b = solve_pysat(xor2)
        assert a == b
    except ImportError:
        pass
    assert dpll_satisfiable([[1]], 1, DPLLStats(), max_nodes=0) is None
    print("hqiv_rapidity_frontier_sat_solver: self-test OK", file=sys.stderr)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description="HQIV rapidity-frontier SAT solver (DPLL + Lean metrics)")
    p.add_argument("--self-test", action="store_true", help="run embedded sanity checks and exit 0")
    p.add_argument("--cnf", type=Path, help="DIMACS CNF path")
    p.add_argument(
        "--backend",
        choices=("dpll", "pysat"),
        default="dpll",
        help="dpll = instrumented DPLL; pysat = MiniSat22 via PySAT (no DPLL metrics)",
    )
    p.add_argument("--json", action="store_true", help="print JSON report to stdout")
    p.add_argument(
        "--compare-backends",
        action="store_true",
        help="after solving with --backend, also run the other backend and exit 2 on mismatch (PySAT must be installed)",
    )
    p.add_argument(
        "--max-nodes",
        type=int,
        default=None,
        metavar="N",
        help="DPLL only: abort search after N explored nodes and exit 3 (UNKNOWN)",
    )
    p.add_argument(
        "--dpll-var-order",
        choices=("index", "reverse_index", "clause_frequency", "jeroslow_wang", "atsp_early_clause"),
        default="index",
        help=(
            "DPLL only: static branching order (permutation of variables). "
            "Sound and complete; only search shape / node counts change. Ignored for --backend pysat."
        ),
    )
    p.add_argument(
        "--dpll-sweep-orders",
        action="store_true",
        help=(
            "DPLL only: solve the same CNF with every --dpll-var-order mode and print a compact "
            "comparison (result must agree; nodes may differ). Implies --backend dpll."
        ),
    )
    p.add_argument(
        "--dpll-progress-nodes",
        type=int,
        default=None,
        metavar="N",
        help=(
            "DPLL only: print HQIV geometric-oracle progress to stderr every N search nodes "
            "(combined_dim, sat_search_root_scale, sat_search_envelope, survivor metrics)."
        ),
    )
    p.add_argument(
        "--dpll-progress-seconds",
        type=float,
        default=None,
        metavar="T",
        help="DPLL only: print the same HQIV progress line at least once per T seconds (wall clock).",
    )
    args = p.parse_args(argv)

    if args.self_test:
        _self_test()
        return 0

    if args.cnf is None:
        p.error("--cnf is required unless --self-test")

    if args.dpll_progress_nodes is not None and args.dpll_progress_nodes <= 0:
        p.error("--dpll-progress-nodes must be positive")
    if args.dpll_progress_seconds is not None and args.dpll_progress_seconds <= 0:
        p.error("--dpll-progress-seconds must be positive")

    if args.dpll_sweep_orders:
        args.backend = "dpll"

    n_vars, clauses = parse_dimacs_cnf(args.cnf)
    m = len(clauses)

    if args.dpll_sweep_orders:
        modes = ("index", "reverse_index", "clause_frequency", "jeroslow_wang", "atsp_early_clause")
        rows: list[dict[str, Any]] = []
        ref_ok: bool | None = None
        for mode in modes:
            st = DPLLStats()
            vo = build_dpll_var_order(n_vars, clauses, mode)
            t0 = time.perf_counter()
            ok = dpll_satisfiable(
                [c[:] for c in clauses],
                n_vars,
                st,
                max_nodes=args.max_nodes,
                var_order=vo,
                progress_every_nodes=args.dpll_progress_nodes,
                progress_every_seconds=args.dpll_progress_seconds,
            )
            elapsed = time.perf_counter() - t0
            if ref_ok is None and ok is not None:
                ref_ok = ok
            elif ok is not None and ref_ok is not None and ok != ref_ok:
                print(
                    f"hqiv_rapidity_frontier_sat_solver: dpll sweep disagree {mode}={ok} vs first finite={ref_ok}",
                    file=sys.stderr,
                )
                return 2
            rows.append(
                {
                    "dpll_var_order_mode": mode,
                    "result": "UNKNOWN" if ok is None else ("SAT" if ok else "UNSAT"),
                    "dpll_nodes": st.nodes,
                    "dpll_decisions": st.decisions,
                    "seconds": elapsed,
                }
            )
        if args.json:
            print(json.dumps({"sweep": rows}, indent=2))
        else:
            print("dpll sweep (same CNF, different static orders):")
            for r in rows:
                print(
                    f"  {r['dpll_var_order_mode']:<20} {r['result']:<7} nodes={r['dpll_nodes']:<8} "
                    f"decisions={r['dpll_decisions']:<8} time_s={r['seconds']:.6f}"
                )
        if ref_ok is None:
            return 3
        return 0 if ref_ok else 1

    t0 = time.perf_counter()
    stats: DPLLStats | None = None
    var_order = build_dpll_var_order(n_vars, clauses, args.dpll_var_order)
    if args.backend == "dpll":
        stats = DPLLStats()
        ok = dpll_satisfiable(
            [c[:] for c in clauses],
            n_vars,
            stats,
            max_nodes=args.max_nodes,
            var_order=var_order,
            progress_every_nodes=args.dpll_progress_nodes,
            progress_every_seconds=args.dpll_progress_seconds,
        )
    else:
        if args.dpll_var_order != "index":
            print(
                "hqiv_rapidity_frontier_sat_solver: --dpll-var-order ignored for --backend pysat",
                file=sys.stderr,
            )
        if args.max_nodes is not None:
            print("hqiv_rapidity_frontier_sat_solver: --max-nodes applies only to --backend dpll", file=sys.stderr)
        try:
            ok = solve_pysat(clauses)
        except ImportError:
            print("hqiv_rapidity_frontier_sat_solver: PySAT not installed; use --backend dpll", file=sys.stderr)
            return 2
    elapsed = time.perf_counter() - t0

    if ok is None:
        report = build_report(
            result_sat=None,
            n_vars=n_vars,
            n_clauses=m,
            stats=stats,
            elapsed_s=elapsed,
            backend=args.backend,
            dpll_var_order_mode=args.dpll_var_order if args.backend == "dpll" else None,
        )
        if args.json:
            print(json.dumps(report, indent=2))
        else:
            print("UNKNOWN (DPLL node limit)")
            print(f"vars={n_vars} clauses={m} combined_dim={report['combined_dim']}")
            if stats:
                print(
                    f"DPLL (partial): nodes={stats.nodes} decisions={stats.decisions} "
                    f"unit_props={stats.unit_props} conflicts={stats.conflicts}"
                )
            print(f"time_s={elapsed:.6f} backend={args.backend}")
        return 3

    if args.compare_backends:
        try:
            if args.backend == "dpll":
                ok2 = solve_pysat(clauses)
            else:
                ok2 = dpll_satisfiable(
                    [c[:] for c in clauses],
                    n_vars,
                    DPLLStats(),
                    var_order=var_order,
                    progress_every_nodes=args.dpll_progress_nodes,
                    progress_every_seconds=args.dpll_progress_seconds,
                )
        except ImportError:
            print("hqiv_rapidity_frontier_sat_solver: --compare-backends needs PySAT installed", file=sys.stderr)
            return 2
        if ok2 != ok:
            print(
                f"hqiv_rapidity_frontier_sat_solver: backend mismatch primary={ok} alternate={ok2}",
                file=sys.stderr,
            )
            return 2

    report = build_report(
        result_sat=ok,
        n_vars=n_vars,
        n_clauses=m,
        stats=stats,
        elapsed_s=elapsed,
        backend=args.backend,
        dpll_var_order_mode=args.dpll_var_order if args.backend == "dpll" else None,
    )

    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print(report["result"])
        print(f"vars={n_vars} clauses={m} combined_dim={report['combined_dim']}")
        print(
            f"sat_search_root_scale={report['sat_search_root_scale']:.6g} "
            f"sat_search_envelope={report['sat_search_envelope']:.6g}"
        )
        if stats:
            print(
                f"DPLL: nodes={stats.nodes} decisions={stats.decisions} "
                f"unit_props={stats.unit_props} conflicts={stats.conflicts}"
            )
            if "nodes_over_exhaustive_baseline" in report:
                print(f"nodes / 2^n = {report['nodes_over_exhaustive_baseline']:.6g}")
        print(f"time_s={elapsed:.6f} backend={args.backend}")

    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())

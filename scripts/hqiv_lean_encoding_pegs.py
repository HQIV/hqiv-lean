#!/usr/bin/env python3
"""
Candidate **encodings** for the open Lean interfaces in ``SATRapidityPlaneBridge.lean`` — not a
benchmark of off-the-shelf CDCL on random CNFs.

Each encoding run emits **pegs**: numbers and checklists naming which fields of
``RibbonCoverCollapseData``, ``DirectionSelectionCertificate``, and the plane / exact-count
layer already have a *concrete* carrier from the encoding, versus what remains schematic.

**Primary references (Lean)**

* ``Hqiv/Geometry/SATRapidityPlaneBridge.lean`` — ``RibbonCoverCollapseData``, ``K_exactUnionCard``,
  ``SuccessorStepResidualControl``, ``planeLocalShellIntersections`` (still abstract on the manifold).
* ``scripts/hqiv_geometric_3sat_demo.py`` — prime-product / Ω(M) story for 3-CNF (optional SAT check).

**ATSP-style vertical layers** (``--encoding atsp_vertical_layers``): variables are **cities** on a
reference line (the ``y = 0`` plane in ``ℝ²``); each clause is a **connector** offset **orthogonal**
to that line (alternating ``±`` height = “above / below” the plane). Literal–clause segments are
Euclidean chords; distances inherit the **triangle inequality** used in Lean’s ``Plane`` model
(``dist_triangle``, ribbon ⇒ annulus in ``SATRapidityAnnulusCircle``). This does **not** by itself
construct ``RibbonCoverCollapseData`` — it pegs the **metric** layer that those proofs consume.

**Hypercube vs geometry:** Boolean truth lives on the logical ``{0,1}^n`` cube; planar / prime /
ATSP embeddings are optional carriers for metrics and annulus-layer intuition. Branching heuristics
in ``hqiv_rapidity_frontier_sat_solver.py`` (``--dpll-var-order``, ``--dpll-sweep-orders``) change
only **search shape**, not satisfiability — they do **not** discharge Lean proof obligations.

**ATSP occurrence-lift experiments** (orthogonal ambient axes + PCA / separation metrics):
``scripts/hqiv_sat_atsp_lift_experiment.py`` (``--suite``, ``--sweep-alpha-beta``).

**This script does not prove theorems.** It is a structured report generator for encoding experiments.

Examples::

  python3 scripts/hqiv_lean_encoding_pegs.py --encoding geometric_prime --formula example
  python3 scripts/hqiv_lean_encoding_pegs.py --encoding geometric_prime --formula random --num-vars 12 --num-clauses 40 --seed 1 --solve
  python3 scripts/hqiv_lean_encoding_pegs.py --encoding geometric_prime --formula known unsat_8_maxterms_3vars --json
  python3 scripts/hqiv_lean_encoding_pegs.py --encoding atsp_vertical_layers --formula example --json
  python3 scripts/hqiv_lean_encoding_pegs.py --list-formulas
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
import random
import sys
from pathlib import Path
from typing import Any


def _load_geometric_demo():
    """Load ``hqiv_geometric_3sat_demo`` without requiring it to be on ``PYTHONPATH``."""

    scripts = Path(__file__).resolve().parent
    spec = importlib.util.spec_from_file_location(
        "hqiv_geometric_3sat_demo", scripts / "hqiv_geometric_3sat_demo.py"
    )
    mod = importlib.util.module_from_spec(spec)
    sys.modules["hqiv_geometric_3sat_demo"] = mod
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod


def formula3sat_to_clauses(demo, f) -> list[list[int]]:
    """DIMACS-style clauses (1-based signed literals) from ``Formula3SAT``."""

    out: list[list[int]] = []
    for c in f.clauses:
        row: list[int] = []
        for lit in c:
            v = lit.var + 1
            row.append(-v if lit.neg else v)
        out.append(row)
    return out


def _sat_search_root_scale(n: int) -> float:
    if n <= 0:
        return 1.0
    return float(n) ** (1.0 / float(n))


def _sat_search_envelope(n: int) -> float:
    return 1.0 + _sat_search_root_scale(n)


def _try_pysat_sat(clauses: list[list[int]]) -> tuple[str, float | None]:
    try:
        from pysat.solvers import Solver
    except ImportError:
        return "pysat_not_installed", None

    import time

    t0 = time.perf_counter()
    with Solver(name="m22") as slv:
        for c in clauses:
            slv.add_clause(c)
        ok = slv.solve()
    return ("SAT" if ok else "UNSAT"), time.perf_counter() - t0


def peg_geometric_prime(demo, f, label: str, solve: bool) -> dict[str, Any]:
    """
    Prime-alphabet encoding: Ω(M), clause products, and SAT manifold dimensions.

    Peg narrative: ``varDim`` / ``clauseDim`` match ``SATSharedManifold``; Ω(M) matches the demo's
    ``θ = π/(2k)`` diagnostic; ``2 * clauseDim`` is the **diagnostic** stand-in for
    ``K_exactUnionCard ≤ 2 * |Q|`` when one tentatively identifies ``|Q|`` with ``clauseDim`` (one
    center per clause) — the formal proof in Lean uses planar fibers, not this identification.
    """

    m = len(f.clauses)
    var_dim = f.num_vars
    clause_dim = m
    combined = var_dim + clause_dim
    omega_m = int(demo.omega_M_exact(f))
    clauses = formula3sat_to_clauses(demo, f)

    primes = demo.first_n_primes(var_dim)
    clause_products = [demo.clause_product(tuple(cl), primes) for cl in f.clauses]

    sat_result: str | None = None
    solve_s: float | None = None
    if solve:
        sat_result, solve_s = _try_pysat_sat(clauses)
        if sat_result == "pysat_not_installed":
            sat_result = None

    # Checklist aligned to RibbonCoverCollapseData fields (informative only).
    ribbon_fields: dict[str, str] = {
        "witness": "open — needs LocalRibbonSectionWitness from geometry",
        "family": "open — AnnulusLatticeFamily not fixed by CNF alone",
        "intersections": "open — Plane → Finset Plane (scaffold: localShellIntersections)",
        "hCover": "open — needs residual → plane center map",
        "hne": "open — q ≠ 0 on carrier",
        "hloc": "open — planeLocalShellIntersections",
        "hK": "partial peg — encoding gives clauseDim; need len(residuals) ≤ K_exactUnionCard(...)",
        "varDim": f"pegged — {var_dim}",
        "clauseDim": f"pegged — {clause_dim}",
        "τBits": "open — choose τBits / countBound policy",
        "countBound": "open — polynomial cardinality slot",
        "hCard": "open — needs family.carrier.card ≤ countBound(...)",
        "hShared": "open — match shared manifold to DirectionSelectionCertificate",
        "hLen": "open — residuals.length = arityResiduals.length",
        "hCountFrontier": "open — sphereCodeBound vs 2*countBound",
        "hPoly": "open — effectiveDim / sphereCodeBound monotonicity",
    }

    return {
        "encoding": "geometric_prime",
        "formula_label": label,
        "formula": {
            "num_vars": var_dim,
            "num_clauses": clause_dim,
            "omega_M": omega_m,
            "theta_denominator_k": omega_m,
            "clause_products_sample": clause_products[:5],
            "clause_products_count": len(clause_products),
        },
        "sat_shared_manifold_dims": {
            "var_dim": var_dim,
            "clause_dim": clause_dim,
            "combined_dim": combined,
            "sat_search_root_scale": _sat_search_root_scale(combined),
            "sat_search_envelope": _sat_search_envelope(combined),
        },
        "plane_bridge_diagnostics": {
            "clause_count_m": m,
            "trivial_2m_upper_if_Q_eq_clauses": 2 * m,
            "note": (
                "Lean: K_exactUnionCard Q intersections ≤ 2 * Q.card under planeLocalShell hypotheses; "
                "treating Q as one center per clause is an encoding experiment, not a proof."
            ),
        },
        "ribbon_cover_collapse_data_pegs": ribbon_fields,
        "optional_solver": (
            None
            if sat_result is None
            else {"backend": "pysat_m22", "result": sat_result, "seconds": solve_s}
        ),
        "dimacs_clause_count": len(clauses),
    }


def _dist_r2(a: tuple[float, float], b: tuple[float, float]) -> float:
    return math.hypot(a[0] - b[0], a[1] - b[1])


def peg_atsp_vertical_layers(demo, f, label: str, solve: bool, layer_height: float) -> dict[str, Any]:
    """
    ATSP metaphor → SAT: each variable index is a **vertical city** (fiber over a point on the base
    line ``y = 0``); each clause is a node displaced along **orthogonal** ``y`` (above/below the
    plane). Chords from clause node to incident variable sites carry Euclidean length; the ambient
    metric is ``dist`` on ``Plane`` in Lean, so **triangle inequality** is the same inequality
    ``ATSPWorstCaseCertified`` / annulus arguments import for geometry (not for Boolean semantics).
    """

    m = len(f.clauses)
    var_dim = f.num_vars
    clause_dim = m
    combined = var_dim + clause_dim
    clauses_dimacs = formula3sat_to_clauses(demo, f)

    h = abs(float(layer_height))
    if h < 1e-6:
        h = 1.0

    # Cities: (i, 0) — parallel vertical lines through each integer i on the reference plane.
    cities: list[tuple[float, float]] = [(float(i), 0.0) for i in range(var_dim)]

    # Clause connectors: staggered in x so nodes are distinct; y = ±h alternates (above/below plane).
    clause_nodes: list[tuple[float, float]] = []
    for j in range(m):
        x = float(var_dim) + 0.5 + 1.25 * float(j)
        y = h if (j % 2 == 0) else -h
        clause_nodes.append((x, y))

    # One Euclidean length per literal occurrence (chord city ↔ clause center).
    literal_chords: list[dict[str, Any]] = []
    for j, cl in enumerate(f.clauses):
        for lit in cl:
            i = lit.var
            a, b = cities[i], clause_nodes[j]
            literal_chords.append(
                {
                    "clause_index": j,
                    "var_index": i,
                    "negated": lit.neg,
                    "length": _dist_r2(a, b),
                }
            )

    # Spot-check triangle inequality on a small point set (must hold in ℝ²).
    sample_pts: list[tuple[float, float]] = cities[: min(4, len(cities))] + clause_nodes[: min(3, len(clause_nodes))]
    tri_checks: list[dict[str, Any]] = []
    for ia in range(len(sample_pts)):
        for ib in range(len(sample_pts)):
            for ic in range(len(sample_pts)):
                if ia == ib or ib == ic or ia == ic:
                    continue
                p, q, r = sample_pts[ia], sample_pts[ib], sample_pts[ic]
                lhs = _dist_r2(p, r)
                rhs = _dist_r2(p, q) + _dist_r2(q, r)
                tri_checks.append(
                    {
                        "lhs_dist_pr": lhs,
                        "rhs_pq_plus_qr": rhs,
                        "holds": lhs <= rhs + 1e-9,
                    }
                )
                if len(tri_checks) >= 24:
                    break
            if len(tri_checks) >= 24:
                break
        if len(tri_checks) >= 24:
            break

    sat_result: str | None = None
    solve_s: float | None = None
    if solve:
        sat_result, solve_s = _try_pysat_sat(clauses_dimacs)
        if sat_result == "pysat_not_installed":
            sat_result = None

    omega_m = int(demo.omega_M_exact(f))

    ribbon_fields: dict[str, str] = {
        "witness": "open — LocalRibbonSectionWitness (clause chords do not fix a ribbon)",
        "family": "open — candidate Q could be finite subset of {cities, clause_nodes} for experiments",
        "intersections": "open — formal Finset per plane point",
        "hCover": "open — map residuals to planeCenterOfResidual",
        "hne": "open — exclude 0 ∈ Plane if Q includes origin",
        "hloc": "partial peg — metric is ℝ²; formal planeLocalShellIntersections still separate",
        "hK": "partial peg — same combinatorial clause_dim / K_exact story as prime encoding",
        "varDim": f"pegged — {var_dim}",
        "clauseDim": f"pegged — {clause_dim}",
        "τBits": "open",
        "countBound": "open",
        "hCard": "open",
        "hShared": "open",
        "hLen": "open",
        "hCountFrontier": "open",
        "hPoly": "open",
    }

    return {
        "encoding": "atsp_vertical_layers",
        "formula_label": label,
        "atsp_sat_correspondence": {
            "cities": "one per Boolean variable — vertical line through (i, 0) in ℝ²",
            "reference_plane": "y = 0 — base line where variable ‘sites’ sit",
            "orthogonal_edges": "segments from each clause node (above/below y=0) to its three variable sites",
            "triangle_inequality": "Euclidean distances on Plane; matches dist_triangle route in SATRapidityAnnulusCircle",
            "boolean_semantics": "unchanged — this embedding does not define satisfaction; it supplies a metric carrier",
        },
        "formula": {
            "num_vars": var_dim,
            "num_clauses": clause_dim,
            "omega_M_cross_link": omega_m,
            "layer_height_abs": h,
        },
        "sat_shared_manifold_dims": {
            "var_dim": var_dim,
            "clause_dim": clause_dim,
            "combined_dim": combined,
            "sat_search_root_scale": _sat_search_root_scale(combined),
            "sat_search_envelope": _sat_search_envelope(combined),
        },
        "planar_embedding": {
            "city_positions_y_eq_0": cities[: min(8, len(cities))],
            "city_positions_truncated": len(cities) > 8,
            "clause_node_positions": clause_nodes[: min(8, len(clause_nodes))],
            "clause_nodes_truncated": len(clause_nodes) > 8,
            "literal_chord_sample": literal_chords[:12],
            "literal_chord_count": len(literal_chords),
        },
        "triangle_inequality_spot_checks": {
            "sample_size": len(tri_checks),
            "all_hold": all(x["holds"] for x in tri_checks),
            "samples": tri_checks[:8],
        },
        "plane_bridge_diagnostics": {
            "clause_count_m": m,
            "trivial_2m_upper_if_Q_eq_clauses": 2 * m,
            "note": (
                "Metric layer aligns with Lean Plane / dist_triangle; ribbon–annulus bridge is in "
                "SATRapidityAnnulusCircle. Boolean structure is still carried by CNF, not by distance alone."
            ),
        },
        "ribbon_cover_collapse_data_pegs": ribbon_fields,
        "optional_solver": (
            None
            if sat_result is None
            else {"backend": "pysat_m22", "result": sat_result, "seconds": solve_s}
        ),
        "dimacs_clause_count": len(clauses_dimacs),
    }


def main() -> int:
    demo = _load_geometric_demo()

    p = argparse.ArgumentParser(description="HQIV Lean encoding peg reports (not generic SAT benchmarks).")
    p.add_argument(
        "--encoding",
        choices=("geometric_prime", "atsp_vertical_layers"),
        default="geometric_prime",
        help="Candidate encoding family to report.",
    )
    p.add_argument(
        "--layer-height",
        type=float,
        default=2.0,
        help="For atsp_vertical_layers: |y| offset of clause nodes above/below the y=0 plane.",
    )
    p.add_argument(
        "--formula",
        choices=("example", "random", "known"),
        default="example",
        help="Which formula to build.",
    )
    p.add_argument("--known-name", default="", help="For --formula known: name from KNOWN_SAT_BENCHMARKS.")
    p.add_argument("--num-vars", type=int, default=8)
    p.add_argument("--num-clauses", type=int, default=32)
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--solve", action="store_true", help="Optional PySAT SAT/UNSAT check (sanity only).")
    p.add_argument("--json", action="store_true")
    p.add_argument("--list-formulas", action="store_true", help="List built-in and known benchmark names.")

    args = p.parse_args()

    if args.list_formulas:
        print("Built-in: example")
        print("TRIAL_FORMULAS (name — use demo directly or extend this script):")
        for name, _f in demo.TRIAL_FORMULAS:
            print(f"  {name}")
        print("KNOWN_SAT_BENCHMARKS (for --formula known --known-name):")
        for t in demo.KNOWN_SAT_BENCHMARKS:
            print(f"  {t[0]}")
        return 0

    f: Any = None
    label = ""

    if args.formula == "example":
        f = demo.EXAMPLE
        label = "EXAMPLE"
    elif args.formula == "random":
        rng = random.Random(args.seed)
        f = demo.random_3sat_formula(args.num_vars, args.num_clauses, rng)
        label = f"random(n={args.num_vars},m={args.num_clauses},seed={args.seed})"
    else:
        if not args.known_name:
            print("error: --formula known requires --known-name", file=sys.stderr)
            return 2
        mp = {t[0]: t for t in demo.KNOWN_SAT_BENCHMARKS}
        if args.known_name not in mp:
            print(f"error: unknown known-name {args.known_name!r}", file=sys.stderr)
            return 2
        f = mp[args.known_name][1]
        label = args.known_name

    if args.encoding == "geometric_prime":
        report = peg_geometric_prime(demo, f, label, args.solve)
    elif args.encoding == "atsp_vertical_layers":
        report = peg_atsp_vertical_layers(demo, f, label, args.solve, args.layer_height)
    else:
        raise SystemExit("internal error: unknown encoding")

    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print(f"Encoding: {report['encoding']}  formula: {report['formula_label']}")
        fd = report["formula"]
        sm = report["sat_shared_manifold_dims"]
        if report["encoding"] == "geometric_prime":
            print(f"  var_dim={fd['num_vars']}  clause_dim={fd['num_clauses']}  Ω(M)={fd['omega_M']}")
        else:
            om = fd.get("omega_M_cross_link")
            print(
                f"  var_dim={fd['num_vars']}  clause_dim={fd['num_clauses']}  "
                f"|layer|={fd['layer_height_abs']:.3f}  Ω(M) cross-link={om}"
            )
        print(f"  combined_dim={sm['combined_dim']}  envelope={sm['sat_search_envelope']:.6f}")
        pb = report["plane_bridge_diagnostics"]
        print(f"  trivial 2|Q| diagnostic (if |Q|=m): {pb['trivial_2m_upper_if_Q_eq_clauses']}")
        if report["encoding"] == "atsp_vertical_layers":
            tri = report["triangle_inequality_spot_checks"]
            print(f"  triangle inequality spot checks: all_hold={tri['all_hold']} (n={tri['sample_size']})")
        if report.get("optional_solver"):
            osolv = report["optional_solver"]
            print(f"  solver: {osolv['result']} in {osolv['seconds']:.4f}s")
        print("  RibbonCoverCollapseData field pegs: see --json")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())

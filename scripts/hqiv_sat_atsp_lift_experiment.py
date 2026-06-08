#!/usr/bin/env python3
"""
ATSP-style **lift** over literal **occurrences** for 3-CNF, with numerical benchmarks.

This is an **experiment harness**, not a Lean proof. It instantiates a concrete ambient
``ℝ^D`` (orthonormal axes: one per occurrence, one per variable “city”, one per clause) and
forms vectors

    lift_k = slack_k · e_occ(k) − α · ρ_k · e_var(i) + β · ρ_k · e_clause(j)

for the *k*-th occurrence of variable *i* in clause *j*.  Projections use either the
**(slack, −αρ)** osculating pair or a **PCA** 2-plane fit across all lifts.

**Benchmarks** favor **encoding-structured** instances (demo formulas + modest random 3-CNF),
not phase-transition random k-SAT.  Metrics highlight what is *numerically* promising for a
low-dimensional ribbon witness:

* PCA explained variance in the top-2 plane (concentration ⇒ a natural osculating plane);
* tour / scan imbalance ``‖Σ lift‖ / Σ ‖lift‖`` under occurrence orderings;
* radial spread of PCA coordinates (annulus / shell thickness proxy);
* pairwise separation in the PCA plane (distinct residuals stay separated).

Examples::

  python3 scripts/hqiv_sat_atsp_lift_experiment.py --formula example
  python3 scripts/hqiv_sat_atsp_lift_experiment.py --suite
  python3 scripts/hqiv_sat_atsp_lift_experiment.py --suite --json
  python3 scripts/hqiv_sat_atsp_lift_experiment.py --sweep-alpha-beta --formula random --num-vars 20 --num-clauses 60 --seed 0
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
import random
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Sequence


def _load_geometric_demo():
    scripts = Path(__file__).resolve().parent
    spec = importlib.util.spec_from_file_location(
        "hqiv_geometric_3sat_demo", scripts / "hqiv_geometric_3sat_demo.py"
    )
    mod = importlib.util.module_from_spec(spec)
    sys.modules["hqiv_geometric_3sat_demo"] = mod
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod


@dataclass(frozen=True)
class Occurrence:
    occ_index: int
    clause_index: int
    var_index: int
    negated: bool


def collect_occurrences(demo, f) -> tuple[list[Occurrence], int, int]:
    """All literal occurrences in clause order (matches a natural scan / ‘tour’ order)."""

    occs: list[Occurrence] = []
    k = 0
    for j, cl in enumerate(f.clauses):
        for lit in cl:
            occs.append(Occurrence(k, j, lit.var, lit.neg))
            k += 1
    return occs, f.num_vars, len(f.clauses)


def ambient_dim(n_occ: int, n_vars: int, n_clauses: int) -> int:
    """One orthonormal axis per occurrence, variable (city), and clause (connector)."""

    return n_occ + n_vars + n_clauses


def build_lifts(
    occs: list[Occurrence],
    n_vars: int,
    n_clauses: int,
    *,
    alpha: float,
    beta: float,
    rho_mode: str,
    slack_mode: str,
) -> tuple[Any, list[float], list[float]]:
    """
    Return (X, slacks, rhos) with X shape (n_occ, D), row k = lift vector in ℝ^D.
    """

    import numpy as np

    n_occ = len(occs)
    D = ambient_dim(n_occ, n_vars, n_clauses)
    X = np.zeros((n_occ, D), dtype=np.float64)
    slacks: list[float] = []
    rhos: list[float] = []

    # Clause widths for slack
    widths: dict[int, int] = {}
    for o in occs:
        widths[o.clause_index] = widths.get(o.clause_index, 0) + 1
    for j in range(n_clauses):
        if j not in widths:
            widths[j] = 3

    for row, o in enumerate(occs):
        wcl = max(1, widths[o.clause_index])
        if slack_mode == "inv_sqrt_width":
            sk = 1.0 / math.sqrt(float(wcl))
        elif slack_mode == "inv_width":
            sk = 1.0 / float(wcl)
        else:
            sk = 1.0

        if rho_mode == "constant":
            rk = 1.0
        elif rho_mode == "clause_phase":
            rk = 1.0 + 0.25 * math.sin(float(o.clause_index))
        elif rho_mode == "occ_index":
            rk = 1.0 / math.sqrt(float(row + 1))
        else:
            rk = 1.0

        slacks.append(sk)
        rhos.append(rk)

        e_occ = o.occ_index
        e_var = n_occ + o.var_index
        e_cl = n_occ + n_vars + o.clause_index
        X[row, e_occ] += sk
        X[row, e_var] += -alpha * rk
        X[row, e_cl] += beta * rk

    return X, slacks, rhos


def pca2_explained_ratio(X: Any) -> tuple[Any, float, float]:
    """Top-2 PCA of centered X; returns (coords n×2, ratio1, ratio2)."""

    import numpy as np

    if X.shape[0] < 2:
        z = np.zeros((X.shape[0], 2))
        return z, 0.0, 0.0
    xc = X - X.mean(axis=0, keepdims=True)
    _, s, vh = np.linalg.svd(xc, full_matrices=False)
    total = float(np.sum(s**2)) + 1e-30
    r1 = float(s[0] ** 2 / total) if len(s) >= 1 else 0.0
    r2 = float(s[1] ** 2 / total) if len(s) >= 2 else 0.0
    # Scores: projection onto first two right singular vectors (rows of vh).
    c0 = xc @ vh[0]
    if len(s) >= 2:
        c1 = xc @ vh[1]
        coords = np.column_stack([c0, c1])
    else:
        coords = np.column_stack([c0, np.zeros_like(c0)])
    return coords, r1, r2


def tour_imbalance(X: Any) -> float:
    """‖Σ x_k‖ / (Σ ‖x_k‖ + ε).  Closer to 1 ⇒ more aligned ‘collinearity’; closer to 0 ⇒ cancellation."""

    import numpy as np

    s = np.sum(X, axis=0)
    num = float(np.linalg.norm(s))
    den = float(np.sum(np.linalg.norm(X, axis=1))) + 1e-15
    return num / den


def annulus_proxy(coords: Any) -> dict[str, float]:
    """Radial mean/std of PCA plane coords (shell thickness heuristic)."""

    import numpy as np

    r = np.linalg.norm(coords, axis=1)
    return {
        "radius_mean": float(np.mean(r)),
        "radius_std": float(np.std(r)),
        "radius_min": float(np.min(r)),
        "radius_max": float(np.max(r)),
    }


def min_pairwise_dist(coords: Any) -> float:
    import numpy as np

    n = coords.shape[0]
    if n < 2:
        return float("inf")
    mind = float("inf")
    for i in range(n):
        for j in range(i + 1, n):
            d = float(np.linalg.norm(coords[i] - coords[j]))
            if d < mind:
                mind = d
    return mind


def osculating2d_slack_var(X: Any, occs: Sequence[Occurrence], n_occ: int) -> Any:
    """Use (occurrence-axis slack, variable-city component) as an explicit 2D chart."""

    import numpy as np

    n = X.shape[0]
    out = np.zeros((n, 2), dtype=np.float64)
    for r, o in enumerate(occs):
        out[r, 0] = X[r, o.occ_index]
        out[r, 1] = X[r, n_occ + o.var_index]
    return out


def run_case(
    demo,
    f,
    label: str,
    *,
    alpha: float,
    beta: float,
    rho_mode: str,
    slack_mode: str,
) -> dict[str, Any]:
    occs, n_vars, n_clauses = collect_occurrences(demo, f)
    n_occ = len(occs)
    D = ambient_dim(n_occ, n_vars, n_clauses)

    import numpy as np

    X, slacks, rhos = build_lifts(
        occs, n_vars, n_clauses, alpha=alpha, beta=beta, rho_mode=rho_mode, slack_mode=slack_mode
    )
    coords_pca, r1, r2 = pca2_explained_ratio(X)
    imb = tour_imbalance(X)
    ann = annulus_proxy(coords_pca)
    mpd = min_pairwise_dist(coords_pca)

    osc2 = osculating2d_slack_var(X, occs, n_occ)
    ann_osc = annulus_proxy(osc2)
    mpd_osc = min_pairwise_dist(osc2)

    return {
        "label": label,
        "n_vars": n_vars,
        "n_clauses": n_clauses,
        "n_occurrences": n_occ,
        "ambient_dim_D": D,
        "alpha": alpha,
        "beta": beta,
        "rho_mode": rho_mode,
        "slack_mode": slack_mode,
        "pca_explained_pc1": r1,
        "pca_explained_pc2": r2,
        "pca_explained_top2": r1 + r2,
        "tour_imbalance_ratio": imb,
        "pca_plane": {**ann, "min_pairwise_dist": mpd},
        "slack_var_chart": {**ann_osc, "min_pairwise_dist": mpd_osc},
        "promising_flags": {
            "pca_concentrated_top2": (r1 + r2) >= 0.85,
            "large_min_sep_pca": mpd >= 0.05 * (ann["radius_mean"] + 1e-9),
            "slack_var_sep": mpd_osc >= 0.01,
        },
    }


def suite_formulas(demo) -> list[tuple[str, Any]]:
    out: list[tuple[str, Any]] = [("example", demo.EXAMPLE)]
    for name, f, _sat, _w, _note in demo.KNOWN_SAT_BENCHMARKS:
        out.append((name, f))
    return out


def main() -> int:
    demo = _load_geometric_demo()
    p = argparse.ArgumentParser(description="ATSP-style SAT lift experiments + benchmarks")
    p.add_argument("--formula", choices=("example", "random", "known"), default="example")
    p.add_argument("--known-name", default="", help="with --formula known")
    p.add_argument("--num-vars", type=int, default=20)
    p.add_argument("--num-clauses", type=int, default=60)
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--alpha", type=float, default=0.7)
    p.add_argument("--beta", type=float, default=0.7)
    p.add_argument("--rho-mode", choices=("constant", "clause_phase", "occ_index"), default="clause_phase")
    p.add_argument(
        "--slack-mode", choices=("inv_sqrt_width", "inv_width", "unit"), default="inv_sqrt_width"
    )
    p.add_argument("--suite", action="store_true", help="run example + known benchmarks + 3 random seeds")
    p.add_argument(
        "--sweep-alpha-beta",
        action="store_true",
        help="grid α,β ∈ {0.25,0.5,1.0} on one formula (promising = high PCA top-2 + separation)",
    )
    p.add_argument("--json", action="store_true")
    args = p.parse_args()

    if args.suite:
        import time

        t0 = time.perf_counter()
        rows: list[dict[str, Any]] = []
        for name, f in suite_formulas(demo):
            rows.append(
                run_case(
                    demo,
                    f,
                    name,
                    alpha=args.alpha,
                    beta=args.beta,
                    rho_mode=args.rho_mode,
                    slack_mode=args.slack_mode,
                )
            )
        for seed in (0, 1, 2):
            rng = random.Random(seed)
            nv = max(1, args.num_vars)
            mc = max(0, args.num_clauses)
            f = demo.random_3sat_formula(nv, mc, rng)
            rows.append(
                run_case(
                    demo,
                    f,
                    f"random(n={f.num_vars},m={args.num_clauses},seed={seed})",
                    alpha=args.alpha,
                    beta=args.beta,
                    rho_mode=args.rho_mode,
                    slack_mode=args.slack_mode,
                )
            )
        wall = time.perf_counter() - t0
        if args.json:
            print(json.dumps({"wall_seconds": wall, "runs": rows}, indent=2))
        else:
            print(
                f"Suite: α={args.alpha} β={args.beta} rho={args.rho_mode} slack={args.slack_mode}  ({wall:.3f}s)\n"
            )
            for r in rows:
                pf = r["promising_flags"]
                print(
                    f"{r['label'][:52]:<52} "
                    f"D={r['ambient_dim_D']:<5} "
                    f"pca12={r['pca_explained_top2']:.3f} "
                    f"imb={r['tour_imbalance_ratio']:.3f} "
                    f"minSep={r['pca_plane']['min_pairwise_dist']:.4f} "
                    f"prom={pf['pca_concentrated_top2']}/{pf['large_min_sep_pca']}"
                )
        return 0

    if args.sweep_alpha_beta:
        rng = random.Random(args.seed)
        if args.formula == "example":
            f, lab = demo.EXAMPLE, "example"
        elif args.formula == "known":
            if not args.known_name:
                print("error: --known-name required", file=sys.stderr)
                return 2
            mp = {t[0]: t for t in demo.KNOWN_SAT_BENCHMARKS}
            if args.known_name not in mp:
                return 2
            f, lab = mp[args.known_name][1], args.known_name
        else:
            f = demo.random_3sat_formula(args.num_vars, args.num_clauses, rng)
            lab = f"random(n={args.num_vars},m={args.num_clauses},s={args.seed})"

        grid = (0.25, 0.5, 1.0)
        sweep: list[dict[str, Any]] = []
        for a in grid:
            for b in grid:
                r = run_case(demo, f, lab, alpha=a, beta=b, rho_mode=args.rho_mode, slack_mode=args.slack_mode)
                sweep.append(
                    {
                        "alpha": a,
                        "beta": b,
                        "pca_top2": r["pca_explained_top2"],
                        "imbalance": r["tour_imbalance_ratio"],
                        "min_sep": r["pca_plane"]["min_pairwise_dist"],
                    }
                )
        best = max(sweep, key=lambda z: z["pca_top2"] + min(1.0, z["min_sep"]))
        if args.json:
            print(json.dumps({"formula": lab, "sweep": sweep, "best_by_pca_plus_sep": best}, indent=2))
        else:
            print(f"Sweep on {lab} (rho={args.rho_mode}, slack={args.slack_mode})")
            for z in sweep:
                print(
                    f"  α={z['alpha']:.2f} β={z['beta']:.2f}  "
                    f"pca12={z['pca_top2']:.3f}  imb={z['imbalance']:.3f}  minSep={z['min_sep']:.5f}"
                )
            print(f"best (pca12 + capped minSep): α={best['alpha']} β={best['beta']}")
        return 0

    if args.formula == "example":
        f, lab = demo.EXAMPLE, "EXAMPLE"
    elif args.formula == "random":
        rng = random.Random(args.seed)
        f = demo.random_3sat_formula(args.num_vars, args.num_clauses, rng)
        lab = f"random(n={args.num_vars},m={args.num_clauses},seed={args.seed})"
    else:
        if not args.known_name:
            print("error: --known-name required", file=sys.stderr)
            return 2
        mp = {t[0]: t for t in demo.KNOWN_SAT_BENCHMARKS}
        if args.known_name not in mp:
            print("error: bad known-name", file=sys.stderr)
            return 2
        f, lab = mp[args.known_name][1], args.known_name

    r = run_case(
        demo,
        f,
        lab,
        alpha=args.alpha,
        beta=args.beta,
        rho_mode=args.rho_mode,
        slack_mode=args.slack_mode,
    )
    if args.json:
        print(json.dumps(r, indent=2))
    else:
        print(json.dumps(r, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

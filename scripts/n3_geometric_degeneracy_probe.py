#!/usr/bin/env python3
"""
Geometric route probe for n=3:
1) exact degenerate case (uniform off-diagonal cost),
2) additive perturbation path from degeneracy,
3) compare oracle best cost vs exact optimum and ratio envelope.
"""

from __future__ import annotations

import argparse
import json
from typing import Any

from edge_space_atsp_oracle import exact_atsp_small, solve_edge_space_atsp


def build_uniform_n3(offdiag: float) -> list[list[float]]:
    return [
        [0.0, offdiag, offdiag],
        [offdiag, 0.0, offdiag],
        [offdiag, offdiag, 0.0],
    ]


def envelope3() -> float:
    return 1.0 + (3.0 ** (1.0 / 3.0))


def run_once(
    dist: list[list[float]],
    rounds: int,
    max_steps: int,
    top_k: int,
    seeded_local_search: bool,
) -> dict[str, Any]:
    out = solve_edge_space_atsp(
        dist=dist,
        rounds=rounds,
        peel_start=2,
        max_steps=max_steps,
        top_k=top_k,
        seeded_local_search=seeded_local_search,
    )
    opt, opt_tour = exact_atsp_small(dist)
    best = float(out["best_by_cost"]["tour_cost"])
    ratio = best / max(1e-12, opt)
    return {
        "oracle_best_cost": best,
        "oracle_best_tour": out["best_by_cost"]["tour"],
        "exact_optimal_cost": opt,
        "exact_optimal_tour": opt_tour,
        "gap_additive": best - opt,
        "ratio": ratio,
        "envelope3": envelope3(),
        "within_envelope3": ratio <= envelope3() + 1e-12,
        "degenerate_uniform_detected": out.get("degenerate_uniform_detected", False),
        "degenerate_uniform_spread": out.get("degenerate_uniform_spread", 0.0),
    }


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="n=3 geometric degeneracy and additive perturbation probe")
    p.add_argument("--offdiag", type=float, default=1.0, help="uniform off-diagonal cost in degenerate case")
    p.add_argument(
        "--deltas",
        type=str,
        default="0.0,0.01,0.05,0.1,0.2,0.5",
        help="comma-separated additive perturbations applied to edge (0->1)",
    )
    p.add_argument("--rounds", type=int, default=1, help="oracle rounds")
    p.add_argument("--max-steps", type=int, default=120, help="oracle max steps")
    p.add_argument("--top-k", type=int, default=6, help="oracle top-k")
    p.add_argument("--seeded-local-search", action=argparse.BooleanOptionalAction, default=True, help="enable seeded 2-opt/3-opt stage")
    p.add_argument("--json", action="store_true", help="emit JSON")
    return p


def main() -> None:
    args = build_parser().parse_args()
    if args.offdiag <= 0.0:
        raise SystemExit("--offdiag must be > 0")
    if args.rounds < 1 or args.max_steps < 1 or args.top_k < 1:
        raise SystemExit("--rounds, --max-steps, --top-k must be >= 1")

    try:
        deltas = [float(x.strip()) for x in args.deltas.split(",") if x.strip()]
    except ValueError as ex:
        raise SystemExit(f"invalid --deltas: {ex}") from ex
    if not deltas:
        raise SystemExit("--deltas must contain at least one value")

    base = build_uniform_n3(args.offdiag)
    baseline = run_once(
        base,
        rounds=args.rounds,
        max_steps=args.max_steps,
        top_k=args.top_k,
        seeded_local_search=args.seeded_local_search,
    )

    rows: list[dict[str, Any]] = []
    for d in deltas:
        pert = [row[:] for row in base]
        pert[0][1] = args.offdiag + d
        row = run_once(
            pert,
            rounds=args.rounds,
            max_steps=args.max_steps,
            top_k=args.top_k,
            seeded_local_search=args.seeded_local_search,
        )
        row["delta_edge_0_1"] = d
        rows.append(row)

    payload = {
        "n": 3,
        "offdiag": args.offdiag,
        "baseline_degenerate": baseline,
        "perturbation_rows": rows,
    }

    if args.json:
        print(json.dumps(payload, indent=2))
        return

    print(
        f"n=3 offdiag={args.offdiag:.6f} "
        f"baseline ratio={baseline['ratio']:.6f} "
        f"gap={baseline['gap_additive']:.6f} "
        f"within_envelope3={baseline['within_envelope3']}"
    )
    print("delta,oracle_cost,exact_cost,gap,ratio,within_envelope3")
    for r in rows:
        print(
            f"{r['delta_edge_0_1']:.6f},"
            f"{r['oracle_best_cost']:.6f},"
            f"{r['exact_optimal_cost']:.6f},"
            f"{r['gap_additive']:.6f},"
            f"{r['ratio']:.6f},"
            f"{r['within_envelope3']}"
        )


if __name__ == "__main__":
    main()


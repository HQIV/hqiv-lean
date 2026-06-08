#!/usr/bin/env python3
"""
Falsification harness for rapidity-inequality prune safety.

For each random small ATSP instance, we compute all exact optimal tours and
check whether a rapidity-dominance edge ledger (at a chosen scale) would prune
every optimal witness. Any such case is a counterexample to witness safety.
"""

from __future__ import annotations

import argparse
import itertools
import math
from dataclasses import dataclass

from directed_torus_atsp_oracle import rapidity_delta, rapidity_dominated_edges, random_asymmetric_matrix


@dataclass
class SafetyStats:
    total: int = 0
    unsafe: int = 0


def closed_tour_cost(dist: list[list[float]], tour: list[int]) -> float:
    n = len(tour)
    return sum(dist[tour[i]][tour[(i + 1) % n]] for i in range(n))


def all_optimal_tours(dist: list[list[float]]) -> tuple[float, list[list[int]]]:
    n = len(dist)
    best = math.inf
    opts: list[list[int]] = []
    for perm in itertools.permutations(range(1, n)):
        tour = [0, *perm]
        c = closed_tour_cost(dist, tour)
        if c < best - 1e-12:
            best = c
            opts = [tour]
        elif abs(c - best) <= 1e-12:
            opts.append(tour)
    return best, opts


def mean_edge_cost(dist: list[list[float]]) -> float:
    n = len(dist)
    s = 0.0
    cnt = 0
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            s += dist[i][j]
            cnt += 1
    return s / float(max(1, cnt))


def tour_has_dominated_edge(tour: list[int], dominated: set[tuple[int, int]]) -> bool:
    n = len(tour)
    for i in range(n):
        if (tour[i], tour[(i + 1) % n]) in dominated:
            return True
    return False


def instance_is_unsafe(dist: list[list[float]], scale: float) -> tuple[bool, int, float, list[int] | None]:
    n = len(dist)
    best_cost, opts = all_optimal_tours(dist)
    du = rapidity_delta(n * n)
    dv = rapidity_delta(2 * n * n)
    dominated = rapidity_dominated_edges(
        dist=dist,
        rapidity_du=du,
        rapidity_dv=dv,
        mean_edge=mean_edge_cost(dist),
        scale=scale,
    )
    if not opts:
        return False, len(dominated), best_cost, None
    unsafe = all(tour_has_dominated_edge(t, dominated) for t in opts)
    return unsafe, len(dominated), best_cost, (opts[0] if opts else None)


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Check rapidity prune witness safety by exact falsification")
    p.add_argument("--n-min", type=int, default=7, help="minimum city count")
    p.add_argument("--n-max", type=int, default=8, help="maximum city count")
    p.add_argument("--trials", type=int, default=100, help="random instances per n")
    p.add_argument("--seed-base", type=int, default=9999, help="seed base")
    p.add_argument(
        "--scales",
        type=str,
        default=f"1.0,{math.sqrt(2):.12f},2.0",
        help="comma-separated rapidity-prune scales to test",
    )
    p.add_argument(
        "--show-first-counterexample",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="print first counterexample metadata for each scale",
    )
    return p


def main() -> None:
    args = build_parser().parse_args()
    if args.n_min < 3 or args.n_max < args.n_min:
        raise SystemExit("require 3 <= n-min <= n-max")
    if args.trials < 1:
        raise SystemExit("--trials must be >= 1")
    scales = [float(x.strip()) for x in args.scales.split(",") if x.strip()]
    if not scales:
        raise SystemExit("at least one scale is required")

    for n in range(args.n_min, args.n_max + 1):
        print(f"n={n}")
        for scale in scales:
            stats = SafetyStats()
            first_cex: tuple[int, int, float, list[int] | None] | None = None
            for t in range(args.trials):
                seed = args.seed_base + 131 * n + t
                dist = random_asymmetric_matrix(n, seed)
                unsafe, dominated_count, best_cost, sample_opt = instance_is_unsafe(dist, scale)
                stats.total += 1
                if unsafe:
                    stats.unsafe += 1
                    if first_cex is None:
                        first_cex = (t, dominated_count, best_cost, sample_opt)
            rate = stats.unsafe / float(max(1, stats.total))
            print(
                f"  scale={scale:.6f} unsafe={stats.unsafe}/{stats.total} "
                f"rate={rate:.4f}"
            )
            if args.show_first_counterexample and first_cex is not None:
                trial_idx, dom_n, best_cost, sample_opt = first_cex
                print(
                    f"    first_counterexample trial={trial_idx} dominated_edges={dom_n} "
                    f"best_cost={best_cost:.6f} sample_opt={sample_opt}"
                )


if __name__ == "__main__":
    main()


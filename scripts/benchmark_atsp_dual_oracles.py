#!/usr/bin/env python3
"""
Run directed-torus and edge-space ATSP oracles on the same problem set.

Reports per-n aggregate metrics for:
  - directed_torus_atsp_oracle
  - edge_space_atsp_oracle
  - hybrid best-of-two (min cost from either oracle per instance)
"""

from __future__ import annotations

import argparse
import statistics
import time
from dataclasses import dataclass

from directed_torus_atsp_oracle import (
    directed_torus_atsp_solver,
    exact_atsp_small,
    random_asymmetric_matrix,
)
from edge_space_atsp_oracle import solve_edge_space_atsp


@dataclass
class InstanceResult:
    n: int
    seed: int
    directed_time_s: float
    directed_cost: float
    edge_time_s: float
    edge_cost: float
    exact_cost: float | None


def pctl(xs: list[float], q: float) -> float:
    if not xs:
        return 0.0
    ys = sorted(xs)
    idx = int(max(0, min(len(ys) - 1, round((len(ys) - 1) * q))))
    return ys[idx]


def run_instance(
    n: int,
    seed: int,
    directed_max_steps: int,
    directed_top_k: int,
    edge_rounds: int,
    edge_peel_start: int,
    edge_max_steps: int,
    edge_top_k: int,
    exact_if_at_most: int,
) -> InstanceResult:
    dist = random_asymmetric_matrix(n, seed)

    t0 = time.perf_counter()
    directed = directed_torus_atsp_solver(
        dist=dist,
        optimizer="iterative-peel-anneal",
        max_steps=directed_max_steps,
        top_k=directed_top_k,
        iterative_rounds=4,
        iterative_arity_start=2,
        iterative_stage_topk=max(12, directed_top_k),
        iterative_early_stop_patience=2,
        iterative_early_stop_tol=1e-9,
        rapidity_prune=True,
        rapidity_prune_scale=1.0,
        rapidity_prune_scale_mode="sqrt-n-over-arity",
        anneal_rapidity_barrier=True,
        anneal_barrier_strength=1.0,
        anneal_rapidity_window=4,
        anneal_rapidity_weight=0.25,
        anneal_rapidity_jitter_weight=0.10,
        anneal_shell_width=0.25,
        anneal_shell_keep_per_band=0,
    )
    directed_time_s = time.perf_counter() - t0
    directed_cost = float(directed["best_by_cost"]["tour_cost"])

    t1 = time.perf_counter()
    edge = solve_edge_space_atsp(
        dist=dist,
        rounds=edge_rounds,
        peel_start=edge_peel_start,
        max_steps=edge_max_steps,
        top_k=edge_top_k,
        rapidity_window=4,
        soft_alpha=0.85,
        use_soft_prune=True,
    )
    edge_time_s = time.perf_counter() - t1
    edge_cost = float(edge["best_by_cost"]["tour_cost"])

    exact_cost: float | None = None
    if n <= exact_if_at_most:
        exact_cost, _ = exact_atsp_small(dist)

    return InstanceResult(
        n=n,
        seed=seed,
        directed_time_s=directed_time_s,
        directed_cost=directed_cost,
        edge_time_s=edge_time_s,
        edge_cost=edge_cost,
        exact_cost=exact_cost,
    )


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Benchmark directed-torus vs edge-space ATSP oracles")
    p.add_argument("--n-min", type=int, default=8, help="minimum city count")
    p.add_argument("--n-max", type=int, default=10, help="maximum city count")
    p.add_argument("--trials", type=int, default=10, help="instances per n")
    p.add_argument("--seed-base", type=int, default=1234, help="seed base")
    p.add_argument("--directed-max-steps", type=int, default=500, help="max steps for directed-torus solver")
    p.add_argument("--directed-top-k", type=int, default=12, help="top-k for directed-torus solver")
    p.add_argument("--edge-rounds", type=int, default=3, help="macro rounds for edge-space solver")
    p.add_argument("--edge-peel-start", type=int, default=2, help="starting arity for edge-space peel")
    p.add_argument("--edge-max-steps", type=int, default=800, help="max steps for edge-space solver")
    p.add_argument("--edge-top-k", type=int, default=12, help="top-k for edge-space solver")
    p.add_argument("--exact-if-at-most", type=int, default=10, help="exact checker threshold")
    return p


def main() -> None:
    args = build_parser().parse_args()
    if args.n_min < 2 or args.n_max < args.n_min:
        raise SystemExit("require 2 <= n-min <= n-max")
    if args.trials < 1:
        raise SystemExit("--trials must be >= 1")

    all_rows: list[InstanceResult] = []
    for n in range(args.n_min, args.n_max + 1):
        for t in range(args.trials):
            seed = args.seed_base + 10007 * n + t
            all_rows.append(
                run_instance(
                    n=n,
                    seed=seed,
                    directed_max_steps=args.directed_max_steps,
                    directed_top_k=args.directed_top_k,
                    edge_rounds=args.edge_rounds,
                    edge_peel_start=args.edge_peel_start,
                    edge_max_steps=args.edge_max_steps,
                    edge_top_k=args.edge_top_k,
                    exact_if_at_most=args.exact_if_at_most,
                )
            )

    print(
        "n,"
        "directed_mean_s,directed_p90_s,directed_cost_mean,"
        "edge_mean_s,edge_p90_s,edge_cost_mean,"
        "hybrid_cost_mean,"
        "directed_gap_mean,edge_gap_mean,hybrid_gap_mean,"
        "wins_directed,wins_edge,wins_tie"
    )

    for n in range(args.n_min, args.n_max + 1):
        rows = [r for r in all_rows if r.n == n]
        d_t = [r.directed_time_s for r in rows]
        e_t = [r.edge_time_s for r in rows]
        d_c = [r.directed_cost for r in rows]
        e_c = [r.edge_cost for r in rows]
        h_c = [min(r.directed_cost, r.edge_cost) for r in rows]

        d_gap: list[float] = []
        e_gap: list[float] = []
        h_gap: list[float] = []
        wins_directed = 0
        wins_edge = 0
        wins_tie = 0

        for r in rows:
            if abs(r.directed_cost - r.edge_cost) <= 1e-9:
                wins_tie += 1
            elif r.directed_cost < r.edge_cost:
                wins_directed += 1
            else:
                wins_edge += 1

            if r.exact_cost is not None:
                d_gap.append(r.directed_cost - r.exact_cost)
                e_gap.append(r.edge_cost - r.exact_cost)
                h_gap.append(min(r.directed_cost, r.edge_cost) - r.exact_cost)

        def mean_or_zero(xs: list[float]) -> float:
            return statistics.mean(xs) if xs else 0.0

        print(
            f"{n},"
            f"{statistics.mean(d_t):.6f},{pctl(d_t,0.9):.6f},{statistics.mean(d_c):.6f},"
            f"{statistics.mean(e_t):.6f},{pctl(e_t,0.9):.6f},{statistics.mean(e_c):.6f},"
            f"{statistics.mean(h_c):.6f},"
            f"{mean_or_zero(d_gap):.6f},{mean_or_zero(e_gap):.6f},{mean_or_zero(h_gap):.6f},"
            f"{wins_directed},{wins_edge},{wins_tie}"
        )


if __name__ == "__main__":
    main()


#!/usr/bin/env python3
"""
Benchmark "no-prune ATSP search" versus "exact step-down n -> floor_n".

This is an empirical harness for the dense ATSP regime where pruning may not
be reliable. It reports runtime statistics for:
  1) geometric no-prune solver at full n; and
  2) exact brute-force chain on progressively smaller matrices.
"""

from __future__ import annotations

import argparse
import math
import statistics
import time
from dataclasses import dataclass

from directed_torus_atsp_oracle import (
    directed_torus_atsp_solver,
    exact_atsp_small,
    rapidity_delta,
    random_asymmetric_matrix,
)


@dataclass
class TrialResult:
    n: int
    trial: int
    no_prune_seconds: float
    no_prune_unique: int
    exact_stepdown_seconds: float
    exact_levels: int


def pctl(xs: list[float], q: float) -> float:
    if not xs:
        return 0.0
    ys = sorted(xs)
    idx = int(max(0, min(len(ys) - 1, round((len(ys) - 1) * q))))
    return ys[idx]


def remove_city(m: list[list[float]], city: int) -> list[list[float]]:
    keep = [i for i in range(len(m)) if i != city]
    return [[m[i][j] for j in keep] for i in keep]


def heaviest_incident_city(m: list[list[float]]) -> int:
    n = len(m)
    if n <= 1:
        return 0
    scores: list[tuple[float, int]] = []
    for i in range(n):
        s = 0.0
        for j in range(n):
            if i == j:
                continue
            s += m[i][j] + m[j][i]
        scores.append((s, i))
    scores.sort(reverse=True)
    return scores[0][1]


def rapidity_guided_city(m: list[list[float]]) -> int:
    """
    Drop city with largest rapidity load in current manifold.

    The load combines:
      - directed skew (outflow - inflow), and
      - outgoing roughness (std-dev),
    normalized by per-manifold rapidity channels (du, dv).
    """
    n = len(m)
    if n <= 1:
        return 0
    du = max(1e-12, rapidity_delta(n * n))
    dv = max(1e-12, rapidity_delta(2 * n * n))
    best_score = -math.inf
    best_city = 0
    for i in range(n):
        out_vals = [m[i][j] for j in range(n) if j != i]
        in_vals = [m[j][i] for j in range(n) if j != i]
        out_mean = sum(out_vals) / max(1, len(out_vals))
        in_mean = sum(in_vals) / max(1, len(in_vals))
        skew = abs(out_mean - in_mean)
        rough = 0.0
        if out_vals:
            var = sum((x - out_mean) ** 2 for x in out_vals) / float(len(out_vals))
            rough = math.sqrt(max(0.0, var))
        load = (skew / du) + (rough / dv)
        if load > best_score:
            best_score = load
            best_city = i
    return best_city


def exact_stepdown_runtime(
    matrix: list[list[float]],
    floor_n: int,
    drop_policy: str,
) -> tuple[float, int]:
    cur = [row[:] for row in matrix]
    total = 0.0
    levels = 0
    while len(cur) >= max(2, floor_n):
        t0 = time.perf_counter()
        exact_atsp_small(cur)
        total += time.perf_counter() - t0
        levels += 1
        if len(cur) == max(2, floor_n):
            break
        if drop_policy == "heaviest-incident":
            city = heaviest_incident_city(cur)
        elif drop_policy == "rapidity-guided":
            city = rapidity_guided_city(cur)
        else:  # tail
            city = len(cur) - 1
        cur = remove_city(cur, city)
    return total, levels


def run_trial(
    n: int,
    trial: int,
    seed_base: int,
    optimizer: str,
    max_steps: int,
    top_k: int,
    floor_n: int,
    drop_policy: str,
) -> TrialResult:
    matrix = random_asymmetric_matrix(n, seed_base + 7919 * n + trial)

    t0 = time.perf_counter()
    payload = directed_torus_atsp_solver(
        dist=matrix,
        max_steps=max_steps,
        top_k=top_k,
        optimizer=optimizer,
        first_sat_stop=False,
    )
    no_prune_seconds = time.perf_counter() - t0

    step_seconds, levels = exact_stepdown_runtime(
        matrix=matrix,
        floor_n=floor_n,
        drop_policy=drop_policy,
    )

    return TrialResult(
        n=n,
        trial=trial,
        no_prune_seconds=no_prune_seconds,
        no_prune_unique=payload.get("unique_tours_sampled", 0),
        exact_stepdown_seconds=step_seconds,
        exact_levels=levels,
    )


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Benchmark no-prune ATSP vs exact step-down chain")
    p.add_argument("--n-min", type=int, default=8, help="smallest n to benchmark")
    p.add_argument("--n-max", type=int, default=11, help="largest n to benchmark")
    p.add_argument("--trials", type=int, default=5, help="number of random trials per n")
    p.add_argument("--seed-base", type=int, default=1234, help="seed base for random matrix generation")
    p.add_argument(
        "--optimizer",
        choices=("golden-section", "spiral"),
        default="golden-section",
        help="no-prune optimizer used for full-n geometric run",
    )
    p.add_argument("--max-steps", type=int, default=1200, help="step budget for geometric no-prune run")
    p.add_argument("--top-k", type=int, default=24, help="top-k retained inside no-prune solver")
    p.add_argument("--floor-n", type=int, default=7, help="stop exact step-down when n reaches this size")
    p.add_argument(
        "--drop-policy",
        choices=("heaviest-incident", "rapidity-guided", "tail"),
        default="rapidity-guided",
        help="how to choose city removed at each exact step-down level",
    )
    return p


def main() -> None:
    args = build_parser().parse_args()
    if args.n_min < 2 or args.n_max < args.n_min:
        raise SystemExit("require 2 <= n-min <= n-max")
    if args.trials < 1:
        raise SystemExit("--trials must be >= 1")
    if args.max_steps < 1:
        raise SystemExit("--max-steps must be >= 1")
    if args.top_k < 1:
        raise SystemExit("--top-k must be >= 1")
    if args.floor_n < 2:
        raise SystemExit("--floor-n must be >= 2")

    all_rows: list[TrialResult] = []
    for n in range(args.n_min, args.n_max + 1):
        for trial in range(args.trials):
            all_rows.append(
                run_trial(
                    n=n,
                    trial=trial,
                    seed_base=args.seed_base,
                    optimizer=args.optimizer,
                    max_steps=args.max_steps,
                    top_k=args.top_k,
                    floor_n=args.floor_n,
                    drop_policy=args.drop_policy,
                )
            )

    print(
        "n,no_prune_mean_s,no_prune_p90_s,stepdown_mean_s,stepdown_p90_s,"
        "stepdown/no_prune,mean_unique,mean_levels"
    )
    for n in range(args.n_min, args.n_max + 1):
        rows = [r for r in all_rows if r.n == n]
        no_prune = [r.no_prune_seconds for r in rows]
        stepdown = [r.exact_stepdown_seconds for r in rows]
        mean_unique = statistics.mean(r.no_prune_unique for r in rows)
        mean_levels = statistics.mean(r.exact_levels for r in rows)
        np_mean = statistics.mean(no_prune)
        sd_mean = statistics.mean(stepdown)
        ratio = sd_mean / max(1e-12, np_mean)
        print(
            f"{n},{np_mean:.6f},{pctl(no_prune, 0.9):.6f},"
            f"{sd_mean:.6f},{pctl(stepdown, 0.9):.6f},"
            f"{ratio:.2f},{mean_unique:.1f},{mean_levels:.1f}"
        )


if __name__ == "__main__":
    main()


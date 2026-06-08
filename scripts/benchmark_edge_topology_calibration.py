#!/usr/bin/env python3
"""
Phase-5 calibration harness for edge-space topology policy.

Runs exact-checkable random ATSP instances and compares topology policy/weight
configurations against the topology-off baseline.
"""

from __future__ import annotations

import argparse
import statistics
import time
from dataclasses import dataclass

from edge_space_atsp_oracle import exact_atsp_small, random_asymmetric_matrix, solve_edge_space_atsp


@dataclass
class TrialResult:
    n: int
    seed: int
    config_name: str
    elapsed_s: float
    gap: float
    top_weight_mean: float


def parse_csv_floats(s: str) -> list[float]:
    return [float(x.strip()) for x in s.split(",") if x.strip()]


def parse_csv_ints(s: str) -> list[int]:
    return [int(x.strip()) for x in s.split(",") if x.strip()]


def parse_csv_strings(s: str) -> list[str]:
    return [x.strip() for x in s.split(",") if x.strip()]


def run_one(
    n: int,
    seed: int,
    rounds: int,
    max_steps: int,
    top_k: int,
    policy: str,
    top_weight: float,
    jitter_weight: float,
    top_window: int,
) -> TrialResult:
    dist = random_asymmetric_matrix(n, seed)
    exact, _ = exact_atsp_small(dist)
    t0 = time.perf_counter()
    payload = solve_edge_space_atsp(
        dist=dist,
        rounds=rounds,
        peel_start=2,
        max_steps=max_steps,
        top_k=top_k,
        rapidity_window=4,
        topology_policy=policy,
        topology_regularizer_weight=top_weight,
        topology_jitter_weight=jitter_weight,
        topology_window=top_window,
    )
    elapsed = time.perf_counter() - t0
    best = float(payload["best_by_cost"]["tour_cost"])
    return TrialResult(
        n=n,
        seed=seed,
        config_name=f"{policy}|w={top_weight:.4f}|j={jitter_weight:.3f}|win={top_window}",
        elapsed_s=elapsed,
        gap=best - exact,
        top_weight_mean=float(payload["mean_topology_weight_applied"]),
    )


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Calibrate Phase-5 topology policy for edge-space ATSP")
    p.add_argument("--n-min", type=int, default=8, help="minimum city count")
    p.add_argument("--n-max", type=int, default=10, help="maximum city count")
    p.add_argument("--trials", type=int, default=4, help="instances per n")
    p.add_argument("--seed-base", type=int, default=1234, help="seed base")
    p.add_argument("--rounds", type=int, default=2, help="edge-space rounds")
    p.add_argument("--max-steps", type=int, default=240, help="edge-space max steps")
    p.add_argument("--top-k", type=int, default=10, help="edge-space top-k")
    p.add_argument("--policies", type=str, default="fixed,residual-gated,arity-ramp,residual-arity", help="comma-separated topology policies")
    p.add_argument("--weights", type=str, default="0.02,0.05,0.08,0.12", help="comma-separated topology base weights")
    p.add_argument("--jitter-weights", type=str, default="0.0,0.5,1.0", help="comma-separated topology jitter weights")
    p.add_argument("--windows", type=str, default="3,4", help="comma-separated topology windows")
    return p


def main() -> None:
    args = build_parser().parse_args()
    if args.n_min < 2 or args.n_max < args.n_min:
        raise SystemExit("require 2 <= n-min <= n-max")
    if args.trials < 1:
        raise SystemExit("--trials must be >= 1")
    if args.rounds < 1 or args.max_steps < 1 or args.top_k < 1:
        raise SystemExit("--rounds, --max-steps, --top-k must be >= 1")

    policies = parse_csv_strings(args.policies)
    weights = parse_csv_floats(args.weights)
    jitter_weights = parse_csv_floats(args.jitter_weights)
    windows = parse_csv_ints(args.windows)
    if not policies or not weights or not jitter_weights or not windows:
        raise SystemExit("policies/weights/jitter-weights/windows must be non-empty")
    if any(w < 0.0 for w in weights):
        raise SystemExit("weights must be >= 0")
    if any(j < 0.0 for j in jitter_weights):
        raise SystemExit("jitter-weights must be >= 0")
    if any(w < 3 for w in windows):
        raise SystemExit("windows must be >= 3")

    baseline_rows: list[TrialResult] = []
    config_rows: dict[str, list[TrialResult]] = {}
    for n in range(args.n_min, args.n_max + 1):
        for t in range(args.trials):
            seed = args.seed_base + 10007 * n + t
            base = run_one(
                n=n,
                seed=seed,
                rounds=args.rounds,
                max_steps=args.max_steps,
                top_k=args.top_k,
                policy="off",
                top_weight=0.0,
                jitter_weight=0.0,
                top_window=3,
            )
            baseline_rows.append(base)

            for policy in policies:
                for tw in weights:
                    for jw in jitter_weights:
                        for win in windows:
                            row = run_one(
                                n=n,
                                seed=seed,
                                rounds=args.rounds,
                                max_steps=args.max_steps,
                                top_k=args.top_k,
                                policy=policy,
                                top_weight=tw,
                                jitter_weight=jw,
                                top_window=win,
                            )
                            config_rows.setdefault(row.config_name, []).append(row)

    baseline_gap = statistics.mean(r.gap for r in baseline_rows)
    baseline_time = statistics.mean(r.elapsed_s for r in baseline_rows)

    print("config,mean_gap,delta_vs_baseline,mean_time_s,mean_topology_weight_applied")
    ranked: list[tuple[float, float, str, float, float]] = []
    for name, rows in config_rows.items():
        mg = statistics.mean(r.gap for r in rows)
        mt = statistics.mean(r.elapsed_s for r in rows)
        mw = statistics.mean(r.top_weight_mean for r in rows)
        ranked.append((mg, mt, name, mw, mg - baseline_gap))
    ranked.sort(key=lambda x: (x[0], x[1]))
    for mg, mt, name, mw, delta in ranked:
        print(f"{name},{mg:.6f},{delta:+.6f},{mt:.4f},{mw:.6f}")

    print(
        f"baseline(off),{baseline_gap:.6f},{0.0:+.6f},{baseline_time:.4f},{0.0:.6f}"
    )


if __name__ == "__main__":
    main()


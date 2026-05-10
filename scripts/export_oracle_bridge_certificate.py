#!/usr/bin/env python3
"""
Export finite-sample OracleBridgeAssumptions-style certificates.

This script emits JSON rows that mirror the Lean bridge contract fields in
`Hqiv/Geometry/ATSPWorstCaseCertified.lean`:
  - n, oracleCost, seedCost, optimalCost, ε
  - tensorResidualErr, rapidityErr, axisErr
and checks the bridge inequalities numerically.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from edge_space_atsp_oracle import exact_atsp_small, random_asymmetric_matrix, solve_edge_space_atsp


def envelope_term(n: int) -> float:
    nn = max(1, n)
    return float(nn) ** (1.0 / float(nn))


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Export OracleBridgeAssumptions-like certificate rows")
    p.add_argument("--n-min", type=int, default=8, help="minimum city count")
    p.add_argument("--n-max", type=int, default=10, help="maximum city count (requires exact checker)")
    p.add_argument("--trials", type=int, default=5, help="instances per n")
    p.add_argument("--seed-base", type=int, default=1234, help="seed base")
    p.add_argument("--rounds", type=int, default=2, help="solver rounds")
    p.add_argument("--max-steps", type=int, default=240, help="solver max steps")
    p.add_argument("--top-k", type=int, default=10, help="solver top-k")
    p.add_argument("--tol", type=float, default=1e-9, help="numeric tolerance for inequality checks")
    p.add_argument("--output-json", type=str, default="data/oracle_bridge_certificate.json", help="output JSON path")
    return p


def main() -> None:
    args = build_parser().parse_args()
    if args.n_min < 2 or args.n_max < args.n_min:
        raise SystemExit("require 2 <= n-min <= n-max")
    if args.n_max > 10:
        raise SystemExit("this exporter requires exact checker; set --n-max <= 10")
    if args.trials < 1:
        raise SystemExit("--trials must be >= 1")
    if args.rounds < 1 or args.max_steps < 1 or args.top_k < 1:
        raise SystemExit("--rounds, --max-steps, --top-k must be >= 1")
    if args.tol < 0.0:
        raise SystemExit("--tol must be >= 0")

    rows: list[dict[str, Any]] = []
    total = 0
    all_valid = 0

    for n in range(args.n_min, args.n_max + 1):
        env = envelope_term(n)
        for t in range(args.trials):
            seed = args.seed_base + 10007 * n + t
            dist = random_asymmetric_matrix(n, seed)
            optimal, optimal_tour = exact_atsp_small(dist)

            # Seed witness from stage-1 (no local completion).
            seed_payload = solve_edge_space_atsp(
                dist=dist,
                rounds=args.rounds,
                peel_start=2,
                max_steps=args.max_steps,
                top_k=args.top_k,
                seeded_local_search=False,
            )
            seed_row = seed_payload["best_by_cost"]
            seed_cost = float(seed_row["tour_cost"])
            tensor_residual_err = float(seed_row.get("trunc_error_bound_empirical", 0.0))
            rapidity_err = float(seed_row.get("rapidity_min_window", 0.0)) + float(
                seed_row.get("rapidity_jitter", 0.0)
            )
            axis_err = float(seed_row.get("topology_regularizer", 0.0))
            eps = tensor_residual_err + rapidity_err + axis_err

            # Final oracle witness with local completion.
            oracle_payload = solve_edge_space_atsp(
                dist=dist,
                rounds=args.rounds,
                peel_start=2,
                max_steps=args.max_steps,
                top_k=args.top_k,
                seeded_local_search=True,
            )
            oracle_row = oracle_payload["best_by_cost"]
            oracle_cost = float(oracle_row["tour_cost"])

            h_opt_pos = optimal > 0.0
            h_proj_residual = seed_cost <= (optimal + tensor_residual_err + rapidity_err + axis_err + args.tol)
            h_residual_budget = (tensor_residual_err + rapidity_err + axis_err) <= (eps + args.tol)
            h_local_completion = oracle_cost <= (seed_cost + args.tol)
            h_eps_envelope = eps <= (optimal * env + args.tol)

            ratio = oracle_cost / max(1e-12, optimal)
            bound = 1.0 + env
            bridge_valid = h_opt_pos and h_proj_residual and h_residual_budget and h_local_completion and h_eps_envelope
            envelope_valid = ratio <= bound + args.tol
            valid = bridge_valid and envelope_valid

            total += 1
            all_valid += int(valid)

            rows.append(
                {
                    "n": n,
                    "seed": seed,
                    "oracleCost": oracle_cost,
                    "seedCost": seed_cost,
                    "optimalCost": optimal,
                    "optimalTour": optimal_tour,
                    "ε": eps,
                    "tensorResidualErr": tensor_residual_err,
                    "rapidityErr": rapidity_err,
                    "axisErr": axis_err,
                    "ratio": ratio,
                    "bound": bound,
                    "checks": {
                        "hOptPos": h_opt_pos,
                        "hProjResidual": h_proj_residual,
                        "hResidualBudget": h_residual_budget,
                        "hLocalCompletion": h_local_completion,
                        "hEpsEnvelope": h_eps_envelope,
                        "envelopeRatio": envelope_valid,
                        "valid": valid,
                    },
                }
            )

    payload = {
        "meta": {
            "n_min": args.n_min,
            "n_max": args.n_max,
            "trials": args.trials,
            "seed_base": args.seed_base,
            "rounds": args.rounds,
            "max_steps": args.max_steps,
            "top_k": args.top_k,
            "tol": args.tol,
            "formula": "oracle/optimal <= 1 + n^(1/n)",
        },
        "summary": {
            "total": total,
            "all_valid": all_valid,
            "pass_rate": float(all_valid) / float(max(1, total)),
        },
        "rows": rows,
    }

    out_path = Path(args.output_json)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    print(
        f"wrote {out_path} rows={total} valid={all_valid} "
        f"pass_rate={payload['summary']['pass_rate']:.3f}"
    )


if __name__ == "__main__":
    main()


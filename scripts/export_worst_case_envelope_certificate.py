#!/usr/bin/env python3
"""
Export finite-sample worst-case envelope certificates for Lean.

The exported JSON rows align with `EnvelopeCertificate` fields in
`Hqiv/Geometry/ATSPWorstCaseCertified.lean`:
  - n
  - oracleCost
  - optimalCost
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from edge_space_atsp_oracle import exact_atsp_small, random_asymmetric_matrix, solve_edge_space_atsp


def envelope_bound(n: int) -> float:
    nn = max(1, n)
    return 1.0 + float(nn) ** (1.0 / float(nn))


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Export finite-sample envelope certificate JSON")
    p.add_argument("--n-min", type=int, default=8, help="minimum city count (exact-checkable range recommended)")
    p.add_argument("--n-max", type=int, default=10, help="maximum city count")
    p.add_argument("--trials", type=int, default=5, help="instances per n")
    p.add_argument("--seed-base", type=int, default=1234, help="seed base")
    p.add_argument("--rounds", type=int, default=2, help="edge-space rounds")
    p.add_argument("--max-steps", type=int, default=240, help="edge-space max steps")
    p.add_argument("--top-k", type=int, default=10, help="edge-space top-k")
    p.add_argument("--ratio-tol", type=float, default=1e-12, help="numeric tolerance for ratio<=bound check")
    p.add_argument("--output-json", type=str, default="data/worst_case_envelope_certificate.json", help="output JSON path")
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
    if args.ratio_tol < 0.0:
        raise SystemExit("--ratio-tol must be >= 0")

    rows: list[dict[str, Any]] = []
    total = 0
    passed = 0
    for n in range(args.n_min, args.n_max + 1):
        bound = envelope_bound(n)
        for t in range(args.trials):
            seed = args.seed_base + 10007 * n + t
            dist = random_asymmetric_matrix(n, seed)
            optimal, _ = exact_atsp_small(dist)
            payload = solve_edge_space_atsp(
                dist=dist,
                rounds=args.rounds,
                peel_start=2,
                max_steps=args.max_steps,
                top_k=args.top_k,
            )
            oracle = float(payload["best_by_cost"]["tour_cost"])
            ratio = oracle / max(1e-12, optimal)
            valid = ratio <= bound + args.ratio_tol
            total += 1
            passed += int(valid)
            rows.append(
                {
                    "n": n,
                    "seed": seed,
                    "oracleCost": oracle,
                    "optimalCost": optimal,
                    "ratio": ratio,
                    "bound": bound,
                    "valid": valid,
                }
            )

    out = {
        "meta": {
            "n_min": args.n_min,
            "n_max": args.n_max,
            "trials": args.trials,
            "seed_base": args.seed_base,
            "rounds": args.rounds,
            "max_steps": args.max_steps,
            "top_k": args.top_k,
            "ratio_tol": args.ratio_tol,
            "formula": "ratio <= 1 + n^(1/n)",
        },
        "summary": {
            "total": total,
            "passed": passed,
            "pass_rate": (float(passed) / float(max(1, total))),
            "all_valid": passed == total,
        },
        "certificates": rows,
    }

    out_path = Path(args.output_json)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2), encoding="utf-8")

    print(
        f"wrote {out_path} rows={total} passed={passed} "
        f"pass_rate={out['summary']['pass_rate']:.3f}"
    )


if __name__ == "__main__":
    main()


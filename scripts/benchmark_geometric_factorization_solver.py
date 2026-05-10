#!/usr/bin/env python3
"""
Benchmark geometric_factorization_solver across increasing bit lengths.

Focus: runtime + success/failure quality of recursive prime factorization export.
"""

from __future__ import annotations

import argparse
import json
import random
import statistics
import time
from pathlib import Path
from typing import Any

import sys

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

import geometric_factorization_solver as gfs  # noqa: E402


def _rand_odd_with_bits(rng: random.Random, bits: int) -> int:
    x = rng.getrandbits(bits)
    x |= (1 << (bits - 1))
    x |= 1
    return x


def _next_probable_prime(rng: random.Random, bits: int, max_tries: int = 50_000) -> int:
    x = _rand_odd_with_bits(rng, bits)
    for _ in range(max_tries):
        if gfs.is_probable_prime(x):
            return x
        x += 2
        if x.bit_length() > bits:
            x = _rand_odd_with_bits(rng, bits)
    raise RuntimeError(f"failed to sample probable prime with bits={bits}")


def _parse_bit_schedule(bits_arg: str) -> list[int]:
    values: list[int] = []
    for tok in bits_arg.split(","):
        tok = tok.strip()
        if not tok:
            continue
        values.append(int(tok))
    if not values:
        raise ValueError("bit schedule is empty")
    if any(b < 2 for b in values):
        raise ValueError("all bit sizes must be >= 2")
    return values


def _sample_composite(rng: random.Random, bitlen: int, mode: str) -> tuple[int, list[int], str]:
    if mode == "semiprime":
        p_bits = bitlen // 2
        q_bits = bitlen - p_bits
        p = _next_probable_prime(rng, p_bits)
        q = _next_probable_prime(rng, q_bits)
        return p * q, sorted([p, q]), "semiprime"
    if mode == "near_semiprime_twos":
        p_bits = max(2, bitlen // 2)
        q_bits = max(2, bitlen - p_bits - 2)
        p = _next_probable_prime(rng, p_bits)
        q = _next_probable_prime(rng, q_bits)
        return (4 * p * q), sorted([2, 2, p, q]), "4*p*q"
    raise ValueError(f"unsupported sample mode: {mode}")


def _bench_one(
    n: int,
    *,
    max_steps_per_node: int,
    max_seconds_per_node: float,
) -> dict[str, Any]:
    started = time.perf_counter()
    rec = gfs.recursive_prime_factorization(
        n,
        max_steps_per_node=max_steps_per_node,
        max_seconds_per_node=max_seconds_per_node,
        search_mode="auto",
        split_mode="auto",
    )
    elapsed = time.perf_counter() - started
    validation = gfs.validate_factor_export(n, rec)
    return {
        "elapsed_s": elapsed,
        "recursive": rec,
        "validation": validation,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Benchmark geometric factorization by bit length")
    parser.add_argument(
        "--bits",
        default="32,48,64,80,96,128,160,192,224,256,320,384,448,512,640,768,896,1024",
        help="comma-separated bit schedule",
    )
    parser.add_argument("--trials-per-bit", type=int, default=1, help="samples per bit size")
    parser.add_argument(
        "--sample-mode",
        choices=("semiprime", "near_semiprime_twos"),
        default="semiprime",
        help="composite sampling mode",
    )
    parser.add_argument("--max-steps-per-node", type=int, default=240, help="recursive node step budget")
    parser.add_argument("--max-seconds-per-node", type=float, default=10.0, help="recursive node time budget")
    parser.add_argument(
        "--stop-on-runtime-over",
        type=float,
        default=10.0,
        help="stop benchmark if any trial exceeds this runtime (<=0 disables)",
    )
    parser.add_argument("--seed", type=int, default=20260420, help="RNG seed")
    parser.add_argument("--json", action="store_true", help="print final JSON summary")
    args = parser.parse_args()

    if args.trials_per_bit < 1:
        raise SystemExit("--trials-per-bit must be >= 1")
    if args.max_steps_per_node < 1:
        raise SystemExit("--max-steps-per-node must be >= 1")
    if args.max_seconds_per_node <= 0:
        raise SystemExit("--max-seconds-per-node must be > 0")

    bit_schedule = _parse_bit_schedule(args.bits)
    rng = random.Random(args.seed)
    rows: list[dict[str, Any]] = []
    stop_threshold = args.stop_on_runtime_over if args.stop_on_runtime_over > 0 else None

    print(
        "bitlen,trial,n_bitlen,elapsed_s,verified,validation_status,failed_checks,"
        "prime_factor_count,unresolved_count,sample_label"
    )

    for bitlen in bit_schedule:
        for trial in range(args.trials_per_bit):
            n, expected, label = _sample_composite(rng, bitlen, args.sample_mode)
            out = _bench_one(
                n,
                max_steps_per_node=args.max_steps_per_node,
                max_seconds_per_node=args.max_seconds_per_node,
            )
            rec = out["recursive"]
            validation = out["validation"]
            row = {
                "bitlen": bitlen,
                "trial": trial,
                "n_bitlen": int(n.bit_length()),
                "elapsed_s": float(out["elapsed_s"]),
                "verified": bool(rec.get("verified_product", False)),
                "validation_status": str(validation.get("status")),
                "failed_checks": list(validation.get("failed_checks", [])),
                "prime_factor_count": len(rec.get("prime_factors", [])),
                "unresolved_count": len(rec.get("unresolved", [])),
                "sample_label": label,
                "expected_factor_count": len(expected),
            }
            rows.append(row)
            print(
                f"{row['bitlen']},{row['trial']},{row['n_bitlen']},{row['elapsed_s']:.6f},"
                f"{row['verified']},{row['validation_status']},{'|'.join(row['failed_checks'])},"
                f"{row['prime_factor_count']},{row['unresolved_count']},{row['sample_label']}"
            )
            if stop_threshold is not None and row["elapsed_s"] > stop_threshold:
                break
        if stop_threshold is not None and rows and rows[-1]["elapsed_s"] > stop_threshold:
            break

    grouped: dict[int, list[dict[str, Any]]] = {}
    for r in rows:
        grouped.setdefault(int(r["bitlen"]), []).append(r)

    summary_rows: list[dict[str, Any]] = []
    for bitlen in sorted(grouped):
        grp = grouped[bitlen]
        times = [float(r["elapsed_s"]) for r in grp]
        succ = [r for r in grp if r["validation_status"] == "pass"]
        summary_rows.append(
            {
                "bitlen": bitlen,
                "trials": len(grp),
                "successes": len(succ),
                "success_rate": len(succ) / len(grp),
                "time_min_s": min(times),
                "time_med_s": statistics.median(times),
                "time_max_s": max(times),
            }
        )

    if args.json:
        print("\nSUMMARY_JSON=")
        print(
            json.dumps(
                {
                    "config": {
                        "bits": bit_schedule,
                        "trials_per_bit": args.trials_per_bit,
                        "sample_mode": args.sample_mode,
                        "max_steps_per_node": args.max_steps_per_node,
                        "max_seconds_per_node": args.max_seconds_per_node,
                        "stop_on_runtime_over": args.stop_on_runtime_over,
                        "seed": args.seed,
                    },
                    "rows": rows,
                    "summary_by_bitlen": summary_rows,
                },
                indent=2,
            )
        )


if __name__ == "__main__":
    main()


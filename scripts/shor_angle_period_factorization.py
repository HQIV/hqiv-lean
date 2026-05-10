#!/usr/bin/env python3
"""
Shor-style angle-period factorization prototype (classical simulation).

Model:
- registers are angle slots on the #Q shell and reflected 2#Q span,
- multiplication gate acts on register pairs,
- period-finding is performed on gate-hit signals (classically simulated).
"""

from __future__ import annotations

import argparse
import json
import math
import time
from typing import Any

import geometric_factorization_solver as base


def q_span(n: int) -> int:
    return max(2, math.isqrt(max(2, n)))


def doubled_q_span(n: int) -> int:
    return 2 * q_span(n)


def counterpart_slot(slot: int, n: int) -> int:
    m = doubled_q_span(n)
    q = q_span(n)
    return (slot + q) % m


def low_branch_candidate(slot_low: int, n: int) -> int:
    q = q_span(n)
    if q <= 1:
        return 2
    return 2 + (slot_low % (q - 1))


def candidate_from_slot(slot: int, n: int) -> int:
    q = q_span(n)
    m = doubled_q_span(n)
    s = slot % m
    low_slot = s % q
    d = low_branch_candidate(low_slot, n)
    if s < q:
        return d
    if d <= 0:
        return n
    return n // d


def multiplication_gate(slot_a: int, slot_b: int, n: int) -> dict[str, Any]:
    a = candidate_from_slot(slot_a, n)
    b = candidate_from_slot(slot_b, n)
    product = a * b
    return {
        "slot_a": slot_a,
        "slot_b": slot_b,
        "a": a,
        "b": b,
        "product": product,
        "hits_n": (product == n),
    }


def _slot_from_phase(phase: float, n: int) -> int:
    tau = 2.0 * math.pi
    m = doubled_q_span(n)
    wrapped = phase % tau
    frac = wrapped / tau
    return int(frac * m) % m


def period_find_from_signal(signal: list[int]) -> dict[str, Any]:
    n = len(signal)
    if n < 4:
        return {"period": None, "score": 0, "lag_scores_top": []}
    centered = [1 if x else -1 for x in signal]
    lag_scores: list[tuple[int, int]] = []
    for lag in range(1, max(2, n // 2)):
        score = 0
        for i in range(0, n - lag):
            score += centered[i] * centered[i + lag]
        lag_scores.append((lag, score))
    lag_scores.sort(key=lambda kv: (-kv[1], kv[0]))
    best_lag, best_score = lag_scores[0]
    return {
        "period": best_lag,
        "score": best_score,
        "lag_scores_top": [{"lag": lag, "score": score} for lag, score in lag_scores[:10]],
    }


def shor_angle_period_once(
    n: int,
    *,
    max_steps: int | None = None,
    max_seconds: float | None = None,
) -> dict[str, Any]:
    if n <= 1:
        return {
            "n": n,
            "hits": [],
            "picked_factor": None,
            "one_step_pick_certificate": {"kind": "one-step-pick", "picked": False, "n": n},
            "period_analysis": [],
            "pipeline_mode": "shor-angle-period-multiplication-gate",
        }

    q = q_span(n)
    m = doubled_q_span(n)
    delta = base.rapidity_delta(n)
    seeds = [0.0, 2.0 * math.pi / 3.0, 4.0 * math.pi / 3.0]

    if max_steps is None:
        max_steps = min(8 * q, 4096)

    started = time.perf_counter()
    hits: list[dict[str, Any]] = []
    signal_per_seed: list[list[int]] = [[] for _ in seeds]
    slot_trace_per_seed: list[list[int]] = [[] for _ in seeds]
    picked_factor: int | None = None
    timed_out = False

    phase = 0.0
    for step in range(max_steps):
        if max_seconds is not None and (time.perf_counter() - started) >= max_seconds:
            timed_out = True
            break
        for seed_idx, seed in enumerate(seeds):
            slot_a = _slot_from_phase(phase + seed, n)
            slot_b = counterpart_slot(slot_a, n)
            gate = multiplication_gate(slot_a, slot_b, n)
            signal_per_seed[seed_idx].append(1 if gate["hits_n"] else 0)
            slot_trace_per_seed[seed_idx].append(slot_a)
            if gate["hits_n"]:
                low = min(gate["a"], gate["b"])
                if 1 < low < n and n % low == 0:
                    picked_factor = low
                    hits.append(
                        {
                            "step": step,
                            "seed_idx": seed_idx,
                            "slot_a": slot_a,
                            "slot_b": slot_b,
                            "a": gate["a"],
                            "b": gate["b"],
                            "picked_factor": low,
                        }
                    )
                    break
        if picked_factor is not None:
            break
        phase += delta

    period_analysis: list[dict[str, Any]] = []
    for seed_idx, sig in enumerate(signal_per_seed):
        per = period_find_from_signal(sig)
        period_analysis.append(
            {
                "seed_idx": seed_idx,
                "signal_hits": sum(sig),
                "samples": len(sig),
                "period": per["period"],
                "period_score": per["score"],
                "lag_scores_top": per["lag_scores_top"],
            }
        )

    cert: dict[str, Any]
    if picked_factor is None:
        cert = {
            "kind": "one-step-pick",
            "picked": False,
            "n": n,
            "reason": "no multiplication-gate period hit produced a nontrivial factor",
        }
        divisors = [1, n]
        symmetric_pair = None
    else:
        cofactor = n // picked_factor
        cert = {
            "kind": "one-step-pick",
            "picked": True,
            "n": n,
            "d": picked_factor,
            "cofactor": cofactor,
            "is_nontrivial": (1 < picked_factor < n),
            "divides": (n % picked_factor == 0),
            "pair_product_ok": (picked_factor * cofactor == n),
        }
        divisors = sorted({1, picked_factor, n})
        symmetric_pair = sorted([picked_factor, cofactor])

    return {
        "n": n,
        "pipeline_mode": "shor-angle-period-multiplication-gate",
        "q_span": q,
        "doubled_q_span": m,
        "rapidity_delta": delta,
        "steps_used": max(len(sig) for sig in signal_per_seed) if signal_per_seed else 0,
        "timed_out": timed_out,
        "elapsed_s": time.perf_counter() - started,
        "hits": hits,
        "picked_factor": picked_factor,
        "divisors": divisors,
        "symmetric_pair": symmetric_pair,
        "one_step_pick_certificate": cert,
        "period_analysis": period_analysis,
    }


def recursive_prime_factorization_shor_angle(
    n: int,
    *,
    max_steps_per_node: int | None = None,
    max_seconds_per_node: float | None = 1.0,
) -> dict[str, Any]:
    if n <= 1:
        return {
            "n": n,
            "prime_factors": [],
            "unresolved": [],
            "trace": [],
            "verified_product": (n == 1),
            "pipeline_mode": "shor-angle-period-multiplication-gate",
        }

    pending: list[int] = [n]
    prime_factors: list[int] = []
    unresolved: list[int] = []
    unresolved_primality_checks: list[dict[str, Any]] = []
    trace: list[dict[str, Any]] = []

    while pending:
        x = pending.pop()
        if x <= 1:
            continue
        if base.is_probable_prime(x):
            prime_factors.append(x)
            trace.append({"n": x, "status": "probable-prime", "split": None})
            continue

        node = shor_angle_period_once(
            x,
            max_steps=max_steps_per_node,
            max_seconds=max_seconds_per_node,
        )
        cert = node.get("one_step_pick_certificate", {})
        d = int(cert.get("d", 0)) if cert.get("picked", False) else 0
        good = bool(
            cert.get("picked", False)
            and cert.get("is_nontrivial", False)
            and cert.get("divides", False)
            and cert.get("pair_product_ok", False)
            and 1 < d < x
        )
        if not good:
            unresolved.append(x)
            probable = base.is_probable_prime(x)
            unresolved_primality_checks.append(
                {
                    "n": x,
                    "probable_prime": probable,
                    "primality_test": "pass" if probable else "fail",
                }
            )
            trace.append(
                {
                    "n": x,
                    "status": "unresolved",
                    "reason": cert.get("reason", "no nontrivial divisor pick"),
                    "steps_used": node.get("steps_used"),
                    "timed_out": node.get("timed_out"),
                    "probable_prime": probable,
                    "primality_test": "pass" if probable else "fail",
                }
            )
            continue

        q = x // d
        trace.append(
            {
                "n": x,
                "status": "split",
                "split": [d, q],
                "steps_used": node.get("steps_used"),
            }
        )
        pending.append(d)
        pending.append(q)

    prime_factors.sort()
    product = 1
    for p in prime_factors:
        product *= p
    verified = (len(unresolved) == 0) and (product == n)
    return {
        "n": n,
        "prime_factors": prime_factors,
        "unresolved": unresolved,
        "unresolved_primality_checks": unresolved_primality_checks,
        "trace": trace,
        "verified_product": verified,
        "pipeline_mode": "shor-angle-period-multiplication-gate",
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Shor-style angle-period factorization prototype")
    parser.add_argument("n", type=int, help="positive integer to probe")
    parser.add_argument("--max-steps", type=int, default=0, help="period samples per node (0 => auto)")
    parser.add_argument("--max-seconds", type=float, default=1.0, help="wall-clock cap for one-step node")
    parser.add_argument("--prime-factorization", action="store_true", help="recursive factorization attempt")
    parser.add_argument(
        "--factor-max-seconds-per-node",
        type=float,
        default=1.0,
        help="wall-clock cap per recursive node",
    )
    parser.add_argument("--json", action="store_true", help="emit JSON payload")
    return parser


def main() -> None:
    args = build_parser().parse_args()
    if args.n < 1:
        raise SystemExit("n must be >= 1")
    if args.max_steps < 0:
        raise SystemExit("--max-steps must be >= 0")
    if args.max_seconds <= 0:
        raise SystemExit("--max-seconds must be > 0")
    if args.factor_max_seconds_per_node <= 0:
        raise SystemExit("--factor-max-seconds-per-node must be > 0")

    payload = shor_angle_period_once(
        args.n,
        max_steps=(None if args.max_steps == 0 else args.max_steps),
        max_seconds=args.max_seconds,
    )
    if args.prime_factorization:
        rec = recursive_prime_factorization_shor_angle(
            args.n,
            max_steps_per_node=(None if args.max_steps == 0 else args.max_steps),
            max_seconds_per_node=args.factor_max_seconds_per_node,
        )
        payload["recursive_factorization"] = rec
        payload["factor_export_validation"] = base.validate_factor_export(args.n, rec)

    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
        return

    print(
        f"n={payload['n']} q_span={payload['q_span']} doubled_q_span={payload['doubled_q_span']} "
        f"pipeline_mode={payload['pipeline_mode']}"
    )
    print(
        f"steps_used={payload['steps_used']} timed_out={payload['timed_out']} "
        f"elapsed_s={payload['elapsed_s']:.6f}"
    )
    print(f"divisors={payload['divisors']}")
    if payload["symmetric_pair"] is not None:
        print(f"symmetric_pair={payload['symmetric_pair']}")
    print(f"one_step_pick_certificate={payload['one_step_pick_certificate']}")
    print(f"period_analysis={payload['period_analysis']}")
    if args.prime_factorization:
        rec = payload["recursive_factorization"]
        validation = payload["factor_export_validation"]
        print(
            f"recursive_factorization_verified={rec['verified_product']} "
            f"prime_factors={rec['prime_factors']} unresolved={rec['unresolved']}"
        )
        print(
            f"factor_export_validation_status={validation['status']} "
            f"failed_checks={validation['failed_checks']}"
        )


if __name__ == "__main__":
    main()


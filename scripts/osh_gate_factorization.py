#!/usr/bin/env python3
"""
OSHoracle-style geometric factorization prototype.

Pipeline per shell step:
expand -> reconstruct -> evolve -> flip -> prune

Registers live in phase-space, candidates are extracted from angle slots on the #Q shell,
and reflected counterparts are co-generated across the doubled-span reflection line.
"""

from __future__ import annotations

import argparse
import json
import math
import time
from dataclasses import asdict
from typing import Any

import geometric_factorization_solver as base


def q_span(n: int) -> int:
    return max(1, math.isqrt(max(1, n)))


def reflection_slot(slot: int, span: int) -> int:
    m = max(1, span)
    return (m - 1 - (slot % m)) % m


def slot_to_candidate(slot: int, n: int) -> int:
    q = q_span(n)
    if q <= 1:
        return 2
    return 2 + (slot % (q - 1))


def candidate_family_from_code(code: int, n: int, doubled_span: int) -> list[int]:
    slot = code % doubled_span
    refl = reflection_slot(slot, doubled_span)
    vals = [slot_to_candidate(slot, n), slot_to_candidate(refl, n)]
    out: list[int] = []
    seen: set[int] = set()
    for v in vals:
        if v not in seen:
            seen.add(v)
            out.append(v)
    return out


def osh_factor_once(
    n: int,
    *,
    max_steps: int | None = 300,
    max_seconds: float | None = None,
    include_trivial_pair: bool = True,
) -> dict[str, Any]:
    if n <= 1:
        return {
            "n": n,
            "divisors": [1],
            "steps_used": 0,
            "candidates_generated": 0,
            "one_step_pick_certificate": {"kind": "one-step-pick", "picked": False, "n": n},
            "pipeline_mode": "osh-expand-reconstruct-evolve-flip-prune",
        }

    forbidden = base.is_forbidden_form(n)
    symmetric_tip_used = not forbidden
    arc_len = (math.pi / 4.0) if symmetric_tip_used else (2.0 * math.pi)
    delta_phi = base.rapidity_delta(n)

    base_register_bits = max(2, base.register_bit_bound_from_sqrt(n))
    register_bits = 2 * base_register_bits
    mask = (1 << register_bits) - 1
    flip_budget_per_seed = min(96, max(8, 3 * base_register_bits))
    slots_per_shell = min(32, max(8, base_register_bits))
    frontier_keep_per_step = min(128, max(16, 4 * base_register_bits))
    prune_keep_per_step = min(16, max(6, base_register_bits // 2 + 1))
    doubled_span = max(2, 2 * q_span(n))

    hits: set[int] = set()
    candidates: list[base.Candidate] = []
    prune_trace: list[dict[str, Any]] = []
    lag_histogram: dict[int, int] = {}
    code_last_seen_step: dict[int, int] = {}

    frontier_codes: set[int] = set()
    frontier_scores: dict[int, tuple[int, int, int, int, int]] = {}

    alpha = 0.0
    step = 0
    steps_used = 0
    early_stopped = False
    timed_out = False
    symmetric_pair: list[int] | None = None
    started_at = time.perf_counter()
    tested_candidates: set[int] = set()

    while True:
        if max_steps is not None and step >= max_steps:
            break
        if max_seconds is not None and (time.perf_counter() - started_at) >= max_seconds:
            timed_out = True
            break

        # expand: build seed codes from phase slots + prior frontier
        seed_codes: set[int] = set(frontier_codes)
        frac = (alpha % arc_len) / arc_len if arc_len > 0 else 0.0
        for slot in range(slots_per_shell):
            slot_frac = (frac + (slot / float(slots_per_shell))) % 1.0
            seed_codes.add(base._seed_code_from_fraction(register_bits, slot_frac))

        # reconstruct: local neighborhoods around each seed
        expanded_codes: set[int] = set()
        for s in seed_codes:
            for c in base._flip_codes(s, register_bits, flip_budget_per_seed):
                expanded_codes.add(c & mask)

        # evolve: gate transforms on expanded codes
        evolved_codes: set[int] = set()
        for c in expanded_codes:
            for g in base._gate_frontier_codes(c, register_bits, step):
                evolved_codes.add(g & mask)

        # flip: changed codes between frontier and evolved frontier
        flipped_codes = (frontier_codes - evolved_codes) | (evolved_codes - frontier_codes)
        active_codes = flipped_codes if flipped_codes else evolved_codes

        step_scored: list[tuple[tuple[int, int, int, int, int], int, base.Candidate]] = []
        for seed_idx, code in enumerate(sorted(active_codes)):
            prev_step = code_last_seen_step.get(code)
            coherence_bonus = 0
            if prev_step is not None:
                lag = step - prev_step
                if lag > 0:
                    lag_histogram[lag] = lag_histogram.get(lag, 0) + 1
                    coherence_bonus = min(16, lag_histogram[lag])
            code_last_seen_step[code] = step

            best_sc_for_code: tuple[int, int, int, int, int] | None = None
            for cand_value in candidate_family_from_code(code, n, doubled_span):
                tested_candidates.add(cand_value)
                derived = cand_value if (cand_value > 1 and n % cand_value == 0) else None
                row = base.Candidate(
                    step=step,
                    seed_idx=(seed_idx % 3),
                    arc_param=float(alpha),
                    derived_divisor=derived,
                )
                candidates.append(row)
                sc = base._candidate_score(n, cand_value, coherence_bonus=coherence_bonus)
                step_scored.append((sc, code, row))
                if best_sc_for_code is None or sc < best_sc_for_code:
                    best_sc_for_code = sc
                if derived is not None:
                    hits.add(cand_value)
                    q = n // cand_value
                    if 1 < q < n and cand_value * q == n:
                        symmetric_pair = sorted([cand_value, q])
                        early_stopped = True
                        steps_used = step + 1
                        break
            if best_sc_for_code is not None:
                prev = frontier_scores.get(code)
                if prev is None or best_sc_for_code < prev:
                    frontier_scores[code] = best_sc_for_code
            if early_stopped:
                break
        if early_stopped:
            break

        # prune: keep top frontier for next shell
        if step_scored:
            step_scored.sort(key=lambda x: (x[0], x[1]))
            top = step_scored[:prune_keep_per_step]
            frontier_ranked = sorted(frontier_scores.items(), key=lambda kv: (kv[1], kv[0]))
            frontier_codes = {code for code, _ in frontier_ranked[:frontier_keep_per_step]}
            if len(frontier_ranked) > 8 * frontier_keep_per_step:
                frontier_scores = dict(frontier_ranked[: 8 * frontier_keep_per_step])
            prune_trace.append(
                {
                    "step": step,
                    "expand_seed_count": len(seed_codes),
                    "reconstruct_count": len(expanded_codes),
                    "evolve_count": len(evolved_codes),
                    "flip_count": len(flipped_codes),
                    "active_count": len(active_codes),
                    "frontier_size": len(frontier_codes),
                    "kept": [
                        {
                            "code": code,
                            "score": list(sc),
                            "derived_divisor": c.derived_divisor,
                        }
                        for sc, code, c in top
                    ],
                }
            )

        alpha += delta_phi
        step += 1

    if steps_used == 0:
        steps_used = step

    if include_trivial_pair:
        hits.add(1)
        hits.add(n)

    divisors = sorted(hits)
    root = max(2, math.isqrt(n))
    candidate_window_size = max(1, root - 1)
    tested_count = len(tested_candidates)
    one_step_pick_certificate = base.build_one_step_pick_certificate(n, candidates)
    periodicity_trace = [
        {"lag": lag, "count": cnt}
        for lag, cnt in sorted(lag_histogram.items(), key=lambda kv: (-kv[1], kv[0]))[:10]
    ]

    return {
        "n": n,
        "forbidden_form": forbidden,
        "divisors": divisors,
        "steps_used": steps_used,
        "candidates_generated": len(candidates),
        "tested_candidate_count": tested_count,
        "candidate_window_size": candidate_window_size,
        "search_coverage_fraction": tested_count / candidate_window_size,
        "pipeline_mode": "osh-expand-reconstruct-evolve-flip-prune",
        "q_span": q_span(n),
        "doubled_span": doubled_span,
        "base_register_bits": base_register_bits,
        "register_bits": register_bits,
        "flip_budget_per_seed": flip_budget_per_seed,
        "slots_per_shell": slots_per_shell,
        "frontier_keep_per_step": frontier_keep_per_step,
        "prune_keep_per_step": prune_keep_per_step,
        "prune_trace": prune_trace,
        "periodicity_trace": periodicity_trace,
        "early_stopped": early_stopped,
        "timed_out": timed_out,
        "elapsed_s": time.perf_counter() - started_at,
        "candidates": [asdict(c) for c in candidates],
        "one_step_pick_certificate": one_step_pick_certificate,
        "symmetric_pair": symmetric_pair,
    }


def recursive_prime_factorization_osh(
    n: int,
    *,
    max_steps_per_node: int | None = 240,
    max_seconds_per_node: float | None = 10.0,
) -> dict[str, Any]:
    if n <= 1:
        return {
            "n": n,
            "prime_factors": [],
            "unresolved": [],
            "trace": [],
            "verified_product": (n == 1),
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

        node = osh_factor_once(
            x,
            max_steps=max_steps_per_node,
            max_seconds=max_seconds_per_node,
            include_trivial_pair=False,
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
                    "candidates_generated": node.get("candidates_generated"),
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
                "candidates_generated": node.get("candidates_generated"),
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
        "pipeline_mode": "osh-expand-reconstruct-evolve-flip-prune",
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="OSHoracle-style gate-frontier factorization")
    parser.add_argument("n", type=int, help="positive integer to probe")
    parser.add_argument("--max-steps", type=int, default=300, help="iteration budget (0 => unbounded)")
    parser.add_argument("--max-seconds", type=float, default=None, help="wall-clock budget in seconds")
    parser.add_argument("--prime-factorization", action="store_true", help="recursive factorization attempt")
    parser.add_argument(
        "--factor-max-seconds-per-node",
        type=float,
        default=10.0,
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
    if args.max_seconds is not None and args.max_seconds <= 0:
        raise SystemExit("--max-seconds must be > 0 when provided")
    if args.factor_max_seconds_per_node is not None and args.factor_max_seconds_per_node <= 0:
        raise SystemExit("--factor-max-seconds-per-node must be > 0 when provided")

    payload = osh_factor_once(
        args.n,
        max_steps=(None if args.max_steps == 0 else args.max_steps),
        max_seconds=args.max_seconds,
        include_trivial_pair=True,
    )
    if args.prime_factorization:
        rec = recursive_prime_factorization_osh(
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
        f"n={payload['n']} steps_used={payload['steps_used']} "
        f"pipeline_mode={payload['pipeline_mode']}"
    )
    print(
        f"candidates_generated={payload['candidates_generated']} early_stopped={payload['early_stopped']} "
        f"timed_out={payload['timed_out']}"
    )
    print(
        f"q_span={payload['q_span']} doubled_span={payload['doubled_span']} "
        f"register_bits={payload['register_bits']}"
    )
    print(
        f"tested_candidate_count={payload['tested_candidate_count']} "
        f"candidate_window_size={payload['candidate_window_size']} "
        f"search_coverage_fraction={payload['search_coverage_fraction']:.6f}"
    )
    print(f"divisors={payload['divisors']}")
    if payload["symmetric_pair"] is not None:
        print(f"symmetric_pair={payload['symmetric_pair']}")
    print(f"one_step_pick_certificate={payload['one_step_pick_certificate']}")
    print(f"periodicity_trace={payload['periodicity_trace']}")
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


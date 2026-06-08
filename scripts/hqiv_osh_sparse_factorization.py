#!/usr/bin/env python3
"""
HQIV-OSH sparse factorization prototype.

This script uses the native sparse simulation pipeline mirrored from Lean OSHoracle:
causalExpandSupport -> denseOfSparse -> applyGateSparse -> detectFlippedKets -> pruneToFlipped.

Factor candidates are read from evolved/pruned sparse indices on each shell step.
"""

from __future__ import annotations

import argparse
import json
import math
import time
from typing import Any

import geometric_factorization_solver as base
import hqiv_quantum_gate_alias_probe as osh


def q_span(n: int) -> int:
    return max(2, math.isqrt(max(2, n)))


def _candidate_from_sparse_idx(idx: int, n: int) -> int:
    q = q_span(n)
    if q <= 1:
        return 2
    return 2 + (abs(idx) % (q - 1))


def _candidate_family_from_sparse_idx(idx: int, n: int) -> list[int]:
    d = _candidate_from_sparse_idx(idx, n)
    vals = [d]
    if d > 0:
        vals.append(max(2, n // d))
    out: list[int] = []
    seen: set[int] = set()
    for v in vals:
        if v not in seen:
            seen.add(v)
            out.append(v)
    return out


def _default_L_for_n(n: int) -> int:
    # Keep basis card (L+1)^2 around #Q scale.
    return max(4, min(1024, q_span(n)))


def _build_shells(L: int, n: int) -> list[int]:
    # Deterministic shell ladder inspired by rapidity phase.
    delta = base.rapidity_delta(n)
    shells: list[int] = []
    phase = 0.0
    for _ in range(L):
        phase += delta
        slot = int((phase / (2.0 * math.pi)) * (L + 1))
        shells.append(1 + (slot % max(1, L)))
    return shells


def osh_sparse_factor_once(
    n: int,
    *,
    L: int | None = None,
    max_steps: int | None = 300,
    max_seconds: float | None = None,
    reference_m: int = 4,
    include_trivial_pair: bool = True,
) -> dict[str, Any]:
    if n <= 1:
        return {
            "n": n,
            "divisors": [1],
            "steps_used": 0,
            "candidates_generated": 0,
            "one_step_pick_certificate": {"kind": "one-step-pick", "picked": False, "n": n},
            "pipeline_mode": "hqiv-osh-sparse-native",
        }

    L_eff = _default_L_for_n(n) if L is None else max(1, L)
    shells = _build_shells(L_eff, n)
    basis = osh.sparse_basis_card(L_eff)

    # Sparse seed: deterministic low-index support like OSH probe.
    seed_size = min(max(16, q_span(n) // 2), basis)
    state = osh.build_seed_register(L_eff, n_points=seed_size)

    hits: set[int] = set()
    candidate_rows: list[base.Candidate] = []
    sparse_trace: list[dict[str, Any]] = []
    tested_candidates: set[int] = set()
    periodic_lags: dict[int, int] = {}
    last_support_hash: int | None = None

    started = time.perf_counter()
    steps_used = 0
    early_stopped = False
    timed_out = False
    symmetric_pair: list[int] | None = None
    total_candidates = 0

    step = 0
    while True:
        if max_steps is not None and step >= max_steps:
            break
        if max_seconds is not None and (time.perf_counter() - started) >= max_seconds:
            timed_out = True
            break

        before = state
        evolved, pivot_flat = osh.apply_gate_sparse_hqiv_native(
            L_eff, before, shells=shells, reference_m=reference_m
        )
        flipped = osh.detect_flipped_kets(before, evolved)
        pruned = osh.prune_to_flipped(flipped, evolved)
        state = pruned if pruned else evolved

        support_hash = hash(tuple(sorted({k.idx for k in state})))
        if last_support_hash is not None and support_hash == last_support_hash:
            periodic_lags[1] = periodic_lags.get(1, 0) + 1
        last_support_hash = support_hash

        step_candidates = 0
        for seed_idx, ket in enumerate(state):
            for cand in _candidate_family_from_sparse_idx(ket.idx, n):
                step_candidates += 1
                total_candidates += 1
                tested_candidates.add(cand)
                derived = cand if (cand > 1 and n % cand == 0) else None
                row = base.Candidate(
                    step=step,
                    seed_idx=(seed_idx % 3),
                    arc_param=float(step),
                    derived_divisor=derived,
                )
                candidate_rows.append(row)
                if derived is not None:
                    hits.add(cand)
                    q = n // cand
                    if 1 < q < n and cand * q == n:
                        symmetric_pair = sorted([cand, q])
                        early_stopped = True
                        steps_used = step + 1
                        break
            if early_stopped:
                break
        sparse_trace.append(
            {
                "step": step,
                "before_len": len(before),
                "evolved_len": len(evolved),
                "flipped_count": len(flipped),
                "pruned_len": len(pruned),
                "active_len": len(state),
                "pivot_flat": pivot_flat,
                "step_candidates": step_candidates,
            }
        )
        if early_stopped:
            break
        step += 1

    if steps_used == 0:
        steps_used = step

    if include_trivial_pair:
        hits.add(1)
        hits.add(n)

    root = max(2, math.isqrt(n))
    candidate_window_size = max(1, root - 1)
    cert = base.build_one_step_pick_certificate(n, candidate_rows)
    periodicity_trace = [{"lag": lag, "count": cnt} for lag, cnt in sorted(periodic_lags.items())]

    return {
        "n": n,
        "pipeline_mode": "hqiv-osh-sparse-native",
        "L": L_eff,
        "basis_card": basis,
        "seed_size": seed_size,
        "steps_used": steps_used,
        "timed_out": timed_out,
        "early_stopped": early_stopped,
        "elapsed_s": time.perf_counter() - started,
        "divisors": sorted(hits),
        "symmetric_pair": symmetric_pair,
        "candidates_generated": total_candidates,
        "tested_candidate_count": len(tested_candidates),
        "candidate_window_size": candidate_window_size,
        "search_coverage_fraction": len(tested_candidates) / candidate_window_size,
        "sparse_trace": sparse_trace,
        "periodicity_trace": periodicity_trace,
        "one_step_pick_certificate": cert,
    }


def recursive_prime_factorization_hqiv_osh(
    n: int,
    *,
    L: int | None = None,
    max_steps_per_node: int | None = 240,
    max_seconds_per_node: float | None = 1.0,
    reference_m: int = 4,
) -> dict[str, Any]:
    if n <= 1:
        return {
            "n": n,
            "prime_factors": [],
            "unresolved": [],
            "trace": [],
            "verified_product": (n == 1),
            "pipeline_mode": "hqiv-osh-sparse-native",
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

        node = osh_sparse_factor_once(
            x,
            L=L,
            max_steps=max_steps_per_node,
            max_seconds=max_seconds_per_node,
            reference_m=reference_m,
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
        "pipeline_mode": "hqiv-osh-sparse-native",
    }


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="HQIV OSH sparse-native factorization")
    p.add_argument("n", type=int, help="positive integer to factor")
    p.add_argument("--L", type=int, default=0, help="harmonic cutoff L (0 => auto from #Q)")
    p.add_argument("--max-steps", type=int, default=240, help="step budget (0 => unbounded)")
    p.add_argument("--max-seconds", type=float, default=1.0, help="wall-clock cap per one-step run")
    p.add_argument("--reference-m", type=int, default=4, help="HQIV referenceM pivot anchor")
    p.add_argument("--prime-factorization", action="store_true", help="recursive factorization")
    p.add_argument(
        "--factor-max-seconds-per-node",
        type=float,
        default=1.0,
        help="wall-clock cap per recursive node",
    )
    p.add_argument("--json", action="store_true", help="emit JSON payload")
    return p


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
    if args.L < 0:
        raise SystemExit("--L must be >= 0")

    L = None if args.L == 0 else args.L
    payload = osh_sparse_factor_once(
        args.n,
        L=L,
        max_steps=(None if args.max_steps == 0 else args.max_steps),
        max_seconds=args.max_seconds,
        reference_m=args.reference_m,
        include_trivial_pair=True,
    )
    if args.prime_factorization:
        rec = recursive_prime_factorization_hqiv_osh(
            args.n,
            L=L,
            max_steps_per_node=(None if args.max_steps == 0 else args.max_steps),
            max_seconds_per_node=args.factor_max_seconds_per_node,
            reference_m=args.reference_m,
        )
        payload["recursive_factorization"] = rec
        payload["factor_export_validation"] = base.validate_factor_export(args.n, rec)

    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
        return

    print(
        f"n={payload['n']} L={payload['L']} basis_card={payload['basis_card']} "
        f"pipeline_mode={payload['pipeline_mode']}"
    )
    print(
        f"steps_used={payload['steps_used']} timed_out={payload['timed_out']} "
        f"elapsed_s={payload['elapsed_s']:.6f}"
    )
    print(
        f"candidates_generated={payload['candidates_generated']} "
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


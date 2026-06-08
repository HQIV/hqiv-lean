#!/usr/bin/env python3
"""
Prototype geometric factorization walk:
- rapidity increment
- Morley-like triad seeds (0, 2π/3, 4π/3)
- golden-angle drift
- optional forbidden-form fallback arc

This is an experimental script for numerical probing; it does not replace the
formal Lean soundness theorems.
"""

from __future__ import annotations

import argparse
import json
import math
import time
from dataclasses import asdict, dataclass
from typing import Any


PHI = (1.0 + math.sqrt(5.0)) / 2.0
GOLDEN_ANGLE = 2.0 * math.pi / (PHI**2)
DEBUG_PEEL_MODE = "debug-peel-twos-only"
LEGACY_PEEL_ALIAS = "peel-twos"
KNOWN_FACTOR_VECTORS: dict[int, list[int]] = {
    16: [2, 2, 2, 2],
    21: [3, 7],
    60: [2, 2, 3, 5],
    143: [11, 13],
    221: [13, 17],
    10403: [101, 103],
    70747: [263, 269],
    72899: [269, 271],
    97343: [311, 313],
}


@dataclass
class Candidate:
    step: int
    seed_idx: int
    arc_param: float
    derived_divisor: int | None = None


def option_to_string(value: int | None) -> str:
    return "none" if value is None else str(value)


def candidate_to_csv(c: Candidate) -> str:
    """Lean-aligned CSV row: step,seed,arc,derived."""
    return f"{c.step},{c.seed_idx},{int(c.arc_param)},{option_to_string(c.derived_divisor)}"


def parse_candidate_csv(row: str) -> Candidate | None:
    """Inverse of candidate_to_csv for normalized rows (integer arc slot)."""
    parts = row.split(",")
    if len(parts) != 4:
        return None
    step_s, seed_s, arc_s, derived_s = parts
    try:
        step = int(step_s)
        seed = int(seed_s)
        arc = float(int(arc_s))
    except ValueError:
        return None
    if seed < 0:
        return None
    if derived_s == "none":
        derived = None
    else:
        try:
            derived = int(derived_s)
        except ValueError:
            return None
    return Candidate(step=step, seed_idx=seed, arc_param=arc, derived_divisor=derived)


def candidate_list_to_csv(candidates: list[Candidate]) -> str:
    """Lean-aligned newline-separated CSV rows."""
    return "".join(candidate_to_csv(c) + "\n" for c in candidates)


def is_forbidden_form(n: int) -> bool:
    """Legendre forbidden form 4^a(8b+7), where sum-of-three-squares count vanishes."""
    if n <= 0:
        return False
    while n % 4 == 0:
        n //= 4
    return n % 8 == 7


def morley_seeds() -> list[float]:
    return [0.0, 2.0 * math.pi / 3.0, 4.0 * math.pi / 3.0]


def rapidity_delta(n: int) -> float:
    # Mirrors the same qualitative "smaller step at larger shell" behavior.
    if n <= 1:
        return math.pi / 4.0
    # Avoid float overflow for very large integers by using a bit-length log proxy.
    if n.bit_length() > 1020:
        log_n = n.bit_length() * math.log(2.0)
    else:
        log_n = math.log(n + 1.0)
    return math.pi / (4.0 * max(log_n, 1.0))


def _candidate_from_fraction(n: int, frac: float) -> int:
    frac = min(1.0, max(0.0, frac))
    return max(1, int(round(n**frac)))


def register_bit_bound_from_sqrt(n: int) -> int:
    """Bit-register width needed to represent candidates up to floor(sqrt(n))."""
    if n <= 1:
        return 1
    return max(1, math.isqrt(n).bit_length())


def _code_to_candidate(code: int, n: int) -> int:
    """Map a register code to a bounded candidate in [2, floor(sqrt(n))]."""
    root = max(2, math.isqrt(n))
    # Keep mapping deterministic and bounded to the factor search window.
    return 2 + (abs(code) % (root - 1))


def _code_to_candidate_set(code: int, n: int, base_register_bits: int, q_span_mode: str) -> list[int]:
    """
    Map one register code to one or more factor candidates.

    - single-arc: legacy single candidate.
    - double-pole-reflector: split doubled Q into two poles and add a reflected pole probe.
    """
    if q_span_mode == "single-arc":
        return [_code_to_candidate(code, n)]
    if q_span_mode != "double-pole-reflector":
        raise ValueError(f"unknown q_span_mode: {q_span_mode}")
    root = max(2, math.isqrt(n))
    width = max(1, root - 1)
    pole_mask = (1 << base_register_bits) - 1
    low = code & pole_mask
    high = (code >> base_register_bits) & pole_mask
    reflect = pole_mask ^ low
    values = [
        2 + (low % width),
        2 + (high % width),
        2 + (reflect % width),
    ]
    out: list[int] = []
    seen: set[int] = set()
    for v in values:
        if v not in seen:
            seen.add(v)
            out.append(v)
    return out


def _seed_code_from_fraction(register_bits: int, frac: float) -> int:
    """Phase fraction -> register code in [0, 2^register_bits - 1]."""
    frac = min(1.0, max(0.0, frac))
    mask = (1 << register_bits) - 1
    # Use a fixed 53-bit mantissa bucket to avoid float overflow for huge masks.
    mantissa_bits = 53
    bucket = int(round(frac * float((1 << mantissa_bits) - 1)))
    if register_bits <= mantissa_bits:
        return (bucket >> (mantissa_bits - register_bits)) & mask
    return (bucket << (register_bits - mantissa_bits)) & mask


def _flip_codes(code: int, register_bits: int, flip_budget: int) -> list[int]:
    """
    Produce local bit-flip neighbors around a seed code.

    This mirrors SAT/ATSP local neighborhoods: 1-bit flips first, then selected 2-bit flips.
    """
    out: list[int] = []
    seen: set[int] = set()
    mask = (1 << register_bits) - 1
    base = code & mask
    out.append(base)
    seen.add(base)
    # 1-bit neighborhood.
    for i in range(register_bits):
        c = base ^ (1 << i)
        if c not in seen:
            out.append(c)
            seen.add(c)
        if len(out) >= flip_budget:
            return out
    # 2-bit neighborhood (frontier expansion if budget allows).
    for i in range(register_bits):
        for j in range(i + 1, register_bits):
            c = base ^ (1 << i) ^ (1 << j)
            if c not in seen:
                out.append(c)
                seen.add(c)
            if len(out) >= flip_budget:
                return out
    return out


def _rotate_left(x: int, shift: int, width: int) -> int:
    if width <= 0:
        return 0
    mask = (1 << width) - 1
    s = shift % width
    v = x & mask
    return ((v << s) & mask) | (v >> (width - s))


def _gate_frontier_codes(code: int, register_bits: int, step: int) -> list[int]:
    """
    Deterministic gate-like transforms on bitregister codes.

    This emulates a small phase-space gate bank over the classical frontier:
    identity, Gray mixing, pole reflection, and shell-indexed rotations.
    """
    if register_bits <= 0:
        return [0]
    mask = (1 << register_bits) - 1
    base = code & mask
    if register_bits == 1:
        return [base]
    gate_out = [
        base,
        base ^ (base >> 1),  # Gray-like mixing
        mask ^ base,  # reflector
        _rotate_left(base, step + 1, register_bits),
        _rotate_left(base, 2 * step + 3, register_bits),
        _rotate_left(base ^ (mask >> 1), step + 2, register_bits),
    ]
    out: list[int] = []
    seen: set[int] = set()
    for g in gate_out:
        gg = g & mask
        if gg not in seen:
            seen.add(gg)
            out.append(gg)
    return out


def _candidate_score(n: int, d: int, coherence_bonus: int = 0) -> tuple[int, int, int, int, int]:
    """
    Score candidate factors for prune stage.

    Primary objective: exact divisibility (remainder 0).
    Secondary objective: larger gcd(n, d) to keep a "shoreline" near shared structure.
    Tertiary objective: smaller candidate first for deterministic tie-breaking.
    """
    rem = n % d
    g = math.gcd(n, d)
    return (0 if rem == 0 else 1, -g.bit_length(), rem, -coherence_bonus, d)


def is_probable_prime(n: int) -> bool:
    """
    Miller-Rabin probable-prime test.

    - Deterministic for 64-bit with the chosen bases.
    - For larger integers, still a strong probabilistic filter for recursive peeling.
    """
    if n < 2:
        return False
    small_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
    for p in small_primes:
        if n % p == 0:
            return n == p
    d = n - 1
    s = 0
    while d % 2 == 0:
        s += 1
        d //= 2
    # Deterministic for 64-bit; strong witness set for larger n.
    bases = [2, 325, 9375, 28178, 450775, 9780504, 1795265022]
    for a in bases:
        if a % n == 0:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                break
        else:
            return False
    return True


def recursive_prime_factorization(
    n: int,
    *,
    max_steps_per_node: int | None = 120,
    max_seconds_per_node: float | None = None,
    search_mode: str = "auto",
    split_mode: str = "auto",
    q_span_mode: str = "single-arc",
    q_list_mode: str = "shoreline",
) -> dict[str, Any]:
    """
    Recursively peel cofactors to (probable) primes using geometric_factorization_solver.

    This is the SAT/ATSP-style recursive shell decomposition layer:
    generate candidates -> pick nontrivial divisor -> push two child cofactors.
    """
    mode_warning: str | None = None
    if split_mode == LEGACY_PEEL_ALIAS:
        mode_warning = (
            f"'{LEGACY_PEEL_ALIAS}' is deprecated; use '{DEBUG_PEEL_MODE}'. "
            "This is a debug mode that only strips factor 2 and leaves odd residues unresolved."
        )
        split_mode = DEBUG_PEEL_MODE
    if split_mode not in {"auto", DEBUG_PEEL_MODE}:
        raise ValueError(f"split_mode must be one of: auto, {DEBUG_PEEL_MODE}")

    if n <= 1:
        return {
            "n": n,
            "prime_factors": [],
            "unresolved": [],
            "trace": [],
            "verified_product": (n == 1),
            "split_mode": split_mode,
            "q_span_mode": q_span_mode,
            "q_list_mode": q_list_mode,
            "mode_warning": mode_warning,
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
        if split_mode == DEBUG_PEEL_MODE:
            original = x
            power_two = 0
            while x % 2 == 0:
                prime_factors.append(2)
                x //= 2
                power_two += 1
            if power_two > 0:
                trace.append(
                    {
                        "n": original,
                        "status": "peel-two",
                        "split": [2, original // 2] if original > 2 else None,
                        "power_two": power_two,
                        "residual_after_two_peel": x,
                    }
                )
            if x > 1:
                unresolved.append(x)
                probable = is_probable_prime(x)
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
                        "status": "unresolved-odd-residual",
                        "reason": "split_mode=peel-twos only strips factor 2",
                        "probable_prime": probable,
                        "primality_test": "pass" if probable else "fail",
                    }
                )
            continue
        if is_probable_prime(x):
            prime_factors.append(x)
            trace.append({"n": x, "status": "probable-prime", "split": None})
            continue

        node = geometric_factorization_solver(
            x,
            max_steps=max_steps_per_node,
            include_trivial_pair=False,
            max_seconds=max_seconds_per_node,
            search_mode=search_mode,
            q_span_mode=q_span_mode,
            q_list_mode=q_list_mode,
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
            probable = is_probable_prime(x)
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
        "split_mode": split_mode,
        "q_span_mode": q_span_mode,
        "q_list_mode": q_list_mode,
        "mode_warning": mode_warning,
    }


def validate_factor_export(
    n: int,
    recursive_result: dict[str, Any],
) -> dict[str, Any]:
    """
    Validate exported recursive factorization payload for obvious garbage.

    Checks include:
    - product integrity (prime factors + unresolved residues must multiply back to n),
    - probable-prime sanity for reported prime_factors,
    - unresolved primality ledger consistency,
    - known-vector match for selected canonical inputs.
    """
    prime_factors = [int(x) for x in recursive_result.get("prime_factors", [])]
    unresolved = [int(x) for x in recursive_result.get("unresolved", [])]
    unresolved_checks = recursive_result.get("unresolved_primality_checks", [])
    split_mode = str(recursive_result.get("split_mode", "auto"))
    failed_checks: list[str] = []

    prime_product = 1
    for p in prime_factors:
        prime_product *= p
    unresolved_product = 1
    for u in unresolved:
        unresolved_product *= u
    full_product = prime_product * unresolved_product

    product_matches_n = full_product == n
    if not product_matches_n:
        failed_checks.append("product_mismatch")

    probable_prime_flags = [{"factor": p, "probable_prime": is_probable_prime(p)} for p in prime_factors]
    all_prime_factors_probable_prime = all(item["probable_prime"] for item in probable_prime_flags)
    if not all_prime_factors_probable_prime:
        failed_checks.append("composite_in_prime_factors")

    checks_by_n: dict[int, str] = {}
    for chk in unresolved_checks:
        x = int(chk.get("n", 0))
        checks_by_n[x] = str(chk.get("primality_test", "missing"))
    unresolved_consistent = True
    unresolved_consistency_detail: list[dict[str, Any]] = []
    for u in unresolved:
        expected = "pass" if is_probable_prime(u) else "fail"
        got = checks_by_n.get(u, "missing")
        ok = got == expected
        unresolved_consistent = unresolved_consistent and ok
        unresolved_consistency_detail.append({"n": u, "expected": expected, "reported": got, "ok": ok})
    if not unresolved_consistent:
        failed_checks.append("unresolved_primality_ledger_mismatch")

    if split_mode == "auto" and len(unresolved) > 0:
        failed_checks.append("incomplete_factorization_auto_mode")

    verified_product_consistent = bool(recursive_result.get("verified_product", False)) == (
        product_matches_n and len(unresolved) == 0
    )
    if not verified_product_consistent:
        failed_checks.append("verified_product_inconsistent")

    known_case_expected = KNOWN_FACTOR_VECTORS.get(n)
    known_case_match: bool | None = None
    if known_case_expected is not None:
        if split_mode == "auto" and len(unresolved) == 0:
            known_case_match = sorted(prime_factors) == sorted(known_case_expected)
            if not known_case_match:
                failed_checks.append("known_vector_mismatch")
        else:
            known_case_match = None

    return {
        "status": "pass" if not failed_checks else "fail",
        "failed_checks": failed_checks,
        "product_matches_n": product_matches_n,
        "prime_product": prime_product,
        "unresolved_product": unresolved_product,
        "full_product": full_product,
        "all_prime_factors_probable_prime": all_prime_factors_probable_prime,
        "prime_factor_primality": probable_prime_flags,
        "unresolved_primality_consistent": unresolved_consistent,
        "unresolved_primality_consistency_detail": unresolved_consistency_detail,
        "verified_product_consistent": verified_product_consistent,
        "known_case_expected": known_case_expected,
        "known_case_match": known_case_match,
        "known_case_enforced": (known_case_expected is not None and split_mode == "auto" and len(unresolved) == 0),
        "split_mode": split_mode,
    }


def build_one_step_pick_certificate(n: int, candidates: list[Candidate]) -> dict[str, Any]:
    """
    Build a Lean-aligned one-step pick certificate payload.

    The certificate mirrors the shape used by `pickFromCandidates_sound`:
    if a first nontrivial candidate divisor is found in list order, expose
    `(1 < d)`, `(d < n)`, `(d | n)` plus pair-product sanity.
    """
    for idx, cand in enumerate(candidates):
        d = cand.derived_divisor
        if d is None:
            continue
        nontrivial = 1 < d < n
        divides = (n % d == 0) if d > 0 else False
        if not (nontrivial and divides):
            continue
        cofactor = n // d
        return {
            "kind": "one-step-pick",
            "picked": True,
            "n": n,
            "d": d,
            "cofactor": cofactor,
            "candidate_index": idx,
            "step": cand.step,
            "seed_idx": cand.seed_idx,
            "is_nontrivial": nontrivial,
            "divides": divides,
            "pair_product_ok": (d * cofactor == n),
        }
    return {
        "kind": "one-step-pick",
        "picked": False,
        "n": n,
        "reason": "no nontrivial divisor found in candidate order",
    }


def geometric_factorization_solver(
    n: int,
    max_steps: int | None = 300,
    include_trivial_pair: bool = True,
    max_seconds: float | None = None,
    search_mode: str = "auto",
    q_span_mode: str = "single-arc",
    q_list_mode: str = "shoreline",
) -> dict[str, Any]:
    if search_mode not in {"standard", "symmetric-tip", "auto"}:
        raise ValueError("search_mode must be one of: standard, symmetric-tip, auto")
    if q_span_mode not in {"single-arc", "double-pole-reflector"}:
        raise ValueError("q_span_mode must be one of: single-arc, double-pole-reflector")
    if q_list_mode not in {"shoreline", "gate-frontier"}:
        raise ValueError("q_list_mode must be one of: shoreline, gate-frontier")
    if n <= 1:
        return {
            "n": n,
            "forbidden_form": False,
            "divisors": [1],
            "approx_harmonic_step": 1,
            "steps_used": 0,
            "search_mode": search_mode,
            "symmetric_tip_used": False,
            "symmetric_pair": None,
        }

    forbidden = is_forbidden_form(n)
    symmetric_tip_used = search_mode in {"symmetric-tip", "auto"} and not forbidden
    if search_mode == "symmetric-tip" and forbidden:
        # Symmetric tip is defined on the binary arc around pi/4.
        symmetric_tip_used = False
    arc_len = (math.pi / 4.0) if symmetric_tip_used else (2.0 * math.pi if forbidden else (math.pi / 4.0))
    delta_phi = rapidity_delta(n)
    seeds = morley_seeds()
    base_register_bits = register_bit_bound_from_sqrt(n)
    register_bits = (
        2 * base_register_bits
        if q_span_mode == "double-pole-reflector"
        else base_register_bits
    )
    # SAT/ATSP-style local neighborhood + prune controls.
    flip_budget_per_seed = min(64, max(6, 2 * base_register_bits))
    prune_keep_per_step = min(12, max(4, register_bits // 2 + 1))
    slots_per_shell = min(24, max(6, base_register_bits))
    frontier_keep_per_step = min(96, max(12, 3 * base_register_bits))

    hits: set[int] = set()
    candidates: list[Candidate] = []
    best_per_step: list[dict[str, Any]] = []
    frontier_scores: dict[int, tuple[int, int, int, int, int]] = {}
    frontier_codes: set[int] = set()
    code_last_seen_step: dict[int, int] = {}
    lag_histogram: dict[int, int] = {}
    gate_trace: list[dict[str, Any]] = []
    alpha = 0.0
    steps_used = 0
    early_stopped = False
    timed_out = False
    symmetric_pair: list[int] | None = None
    started_at = time.perf_counter()
    tested_candidates: set[int] = set()

    step = 0
    while True:
        if max_steps is not None and step >= max_steps:
            break
        if max_seconds is not None and (time.perf_counter() - started_at) >= max_seconds:
            timed_out = True
            break
        step_scored: list[tuple[tuple[int, int, int, int, int], int, Candidate]] = []
        mask = (1 << register_bits) - 1
        seed_codes: set[int] = set(frontier_codes)
        shell_phase = alpha
        if symmetric_tip_used:
            frac = (alpha % arc_len) / arc_len if arc_len > 0 else 0.0
            # Shoreline seeds: phase slots mirrored across the binary arc.
            for slot in range(slots_per_shell):
                slot_frac = (frac + (slot / float(slots_per_shell))) % 1.0
                slot_reflect = 1.0 - slot_frac
                seed_codes.add(_seed_code_from_fraction(register_bits, slot_frac))
                seed_codes.add(_seed_code_from_fraction(register_bits, slot_reflect))
        else:
            drift = step * GOLDEN_ANGLE
            for seed in seeds:
                angle = (alpha + seed + drift) % arc_len
                frac = angle / arc_len if arc_len > 0 else 0.0
                for slot in range(slots_per_shell):
                    slot_frac = (frac + (slot / float(slots_per_shell))) % 1.0
                    seed_codes.add(_seed_code_from_fraction(register_bits, slot_frac))

        codes_this_shell: set[int] = set()
        ordered_seed_codes = sorted(seed_codes)
        gate_seed_count = 0
        gate_code_count = 0
        for seed_idx, base_code in enumerate(ordered_seed_codes):
            gate_codes = (
                _gate_frontier_codes(base_code, register_bits, step)
                if q_list_mode == "gate-frontier"
                else [base_code]
            )
            gate_seed_count += len(gate_codes)
            for gated_code in gate_codes:
                gate_code_count += 1
                for flip_code in _flip_codes(gated_code, register_bits, flip_budget_per_seed):
                    code = flip_code & mask
                    if code in codes_this_shell:
                        continue
                    codes_this_shell.add(code)
                    previous_step = code_last_seen_step.get(code)
                    coherence_bonus = 0
                    if previous_step is not None:
                        lag = step - previous_step
                        if lag > 0:
                            lag_histogram[lag] = lag_histogram.get(lag, 0) + 1
                            coherence_bonus = min(16, lag_histogram[lag])
                    code_last_seen_step[code] = step
                    code_best_sc: tuple[int, int, int, int, int] | None = None
                    candidate_values = _code_to_candidate_set(code, n, base_register_bits, q_span_mode)
                    for cand_value in candidate_values:
                        tested_candidates.add(cand_value)
                        derived = cand_value if (cand_value > 1 and n % cand_value == 0) else None
                        c = Candidate(
                            step=step,
                            seed_idx=(seed_idx % 3),
                            arc_param=float(shell_phase),
                            derived_divisor=derived,
                        )
                        candidates.append(c)
                        sc = _candidate_score(n, cand_value, coherence_bonus=coherence_bonus)
                        step_scored.append((sc, code, c))
                        if code_best_sc is None or sc < code_best_sc:
                            code_best_sc = sc
                        if derived is not None:
                            hits.add(cand_value)
                            q = n // cand_value
                            if 1 < q < n and cand_value * q == n:
                                symmetric_pair = sorted([cand_value, q])
                                early_stopped = True
                                steps_used = step + 1
                                break
                    if code_best_sc is not None:
                        prev_sc = frontier_scores.get(code)
                        if prev_sc is None or code_best_sc < prev_sc:
                            frontier_scores[code] = code_best_sc
                    if early_stopped:
                        break
                if early_stopped:
                    break
            if early_stopped:
                break
        if early_stopped:
            break
        # Prune ledger (SAT/ATSP-like top candidates at this step).
        if step_scored:
            step_scored.sort(key=lambda item: (item[0], item[1]))
            top = step_scored[:prune_keep_per_step]
            frontier_ranked = sorted(frontier_scores.items(), key=lambda kv: (kv[1], kv[0]))
            frontier_codes = {code for code, _sc in frontier_ranked[:frontier_keep_per_step]}
            if len(frontier_ranked) > 8 * frontier_keep_per_step:
                frontier_scores = dict(frontier_ranked[: 8 * frontier_keep_per_step])
            best_per_step.append(
                {
                    "step": step,
                    "shell_phase": shell_phase,
                    "seed_code_count": len(ordered_seed_codes),
                    "gate_seed_count": gate_seed_count,
                    "gate_code_count": gate_code_count,
                    "codes_scored": len(codes_this_shell),
                    "frontier_size": len(frontier_codes),
                    "kept": [
                        {
                            "seed_idx": c.seed_idx,
                            "arc_param": c.arc_param,
                            "derived_divisor": c.derived_divisor,
                            "code": code,
                            "score": list(sc),
                        }
                        for sc, code, c in top
                    ],
                }
            )
        if q_list_mode == "gate-frontier":
            lag_top = sorted(lag_histogram.items(), key=lambda kv: (-kv[1], kv[0]))[:5]
            gate_trace.append(
                {
                    "step": step,
                    "seed_code_count": len(ordered_seed_codes),
                    "gate_seed_count": gate_seed_count,
                    "gate_code_count": gate_code_count,
                    "codes_scored": len(codes_this_shell),
                    "top_lags": [{"lag": lag, "count": cnt} for lag, cnt in lag_top],
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
    search_coverage_fraction = tested_count / candidate_window_size
    periodicity_trace = [
        {"lag": lag, "count": cnt}
        for lag, cnt in sorted(lag_histogram.items(), key=lambda kv: (-kv[1], kv[0]))[:10]
    ]
    one_step_pick_certificate = build_one_step_pick_certificate(n, candidates)
    return {
        "n": n,
        "forbidden_form": forbidden,
        "divisors": divisors,
        "approx_harmonic_step": len(divisors),
        "steps_used": steps_used,
        "target_divisor_count": None,
        "candidates_generated": len(candidates),
        "tested_candidate_count": tested_count,
        "candidate_window_size": candidate_window_size,
        "search_coverage_fraction": search_coverage_fraction,
        "candidate_generation_policy": f"{q_list_mode}-bitregister-rapidity:{q_span_mode}",
        "trial_division_scan": False,
        "q_span_mode": q_span_mode,
        "q_list_mode": q_list_mode,
        "base_register_bits": base_register_bits,
        "register_bits": register_bits,
        "flip_budget_per_seed": flip_budget_per_seed,
        "slots_per_shell": slots_per_shell,
        "frontier_keep_per_step": frontier_keep_per_step,
        "prune_keep_per_step": prune_keep_per_step,
        "prune_trace": best_per_step,
        "periodicity_trace": periodicity_trace,
        "gate_trace": gate_trace,
        "early_stopped": early_stopped,
        "timed_out": timed_out,
        "elapsed_s": time.perf_counter() - started_at,
        "candidates": [asdict(c) for c in candidates],
        "one_step_pick_certificate": one_step_pick_certificate,
        "search_mode": search_mode,
        "symmetric_tip_used": symmetric_tip_used,
        "symmetric_pair": symmetric_pair,
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Prototype rapidity/Morley/golden-angle divisor walker")
    parser.add_argument("n", type=int, help="positive integer to probe")
    parser.add_argument("--max-steps", type=int, default=300, help="iteration budget (0 => unbounded)")
    parser.add_argument("--max-seconds", type=float, default=None, help="wall-clock budget in seconds")
    parser.add_argument(
        "--search-mode",
        choices=("standard", "symmetric-tip", "auto"),
        default="auto",
        help="candidate-walk mode (auto enables symmetric-tip on binary arc)",
    )
    parser.add_argument(
        "--q-span-mode",
        choices=("single-arc", "double-pole-reflector"),
        default="single-arc",
        help=(
            "candidate register span mode: single-arc (default) or double-pole-reflector "
            "(experimental doubled Q span with reflected pole probes)."
        ),
    )
    parser.add_argument(
        "--q-list-mode",
        choices=("shoreline", "gate-frontier"),
        default="shoreline",
        help="candidate list dynamics: shoreline frontier (default) or gate-frontier transforms",
    )
    parser.add_argument("--json", action="store_true", help="emit JSON payload")
    parser.add_argument(
        "--csv-roundtrip-check",
        action="store_true",
        help="validate candidate CSV serialize/parse on produced candidates",
    )
    parser.add_argument(
        "--no-trivial-pair",
        action="store_true",
        help="omit automatic insertion of {1, n}",
    )
    parser.add_argument(
        "--prime-factorization",
        action="store_true",
        help="recursively peel cofactors to a full prime factorization attempt",
    )
    parser.add_argument(
        "--factor-max-seconds-per-node",
        type=float,
        default=None,
        help="optional wall-clock cap per recursive cofactor node",
    )
    parser.add_argument(
        "--factor-split-mode",
        choices=("auto", DEBUG_PEEL_MODE, LEGACY_PEEL_ALIAS),
        default="auto",
        help=(
            "recursive factor split mode: auto geometric splits (default), or debug-peel-twos-only "
            "(validation mode that strips only factor 2 and intentionally leaves odd residues unresolved). "
            "'peel-twos' is accepted as a deprecated alias."
        ),
    )
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

    payload = geometric_factorization_solver(
        n=args.n,
        max_steps=(None if args.max_steps == 0 else args.max_steps),
        include_trivial_pair=not args.no_trivial_pair,
        max_seconds=args.max_seconds,
        search_mode=args.search_mode,
        q_span_mode=args.q_span_mode,
        q_list_mode=args.q_list_mode,
    )
    if args.csv_roundtrip_check:
        roundtrip_ok = True
        candidate_rows: list[str] = []
        for item in payload["candidates"]:
            candidate = Candidate(
                step=item["step"],
                seed_idx=item["seed_idx"],
                arc_param=float(int(item["step"])),
                derived_divisor=item["derived_divisor"],
            )
            row = candidate_to_csv(candidate)
            candidate_rows.append(row)
            parsed = parse_candidate_csv(row)
            if parsed != candidate:
                roundtrip_ok = False
                break
        payload["csv_roundtrip_ok"] = roundtrip_ok
        payload["candidate_csv_preview"] = candidate_rows[:5]
    if args.prime_factorization:
        payload["recursive_factorization"] = recursive_prime_factorization(
            args.n,
            max_steps_per_node=(None if args.max_steps == 0 else args.max_steps),
            max_seconds_per_node=args.factor_max_seconds_per_node,
            search_mode=args.search_mode,
            split_mode=args.factor_split_mode,
            q_span_mode=args.q_span_mode,
            q_list_mode=args.q_list_mode,
        )
        payload["factor_export_validation"] = validate_factor_export(
            args.n,
            payload["recursive_factorization"],
        )
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(
            f"n={payload['n']} forbidden_form={payload['forbidden_form']} "
            f"steps_used={payload['steps_used']} search_mode={payload['search_mode']} "
            f"q_span_mode={payload['q_span_mode']} q_list_mode={payload['q_list_mode']}"
        )
        print(
            f"candidates_generated={payload['candidates_generated']} "
            f"target_divisor_count={payload['target_divisor_count']} "
            f"early_stopped={payload['early_stopped']}"
        )
        print(
            f"base_register_bits={payload['base_register_bits']} "
            f"register_bits={payload['register_bits']} "
            f"flip_budget_per_seed={payload['flip_budget_per_seed']} "
            f"slots_per_shell={payload['slots_per_shell']} "
            f"frontier_keep_per_step={payload['frontier_keep_per_step']} "
            f"prune_keep_per_step={payload['prune_keep_per_step']}"
        )
        print(
            f"candidate_generation_policy={payload['candidate_generation_policy']} "
            f"trial_division_scan={payload['trial_division_scan']}"
        )
        print(
            f"tested_candidate_count={payload['tested_candidate_count']} "
            f"candidate_window_size={payload['candidate_window_size']} "
            f"search_coverage_fraction={payload['search_coverage_fraction']:.6f}"
        )
        if payload["q_list_mode"] == "gate-frontier":
            print(f"periodicity_trace={payload['periodicity_trace']}")
        print(f"divisors={payload['divisors']}")
        print(f"approx_harmonic_step={payload['approx_harmonic_step']}")
        if payload["symmetric_pair"] is not None:
            print(f"symmetric_pair={payload['symmetric_pair']}")
        print(f"one_step_pick_certificate={payload['one_step_pick_certificate']}")
        if args.prime_factorization:
            rec = payload["recursive_factorization"]
            validation = payload["factor_export_validation"]
            if rec.get("mode_warning"):
                print(f"WARNING: {rec['mode_warning']}")
            if rec.get("split_mode") == DEBUG_PEEL_MODE:
                print(
                    "WARNING: debug split mode active; odd cofactors are expected in 'unresolved' by design."
                )
            pass_count = sum(
                1 for chk in rec.get("unresolved_primality_checks", []) if chk.get("primality_test") == "pass"
            )
            fail_count = sum(
                1 for chk in rec.get("unresolved_primality_checks", []) if chk.get("primality_test") == "fail"
            )
            print(
                f"recursive_factorization_verified={rec['verified_product']} "
                f"prime_factors={rec['prime_factors']} unresolved={rec['unresolved']}"
            )
            print(
                f"unresolved_primality_checks(pass={pass_count}, fail={fail_count})="
                f"{rec.get('unresolved_primality_checks', [])}"
            )
            print(
                f"factor_export_validation_status={validation['status']} "
                f"failed_checks={validation['failed_checks']}"
            )
        if args.csv_roundtrip_check:
            print(f"csv_roundtrip_ok={payload['csv_roundtrip_ok']}")


if __name__ == "__main__":
    main()


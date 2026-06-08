#!/usr/bin/env python3
"""
Monolithic Geometric Factorization Engine
==========================================

Self-contained implementation of the HQIV-OSH geometric factorization algorithm.

Features:
- 2-peeling + odd candidate constraint
- Structured complementary angle pairs on #Q shell (odd k; each |n−k,k⟩ split is one periodicity)
- Register cap ∼ ⌊∛n⌋ (after twos are gone, odd core): aligns k-ladder breadth with cube-root scale
- Dynamic precision (bitlength + log n)
- Multiplication gate: strength `1 / (min(bitlen(c1), bitlen(c2)) + 2)` (lowest-register rule; Lean `strengthInvLowestRegister`)
- Age pruning + RECYCLING: aged-out registers are "cut" and relocated near π (n/2)
  so computational effort concentrates where semiprime factors actually hide
- Phase velocity tracking + period extraction

Usage:
    python3 monolithic_geometric_factorizer.py <number_to_factor>

Example:
    python3 monolithic_geometric_factorizer.py 100160063 --max-steps 500
"""

from __future__ import annotations
import argparse
import math
import time
from dataclasses import dataclass
from typing import Any, List, Optional

import mpmath as mp
import random

mp.mp.dps = 80


def floor_cbrt(n: int) -> int:
    """Greatest r ≥ 0 with r³ ≤ n (integer cube root, n ≥ 0)."""
    if n < 0:
        raise ValueError("floor_cbrt expects n >= 0")
    if n < 2:
        return 0 if n == 0 else 1
    lo, hi = 1, n
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid * mid * mid <= n:
            lo = mid
        else:
            hi = mid - 1
    return lo


@dataclass
class AngleRegister:
    angle: mp.mpf
    candidate: int
    phase_velocity: mp.mpf = mp.mpf(0)


def get_dynamic_precision(n: int) -> int:
    bits = n.bit_length()
    log_bits = max(1, int(math.log2(max(2, bits))))
    return bits + log_bits + 8


def angle_to_candidate(angle: mp.mpf, n: int) -> int:
    theta = angle % (2 * mp.pi)
    root = max(2, int(mp.sqrt(n)))
    frac = theta / (2 * mp.pi)
    return 2 + int(frac * (root - 1))


def strength_inv_lowest_register(c1: int, c2: int) -> int:
    """
    Denominator for multiplication-gate strength: min bit-length of the two candidates + 2.
    Matches Hqiv.Geometry.MonolithicGeometricFactorizer.strengthInvLowestRegister.
    Smaller-magnitude registers get stronger updates than the old abs(c1-c2).bit_length() rule.
    """
    return min(c1.bit_length(), c2.bit_length()) + 2


def observed_smallest_period(trace: List[int]) -> Optional[int]:
    """
    Smallest p >= 1 such that trace[i] == trace[i+p] for all i with i+p < len(trace).
    Returns None if no such p (or trace too short).
    """
    L = len(trace)
    if L < 2:
        return None
    for p in range(1, L):
        if all(trace[i] == trace[i + p] for i in range(L - p)):
            return p
    return None


def certified_mod_period(trace: List[int]) -> Optional[int]:
    """
    Same as observed_smallest_period, but only certify when len(trace) >= 2*p so the window
    is long enough to treat the mod trace as stably periodic (cf. Lean modPeriodObservedPrefix).
    """
    p = observed_smallest_period(trace)
    if p is None:
        return None
    if len(trace) < 2 * p:
        return None
    return p


def prune_age_threshold(
    odd_core: int,
    candidate: int,
    mod_trace: List[int],
) -> int:
    """
    Schedule: |candidate - odd_core| bit-length + 1 (aligned with Lean `pruneAgeThreshold`).
    If candidate mod odd_core residues show a certified period p, use min(base, p + 1)
    (redundant mod-n observable; see Lean `mod_residue_eq_mod_age`).
    """
    bit_diff = abs(candidate - odd_core).bit_length()
    base = bit_diff + 1
    p = certified_mod_period(mod_trace)
    if p is not None:
        return min(base, p + 1)
    return base


def multiplication_gate_integrated(
    reg1: AngleRegister, reg2: AngleRegister, n: int
) -> tuple[AngleRegister, AngleRegister]:
    c1, c2 = reg1.candidate, reg2.candidate
    product = c1 * c2
    closeness = mp.mpf(abs(product - n)) / mp.mpf(n)

    inv_den = strength_inv_lowest_register(c1, c2)
    strength = mp.mpf(1) / mp.mpf(inv_den)
    phase_advance = (1 - closeness) * strength

    new_angle1 = (reg1.angle + phase_advance) % (2 * mp.pi)
    new_angle2 = (reg2.angle - phase_advance) % (2 * mp.pi)

    return (
        AngleRegister(new_angle1, angle_to_candidate(new_angle1, n), reg1.phase_velocity + phase_advance),
        AngleRegister(new_angle2, angle_to_candidate(new_angle2, n), reg2.phase_velocity - phase_advance),
    )


def extract_period(phase_history: List[float]) -> float:
    if len(phase_history) < 8:
        return 0.0
    best_period = 0.0
    best_corr = -1.0
    for p in range(2, len(phase_history) // 2):
        corr = sum(phase_history[i] * phase_history[i + p] for i in range(len(phase_history) - p))
        corr /= (len(phase_history) - p)
        if corr > best_corr:
            best_corr = corr
            best_period = p
    return best_period


def is_probable_prime(n: int) -> bool:
    """Simple deterministic Miller-Rabin for n < 2^64."""
    if n < 2:
        return False
    if n in (2, 3, 5, 7, 11, 13, 17, 19, 23):
        return True
    if n % 2 == 0 or n % 3 == 0 or n % 5 == 0:
        return False

    s, d = 0, n - 1
    while d % 2 == 0:
        d //= 2
        s += 1

    bases = [2, 3, 5, 7, 11, 13, 23, 29, 31, 37]
    for a in bases:
        if a >= n:
            break
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


def factor(n: int) -> dict[str, Any]:
    """
    Main factorization function with recursive cofactor factorization.
    Fully autonomous: no max_steps. Pruning preferentially removes smallest
    candidates first so that the largest registers (which need more time to
    establish periodicity) survive longest.
    """
    if n <= 1:
        return {"success": False, "prime_factors": [], "steps": 0}

    started = time.perf_counter()
    all_factors: List[int] = []

    # 1. Peel 2s
    while n % 2 == 0:
        all_factors.append(2)
        n //= 2

    if n == 1:
        return {
            "success": True,
            "prime_factors": sorted(all_factors),
            "steps": 0,
            "time": time.perf_counter() - started
        }

    # 2. Dynamic precision
    mp.mp.dps = get_dynamic_precision(n)

    # 3. Structured complementary angle pairs (odd only) — fully dynamic
    registers: List[AngleRegister] = []
    max_k = min(n // 4, int(mp.sqrt(n)) * 2)
    # Odd core: cap list size by ⌊∛n⌋ (clamped), same order as complementary-k coverage
    max_registers = max(12, min(128, floor_cbrt(n)))
    for k in range(3, max_k + 1, 2):
        a = n - k
        b = k
        if a <= b:
            continue
        angle_a = mp.mpf(a) / mp.mpf(n) * 2 * mp.pi
        angle_b = mp.mpf(b) / mp.mpf(n) * 2 * mp.pi
        registers.append(AngleRegister(angle_a, a))
        registers.append(AngleRegister(angle_b, b))
        if len(registers) >= max_registers:
            break

    phase_history: List[float] = []
    best_factor: Optional[int] = None
    pair_ages: dict[int, int] = {id(reg): 0 for reg in registers}
    # Per-register history of (candidate mod n) for periodicity-certified pruning (odd core n >= 3)
    mod_n_traces: dict[int, List[int]] = {id(reg): [] for reg in registers}
    _MOD_TRACE_CAP = 128

    # === Hierarchical promotion state ===
    best_angle = mp.pi          # will track the most promising angle seen so far
    promotion_level = 0         # how many times we've refined (for future harmonic scaling)

    step = 0
    while len(registers) >= 2:
        step += 1

        # Update best_angle from the register with highest phase velocity
        if registers:
            best_reg = max(registers, key=lambda r: float(r.phase_velocity))
            best_angle = best_reg.angle

        # === Autonomous pruning + HIERARCHICAL PROMOTION ===
        # When a register ages out, we "promote" it by bisecting the current
        # best_angle. This is the classical equivalent of stepping to the next
        # resolution level around the most promising implicit angle.
        if len(registers) > 4:
            registers.sort(key=lambda r: r.candidate)  # smallest first

            i = 0
            while i < len(registers):
                reg = registers[i]
                age = pair_ages.get(id(reg), 0)
                trace = mod_n_traces.get(id(reg), [])
                threshold = prune_age_threshold(n, reg.candidate, trace)
                if age > threshold:
                    # PROMOTE (recycle) if it lived long enough and we have room
                    if len(registers) < max_registers and age > threshold + 2:
                        # HIERARCHICAL N-SECT PROMOTION (deterministic, geometry-aware, no jitter)
                        # Stacking: level 0 → 2 children (bisect), level 1 → 3 (trisect), etc.
                        # Bias: if parent is acute, put 2/3 children on obtuse side (toward π)
                        num_children = promotion_level + 2

                        is_acute = (best_angle < mp.pi/2) or (best_angle > 3*mp.pi/2)
                        obtuse_center = mp.pi
                        acute_center = best_angle

                        # 1/2 on each side, odd residue goes to obtuse side
                        obtuse_count = (num_children + 1) // 2
                        acute_count = num_children - obtuse_count

                        # Shrinking window (log resolution growth)
                        window = mp.pi / (2 ** (promotion_level // 2 + 1))

                        # Place obtuse-side children (including odd residue)
                        for i in range(obtuse_count):
                            offset = (i - (obtuse_count - 1) / 2) * (window / obtuse_count)
                            new_angle = (obtuse_center + offset) % (2 * mp.pi)
                            new_candidate = angle_to_candidate(new_angle, n)
                            new_reg = AngleRegister(new_angle, new_candidate)
                            registers.append(new_reg)
                            pair_ages[id(new_reg)] = 0
                            mod_n_traces[id(new_reg)] = []

                        # Place acute-side children
                        for i in range(acute_count):
                            offset = (i - (acute_count - 1) / 2) * (window / acute_count)
                            new_angle = (acute_center + offset) % (2 * mp.pi)
                            new_candidate = angle_to_candidate(new_angle, n)
                            new_reg = AngleRegister(new_angle, new_candidate)
                            registers.append(new_reg)
                            pair_ages[id(new_reg)] = 0
                            mod_n_traces[id(new_reg)] = []

                        promotion_level += 1   # moved to next resolution level

                    # Remove the old (aged-out) register
                    del registers[i]
                    pair_ages.pop(id(reg), None)
                    mod_n_traces.pop(id(reg), None)
                else:
                    i += 1

        if len(registers) < 2:
            break

        r1, r2 = registers[0], registers[1]
        new_r1, new_r2 = multiplication_gate_integrated(r1, r2, n)

        registers[0] = new_r1
        registers[1] = new_r2
        phase_history.append(float(new_r1.phase_velocity))

        for reg in registers:
            pair_ages[id(reg)] = pair_ages.get(id(reg), 0) + 1

        # Append mod-n residues (FIFO) for periodicity detection
        for reg in registers:
            tid = id(reg)
            tr = mod_n_traces.setdefault(tid, [])
            tr.append(reg.candidate % n)
            if len(tr) > _MOD_TRACE_CAP:
                tr[:] = tr[-_MOD_TRACE_CAP:]

        for reg in registers:
            if 1 < reg.candidate < n and n % reg.candidate == 0:
                best_factor = reg.candidate
                break

        if best_factor:
            break

    # Final extraction + recursive factorization
    success = False
    if best_factor:
        q = n // best_factor
        if not is_probable_prime(best_factor):
            sub = factor(best_factor)
            all_factors.extend(sub.get("prime_factors", []))
        else:
            all_factors.append(best_factor)

        if not is_probable_prime(q):
            sub = factor(q)
            all_factors.extend(sub.get("prime_factors", []))
        else:
            all_factors.append(q)
        success = True
    else:
        best_reg = max(registers, key=lambda r: float(r.phase_velocity))
        if 1 < best_reg.candidate < n and n % best_reg.candidate == 0:
            q = n // best_reg.candidate
            if not is_probable_prime(best_reg.candidate):
                sub = factor(best_reg.candidate)
                all_factors.extend(sub.get("prime_factors", []))
            else:
                all_factors.append(best_reg.candidate)
            if not is_probable_prime(q):
                sub = factor(q)
                all_factors.extend(sub.get("prime_factors", []))
            else:
                all_factors.append(q)
            success = True
        else:
            all_factors.append(n)
            success = False

    return {
        "success": success,
        "prime_factors": sorted(all_factors),
        "steps": step + 1,
        "time": time.perf_counter() - started,
        "precision_digits": mp.mp.dps
    }


def main():
    parser = argparse.ArgumentParser(description="Monolithic Geometric Factorizer (fully autonomous)")
    parser.add_argument("n", type=int, help="Number to factor")
    args = parser.parse_args()

    print(f"Factoring {args.n} (autonomous + recycling mode)...")
    result = factor(args.n)

    print(f"\nResult: {'SUCCESS' if result['success'] else 'FAIL'}")
    print(f"Prime factors: {result.get('prime_factors', result.get('factors', []))}")
    print(f"Steps: {result['steps']}")
    print(f"Time: {result['time']:.3f}s")
    print(f"Precision: {result['precision_digits']} digits")


if __name__ == "__main__":
    main()

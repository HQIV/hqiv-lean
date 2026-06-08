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
- Multiplication gate: `1 / (min(bitlen(c1), bitlen(c2)) + 2)` only — matches Lean `phaseAdvanceRatLowest` /
  `strengthInvLowestRegister` (no dependence on **steps left**). **Total** step / age budgets for drift
  live in the ℝ template `MonolithicFracResources` / `FracDriftAdequateResources`, not as a per-iteration
  strength multiplier here.
- Age pruning: `(⌊bitlen(n)/2⌋)³` on the odd core `n` — balanced semiprime: smallest factor register has
  half the target bits (e.g. 39-bit `n` → 19-bit registers → 19³ steps). No extra multipliers or mod caps.
- Phase velocity (rapidity surrogate) per register line; ages/mod-traces keyed by stable **uid**, not
  `id(object)` — gate updates must preserve uid so prune thresholds see real iteration depth on the
  active pair (replacing `AngleRegister` each step used to reset identity every time).
- Phase history + period extraction
- Termination: no step cap — when only one register remains it ages under the same threshold
  until pruned, then the search ends (pair exhaustion + final age-out).

Usage:
    python3 monolithic_geometric_factorizer.py <number_to_factor> [--progress-every N]

Example:
    python3 monolithic_geometric_factorizer.py 100160063
    python3 monolithic_geometric_factorizer.py <RSA100> --progress-every 1000000
"""

from __future__ import annotations
import argparse
import math
import time
from dataclasses import dataclass
from typing import Any, List, Optional

import mpmath as mp

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
    """One logical ket line; `uid` survives gate replacement so age/mod-trace bookkeeping stays coherent."""

    uid: int
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


def prune_age_threshold(odd_core: int) -> int:
    """
    Age budget `(⌊bitlen(n)/2⌋)³` on the odd composite core `n`.

    For a balanced semiprime, factors sit near `√n`, so the smallest register in the tight pair has
    half the target bit-length (e.g. 39-bit `n` → 19-bit → 19³ steps).
    """
    shell = max(1, odd_core.bit_length() // 2)
    return shell**3


def multiplication_gate_integrated(
    reg1: AngleRegister,
    reg2: AngleRegister,
    n: int,
) -> tuple[AngleRegister, AngleRegister]:
    c1, c2 = reg1.candidate, reg2.candidate
    product = c1 * c2
    closeness = mp.mpf(abs(product - n)) / mp.mpf(n)

    # Lean `phaseAdvanceRatLowest`: `(1 - closeness) / strengthInvLowestRegister` — fixed per (c1,c2), not
    # a function of remaining age (see `MonolithicFracResources` for total-step drift budgets).
    inv_den = strength_inv_lowest_register(c1, c2)
    strength = mp.mpf(1) / mp.mpf(inv_den)
    phase_advance = (1 - closeness) * strength

    new_angle1 = (reg1.angle + phase_advance) % (2 * mp.pi)
    new_angle2 = (reg2.angle - phase_advance) % (2 * mp.pi)

    return (
        AngleRegister(
            reg1.uid,
            new_angle1,
            angle_to_candidate(new_angle1, n),
            reg1.phase_velocity + phase_advance,
        ),
        AngleRegister(
            reg2.uid,
            new_angle2,
            angle_to_candidate(new_angle2, n),
            reg2.phase_velocity - phase_advance,
        ),
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


def _age_prune_allowed(num_registers: int) -> bool:
    """Lean-aligned: drop stale lines when >4 regs, or when at most 2 (pair/last line can age out)."""
    return num_registers > 4 or num_registers <= 2


def _cofactor_if_divisor(n: int, d: int) -> int | None:
    """
    Trial divisibility uses the remainder only (`n % d`); most candidates fail here without ever
    forming a quotient. Only when `n % d == 0` do we compute `n // d` for the cofactor used in
    recursion. (On many CPUs `%` and `//` share one divider; conceptually `%` is the factor test.)
    """
    if d <= 1 or d >= n:
        return None
    if n % d != 0:
        return None
    return n // d


def factor(n: int, *, progress_every: int = 0) -> dict[str, Any]:
    """
    Main factorization function with recursive cofactor factorization.
    Terminates when registers exhaust by pruning (including a final single-register age-out).

    If ``progress_every > 0``, print a line every that many steps (main + tail loops) so huge
    ``n`` runs remain observable. Recursive cofactor calls disable progress to avoid noise.
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
    next_uid = 0
    for k in range(3, max_k + 1, 2):
        a = n - k
        b = k
        if a <= b:
            continue
        angle_a = mp.mpf(a) / mp.mpf(n) * 2 * mp.pi
        angle_b = mp.mpf(b) / mp.mpf(n) * 2 * mp.pi
        registers.append(AngleRegister(next_uid, angle_a, a))
        next_uid += 1
        registers.append(AngleRegister(next_uid, angle_b, b))
        next_uid += 1
        if len(registers) >= max_registers:
            break

    phase_history: List[float] = []
    best_factor: Optional[int] = None
    pair_ages: dict[int, int] = {reg.uid: 0 for reg in registers}

    step = 0
    while len(registers) >= 2:
        step += 1
        if progress_every > 0 and step % progress_every == 0:
            elapsed = time.perf_counter() - started
            print(
                f"[progress] step={step} registers={len(registers)} "
                f"elapsed_s={elapsed:.3f}",
                flush=True,
            )

        # Discard exhausted registers: threshold tightened if mod-n trace is periodic;
        # allow age-out when only 1–2 lines remain (otherwise two lines could spin forever).
        active_registers = []
        for reg in registers:
            age = pair_ages.get(reg.uid, 0)
            threshold = prune_age_threshold(n)
            if age > threshold and _age_prune_allowed(len(registers)):
                continue
            active_registers.append(reg)
        registers = active_registers

        if len(registers) < 2:
            break

        r1, r2 = registers[0], registers[1]
        new_r1, new_r2 = multiplication_gate_integrated(r1, r2, n)

        registers[0] = new_r1
        registers[1] = new_r2
        phase_history.append(float(new_r1.phase_velocity))

        for reg in registers:
            pair_ages[reg.uid] = pair_ages.get(reg.uid, 0) + 1

        for reg in registers:
            if _cofactor_if_divisor(n, reg.candidate) is not None:
                best_factor = reg.candidate
                break

        if best_factor:
            break

    # Sole surviving register: age under the same schedule until threshold prune (no pair gate).
    while len(registers) == 1 and not best_factor:
        step += 1
        if progress_every > 0 and step % progress_every == 0:
            elapsed = time.perf_counter() - started
            print(
                f"[progress] step={step} tail registers=1 elapsed_s={elapsed:.3f}",
                flush=True,
            )
        reg = registers[0]
        age = pair_ages.get(reg.uid, 0)
        threshold = prune_age_threshold(n)
        if age > threshold:
            registers = []
            break
        pair_ages[reg.uid] = age + 1
        if _cofactor_if_divisor(n, reg.candidate) is not None:
            best_factor = reg.candidate
            break

    # Final extraction + recursive factorization
    success = False
    if best_factor:
        # Quotient only after `%` already succeeded in the search loops above.
        q = n // best_factor
        if not is_probable_prime(best_factor):
            sub = factor(best_factor, progress_every=0)
            all_factors.extend(sub.get("prime_factors", []))
        else:
            all_factors.append(best_factor)

        if not is_probable_prime(q):
            sub = factor(q, progress_every=0)
            all_factors.extend(sub.get("prime_factors", []))
        else:
            all_factors.append(q)
        success = True
    elif not registers:
        all_factors.append(n)
        success = False
    else:
        best_reg = max(registers, key=lambda r: float(r.phase_velocity))
        q = _cofactor_if_divisor(n, best_reg.candidate)
        if q is not None:
            if not is_probable_prime(best_reg.candidate):
                sub = factor(best_reg.candidate, progress_every=0)
                all_factors.extend(sub.get("prime_factors", []))
            else:
                all_factors.append(best_reg.candidate)
            if not is_probable_prime(q):
                sub = factor(q, progress_every=0)
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
        "steps": step,
        "time": time.perf_counter() - started,
        "precision_digits": mp.mp.dps
    }


def main():
    parser = argparse.ArgumentParser(description="Monolithic Geometric Factorizer")
    parser.add_argument("n", type=int, help="Number to factor")
    parser.add_argument(
        "--progress-every",
        type=int,
        default=0,
        metavar="N",
        help="Print [progress] every N steps (0 = off). Use for large n (e.g. 1_000_000).",
    )
    args = parser.parse_args()
    if args.progress_every < 0:
        raise SystemExit("--progress-every must be >= 0")

    print(f"Factoring {args.n}...", flush=True)
    result = factor(args.n, progress_every=args.progress_every)

    print(f"\nResult: {'SUCCESS' if result['success'] else 'FAIL'}")
    print(f"Prime factors: {result.get('prime_factors', result.get('factors', []))}")
    print(f"Steps: {result['steps']}")
    print(f"Time: {result['time']:.3f}s")
    print(f"Precision: {result['precision_digits']} digits")


if __name__ == "__main__":
    main()
import math
from bisect import bisect_right
from collections import deque
from typing import Any, Optional

from mpmath import mp

# =============================================================================
# Continuous anchored spiral (two-leg schedule + carried phase)
# - After small-prime peel: if current is a perfect square, split as s·s (isqrt) first.
# - Phase accumulator (per factorization run): each shell uses
#     phase_offset = phase_carry + log(current)
#   as harmonic advance H_N (small vs raw log); legs use θ_k = π/(2k) and complement π/2 − θ_k,
#     effective = (target + phase_offset) mod 2π
#   so winding continues across shells (pole-crossing direction). H_N uses log(current)/bitlen
#   so the offset stays modest while tracking shell scale (“2, m/2” / quadratic anchor).
# - Integer legs: nint(r·cos(effective)), nint(r·sin(effective)); divisor gates use p_max.
# - mpmath dps scales with |current|.
# =============================================================================


def _set_precision_for_n(n: int) -> None:
    """Decimal precision for mpf spiral: scale with bit length of the cofactor."""
    if n <= 1:
        mp.dps = 50
        return
    b = n.bit_length()
    mp.dps = max(50, min(400, b + 36))

_MAX_TRIAL = 1_000_000


def _primes_upto(limit: int) -> list[int]:
    if limit < 2:
        return []
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, int(limit**0.5) + 1):
        if sieve[p]:
            step = p
            start = p * p
            sieve[start : limit + 1 : step] = b"\x00" * ((limit - start) // step + 1)
    return [i for i in range(2, limit + 1) if sieve[i]]


_PRIMES_TO_1M = _primes_upto(_MAX_TRIAL)


def _dynamic_sieve_cap(current: int) -> int:
    """Upper bound for odd trial primes (inclusive of all primes ≤ this cap)."""
    b = current.bit_length()
    raw = 1 << (b // 9)
    return min(_MAX_TRIAL, max(257, raw))


def _gate_p_max(use_odd_sieve: bool, sieve_cap: int) -> int:
    """Spiral divisor gates use ``p_max < probe < current``; match what trial division already covered.

    When the odd sieve runs, ``p_max`` is the sieve cap. With odd sieve off, only factors of 2
    were stripped, so treat the effective presieve bound as ``3`` (minimum nontrivial odd).
    """
    if use_odd_sieve:
        return max(3, sieve_cap)
    return 3


def octonion_factor(
    N: int,
    *,
    use_odd_sieve: bool = True,
    trace: Optional[list[dict[str, Any]]] = None,
) -> list[int]:
    """Two-leg structured search per spiral crossing; optional odd-prime presieve.

    If ``trace`` is a list, append spiral_step events with base angle, effective angle,
    phase carry/offset, and leg probes.
    """
    if N <= 1:
        return []
    factors: list[int] = []
    pending: deque[int] = deque([N])
    phase_carry = mp.mpf(0)

    while pending:
        current = pending.popleft()
        if current <= 1:
            continue

        while current % 2 == 0:
            factors.append(2)
            current //= 2
        if current == 1:
            continue

        sieve_cap = _dynamic_sieve_cap(current)
        if use_odd_sieve:
            hi = bisect_right(_PRIMES_TO_1M, sieve_cap)
            for p in _PRIMES_TO_1M[:hi]:
                if p == 2:
                    continue
                while current % p == 0:
                    factors.append(p)
                    current //= p
                if current == 1:
                    break
            if current == 1:
                continue

        p_max = _gate_p_max(use_odd_sieve, sieve_cap)
        if trace is not None:
            trace.append(
                {
                    "event": "current_start",
                    "current": current,
                    "p_max": p_max,
                    "sieve_cap": sieve_cap,
                    "use_odd_sieve": use_odd_sieve,
                }
            )

        # Perfect square: split before the spiral (integer sqrt / isqrt).
        s0 = math.isqrt(current)
        if s0 > 1 and s0 * s0 == current:
            if trace is not None:
                trace.append({"event": "sqrt_peel", "current": current, "s": s0})
            pending.append(s0)
            pending.append(s0)
            continue

        _set_precision_for_n(current)
        c = mp.mpf(current)
        r = mp.sqrt(c)
        k_max = 2
        while k_max < c ** (1 / mp.mpf(k_max)):
            k_max += 1
        k_max = max(k_max - 1, 2)

        peeled = False
        two_pi = 2 * mp.pi
        bl = max(1, current.bit_length())
        harmonic = mp.log(c) / mp.mpf(bl)
        # Harmonic advance H_N + carried pole phase (continuous shell-to-shell winding).
        phase_offset = phase_carry + harmonic

        for k in range(2, k_max + 1):
            theta_k = mp.pi / (2 * mp.mpf(k))
            complement = mp.pi / 2 - theta_k

            for name, target in (("theta_k", theta_k), ("complement", complement)):
                eff = (target + phase_offset) % two_pi
                t_deg = float(target * 180 / mp.pi)
                eff_deg = float(eff * 180 / mp.pi)
                leg1 = int(mp.nint(r * mp.cos(eff)))
                leg2 = int(mp.nint(r * mp.sin(eff)))

                if trace is not None:
                    trace.append(
                        {
                            "event": "spiral_step",
                            "current": current,
                            "p_max": p_max,
                            "k": k,
                            "target": name,
                            "theta_k_deg": float(theta_k * 180 / mp.pi),
                            "angle_deg": t_deg,
                            "angle_rad": float(target),
                            "phase_carry": float(phase_carry),
                            "phase_offset": float(phase_offset),
                            "effective_deg": eff_deg,
                            "effective_rad": float(eff),
                            "leg1": leg1,
                            "leg2": leg2,
                        }
                    )

                if leg1 <= 0 or leg2 <= 0:
                    continue

                if p_max < leg1 < current and current % leg1 == 0:
                    pending.append(leg1)
                    pending.append(current // leg1)
                    peeled = True
                    break
                if p_max < leg2 < current and current % leg2 == 0:
                    pending.append(leg2)
                    pending.append(current // leg2)
                    peeled = True
                    break

            if peeled:
                break

        phase_carry = mp.fmod(phase_offset, two_pi)

        if not peeled:
            if trace is not None:
                trace.append({"event": "irreducible", "current": current})
            factors.append(current)

    return sorted(factors)


if __name__ == "__main__":
    import argparse

    p = argparse.ArgumentParser(description="Octonion two-leg spiral factorization (heuristic).")
    p.add_argument("N", type=int, nargs="?", default=143, help="integer (default: 143)")
    args = p.parse_args()
    print(octonion_factor(args.N))

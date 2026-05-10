#!/usr/bin/env python3
"""
Plastic Spiral Factorization Oracle v3 (in-repo)

Pure plastic workflow:
- Adaptive arity up to ~ n^(1/3)
- Per-arity step budgets ~ n^(1/k)
- Multi-seed k-arc sampling
- Direct + continued-fraction snap scoring
- Prime-selective extraction

No trial-division fallback is used in this file.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Dict, Iterable, List, Tuple

PLASTIC = 1.32471795724474602596
TWO_PI = 2.0 * math.pi
PLASTIC_ANGLE = TWO_PI / PLASTIC


def is_probable_prime(n: int) -> bool:
    """Deterministic Miller-Rabin for 64-bit integers."""
    if n < 2:
        return False
    small_primes = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29)
    for p in small_primes:
        if n == p:
            return True
        if n % p == 0:
            return False

    d = n - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1

    # Deterministic bases for n < 2^64
    for a in (2, 325, 9375, 28178, 450775, 9780504, 1795265022):
        if a % n == 0:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        witness = True
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                witness = False
                break
        if witness:
            return False
    return True


def continued_fraction_convergents(x: float, max_terms: int = 20) -> List[Tuple[int, int]]:
    """Return convergents p/q for x via standard CF recurrence."""
    a0 = math.floor(x)
    p_nm2, p_nm1 = 0, 1
    q_nm2, q_nm1 = 1, 0
    p_n = a0 * p_nm1 + p_nm2
    q_n = a0 * q_nm1 + q_nm2
    out = [(int(p_n), int(q_n))]

    frac = x - a0
    for _ in range(max_terms - 1):
        if abs(frac) < 1e-15:
            break
        a = math.floor(1.0 / frac)
        frac = 1.0 / frac - a
        p_np1 = a * p_n + p_nm1
        q_np1 = a * q_n + q_nm1
        out.append((int(p_np1), int(q_np1)))
        p_nm2, p_nm1, p_n = p_nm1, p_n, p_np1
        q_nm2, q_nm1, q_n = q_nm1, q_n, q_np1
    return out


@dataclass(frozen=True)
class SnapHit:
    k: int
    step: int
    seed_idx: int
    divisor: int
    score: float
    channel: str


def root_scale_bound(n: int, k: int, stretch: float = 1.8) -> int:
    if k <= 1:
        return max(5, int(stretch * n))
    return max(5, int((n ** (1.0 / k)) * stretch))


def iter_k_values(n: int, min_k: int = 3) -> Iterable[int]:
    max_k = max(12, int(n ** (1.0 / 3.0)) + 3)
    return range(min_k, max_k + 1)


def plastic_spiral_snap(
    n: int,
    tolerance: float = 8e-3,
    max_cf_terms: int = 14,
) -> Dict[int, List[SnapHit]]:
    """
    Evaluate plastic snaps across adaptive k.

    Returns: k -> list of best hits (deduplicated by divisor).
    """
    results: Dict[int, List[SnapHit]] = {}
    if n < 4:
        return results

    for k in iter_k_values(n):
        step_bound = root_scale_bound(n, k)
        best_by_divisor: Dict[int, SnapHit] = {}

        for step in range(1, step_bound + 1):
            theta = (step * PLASTIC_ANGLE) % TWO_PI
            for seed_idx in range(k):
                seed_angle = TWO_PI * seed_idx / k
                total = (theta + seed_angle) % TWO_PI
                norm = total / TWO_PI
                if norm <= 1e-15:
                    continue

                # Direct reciprocal snap
                d_direct = int(round(1.0 / norm))
                if 2 < d_direct < n:
                    score = abs(norm - (1.0 / d_direct))
                    if score < tolerance and n % d_direct == 0:
                        hit = SnapHit(k, step, seed_idx, d_direct, score, "direct")
                        prev = best_by_divisor.get(d_direct)
                        if prev is None or hit.score < prev.score:
                            best_by_divisor[d_direct] = hit

                # Continued-fraction denominator snaps
                for p, q in continued_fraction_convergents(norm, max_terms=max_cf_terms):
                    if q <= 1 or q >= n:
                        continue
                    score = abs(norm - (p / q))
                    if score < tolerance * 0.1 and n % q == 0:
                        hit = SnapHit(k, step, seed_idx, q, score, "cf")
                        prev = best_by_divisor.get(q)
                        if prev is None or hit.score < prev.score:
                            best_by_divisor[q] = hit

        results[k] = sorted(best_by_divisor.values(), key=lambda h: (h.score, h.step, h.divisor))
    return results


def factor_with_plastic_v3(n: int, verbose: bool = True) -> Dict[str, object]:
    """
    Prime-selective factor extraction from plastic snaps.

    No classical fallback; any unresolved cofactor is reported explicitly.
    """
    if n < 2:
        return {"n": n, "factors": [], "remaining": n, "complete": True, "hits_by_k": {}}

    original_n = n
    factors: List[int] = []

    # Strip 2 exactly; this is not trial-division fallback.
    while n % 2 == 0:
        factors.append(2)
        n //= 2

    hits_by_k = plastic_spiral_snap(original_n)

    prime_candidates = sorted(
        {
            h.divisor
            for hits in hits_by_k.values()
            for h in hits
            if h.divisor > 2 and original_n % h.divisor == 0 and is_probable_prime(h.divisor)
        }
    )

    remaining = n
    for p in prime_candidates:
        while remaining > 1 and remaining % p == 0:
            factors.append(p)
            remaining //= p

    factors.sort()
    complete = remaining == 1

    if verbose:
        print(f"n={original_n}  factors={factors}  remaining={remaining}  complete={complete}")
        for k in sorted(hits_by_k):
            hits = hits_by_k[k]
            if not hits:
                continue
            top = [h.divisor for h in hits[:5]]
            print(f"  k={k:2d} hits={len(hits):2d} top_divisors={top}")

    return {
        "n": original_n,
        "factors": factors,
        "remaining": remaining,
        "complete": complete,
        "hits_by_k": hits_by_k,
    }


if __name__ == "__main__":
    for example in (27, 221, 10403, 10007):
        print("\n---")
        factor_with_plastic_v3(example, verbose=True)

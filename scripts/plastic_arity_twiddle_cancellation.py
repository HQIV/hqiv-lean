#!/usr/bin/env python3
"""
Probe the "arity-permutation cancellation" hypothesis with a plastic twiddle.

Model:
  - For each n, build ordered nontrivial factor pairs (a, b) with a*b = n, a,b >= 2.
  - Define an antisymmetric twiddle term T(a,b;n) so T(b,a;n) = -T(a,b;n).
  - Composite channels cancel pairwise across (a,b) vs (b,a).
  - Prime n has no nontrivial pair on first pass, so a prime residue survives.

This is a structural sanity check for the cancellation mechanism, not a proof of
closed-form equality to zeta values.
"""

from __future__ import annotations

import argparse
import cmath
import math
import itertools
from typing import Iterable

import mpmath as mp

RHO = 1.3247179572447458


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def primes_upto(N: int) -> list[int]:
    return [p for p in range(2, N + 1) if is_prime(p)]


def unordered_factor_pairs(n: int) -> list[tuple[int, int]]:
    """Return [(a,b)] with a*b=n, 2 <= a <= b, and b>=2."""
    out: list[tuple[int, int]] = []
    a = 2
    while a * a <= n:
        if n % a == 0:
            b = n // a
            if b >= 2:
                out.append((a, b))
        a += 1
    return out


def plastic_angle(n: int, *, phase_scale: float) -> float:
    """Base angle per index n."""
    return phase_scale * (2.0 * math.pi * n / RHO)


def pair_term(a: int, b: int, n: int, *, s: float, phase_scale: float) -> complex:
    """
    Antisymmetric term: T(b,a;n) = -T(a,b;n) when amplitude is symmetric.
    """
    amp = 1.0 / (float(n) ** s) / float(a + b)
    theta = plastic_angle(n, phase_scale=phase_scale)
    # Equivalent to amp * sin((a-b)*theta), kept in complex form for flexibility.
    return amp * (cmath.exp(1j * (a - b) * theta) - cmath.exp(-1j * (a - b) * theta)) / (2j)


def ordered_pair_sum(n: int, *, s: float, phase_scale: float) -> complex:
    total = 0j
    for a, b in unordered_factor_pairs(n):
        total += pair_term(a, b, n, s=s, phase_scale=phase_scale)
        total += pair_term(b, a, n, s=s, phase_scale=phase_scale)
    return total


def ordered_triple_factorizations(n: int) -> list[tuple[int, int, int]]:
    """
    Return ordered triples (a,b,c) with a*b*c=n and a,b,c>=2.
    """
    out: list[tuple[int, int, int]] = []
    if n < 8:
        return out
    for a in range(2, n + 1):
        if n % a != 0:
            continue
        n2 = n // a
        for b in range(2, n2 + 1):
            if n2 % b != 0:
                continue
            c = n2 // b
            if c >= 2:
                out.append((a, b, c))
    return out


def perm_sign_3(base: tuple[int, int, int], perm: tuple[int, int, int]) -> int:
    """
    Signature (+1/-1) of permutation sending `base` to `perm`.
    Assumes distinct entries; caller handles duplicate-entry fallback.
    """
    idx = {v: i for i, v in enumerate(base)}
    p = [idx[v] for v in perm]
    inv = 0
    for i in range(3):
        for j in range(i + 1, 3):
            if p[i] > p[j]:
                inv += 1
    return -1 if (inv % 2) else 1


def triple_orbit_term(a: int, b: int, c: int, n: int, *, s: float, phase_scale: float) -> complex:
    """
    Antisymmetric sum over S3 permutations for one unordered triple orbit.
    For distinct (a,b,c), this cancels exactly by sign symmetry.
    """
    base = (a, b, c)
    if len(set(base)) < 3:
        # Degenerate orbit: no strict antisymmetry guarantee.
        return 0j
    theta = plastic_angle(n, phase_scale=phase_scale)
    amp = 1.0 / (float(n) ** s) / float(a + b + c)
    total = 0j
    for p in itertools.permutations(base):
        sgn = perm_sign_3(base, p)
        ph = cmath.exp(1j * theta * (p[0] + 2 * p[1] + 3 * p[2]))
        total += sgn * amp * ph
    return total


def ordered_triple_sum(n: int, *, s: float, phase_scale: float) -> complex:
    """
    Sum one representative per unordered triple orbit, then antisymmetrize via S3.
    """
    seen: set[tuple[int, int, int]] = set()
    total = 0j
    for a, b, c in ordered_triple_factorizations(n):
        key = tuple(sorted((a, b, c)))
        if key in seen:
            continue
        seen.add(key)
        total += triple_orbit_term(a, b, c, n, s=s, phase_scale=phase_scale)
    return total


def prime_first_pass_term(n: int, *, s: float, phase_scale: float, prime_weight: float) -> complex:
    if not is_prime(n):
        return 0j
    theta = plastic_angle(n, phase_scale=phase_scale)
    return prime_weight * (1.0 / (float(n) ** s)) * cmath.exp(1j * theta)


def twisted_prime_chi(p: int, *, phase_scale: float) -> complex:
    """
    Prime character-like twiddle used in both sum and product diagnostics.
    """
    return cmath.exp(1j * plastic_angle(p, phase_scale=phase_scale))


def euler_product_diagnostics(
    N: int,
    *,
    s: float,
    phase_scale: float,
    prime_weight: float,
) -> dict[str, complex | float | int]:
    """
    Compare a twiddled prime sum to an Euler-style prime product:
      S_p := Σ_{p<=N} prime_weight * χ(p) / p^s
      P_N := Π_{p<=N} (1 - prime_weight * χ(p) / p^s)^(-1)
    and exp(S_p), which is the first-log approximation to P_N.
    """
    ps = primes_upto(N)
    s_p = 0j
    log_p_n = 0j
    p_n = 1 + 0j
    min_denom = float("inf")

    for p in ps:
        z = prime_weight * twisted_prime_chi(p, phase_scale=phase_scale) / (float(p) ** s)
        s_p += z
        denom = 1 - z
        dabs = abs(denom)
        min_denom = min(min_denom, dabs)
        if dabs == 0.0:
            # Exact pole for truncated product.
            return {
                "prime_terms": len(ps),
                "prime_sum": s_p,
                "euler_product": complex(float("inf"), 0.0),
                "exp_prime_sum": cmath.exp(s_p),
                "product_minus_exp_sum": complex(float("inf"), 0.0),
                "product_minus_zeta3": complex(float("inf"), 0.0),
                "min_product_denom_abs": 0.0,
            }
        p_n *= 1.0 / denom
        # principal log branch; enough for empirical local diagnostics
        log_p_n += -cmath.log(denom)

    exp_s_p = cmath.exp(s_p)
    z3 = complex(float(mp.zeta(3)), 0.0)
    return {
        "prime_terms": len(ps),
        "prime_sum": s_p,
        "euler_product": p_n,
        "log_euler_product": log_p_n,
        "exp_prime_sum": exp_s_p,
        "product_minus_exp_sum": p_n - exp_s_p,
        "product_minus_zeta3": p_n - z3,
        "min_product_denom_abs": min_denom if ps else float("inf"),
    }


def run_probe(
    N: int,
    *,
    s: float,
    phase_scale: float,
    prime_weight: float,
) -> dict[str, complex | float | int]:
    pair_total = 0j
    triple_total = 0j
    prime_total = 0j
    max_pair_leak = 0.0
    max_triple_leak = 0.0
    composite_count = 0
    prime_count = 0

    for n in range(2, N + 1):
        p = ordered_pair_sum(n, s=s, phase_scale=phase_scale)
        t3 = ordered_triple_sum(n, s=s, phase_scale=phase_scale)
        pair_total += p
        triple_total += t3
        max_pair_leak = max(max_pair_leak, abs(p))
        max_triple_leak = max(max_triple_leak, abs(t3))
        if unordered_factor_pairs(n):
            composite_count += 1
        if is_prime(n):
            prime_count += 1
        prime_total += prime_first_pass_term(n, s=s, phase_scale=phase_scale, prime_weight=prime_weight)

    combined = pair_total + triple_total + prime_total
    z3 = complex(float(mp.zeta(3)), 0.0)
    return {
        "N": N,
        "s": s,
        "pair_total": pair_total,
        "triple_total": triple_total,
        "prime_total": prime_total,
        "combined": combined,
        "zeta3": z3,
        "err_vs_zeta3": abs(combined - z3),
        "max_pair_leak": max_pair_leak,
        "max_triple_leak": max_triple_leak,
        "composite_count": composite_count,
        "prime_count": prime_count,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Plastic twiddle arity-cancellation probe")
    parser.add_argument("--N", type=int, default=300, help="sum range n=2..N")
    parser.add_argument("--s", type=float, default=3.0, help="Dirichlet decay exponent")
    parser.add_argument(
        "--phase-scale",
        type=float,
        default=1.0,
        help="global scale in theta_n = phase_scale * (2π n / rho)",
    )
    parser.add_argument("--prime-weight", type=float, default=1.0, help="weight on surviving prime first-pass terms")
    parser.add_argument(
        "--report-euler-product",
        action="store_true",
        help="also report twisted Euler-prime-product diagnostics",
    )
    args = parser.parse_args()

    if args.N < 2:
        raise SystemExit("N must be >= 2")
    if args.s <= 1.0:
        raise SystemExit("Use s > 1 for a convergent Dirichlet envelope.")

    res = run_probe(
        args.N,
        s=args.s,
        phase_scale=args.phase_scale,
        prime_weight=args.prime_weight,
    )

    print(f"N={res['N']} s={res['s']} phase_scale={args.phase_scale} prime_weight={args.prime_weight}")
    print(f"composites={res['composite_count']} primes={res['prime_count']}")
    print(f"pair_total={res['pair_total']}  |pair_total|={abs(res['pair_total']):.12g}")
    print(f"max_pair_leak_per_n={res['max_pair_leak']:.12g}")
    print(f"triple_total={res['triple_total']}  |triple_total|={abs(res['triple_total']):.12g}")
    print(f"max_triple_leak_per_n={res['max_triple_leak']:.12g}")
    print(f"prime_total={res['prime_total']}  |prime_total|={abs(res['prime_total']):.12g}")
    print(f"combined={res['combined']}  |combined|={abs(res['combined']):.12g}")
    print(f"zeta3={float(res['zeta3'].real):.15g}")
    print(f"|combined-zeta3|={res['err_vs_zeta3']:.12g}")
    if args.report_euler_product:
        e = euler_product_diagnostics(
            args.N,
            s=args.s,
            phase_scale=args.phase_scale,
            prime_weight=args.prime_weight,
        )
        print("--- twisted Euler-prime-product diagnostics ---")
        print(f"prime_terms={e['prime_terms']}")
        print(f"prime_sum={e['prime_sum']}  |prime_sum|={abs(e['prime_sum']):.12g}")
        print(f"exp(prime_sum)={e['exp_prime_sum']}  |exp(prime_sum)|={abs(e['exp_prime_sum']):.12g}")
        print(f"euler_product={e['euler_product']}  |euler_product|={abs(e['euler_product']):.12g}")
        print(
            "|euler_product - exp(prime_sum)|="
            f"{abs(e['product_minus_exp_sum']):.12g}"
        )
        print(
            "|euler_product - zeta3|="
            f"{abs(e['product_minus_zeta3']):.12g}"
        )
        print(f"min |1 - z_p| over primes={e['min_product_denom_abs']:.12g}")


if __name__ == "__main__":
    main()

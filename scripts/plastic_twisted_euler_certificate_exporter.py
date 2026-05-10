#!/usr/bin/env python3
"""
Plastic Twisted Euler Character — finite-N certificate exporter.

This version aligns with the antisymmetric arity-cancellation model used in:
  scripts/plastic_arity_twiddle_cancellation.py

Outputs a JSON certificate for five steps:
1) multiplicative twiddle character witness (exact by construction),
2) mirror cancellation witness on paired arities,
3) surviving prime Dirichlet residue (finite partial),
4) twisted Euler product/log consistency diagnostics,
5) distance-to-zeta target snapshot.

Default phase law is **linear in the index**, matching Lean `plasticSpiralPhaseAtStep`
(`spiralPlasticAngle * m`). An optional `--phase-law power` mode is explicitly labeled
experimental (not present in Lean).
"""

from __future__ import annotations

import argparse
import cmath
import json
import math
from dataclasses import asdict, dataclass
from typing import Any

import mpmath as mp


RHO = 1.3247179572447458
# Matches `spiralPlasticAngle` in `Hqiv.Story.PlasticSpiralInterceptCoverage`.
PLASTIC_ANGLE = 2.0 * math.pi / RHO


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


def prime_factorization(n: int) -> dict[int, int]:
    out: dict[int, int] = {}
    x = n
    d = 2
    while d * d <= x:
        while x % d == 0:
            out[d] = out.get(d, 0) + 1
            x //= d
        d = 3 if d == 2 else d + 2
    if x > 1:
        out[x] = out.get(x, 0) + 1
    return out


def plastic_theta_linear(n: int) -> float:
    """Lean `plasticSpiralPhaseAtStep n` (as ℝ): `spiralPlasticAngle * n`."""
    return PLASTIC_ANGLE * float(n)


def plastic_theta_power(n: int, exponent: float) -> float:
    """Experimental: `spiralPlasticAngle * n^exponent` (not in Lean)."""
    return PLASTIC_ANGLE * (float(n) ** exponent)


def chi_prime(p: int, *, phase_law: str, power_exponent: float) -> complex:
    if phase_law == "linear":
        return cmath.exp(1j * plastic_theta_linear(p))
    if phase_law == "power":
        return cmath.exp(1j * plastic_theta_power(p, power_exponent))
    raise ValueError(f"unknown phase_law {phase_law!r}")


def chi_multiplicative(n: int, *, phase_law: str, power_exponent: float) -> complex:
    """
    Completely multiplicative extension from prime phases:
      χ(n) = Π_{p^e || n} χ(p)^e
    """
    if n == 1:
        return 1 + 0j
    fac = prime_factorization(n)
    out = 1 + 0j
    for p, e in fac.items():
        out *= chi_prime(p, phase_law=phase_law, power_exponent=power_exponent) ** e
    return out


def unordered_factor_pairs(n: int) -> list[tuple[int, int]]:
    out: list[tuple[int, int]] = []
    for a in range(2, int(math.isqrt(n)) + 1):
        if n % a == 0:
            b = n // a
            if b >= 2:
                out.append((a, b))
    return out


def pair_term_from_chi(a: int, b: int, n: int, s: float, *, phase_law: str, power_exponent: float) -> complex:
    """
    Antisymmetric arity pairing built from the *same* χ as Step 1:
      T(a,b) ∝ (χ(a) χ(b)⁻¹ - χ(b) χ(a)⁻¹) = 2i Im(χ(a) χ(b)⁻¹)
    so T(b,a) = -T(a,b) by construction.
    """
    amp = 1.0 / (float(n) ** s) / float(a + b)
    ca = chi_multiplicative(a, phase_law=phase_law, power_exponent=power_exponent)
    cb = chi_multiplicative(b, phase_law=phase_law, power_exponent=power_exponent)
    return amp * (ca / cb - cb / ca) / 2.0


@dataclass
class Certificate:
    N: int
    s: float
    phase_law: str
    power_exponent: float | None
    step1_multiplicative_character: dict[str, Any]
    step2_mirror_cancellation: dict[str, Any]
    step3_prime_dirichlet_residue: dict[str, Any]
    step4_euler_log_identity: dict[str, Any]
    step5_closed_form_target: dict[str, Any]


def generate_certificate(N: int, s: float, *, phase_law: str, power_exponent: float) -> Certificate:
    primes = primes_upto(N)
    exp_note = power_exponent if phase_law == "power" else None

    # Step 1: exact multiplicativity witness
    mul_checks = []
    max_mul_defect = 0.0
    for m in range(2, min(N, 30)):
        for n in range(2, min(N, 30)):
            lhs = chi_multiplicative(m * n, phase_law=phase_law, power_exponent=power_exponent)
            rhs = (
                chi_multiplicative(m, phase_law=phase_law, power_exponent=power_exponent)
                * chi_multiplicative(n, phase_law=phase_law, power_exponent=power_exponent)
            )
            defect = abs(lhs - rhs)
            max_mul_defect = max(max_mul_defect, defect)
            if len(mul_checks) < 8:
                mul_checks.append({"m": m, "n": n, "defect": defect})
    step1 = {
        "description": (
            "Completely multiplicative character from prime phases; "
            "`linear` matches Lean `plasticSpiralPhaseAtStep` (angle ∝ index)."
        ),
        "phase_law": phase_law,
        "power_exponent": exp_note,
        "prime_values_sample": {
            str(p): str(chi_prime(p, phase_law=phase_law, power_exponent=power_exponent)) for p in primes[:10]
        },
        "max_multiplicativity_defect_small_grid": max_mul_defect,
        "checks_sample": mul_checks,
    }

    # Step 2: antisymmetric mirror cancellation witness
    sample_rows = []
    max_pair_leak = 0.0
    for n in range(4, min(N, 100) + 1):
        pairs = unordered_factor_pairs(n)
        if not pairs:
            continue
        for a, b in pairs[:3]:
            t_ab = pair_term_from_chi(a, b, n, s, phase_law=phase_law, power_exponent=power_exponent)
            t_ba = pair_term_from_chi(b, a, n, s, phase_law=phase_law, power_exponent=power_exponent)
            leak = abs(t_ab + t_ba)
            max_pair_leak = max(max_pair_leak, leak)
            if len(sample_rows) < 10:
                sample_rows.append(
                    {
                        "n": n,
                        "a": a,
                        "b": b,
                        "T(a,b)": str(t_ab),
                        "T(b,a)": str(t_ba),
                        "pair_sum_abs": leak,
                    }
                )
    step2 = {
        "description": "Antisymmetry T(a,b)+T(b,a)=0 with T built from χ(a)/χ(b)-χ(b)/χ(a) (same χ as Step 1)",
        "max_pair_sum_abs": max_pair_leak,
        "sampled_pairs": sample_rows,
    }

    # Step 3: surviving prime channel partial
    prime_terms = [
        chi_prime(p, phase_law=phase_law, power_exponent=power_exponent) / (float(p) ** s) for p in primes
    ]
    prime_sum = sum(prime_terms, 0j)
    step3 = {
        "description": "Finite prime Dirichlet residue Σ_{p<=N} χ(p)/p^s",
        "prime_count": len(primes),
        "value": str(prime_sum),
    }

    # Step 4: twisted Euler product + log consistency
    prod = 1 + 0j
    log_sum = 0 + 0j
    min_denom_abs = float("inf")
    for p in primes:
        z = chi_prime(p, phase_law=phase_law, power_exponent=power_exponent) / (float(p) ** s)
        denom = 1 - z
        min_denom_abs = min(min_denom_abs, abs(denom))
        prod *= 1.0 / denom
        log_sum += -cmath.log(denom)
    step4 = {
        "description": "P_N = Π_{p<=N}(1-χ(p)/p^s)^(-1), principal log consistency",
        "P_N": str(prod),
        "log_P_N": str(log_sum),
        "exp_log_consistency_abs": abs(prod - cmath.exp(log_sum)),
        "exp_prime_sum_abs": abs(prod - cmath.exp(prime_sum)),
        "min_denom_abs": min_denom_abs,
    }

    # Step 5: zeta target proximity snapshot
    z3 = complex(float(mp.zeta(3)), 0.0)
    contraction = 1.0 / (RHO**3)
    heuristic_bound = contraction ** max(1.0, s - 1.0)
    step5 = {
        "description": "Finite-N target check against ζ(3)",
        "zeta3": float(z3.real),
        "distance_abs": abs(prod - z3),
        "product_minus_zeta3": str(prod - z3),
        "heuristic_contraction_bound": heuristic_bound,
    }

    return Certificate(
        N=N,
        s=s,
        phase_law=phase_law,
        power_exponent=exp_note,
        step1_multiplicative_character=step1,
        step2_mirror_cancellation=step2,
        step3_prime_dirichlet_residue=step3,
        step4_euler_log_identity=step4,
        step5_closed_form_target=step5,
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--N", type=int, default=300)
    parser.add_argument("--s", type=float, default=3.0)
    parser.add_argument(
        "--phase-law",
        choices=["linear", "power"],
        default="linear",
        help="`linear` matches Lean plastic spiral phase; `power` is an experimental deformation",
    )
    parser.add_argument(
        "--power-exponent",
        type=float,
        default=1.0,
        help="only used when --phase-law=power (sets angle ∝ n^exponent after the plastic prefactor)",
    )
    parser.add_argument("--output", type=str, default="plastic_euler_certificate.json")
    args = parser.parse_args()

    if args.N < 5:
        raise SystemExit("N must be >= 5")
    if args.s <= 1.0:
        raise SystemExit("Use s > 1")

    pow_exp = args.power_exponent if args.phase_law == "power" else 1.0
    cert = generate_certificate(args.N, args.s, phase_law=args.phase_law, power_exponent=pow_exp)
    with open(args.output, "w", encoding="utf-8") as f:
        json.dump(asdict(cert), f, indent=2)

    print(f"Certificate written to {args.output}")
    print(f"Step2 max pair leak: {cert.step2_mirror_cancellation['max_pair_sum_abs']:.3e}")
    print(f"Step5 distance to zeta(3): {cert.step5_closed_form_target['distance_abs']:.6f}")


if __name__ == "__main__":
    main()


#!/usr/bin/env python3
"""
Numerical exploration for the Lean `default3DCoeff` + `constantTerm` story
(`Hqiv.Story.PlasticSpiralInterceptCoverage`).

Computes
  S(M) = constantTerm + mult * Σ_{m=0}^{M-1} default3DCoeff(m) / ρ^{3m}
         * exp(2π i · plasticSpiralPhaseAtStep(m))
optionally rotated in ℂ by `post_phase` (radians), and reports |S(M) - ζ(3)|.

Use `--sweep` to try built-in constantTerm candidates and a small grid of
`mult` / `post_phase` (search is crude but fast).
"""

from __future__ import annotations

import argparse
import cmath
import math
from typing import Callable

import mpmath as mp


SPIRAL_PLASTIC_NUMBER = 1.3247179572447458


def plastic_spiral_phase_at_step(m: int) -> float:
    return (2.0 * math.pi / SPIRAL_PLASTIC_NUMBER) * float(m)


def lattice_digits(m: int) -> tuple[int, int, int]:
    return (m % 10, (m // 10) % 10, m // 100)


def lattice_near_diagonal(m: int) -> bool:
    j, k, l_ = lattice_digits(m)
    pts = (j, k, l_)
    for i in range(3):
        for j2 in range(3):
            if i != j2 and abs(pts[i] - pts[j2]) <= 1:
                return True
    return False


def default_coeff(m: int, prime_cross: Callable[[int, int], bool]) -> float:
    base = 1.0 / float(m + 1) ** 3
    boost = 1.5 if lattice_near_diagonal(m) else 1.0
    j, k, _ = lattice_digits(m)
    prime_bonus = 2.0 if prime_cross(j, k) else 1.0
    return base * boost * prime_bonus


def plastic_phase_factor(m: int) -> complex:
    """Lean `plasticPhaseFactor m` = `exp(2π i · plasticSpiralPhaseAtStep m)`."""
    ang = plastic_spiral_phase_at_step(m)
    return cmath.exp(2j * math.pi * ang)


def partial_sum(M: int, prime_cross: Callable[[int, int], bool]) -> complex:
    rho = SPIRAL_PLASTIC_NUMBER
    s = 0j
    for m in range(M):
        term = default_coeff(m, prime_cross) / (rho ** (3 * m)) * plastic_phase_factor(m)
        s += term
    return s


def constant_from_name(name: str) -> complex:
    """Built-in real `constantTerm` candidates (extend as needed)."""
    rho = SPIRAL_PLASTIC_NUMBER
    pi = math.pi
    if name in ("none", "0"):
        return 0j
    if name == "pi3_32":
        return complex(pi**3 / 32.0, 0.0)
    if name == "rho3":
        return complex(rho**3, 0.0)
    if name == "inv_rho_minus_one":
        return complex(1.0 / (rho - 1.0), 0.0)
    if name == "pi3_32_plus_inv_rho_minus_one":
        return complex(pi**3 / 32.0 + 1.0 / (rho - 1.0), 0.0)
    if name == "pi3_32_plus_rho3":
        return complex(pi**3 / 32.0 + rho**3, 0.0)
    raise ValueError(f"unknown constant preset {name!r}")


def combined_value(
    partial: complex,
    *,
    constant: complex,
    mult: float,
    post_phase: float,
) -> complex:
    raw = constant + mult * partial
    return raw * cmath.exp(1j * post_phase)


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("-M", type=int, default=200, help="number of terms m = 0 .. M-1")
    p.add_argument(
        "--prime-mod",
        type=int,
        default=0,
        help="if >0, prime_cross(j,k) when (j*k) %% prime_mod == 1 (toy predicate)",
    )
    p.add_argument(
        "--constant",
        default="none",
        help="constantTerm preset: none, pi3_32, rho3, inv_rho_minus_one, "
        "pi3_32_plus_inv_rho_minus_one, pi3_32_plus_rho3",
    )
    p.add_argument("--mult", type=float, default=1.0, help="real multiplier on the tail partial sum")
    p.add_argument(
        "--post-phase",
        type=float,
        default=0.0,
        help="multiply (constant + mult*partial) by exp(i * post_phase), radians",
    )
    p.add_argument(
        "--sweep",
        action="store_true",
        help="print a small grid over constants / mult / post_phase (ignores single-run args except -M, --prime-mod)",
    )
    p.add_argument(
        "--sweep-top",
        type=int,
        default=8,
        help="with --sweep, also print this many best (constant, mult, phase) rows",
    )
    args = p.parse_args()

    if args.M < 1:
        raise SystemExit("M must be >= 1")

    def prime_cross(j: int, k: int) -> bool:
        if args.prime_mod <= 0:
            return False
        return (j * k) % args.prime_mod == 1

    z3 = complex(float(mp.zeta(3)), 0.0)
    partial = partial_sum(args.M, prime_cross)

    if args.sweep:
        constants = [
            "none",
            "pi3_32",
            "rho3",
            "inv_rho_minus_one",
            "pi3_32_plus_inv_rho_minus_one",
            "pi3_32_plus_rho3",
        ]
        mults = [0.5, 0.75, 1.0, 1.25, 1.5, 2.0]
        phases = [0.0, 0.02, -0.02, 0.05, -0.05, 0.1, -0.1]
        rows: list[tuple[float, str, float, float, complex]] = []
        for cname in constants:
            c0 = constant_from_name(cname)
            for mlt in mults:
                for ph in phases:
                    v = combined_value(partial, constant=c0, mult=mlt, post_phase=ph)
                    err = abs(v - z3)
                    rows.append((err, cname, mlt, ph, v))
        rows.sort(key=lambda t: t[0])
        print(f"M={args.M}  |partial|={abs(partial):.12g}")
        print(f"ζ(3)={float(z3.real):.15g}")
        print("sweep: best |combined - ζ(3)|")
        err, cname, mlt, ph, v = rows[0]
        print(f"  best constant={cname} mult={mlt} post_phase={ph}")
        print(f"  combined={v}  err={err:.12g}")
        k = max(0, args.sweep_top)
        if k > 1:
            print(f"top-{min(k, len(rows))} (err, constant, mult, post_phase, Re(combined), Im(combined)):")
            for row in rows[:k]:
                e, cn, ml, ph2, vv = row
                print(f"  {e:.12g}  {cn}  {ml}  {ph2}  {vv.real:.12g}  {vv.imag:.12g}")
        return

    c0 = constant_from_name(args.constant)
    v = combined_value(partial, constant=c0, mult=args.mult, post_phase=args.post_phase)
    err = abs(v - z3)
    print(f"M={args.M}  partial={partial}  |partial|={abs(partial):.12g}")
    print(f"constant={args.constant} -> C={c0}")
    print(f"mult={args.mult} post_phase={args.post_phase}")
    print(f"combined={v}  |combined|={abs(v):.12g}")
    print(f"ζ(3)={float(z3.real):.15g}")
    print(f"|combined - ζ(3)|={err:.12g}")


if __name__ == "__main__":
    main()

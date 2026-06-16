#!/usr/bin/env python3
"""Probe the Hopf j–k unit-circle zero readout on the critical line.

Lean chart (S3HopfJKUnitCircleZeroReadout.lean):
  (j, k) = (cos t, sin t) on S¹
  phase = exp(i * π * j * k)
  amplitude = (j + k) / √2
  ζ(½+it) = 0  ⟺  amplitude = 0  ⟺  j + k = 0   (conditional on rolling bridge)

Unconditional geometry: balance when cos(t) + sin(t) = 0 (t ≡ 3π/4 mod 2π).
"""

from __future__ import annotations

import argparse
import math

import mpmath as mp


def hopf_jk_point(t: mp.mpf) -> tuple[mp.mpf, mp.mpf]:
    return mp.cos(t), mp.sin(t)


def hopf_jk_product(t: mp.mpf) -> mp.mpf:
    j, k = hopf_jk_point(t)
    return j * k


def hopf_jk_phase(t: mp.mpf) -> mp.mpc:
    return mp.e ** (mp.j * mp.pi * hopf_jk_product(t))


def hopf_jk_amplitude(t: mp.mpf) -> mp.mpf:
    j, k = hopf_jk_point(t)
    return (j + k) / mp.sqrt(2)


def hopf_jk_twiddle(t: mp.mpf) -> mp.mpc:
    return hopf_jk_phase(t) * hopf_jk_amplitude(t)


def is_balance(t: mp.mpf, tol: float = 1e-12) -> bool:
    j, k = hopf_jk_point(t)
    return abs(j + k) < tol


def probe(t: float, zeta_tol: float = 1e-4) -> None:
    t = mp.mpf(t)
    j, k = hopf_jk_point(t)
    s = mp.mpc("0.5", t)
    z = mp.zeta(s)
    print(f"t = {t}")
    print(f"  (j, k) = ({j}, {k})   j²+k² = {float(j*j + k*k):.6g}")
    print(f"  j·k = {hopf_jk_product(t)}")
    print(f"  phase exp(iπjk) = {hopf_jk_phase(t)}")
    print(f"  amplitude (j+k)/√2 = {hopf_jk_amplitude(t)}")
    print(f"  twiddle = phase × amplitude = {hopf_jk_twiddle(t)}")
    print(f"  ζ(½+it) = {z}   |ζ| = {float(abs(z)):.6g}")
    print(f"  balance (j+k=0): {is_balance(t)}")
    print(f"  near ζ-zero (tol={zeta_tol}): {abs(z) < zeta_tol}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--t", type=float, default=3 * math.pi / 4,
                        help="cover height t (default 3π/4 balance point)")
    parser.add_argument("--scan-balance", action="store_true",
                        help="show balance locus samples")
    parser.add_argument("--prec", type=int, default=50)
    args = parser.parse_args()
    mp.dps = args.prec

    if args.scan_balance:
        for m in range(-2, 3):
            t = 3 * mp.pi / 4 + m * 2 * mp.pi
            print(f"t = {t}: balance={is_balance(t)} amp={hopf_jk_amplitude(t)}")
        return

    probe(args.t)


if __name__ == "__main__":
    main()

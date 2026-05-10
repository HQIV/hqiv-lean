#!/usr/bin/env python3
"""
Plastic -> zeta phase probe (empirical).

Pipeline:
1) Run plastic root-scale snaps (from scripts/plastic_spiral_v3.py)
2) Keep prime snaps (p, step m, arity k)
3) Map each snap to an effective height t_eff via rapidity scaling
4) Evaluate arg(zeta(1/2 + i t_eff)) and |zeta(1/2 + i t_eff)|
5) Compare t_eff set to first known nontrivial zeros of zeta
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

import mpmath as mp

# local imports (same folder)
import plastic_spiral_v3 as psv3
from factor_from_curvature import delta_theta_prime_float, rapidity_phase_from_omega


FIRST_ZETA_ZEROS = [
    14.134725141734693790457251983562,
    21.022039638771554992628479593896,
    25.010857580145688763213790992562,
    30.424876125859513210311897530584,
    32.935061587739189690662368964074,
    37.586178158825671257217763480705,
    40.918719012147495187398126914633,
    43.327073280914999519496122165406,
    48.005150881167159727942472749427,
    49.773832477672302181916784678563,
]


@dataclass(frozen=True)
class PhaseProbePoint:
    n: int
    k: int
    step: int
    prime: int
    score: float
    t_eff: float
    zeta_abs: float
    zeta_arg: float


def effective_height_from_step(
    step: int,
    *,
    k: int,
    prime: int,
    phi: float,
    t_param: float,
    omega_k: float,
    t_scale: float,
) -> float:
    # Reuse existing rapidity scaling channel in repo:
    # t_eff := t_scale * (phi*t*omega) * delta_theta_prime(step)
    phase = rapidity_phase_from_omega(phi, t_param, omega_k)
    base = phase * delta_theta_prime_float(float(step))
    # Distinguish snap channels by arity + prime weight.
    # This keeps rapidity scaling central while avoiding degenerate identical t_eff.
    weight = 1.0 + (math.log(max(3, prime)) / float(max(2, k)))
    return float(t_scale * base * weight)


def iter_prime_snaps(ns: Iterable[int]) -> Iterable[tuple[int, psv3.SnapHit]]:
    for n in ns:
        hits_by_k = psv3.plastic_spiral_snap(n)
        for k, hits in hits_by_k.items():
            for h in hits:
                if h.divisor > 2 and psv3.is_probable_prime(h.divisor):
                    yield n, h


def nearest_zero_distance(t_eff: float) -> tuple[float, float]:
    nearest = min(FIRST_ZETA_ZEROS, key=lambda z: abs(t_eff - z))
    return abs(t_eff - nearest), nearest


def run_probe(
    ns: list[int],
    *,
    phi: float,
    t_param: float,
    omega_k: float,
    t_scale: float,
    max_points: int,
    mp_dps: int,
) -> list[PhaseProbePoint]:
    mp.mp.dps = mp_dps
    points: list[PhaseProbePoint] = []
    seen: set[tuple[int, int, int]] = set()  # (prime, k, step)

    for n, h in iter_prime_snaps(ns):
        key = (h.divisor, h.k, h.step)
        if key in seen:
            continue
        seen.add(key)

        t_eff = effective_height_from_step(
            h.step,
            k=h.k,
            prime=h.divisor,
            phi=phi,
            t_param=t_param,
            omega_k=omega_k,
            t_scale=t_scale,
        )
        if not math.isfinite(t_eff):
            continue
        t_eff = abs(t_eff)

        s = mp.mpf("0.5") + 1j * mp.mpf(t_eff)
        z = mp.zeta(s)
        z_abs = float(abs(z))
        z_arg = float(mp.arg(z))
        points.append(
            PhaseProbePoint(
                n=n,
                k=h.k,
                step=h.step,
                prime=h.divisor,
                score=h.score,
                t_eff=t_eff,
                zeta_abs=z_abs,
                zeta_arg=z_arg,
            )
        )

    # Best "zero-like" points first: low |zeta|, then near known zeros.
    points.sort(key=lambda p: (p.zeta_abs, nearest_zero_distance(p.t_eff)[0], p.score))
    return points[:max_points]


def main() -> None:
    parser = argparse.ArgumentParser(description="Plastic snap to zeta phase probe")
    parser.add_argument(
        "--n-list",
        default="221,945,10403,70747,97343",
        help="Comma-separated n values used for plastic prime snaps",
    )
    parser.add_argument("--phi", type=float, default=1.0)
    parser.add_argument("--t-param", type=float, default=1.0, help="Rapidity t parameter")
    parser.add_argument("--omega-k", type=float, default=1.0)
    parser.add_argument("--t-scale", type=float, default=10.0, help="Scale factor for t_eff")
    parser.add_argument("--max-points", type=int, default=25)
    parser.add_argument("--mp-dps", type=int, default=50)
    args = parser.parse_args()

    ns = [int(x.strip()) for x in args.n_list.split(",") if x.strip()]
    points = run_probe(
        ns,
        phi=args.phi,
        t_param=args.t_param,
        omega_k=args.omega_k,
        t_scale=args.t_scale,
        max_points=max(1, args.max_points),
        mp_dps=max(25, args.mp_dps),
    )

    print(f"n_list={ns}")
    print(f"points={len(points)}")
    print("idx | n | p | k | step | t_eff | |zeta| | arg(zeta) | nearest_zero | dist")
    print("-" * 108)
    for i, p in enumerate(points, start=1):
        dist, z0 = nearest_zero_distance(p.t_eff)
        print(
            f"{i:>3} | {p.n:>6} | {p.prime:>5} | {p.k:>2} | {p.step:>4} | "
            f"{p.t_eff:>8.4f} | {p.zeta_abs:>9.5g} | {p.zeta_arg:>10.5f} | "
            f"{z0:>11.5f} | {dist:>7.4f}"
        )


if __name__ == "__main__":
    main()

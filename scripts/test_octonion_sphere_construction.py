#!/usr/bin/env python3
"""
Numerical checks aligned with `Hqiv/Algebra/OctonionSphereConstruction.lean`.

Run: python3 scripts/test_octonion_sphere_construction.py
"""

from __future__ import annotations

import math


def continuous_ball_volume8(r: float) -> float:
    """V8(r) = pi^4/24 * r^8 (matches Lean `continuousBallVolume8`)."""
    return (math.pi**4 / 24.0) * (r**8)


def continuous_sphere_area7(r: float) -> float:
    """A7(r) = pi^4/3 * r^7 (matches Lean `continuousSphereArea7`)."""
    return (math.pi**4 / 3.0) * (r**7)


def deriv_volume_numeric(r: float, eps: float = 1e-6) -> float:
    """Finite-difference derivative of V8 at r (sanity vs closed form A7)."""
    return (continuous_ball_volume8(r + eps) - continuous_ball_volume8(r - eps)) / (2 * eps)


def main() -> None:
    m = 143
    r = math.sqrt(m)
    v8 = continuous_ball_volume8(r)
    a7 = continuous_sphere_area7(r)
    a7_fd = deriv_volume_numeric(r)

    # Example lattice vector (9,7,3,2,0,0,0,0) from four-squares padding
    vec = (9, 7, 3, 2, 0, 0, 0, 0)
    norm_sq = sum(x * x for x in vec)
    assert norm_sq == m

    phi = (1.0 + math.sqrt(5.0)) / 2.0
    phi2 = phi - 1.0
    phase1 = (2.0 * math.pi) * (v8 * phi % 1.0)
    phase2 = (2.0 * math.pi) * (v8 * phi2 % 1.0)

    tol = 1e-5
    assert abs(a7_fd - a7) < tol * max(1.0, abs(a7)), (a7_fd, a7)

    print("Octonion / R^8 sphere construction — numeric witnesses")
    print(f"  m = {m}, r = sqrt(m) = {r:.6f}")
    print(f"  V8(r) = pi^4/24 * r^8 = {v8:.6e}")
    print(f"  A7(r) = pi^4/3 * r^7 = {a7:.6e}")
    print(f"  finite-diff dV8/dr ≈ {a7_fd:.6e} (tol {tol})")
    print(f"  lattice vector {vec} has sum of squares = {norm_sq}")
    print(f"  double-unwrap phases (rad): phi1={phase1:.6f}, phi2={phase2:.6f}")
    print("OK")


if __name__ == "__main__":
    main()

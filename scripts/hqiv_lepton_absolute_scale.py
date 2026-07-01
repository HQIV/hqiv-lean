#!/usr/bin/env python3
"""Charged-lepton absolute scale: m_ℓ = massUnit · λ_min(n) = massUnit · (n+1)."""

from __future__ import annotations

GENERATIONS = (
    ("electron", 1),
    ("muon", 2),
    ("tau", 3),
)


def lepton_mass(mass_unit: float, winding: int) -> float:
    return mass_unit * (winding + 1)


def main() -> None:
    mass_unit = 5.0  # lock-in N = massUnit
    print("HQIV lepton absolute scale — massUnit · (n+1)\n")
    print(f"lock-in massUnit = {mass_unit}")
    masses = {}
    for name, n in GENERATIONS:
        m = lepton_mass(mass_unit, n)
        masses[name] = m
        print(f"  {name:8s}  n={n}  λ_min={n+1}  m = {m:.1f}")
    e, mu, tau = masses["electron"], masses["muon"], masses["tau"]
    assert abs(mu / e - 1.5) < 1e-12
    assert abs(tau / mu - 4 / 3) < 1e-12
    assert abs(tau / e - 2.0) < 1e-12
    print("\nratios μ/e=3/2, τ/μ=4/3, τ/e=2: OK")
    print("MeV labels: comparison layer only (not spine input)")


if __name__ == "__main__":
    main()

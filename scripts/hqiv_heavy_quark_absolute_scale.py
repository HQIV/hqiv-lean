#!/usr/bin/env python3
"""Heavy-quark constituent scale: m_q = massUnit · 9·λ_min(n)/4 = massUnit · 9·(n+1)/4."""

from __future__ import annotations

GENERATIONS = (
    ("first (u/d scale)", 1),
    ("second (c/s scale)", 2),
    ("third (t/b scale)", 3),
)

CASIMIR_RATIO = 9 / 4


def quark_mass(mass_unit: float, winding: int) -> float:
    return mass_unit * 9 * (winding + 1) / 4


def lepton_mass(mass_unit: float, winding: int) -> float:
    return mass_unit * (winding + 1)


def main() -> None:
    mass_unit = 5.0  # lock-in N = massUnit
    print("HQIV heavy-quark absolute scale — massUnit · 9·(n+1)/4\n")
    print(f"lock-in massUnit = {mass_unit}")
    masses = {}
    for name, n in GENERATIONS:
        m = quark_mass(mass_unit, n)
        masses[n] = m
        print(f"  {name:22s}  n={n}  λ_min={n+1}  m = {m:g}")
    m1, m2, m3 = masses[1], masses[2], masses[3]
    assert abs(m2 / m1 - 1.5) < 1e-12
    assert abs(m3 / m2 - 4 / 3) < 1e-12
    print("\nwithin-quark ratios gen2/gen1=3/2, gen3/gen2=4/3: OK")
    for n in (1, 2, 3):
        ratio = quark_mass(mass_unit, n) / lepton_mass(mass_unit, n)
        assert abs(ratio - CASIMIR_RATIO) < 1e-12
    print(f"cross-sector quark/lepton at matched n = {CASIMIR_RATIO} (= C_A/C_F): OK")
    assert abs(m1 - 45 / 2) < 1e-12
    assert abs(m2 - 135 / 4) < 1e-12
    assert abs(m3 - 45) < 1e-12
    print("lock-in (45/2, 135/4, 45): OK")
    print("MeV labels: comparison layer only (not spine input)")


if __name__ == "__main__":
    main()

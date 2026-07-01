#!/usr/bin/env python3
"""TUFT chart diamond: t = λ_min, N = λ_min + 1 on balanced chart rows; lock-in readout."""

from __future__ import annotations

WINDINGS = (1, 2, 3)


def chart_shell(n: int) -> int:
    return n + 1


def beltrami_min(n: int) -> float:
    return float(n + 1)


def mass_unit_at_chart(phi: float, phi_pot: float, n: int) -> float:
    """N = 1 + Φ + φ·t with t = chart shell m."""
    m = chart_shell(n)
    return 1 + phi_pot + phi * m


def lockin_readout(mass_unit_lock: float, n: int) -> float:
    return mass_unit_lock * beltrami_min(n)


def main() -> None:
    print("HQIV TUFT Beltrami mass functional\n")
    print("balanced chart rows (φ=1, Φ=0):")
    for n in WINDINGS:
        lam = beltrami_min(n)
        n_lapse = mass_unit_at_chart(1.0, 0.0, n)
        print(f"  winding n={n}  m={chart_shell(n)}  λ_min={lam:g}  N={n_lapse:g}  (N=λ_min+1)")
        assert abs(n_lapse - (lam + 1)) < 1e-12
    print("N = λ_min + 1 on chart rows: OK")

    mass_unit = 5.0
    print(f"\nlock-in readout massUnit={mass_unit}")
    for n in WINDINGS:
        m = lockin_readout(mass_unit, n)
        print(f"  n={n}  m = massUnit·λ_min = {m:g}")
    assert lockin_readout(5, 1) == 10
    assert lockin_readout(5, 2) == 15
    assert lockin_readout(5, 3) == 20
    print("lock-in (10, 15, 20): OK")


if __name__ == "__main__":
    main()

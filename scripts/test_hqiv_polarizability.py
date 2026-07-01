#!/usr/bin/env python3
"""Tests: atomic polarizability from the binding-well field response (α = q²/k)."""

from __future__ import annotations

import unittest

import hqiv_polarizability as pol


class FloorRelationTests(unittest.TestCase):
    def test_polarizability_is_soft_factor_times_floor(self) -> None:
        for z in range(1, 19):
            self.assertAlmostEqual(
                pol.polarizability_angstrom3(z),
                pol.SOFT_COULOMB_ENHANCEMENT * pol.polarizability_floor_angstrom3(z),
                places=9,
            )

    def test_hydrogen_floor_is_one_bohr3(self) -> None:
        # H: n=1, z_eff=1, N_val=1 -> floor = 1 a0^3 exactly
        self.assertAlmostEqual(pol.polarizability_floor_bohr3(1), 1.0, places=9)

    def test_hydrogen_matches_exact_4p5_bohr3(self) -> None:
        # soft-well H polarizability = 9/2 a0^3 = 0.667 A^3 (the exact value)
        self.assertAlmostEqual(pol.polarizability_angstrom3(1), 0.667, places=2)


class PeriodicTrendTests(unittest.TestCase):
    def setUp(self) -> None:
        self.a = {r.symbol: r.polarizability_a3 for r in pol.panel_readout()}

    def test_noble_gases_increase_down_group(self) -> None:
        self.assertLess(self.a["He"], self.a["Ne"])
        self.assertLess(self.a["Ne"], self.a["Ar"])

    def test_alkali_far_exceeds_noble_gas(self) -> None:
        self.assertGreater(self.a["Li"], 5.0 * self.a["Ne"])
        self.assertGreater(self.a["Na"], 5.0 * self.a["Ar"])

    def test_monotone_decrease_across_period3(self) -> None:
        period3 = ["Na", "Mg", "Al", "Si", "P", "S", "Cl", "Ar"]
        vals = [self.a[s] for s in period3]
        for lo, hi in zip(vals[1:], vals[:-1]):
            self.assertLess(lo, hi)


class AccuracyTests(unittest.TestCase):
    def test_light_atoms_within_factor_two(self) -> None:
        for r in pol.panel_readout():
            ratio = r.experiment_a3 / r.polarizability_a3
            self.assertGreater(ratio, 0.5, f"{r.symbol} too high")
            self.assertLess(ratio, 2.0, f"{r.symbol} too low")


if __name__ == "__main__":
    unittest.main()

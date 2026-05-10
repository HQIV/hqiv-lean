"""Tests for `bonded_horizon_casimir_float` (mirror of `BondedHorizonCasimir.lean`)."""

from __future__ import annotations

import unittest


class TestBondedHorizonCasimirFloat(unittest.TestCase):
    def test_h2_surplus_consistent(self) -> None:
        from bonded_horizon_casimir_float import (
            bond_horizon_surplus_dimless,
            covalent_dimer_two_electron_surplus_dimless,
        )
        from nuclear_torus_casimir_float import perturbed_casimir_energy

        a = bond_horizon_surplus_dimless(2, 1, 1)
        b = covalent_dimer_two_electron_surplus_dimless()
        self.assertAlmostEqual(a, b, places=10)
        self.assertAlmostEqual(
            a,
            perturbed_casimir_energy(2) - 2 * perturbed_casimir_energy(1),
            places=10,
        )

    def test_ionic_equals_bond_with_sum(self) -> None:
        from bonded_horizon_casimir_float import bond_horizon_surplus_dimless, ionic_bond_surplus_dimless

        self.assertAlmostEqual(ionic_bond_surplus_dimless(3, 5), bond_horizon_surplus_dimless(8, 3, 5), places=10)


if __name__ == "__main__":
    unittest.main()

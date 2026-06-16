#!/usr/bin/env python3
"""Tests for aqueous electrolyte on ionic-bond spine."""

import unittest

import hqiv_electrolyte_solution as els
import hqiv_ionic_bond_network as ibn


class TestElectrolyteSolution(unittest.TestCase):
    def test_pure_water_limit(self) -> None:
        out = els.salt_water_response_readout(salinity_g_per_kg=0.0)
        self.assertAlmostEqual(out["density_g_cm3"], 1.0, places=3)
        self.assertEqual(out["ionic_conductivity_S_m"], 0.0)

    def test_seawater_density_order_of_magnitude(self) -> None:
        out = els.salt_water_response_readout(salinity_g_per_kg=35.0)
        self.assertGreater(out["density_g_cm3"], 1.02)
        self.assertLess(out["density_g_cm3"], 1.05)

    def test_includes_ionic_lattice_witness(self) -> None:
        out = els.salt_water_response_readout()
        self.assertIn("ionic_lattice_witness", out)
        self.assertEqual(out["ionic_lattice_witness"]["salt"], "NaCl")

    def test_conductivity_order_of_magnitude_at_35psu(self) -> None:
        out = els.salt_water_response_readout(salinity_g_per_kg=35.0)
        self.assertGreater(out["ionic_conductivity_S_m"], 1.0e-4)
        self.assertLess(out["ionic_conductivity_S_m"], 5.0)

    def test_freezing_depression_positive(self) -> None:
        out = els.salt_water_response_readout(salinity_g_per_kg=35.0)
        self.assertGreater(out["freezing_point_depression_K"], 0.5)
        self.assertLess(out["freezing_point_depression_K"], 5.0)


if __name__ == "__main__":
    unittest.main()

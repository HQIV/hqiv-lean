#!/usr/bin/env python3
"""Tests for salt melting point + refractive index on ionic-bond spine."""

import unittest

import hqiv_salt_phase_response as spr
import hqiv_ionic_bond_network as ibn


class TestSaltPhaseResponse(unittest.TestCase):
    def test_nacl_melt_order_of_magnitude(self) -> None:
        out = spr.salt_phase_response_readout(ibn.NACL_SALT)
        self.assertGreater(out["T_melt_K"], 800.0)
        self.assertLess(out["T_melt_K"], 1500.0)

    def test_nacl_refractive_index_order_of_magnitude(self) -> None:
        out = spr.salt_phase_response_readout(ibn.NACL_SALT)
        self.assertGreater(out["refractive_index_solid"], 1.3)
        self.assertLess(out["refractive_index_solid"], 1.8)

    def test_nacl_density_order_of_magnitude(self) -> None:
        out = spr.salt_phase_response_readout(ibn.NACL_SALT)
        self.assertGreater(out["density_g_cm3"], 2.0)
        self.assertLess(out["density_g_cm3"], 2.4)

    def test_ionic_lattice_witness_present(self) -> None:
        out = spr.salt_phase_response_readout(ibn.NACL_SALT)
        self.assertIn("ionic_lattice_witness", out)
        self.assertEqual(out["ionic_lattice_witness"]["salt"], "NaCl")

    def test_solid_at_low_temperature(self) -> None:
        out = spr.salt_phase_response_readout(ibn.NACL_SALT, temperature_k=300.0)
        self.assertIn(out["phase_at_T_P"], ("solid", "molecular_cluster"))

    def test_nacl_crystalline_rho_not_saturated(self) -> None:
        out = spr.salt_phase_response_readout(ibn.NACL_SALT)
        rho_c = out["crystalline_curvature_density_fraction"]
        self.assertIsNotNone(rho_c)
        self.assertLess(float(rho_c), 0.95)
        self.assertGreater(float(rho_c), 0.55)


if __name__ == "__main__":
    unittest.main()

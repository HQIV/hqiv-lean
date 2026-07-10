"""Tests for fracture-scale crystal witnesses."""

from __future__ import annotations

import unittest

import hqiv_crystal_fracture_witness as cfw
import hqiv_ionic_bond_network as ibn
import hqiv_metallic_bond_network as mbn


class TestCrystalFractureWitness(unittest.TestCase):
    def test_fracture_rows_use_scale_proxy_names(self) -> None:
        row = cfw.ionic_fracture_row(ibn.NACL_SALT)
        self.assertIn("K_scale_candidate_Pa_sqrt_m", row)
        self.assertNotIn("K_IC_candidate_Pa_sqrt_m", row)
        self.assertTrue(row["interpretation"].endswith("no handbook K_IC input"))

    def test_ionic_more_cleavage_localized_than_copper(self) -> None:
        nacl = cfw.ionic_fracture_row(ibn.NACL_SALT)
        cu = cfw.metallic_fracture_row(mbn.CU_LATTICE)
        self.assertGreater(nacl["cleavage_localization_index"], 0.0)
        self.assertGreaterEqual(cu["ductile_carrier_score"], 0.0)
        self.assertGreater(nacl["cleavage_localization_index"], cu["cleavage_localization_index"])

    def test_acoustic_velocity_proxy_positive_for_witnesses(self) -> None:
        for row in (
            cfw.ionic_fracture_row(ibn.NACL_SALT),
            cfw.metallic_fracture_row(mbn.CU_LATTICE),
        ):
            self.assertGreater(row["sound_speed_proxy_m_s"], 0.0)

    def test_piezo_stiffness_zero_stress_recovers_thermal(self) -> None:
        out = cfw.piezo_stiffness_equilibrium_strain(
            2.5, 1.0, 6.0, 0.0, thermal_strain=0.1
        )
        self.assertTrue(out["converged"])
        self.assertAlmostEqual(out["equilibrium_strain"], 0.1, places=9)
        self.assertAlmostEqual(out["contact_length_angstrom"], 2.5 * 1.1, places=9)

    def test_piezo_stiffness_external_stress_raises_strain(self) -> None:
        base = cfw.piezo_stiffness_equilibrium_strain(2.5, 1.0, 6.0, 0.0)
        stressed = cfw.piezo_stiffness_equilibrium_strain(
            2.5, 1.0, 6.0, 1.0e9, thermal_strain=0.0
        )
        self.assertGreater(stressed["equilibrium_strain"], base["equilibrium_strain"])
        self.assertLess(stressed["stiffness_ratio"], 1.0)


if __name__ == "__main__":
    unittest.main()

#!/usr/bin/env python3
"""Crystalline ρ_curv: network-derived melt ratios (not fixed constants)."""

import unittest

import hqiv_ionic_bond_network as ibn
import hqiv_phase_geometry_density as pgd
import hqiv_salt_phase_response as spr


class TestCrystallineCurvatureDensity(unittest.TestCase):
    def test_ice_and_curvature_fraction_agree(self) -> None:
        cell = pgd.phase_unit_cell("H2O", "Ih")
        rho = pgd.density_g_cm3(cell)
        self.assertAlmostEqual(
            pgd.curvature_density_fraction(rho, "H2O"),
            pgd.crystalline_curvature_density_fraction(
                rho, motif="tetrahedral_hbond", n_coord=4, molecule="H2O"
            ),
            places=6,
        )

    def test_ice_ratio_from_neighbor_overlap(self) -> None:
        from hqiv_lab.coordination import infer_monomer_geometry
        from hqiv_lab.packing import molecular_melt_density_ratio, neighbor_covalent_lapse_overlap_factor
        from hqiv_lab.spec import MoleculeSpec
        import hqiv_lean_physics_primitives as lean

        mono = infer_monomer_geometry(MoleculeSpec.from_chart_name("H2O"))
        overlap = neighbor_covalent_lapse_overlap_factor(mono)
        ratio, solid_denser = molecular_melt_density_ratio(mono)
        self.assertFalse(solid_denser)
        self.assertAlmostEqual(
            ratio,
            overlap * lean.PHASE_LIFT_3 / (1.0 + lean.ALPHA),
            places=6,
        )

    def test_ionic_not_water_isomorph(self) -> None:
        salt = ibn.NACL_SALT
        rho = spr.salt_crystal_density_g_cm3(salt)
        unrelated_host = min(1.0, rho / pgd.liquid_reference_density_g_cm3("H2O"))
        ionic = pgd.crystalline_curvature_density_fraction(
            rho, motif="ionic_lattice", n_coord=6, salt=salt
        )
        self.assertEqual(unrelated_host, 1.0)
        self.assertGreater(ionic, 0.72)
        self.assertLess(ionic, 0.85)

    def test_ionic_melt_ratio_varies_by_salt(self) -> None:
        nacl, _ = pgd.resolve_crystalline_melt_density_ratio(
            motif="ionic_lattice", n_coord=6, salt=ibn.NACL_SALT
        )
        lih, _ = pgd.resolve_crystalline_melt_density_ratio(
            motif="ionic_lattice", n_coord=6, salt=ibn.LIH_SALT
        )
        self.assertNotAlmostEqual(nacl, lih, places=2)

    def test_ionic_melt_reference_from_network(self) -> None:
        salt = ibn.NACL_SALT
        rho = spr.salt_crystal_density_g_cm3(salt)
        ratio, solid_denser = pgd.resolve_crystalline_melt_density_ratio(
            motif="ionic_lattice", n_coord=6, salt=salt
        )
        self.assertTrue(solid_denser)
        rho_m = pgd.derived_melt_reference_density_g_cm3(
            rho, motif="ionic_lattice", n_coord=6, salt=salt
        )
        self.assertAlmostEqual(rho_m / rho, ratio, places=6)


if __name__ == "__main__":
    unittest.main()

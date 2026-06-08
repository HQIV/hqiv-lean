#!/usr/bin/env python3
"""Phase geometry → density → melt curvature (H₂O ice Ih witness)."""

import unittest

import hqiv_phase_geometry_density as pgd
import hqiv_thermodynamic_phase_from_tp as tptp


class TestPhaseGeometryDensity(unittest.TestCase):
    def test_h2o_ih_density_near_ice(self) -> None:
        cell = pgd.phase_unit_cell("H2O", "Ih")
        rho = pgd.density_g_cm3(cell)
        self.assertAlmostEqual(rho, 0.88, delta=0.06)

    def test_curvature_fraction_from_geometry(self) -> None:
        rho = pgd.density_g_cm3(pgd.phase_unit_cell("H2O", "Ih"))
        frac = pgd.curvature_density_fraction(rho, "H2O")
        self.assertAlmostEqual(frac, 0.88, delta=0.06)

    def test_bulk_h2o_uses_derived_rho_not_unity(self) -> None:
        mat = tptp.material_scales_bulk_h2o()
        self.assertLess(mat.medium_density_fraction or 1.0, 0.95)
        self.assertGreater(mat.medium_density_fraction or 0.0, 0.80)

    def test_melt_near_273k_with_phase_geometry(self) -> None:
        mat = tptp.material_scales_bulk_h2o()
        t_sl = tptp.solid_liquid_transition_temperature_K(mat, pressure_Pa=tptp.STP_PRESSURE_PA)
        self.assertAlmostEqual(t_sl, 273.15, delta=1.5)

    def test_orbital_curvature_at_two_earth_radii(self) -> None:
        w = pgd.orbital_phase_witness_earth(2.0 * pgd.EARTH_RADIUS_M)
        rho = pgd.orbital_curvature_density_fraction(w)
        self.assertAlmostEqual(rho, 0.4, places=3)

    def test_orbital_curvature_dilute_at_large_r(self) -> None:
        w = pgd.orbital_phase_witness_earth(1.0e9 * pgd.EARTH_RADIUS_M)
        rho = pgd.orbital_curvature_density_fraction(w)
        self.assertLess(rho, 1.0e-6)

    def test_flyby_kappa_from_phase(self) -> None:
        w = pgd.orbital_phase_witness_earth(2.0 * pgd.EARTH_RADIUS_M)
        kappa = pgd.flyby_dynamic_kappa_phi_from_phase(w, 1.0)
        self.assertLess(kappa, 5.0)
        self.assertGreater(kappa, 0.0)


if __name__ == "__main__":
    unittest.main()

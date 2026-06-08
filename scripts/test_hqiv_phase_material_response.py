#!/usr/bin/env python3
"""Tests for phase-geometry material response (n, ε_r, k_th, σ slot)."""

import unittest

import hqiv_phase_material_response as pmr
import hqiv_phase_geometry_density as pgd


class TestPhaseMaterialResponse(unittest.TestCase):
    def test_clausius_mossotti_refractive_index_monotone(self) -> None:
        n_lo = pmr.refractive_index_from_clausius_mossotti(0.05)
        n_hi = pmr.refractive_index_from_clausius_mossotti(0.15)
        self.assertLess(n_lo, n_hi)
        self.assertGreaterEqual(n_lo, 1.0)

    def test_dielectric_equals_n_squared(self) -> None:
        n = 1.31
        self.assertAlmostEqual(pmr.dielectric_constant_from_refractive_index(n), n * n)

    def test_h2o_ice_refractive_index_near_131(self) -> None:
        out = pmr.material_response_readout("H2O", allotrope="Ih", phase="solid")
        self.assertAlmostEqual(out["refractive_index"], 1.31, delta=0.05)
        self.assertGreater(out["dielectric_constant"], 1.6)
        self.assertLess(out["dielectric_constant"], 1.8)

    def test_h2o_liquid_refractive_index_near_133(self) -> None:
        out = pmr.material_response_readout("H2O", phase="liquid")
        self.assertAlmostEqual(out["refractive_index"], 1.33, delta=0.05)

    def test_h2o_ice_thermal_conductivity_order_of_magnitude(self) -> None:
        out = pmr.material_response_readout("H2O", allotrope="Ih", phase="solid")
        k = out["thermal_conductivity_W_mK"]
        self.assertGreater(k, 0.5)
        self.assertLess(k, 8.0)

    def test_liquid_water_lower_conductivity_than_ice(self) -> None:
        ice = pmr.material_response_readout("H2O", allotrope="Ih", phase="solid")
        liq = pmr.material_response_readout("H2O", phase="liquid")
        self.assertGreater(ice["thermal_conductivity_W_mK"], liq["thermal_conductivity_W_mK"])

    def test_pure_water_ionic_conductivity_zero(self) -> None:
        out = pmr.material_response_readout("H2O", phase="liquid", carrier_fraction=0.0)
        self.assertEqual(out["ionic_conductivity_S_m"], 0.0)

    def test_polarizability_increases_with_curvature_density(self) -> None:
        xi = pgd.material_scales_with_phase_geometry("H2O").contact_xi
        a_dilute = pmr.hqiv_polarizability_angstrom3("H2O", 0.0, xi)
        a_bulk = pmr.hqiv_polarizability_angstrom3("H2O", 0.92, xi)
        self.assertGreater(a_bulk, a_dilute)

    def test_ice_higher_refractive_index_than_dilute_limit(self) -> None:
        ice = pmr.material_response_readout("H2O", allotrope="Ih", phase="solid")
        # Gas-phase proxy: liquid density scale but ρ_curv → 0 polarizability channel
        xi = ice["contact_xi"]
        alpha_gas = pmr.hqiv_polarizability_angstrom3("H2O", 0.0, xi)
        cm_gas = pmr.clausius_mossotti_ratio(
            1e-6, 18.015, alpha_gas, coordination_divisor=1.0
        )
        n_gas = pmr.refractive_index_from_clausius_mossotti(cm_gas)
        self.assertGreater(ice["refractive_index"], n_gas)

    def test_readout_keys(self) -> None:
        out = pmr.material_response_readout("CH4", allotrope="solid_I", phase="solid")
        for key in (
            "refractive_index",
            "dielectric_constant",
            "thermal_conductivity_W_mK",
            "ionic_conductivity_S_m",
            "clausius_mossotti_ratio",
            "molar_heat_capacity_J_per_mol_K",
            "latent_heat_fusion_J_per_mol",
            "dynamic_viscosity_Pa_s",
            "birefringence_delta_n",
        ):
            self.assertIn(key, out)

    def test_h2o_molar_heat_capacity_near_75(self) -> None:
        liq = pmr.material_response_readout("H2O", phase="liquid")
        self.assertAlmostEqual(liq["molar_heat_capacity_J_per_mol_K"], 74.0, delta=15.0)
        ice = pmr.material_response_readout("H2O", allotrope="Ih", phase="solid")
        self.assertGreater(ice["molar_heat_capacity_J_per_mol_K"], liq["molar_heat_capacity_J_per_mol_K"])

    def test_latent_heat_fusion_positive(self) -> None:
        out = pmr.material_response_readout("H2O", phase="solid")
        self.assertGreater(out["latent_heat_fusion_J_per_mol"], 1000.0)

    def test_liquid_water_viscosity_order_of_magnitude(self) -> None:
        out = pmr.material_response_readout("H2O", phase="liquid", temperature_k=273.15)
        eta = out["dynamic_viscosity_Pa_s"]
        self.assertGreater(eta, 1.0e-6)
        self.assertLess(eta, 1.0e-2)

    def test_solid_viscosity_infinite(self) -> None:
        out = pmr.material_response_readout("H2O", phase="solid")
        self.assertEqual(out["dynamic_viscosity_Pa_s"], float("inf"))

    def test_ice_ih_birefringence_small(self) -> None:
        out = pmr.material_response_readout("H2O", allotrope="Ih", phase="solid")
        dn = out["birefringence_delta_n"]
        self.assertGreater(dn, 1.0e-4)
        self.assertLess(dn, 1.0e-2)
        self.assertAlmostEqual(out["refractive_index_ordinary"], 1.31, delta=0.06)

    def test_condensed_panel_refractive_index_theta_slot(self) -> None:
        """η = θ/θ₀ optical slot across GMTKN55 condensed motifs."""
        h2o_ice = pmr.material_response_readout("H2O", allotrope="Ih", phase="solid")
        self.assertAlmostEqual(h2o_ice["optical_phase_eta"], 1.0, delta=0.05)
        self.assertAlmostEqual(h2o_ice["refractive_index"], 1.31, delta=0.06)
        h2o_liq = pmr.material_response_readout("H2O", phase="liquid")
        self.assertAlmostEqual(h2o_liq["refractive_index"], 1.33, delta=0.06)
        ch4 = pmr.material_response_readout(
            "CH4", allotrope="solid_I", phase="solid", temperature_k=90.0
        )
        self.assertAlmostEqual(ch4["refractive_index"], 1.10, delta=0.08)
        nh3 = pmr.material_response_readout("NH3", phase="liquid", temperature_k=195.0)
        self.assertAlmostEqual(nh3["refractive_index"], 1.33, delta=0.08)
        hf = pmr.material_response_readout("HF", phase="solid", temperature_k=190.0)
        self.assertAlmostEqual(hf["refractive_index"], 1.20, delta=0.08)

    def test_readout_includes_optical_theta(self) -> None:
        out = pmr.material_response_readout("NH3", phase="solid")
        self.assertIn("optical_phase_eta", out)
        self.assertIn("optical_geff", out)
        self.assertGreater(out["optical_geff"], 0.0)


if __name__ == "__main__":
    unittest.main()

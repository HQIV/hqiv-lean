"""Tests for hqiv_solar_dynamics.py."""

import json
import math
import tempfile
import unittest
from pathlib import Path

import hqiv_solar_dynamics as sd


class TestHQIVSolarDynamics(unittest.TestCase):
    def test_phi_jump_matches_lean_closed_form(self) -> None:
        self.assertAlmostEqual(sd.phi_jump(0, 4), 8.0)
        self.assertAlmostEqual(sd.phi_jump(4, 4), 0.0)
        self.assertAlmostEqual(sd.phi_jump(2, 8), 12.0)

    def test_hqiv_axial_field_vanishes_at_zero_gradient(self) -> None:
        fields = sd.hqiv_axial_field(100.0, 1.0e6, 0.0, coupling_log=1.0)
        self.assertAlmostEqual(fields["E_HQIV"], 0.0)
        self.assertAlmostEqual(fields["E_eff"], fields["E_ohm"])

    def test_hqiv_axial_field_scales_linearly_with_gradient(self) -> None:
        f1 = sd.hqiv_axial_field(0.0, 1.0, 2.0, coupling_log=1.0)
        f2 = sd.hqiv_axial_field(0.0, 1.0, 4.0, coupling_log=1.0)
        self.assertAlmostEqual(f2["E_HQIV"], 2.0 * f1["E_HQIV"])

    def test_heating_flux_nonneg_under_positive_conventions(self) -> None:
        flux = sd.heating_flux_boundary(
            nq=1.0e20,
            v_parallel=5.0e3,
            phi_photo=sd.phi_of_shell(0),
            phi_corona=sd.phi_of_shell(4),
            coupling_log=1.0,
        )
        self.assertGreater(flux, 0.0)

    def test_flux_tube_equal_shells_zero_boundary_flux(self) -> None:
        row = sd.solar_flux_tube_readout(m_photo=3, m_corona=3)
        self.assertAlmostEqual(row.delta_phi, 0.0)
        self.assertAlmostEqual(row.heating_flux_boundary, 0.0)

    def test_solar_shear_gate_zero_at_pole(self) -> None:
        self.assertAlmostEqual(sd.solar_shear_gate(0.0), 0.0)

    def test_cycle_oscillator_period_increases_with_threshold(self) -> None:
        low = sd.solar_cycle_oscillator(discharge_threshold=1.0)
        high = sd.solar_cycle_oscillator(discharge_threshold=10.0)
        self.assertGreater(high.estimated_period_days, low.estimated_period_days)

    def test_active_belt_witness_from_gamma(self) -> None:
        belt = sd.solar_active_belt_witness()
        self.assertAlmostEqual(belt["latitude_monogamy_deg"], 90.0 - math.degrees(math.acos(sd.GAMMA)), places=5)
        self.assertAlmostEqual(
            belt["latitude_rindler_half_deg"],
            math.degrees(math.asin(math.sqrt(sd.GAMMA / 2.0))),
            places=5,
        )

    def test_cycle_oscillator_uses_rindler_half_belt_by_default(self) -> None:
        belt = sd.solar_active_belt_witness()
        cycle = sd.solar_cycle_oscillator()
        expected_sin = sd.sin_colatitude_from_heliographic_latitude(belt["latitude_rindler_half_deg"])
        shear = sd.solar_shear_gate(expected_sin)
        low = sd.solar_cycle_oscillator(sin_colatitude=expected_sin * 0.5)
        self.assertLess(cycle.estimated_period_years, low.estimated_period_years)
        self.assertAlmostEqual(cycle.estimated_period_years, 11.3, delta=0.5)
        self.assertGreater(shear, sd.solar_shear_gate(sd.sin_colatitude_from_heliographic_latitude(30.0)))

    def test_cycle_oscillator_near_jupiter_period(self) -> None:
        cycle = sd.solar_cycle_oscillator()
        self.assertAlmostEqual(cycle.jupiter_orbital_carrier_years, 11.862)
        self.assertGreater(cycle.estimated_period_years, 8.0)
        self.assertLess(cycle.estimated_period_years, 16.0)
        self.assertGreater(cycle.outside_gate, 1.0)
        self.assertGreater(cycle.planetary_multiplier, 1.0)

    def test_galactic_outside_gate_positive(self) -> None:
        outside = sd.solar_whim_galactic_outside_gate()
        self.assertGreater(outside["epsilon_galactic"], 0.0)
        self.assertGreater(outside["geff_modulator"], 1.0)
        self.assertGreater(outside["whim_boundary_shape"], 0.0)
        self.assertGreater(outside["combined_outside_gate"], 1.0)

    def test_planetary_magnetic_coupling_positive(self) -> None:
        planetary = sd.solar_planetary_magnetic_coupling(alignment_sin=0.5)
        self.assertGreater(planetary["planetary_magnetic_coupling"], 0.0)
        self.assertGreater(planetary["combined_multiplier"], 1.0)

    def test_environment_phase_exceeds_interior(self) -> None:
        interior = sd.solar_cycle_phase(0, 8, 1)
        env = sd.solar_cycle_environment_phase(0, 8, 1, alignment_sin=0.5)
        self.assertGreater(env, interior)

    def test_sunspot_pin_inactive_below_threshold(self) -> None:
        pin = sd.sunspot_pin_readout(gate=1.0, threshold=5.0)
        self.assertFalse(pin.pin_active)
        self.assertAlmostEqual(pin.pin_stress, 0.0)

    def test_sunspot_pin_active_above_threshold(self) -> None:
        pin = sd.sunspot_pin_readout(gate=10.0, threshold=1.0)
        self.assertTrue(pin.pin_active)
        self.assertGreater(pin.pin_stress, 0.0)

    def test_json_payload_structure(self) -> None:
        payload = sd.build_readout_payload()
        self.assertIn("lean_modules", payload)
        self.assertIn("proved_algebra", payload)
        self.assertIn("readout_model", payload)
        self.assertIn("heating_comparison", payload)
        self.assertIn("outside_curvature_whim", payload["readout_model"])
        self.assertIn("planetary_magnetic_coupling", payload["readout_model"])
        self.assertIn("Hqiv.Physics.CoronalHeatingComparisonWitness", payload["lean_modules"])

    def test_coronal_heating_comparison_hqiv_length_independent(self) -> None:
        row = sd.coronal_heating_comparison_readout(loop_length_1=1.0e8, loop_length_2=3.0e8)
        self.assertTrue(row.hqiv_length_independent)
        self.assertAlmostEqual(row.hqiv_flux_loop_1, row.hqiv_flux_loop_2)
        self.assertTrue(row.wave_length_fluxes_differ)
        self.assertNotAlmostEqual(row.wave_flux_loop_1, row.wave_flux_loop_2)

    def test_coronal_heating_comparison_ratios(self) -> None:
        row = sd.coronal_heating_comparison_readout()
        self.assertAlmostEqual(row.hqiv_to_alfven, row.hqiv_flux / row.alfven_flux)
        self.assertAlmostEqual(row.hqiv_to_nanoflare, row.hqiv_flux / row.nanoflare_flux)
        self.assertEqual(row.claim_status, "comparison_witness")

    def test_alfven_flux_zero_damping(self) -> None:
        self.assertAlmostEqual(sd.alfven_wave_heating_flux_density(1.0, 1.0e6, 0.0), 0.0)

    def test_estar_calibration_roundtrip(self) -> None:
        p_ph = sd.phi_of_shell(0)
        p_cor = sd.phi_of_shell(8)
        target = 1.0e3
        nq = 1.0e20
        v_par = 5.0e3
        lam = 1.0
        e_star = sd.estar_for_target_heating_flux(target, nq, v_par, p_ph, p_cor, coupling_log=lam)
        flux = sd.heating_flux_boundary(nq, v_par, p_ph, p_cor, e_star=e_star, coupling_log=lam)
        self.assertAlmostEqual(flux, target, delta=target * 1.0e-9)

    def test_nanoflare_flux_zero_cross_section(self) -> None:
        self.assertAlmostEqual(sd.nanoflare_heating_flux_density(1.0e24, 1.0, 0.0), 0.0)

    def test_json_cli_roundtrip(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "solar.json"
            sd.build_readout_payload()
            import subprocess
            import sys

            subprocess.run(
                [
                    sys.executable,
                    str(Path(__file__).resolve().parent / "hqiv_solar_dynamics.py"),
                    "--json",
                    str(out),
                ],
                check=True,
                env={**dict(__import__("os").environ), "PYTHONPATH": str(Path(__file__).resolve().parent)},
            )
            data = json.loads(out.read_text(encoding="utf-8"))
            self.assertEqual(data["source"], "scripts/hqiv_solar_dynamics.py")
            self.assertIn("flux_tube", data)
            self.assertIn("heating_comparison", data)


if __name__ == "__main__":
    unittest.main()

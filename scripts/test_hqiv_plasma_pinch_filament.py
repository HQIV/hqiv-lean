"""Tests for hqiv_plasma_pinch_filament.py."""

from __future__ import annotations

import math
import unittest

import hqiv_plasma_pinch_filament as pinch


class TestPlasmaPinchFilament(unittest.TestCase):
    def test_B_theta_and_pressure_consistent(self) -> None:
        I, r = 1.0e3, 0.01
        B = pinch.pinch_azimuthal_field(I, r)
        p1 = pinch.magnetic_pinch_pressure(B)
        p2 = pinch.pinch_azimuthal_pressure(I, r)
        self.assertAlmostEqual(p1, p2, places=6)

    def test_bennett_current_positive(self) -> None:
        I = pinch.bennett_equilibrium_current(0.1, 1.0e4)
        self.assertGreater(I, 0.0)

    def test_compression_ratio_scales_as_inverse_r_sq(self) -> None:
        c1 = pinch.pinch_compression_ratio(1.0, 0.5)
        c2 = pinch.pinch_compression_ratio(1.0, 0.25)
        self.assertAlmostEqual(c1, 4.0)
        self.assertAlmostEqual(c2, 16.0)
        self.assertAlmostEqual(c2 / c1, 4.0)

    def test_hot_current_pressure_mono_in_J(self) -> None:
        r = 1.0e5
        p_lo = pinch.hot_current_pinch_pressure(1.0, r)
        p_hi = pinch.hot_current_pinch_pressure(10.0, r)
        self.assertGreater(p_hi, p_lo)
        self.assertAlmostEqual(p_hi / p_lo, 100.0, places=4)

    def test_coronal_readout_enhancement_gt_one(self) -> None:
        out = pinch.coronal_flux_tube_pinch_readout(5.0, 1.0e5, R_loop_m=1.0e6, r_pinch_m=1.0e4)
        self.assertGreater(out.compression.compression_ratio, 1.0)
        self.assertEqual(out.q_dot_enhancement, out.compression.heating_enhancement)

    def test_whim_phi_enhancement_nonneg(self) -> None:
        out = pinch.whim_filament_pinch_readout(
            3.086e21,
            3.086e22,
            r_pinch_m=1.543e20,
        )
        self.assertGreaterEqual(out.phi_pinch_enhancement, 0.0)
        self.assertIn("hypothesis", out.note.lower())

    def test_beta_balance_coronal(self) -> None:
        beta = pinch.beta_pinch_balance_readout(
            pinch.CORONAL_FILAMENT_N_M3,
            pinch.CORONAL_FILAMENT_T_K,
            1.0e5,
            regime="coronal",
        )
        self.assertAlmostEqual(beta.beta, 1.0, places=6)
        self.assertTrue(beta.balance_ok)
        self.assertGreater(beta.current_density_a_m2, 0.0)

    def test_cosmic_epoch_derived_t_cmb(self) -> None:
        ep = pinch.derive_cosmic_filament_epoch()
        self.assertGreater(ep.T_cmb_K, 2.0)
        self.assertLess(ep.T_cmb_K, 3.5)
        self.assertGreater(ep.age_ratio_wall_over_apparent, 1.0)
        self.assertEqual(pinch.COOLING_ALPHA, 3.0 / 5.0)
        self.assertEqual(pinch.PINCH_HEATING_FRACTION, 2.0 / 5.0)

    def test_coupled_whim_filament_radiative_closure(self) -> None:
        coupled = pinch.coupled_whim_filament_readout(3.086e22, 1.543e20)
        self.assertTrue(coupled.radiative_ok)
        self.assertGreater(coupled.T_K, coupled.epoch.T_cmb_K)
        self.assertGreater(coupled.n_m3, 0.0)
        residual = pinch.whim_radiative_equilibrium_residual(
            coupled.n_m3, coupled.T_K, epoch=coupled.epoch
        )
        self.assertLess(abs(residual), 1.0e-10)

    def test_whim_equilibrium_density_at_coupled_temperature(self) -> None:
        coupled = pinch.coupled_whim_filament_readout(3.086e22, 1.543e20)
        n = pinch.whim_equilibrium_density_m3(coupled.T_K, epoch=coupled.epoch)
        self.assertAlmostEqual(n, coupled.n_m3, places=4)

    def test_coupled_node_hotter_than_spine(self) -> None:
        R, r_spine, r_pinch = 3.086e22, 3.086e21, 1.543e20
        spine = pinch.coupled_whim_filament_readout(R, r_pinch, n_filaments=1)
        node = pinch.coupled_whim_filament_readout(R, r_pinch, n_filaments=4)
        self.assertEqual(node.node_thermal_multiplier, 16.0)
        self.assertGreater(node.T_K, spine.T_K)
        self.assertGreater(node.n_m3, spine.n_m3)

    def test_coupled_whim_filament_node_readout(self) -> None:
        r_spine = 3.086e21
        out = pinch.coupled_whim_filament_node_readout(r_spine, 3.086e22, 4, r_pinch_m=1.543e20)
        self.assertTrue(out.coupled.radiative_ok)
        self.assertEqual(out.coupled.n_filaments, 4)
        self.assertGreater(out.node_localized_intensity, 100.0)
        spine_p = pinch.hot_current_pinch_pressure(out.beta_spine.current_density_a_m2, r_spine)
        self.assertGreater(out.node.p_pinch_pa, spine_p)

    def test_node_thermal_load_multiplier_algebra(self) -> None:
        self.assertEqual(pinch.node_thermal_load_multiplier(1), 1.0)
        self.assertEqual(pinch.node_thermal_load_multiplier(4), 16.0)
        R, r = 3.086e22, 3.086e21
        ratio = pinch.node_localized_intensity(R, r, 4) / pinch.pinch_compression_ratio(R, r)
        self.assertAlmostEqual(ratio, 16.0, places=6)

    def test_beta_balance_whim_derived_j(self) -> None:
        r = 3.086e21
        coupled = pinch.coupled_whim_filament_readout(3.086e22, 1.543e20)
        beta = pinch.beta_pinch_balance_readout(coupled.n_m3, coupled.T_K, r)
        out = pinch.whim_filament_pinch_readout(r, 3.086e22)
        self.assertAlmostEqual(out.J_spine_A_m2, beta.current_density_a_m2, places=12)

    def test_node_intensity_scales_with_n(self) -> None:
        R, r = 3.086e22, 1.543e20
        c2 = pinch.node_localized_intensity(R, r, 2)
        c5 = pinch.node_localized_intensity(R, r, 5)
        self.assertGreater(c5, c2)

    def test_pinch_state_bennett_slot(self) -> None:
        st = pinch.pinch_state_at_radius(500.0, 0.05, delta_p_Pa=1.0e3)
        self.assertIsNotNone(st.bennett_I_A)
        assert st.bennett_I_A is not None
        self.assertGreater(st.bennett_I_A, 0.0)


if __name__ == "__main__":
    unittest.main()

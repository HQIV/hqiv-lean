"""Tests for hqiv_wide_binary.py."""

from __future__ import annotations

import math
import unittest

import hqiv_wide_binary as wb


class TestHQIVWideBinary(unittest.TestCase):
    def test_circular_period_matches_kepler(self) -> None:
        preset = wb.WIDE_BINARY_PRESETS["demo_circular_1au"]
        p = wb.period_years(preset.elements.semi_major_axis_m, preset.star1.mass_kg, preset.star2.mass_kg)
        # Relative-orbit semi-major 1 AU with 2 M_sun total mass ⇒ P = 1/sqrt(2) yr.
        self.assertAlmostEqual(p, 1.0 / math.sqrt(2.0), delta=0.01)

    def test_hqiv_screen_stronger_at_apastron(self) -> None:
        preset = wb.WIDE_BINARY_PRESETS["demo_wide_eccentric"]
        ratios = wb.peri_apo_acceleration_ratio(preset, use_spin_lapse=True, use_rindler_denominator=False)
        self.assertGreater(ratios["periastron"]["hqiv_over_newton"], 1.0)
        self.assertGreater(ratios["apastron"]["hqiv_over_newton"], ratios["periastron"]["hqiv_over_newton"])

    def test_preset_payload_finite(self) -> None:
        payload = wb.preset_payload("demo_circular_1au", t_yr=0.5, dt_days=1.0)
        self.assertEqual(payload["preset"], "demo_circular_1au")
        self.assertTrue(math.isfinite(payload["integration"]["final_separation_au"]))

    def test_spin_axis_grid_covers_sphere(self) -> None:
        grid = wb.spin_axis_unit_grid(step_deg=90.0)
        self.assertGreaterEqual(len(grid), 3)
        for _, _, axis in grid:
            self.assertAlmostEqual(wb.vec_norm(axis), 1.0, places=6)

    def test_dual_spin_sweep_increases_gamma_at_most_coupled(self) -> None:
        preset = wb.WIDE_BINARY_PRESETS["literature_scale_10kau"]
        m1 = preset.star1.mass_kg
        m2 = preset.star2.mass_kg
        r1, v1, r2, v2 = wb.elements_to_barycentric(preset.elements, m1, m2)
        out = wb.dual_spin_axis_sweep(
            r1, v1, r2, v2, preset.star1, preset.star2,
            axis_step_deg=90.0,
            omega_breakup_fraction=0.5,
            omega_sweep_steps=8,
            use_rindler_denominator=False,
            independent_star_axes=True,
        )
        base = float(out["baseline_no_spin"]["gamma_eff_mean"])
        best = float(out["phase2_omega_sweep_at_best_axes"]["best_gamma_eff_mean"])
        self.assertGreaterEqual(best, base)
        self.assertLess(best, 1.01)


if __name__ == "__main__":
    unittest.main()

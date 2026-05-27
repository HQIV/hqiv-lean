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


if __name__ == "__main__":
    unittest.main()

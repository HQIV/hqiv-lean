"""Tests for hqiv_galaxy_rotation.py."""

from __future__ import annotations

import math
import unittest

import hqiv_galaxy_rotation as gal


class TestHQIVGalaxyRotation(unittest.TestCase):
    def test_exponential_disk_mass_limits(self) -> None:
        disk = gal.GalaxyDisk()
        self.assertAlmostEqual(gal.exponential_disk_mass_inside(0.0, disk.disk_mass_kg, disk.scale_length_m), 0.0)
        self.assertGreater(
            gal.exponential_disk_mass_inside(20.0 * disk.scale_length_m, disk.disk_mass_kg, disk.scale_length_m),
            0.999999 * disk.disk_mass_kg,
        )

    def test_mass_horizon_doppler_projection(self) -> None:
        v = 220_000.0
        full = gal.mass_horizon_doppler_lapse(v, projection=1.0, use_rindler_denominator=False)
        polar = gal.mass_horizon_doppler_lapse(v, projection=0.0, use_rindler_denominator=False)
        self.assertAlmostEqual(full, 2.0 * v / gal.C_LIGHT)
        self.assertEqual(polar, 0.0)

    def test_rindler_denominator_suppresses_local_disk_lapse(self) -> None:
        v = 220_000.0
        raw = gal.mass_horizon_doppler_lapse(v, use_rindler_denominator=False)
        screened = gal.mass_horizon_doppler_lapse(v, use_rindler_denominator=True)
        self.assertGreater(raw, screened)
        self.assertGreater(gal.rindler_denominator(v), 1.0)

    def test_hqiv_rotation_point_is_finite_and_above_baryonic(self) -> None:
        disk = gal.GalaxyDisk()
        row = gal.hqiv_rotation_point(8.0 * gal.KPC, disk, use_rindler_denominator=False)
        self.assertTrue(math.isfinite(row.hqiv_speed_km_s))
        self.assertGreaterEqual(row.hqiv_speed_km_s, row.baryonic_speed_km_s)
        self.assertGreater(row.one_minus_f_full, 0.0)

    def test_named_presets_return_reference_models(self) -> None:
        self.assertIn("ngc3198", gal.GALAXY_PRESETS)
        payload = gal.preset_payload("ngc3198", n=5)
        self.assertEqual(payload["preset"], "ngc3198")
        self.assertEqual(len(payload["rows"]), 5)
        ref = payload["reference_model"]
        self.assertGreater(ref["hqiv_speed_km_s"], 0.0)
        self.assertGreater(payload["observed_flat_km_s"], 0.0)


if __name__ == "__main__":
    unittest.main()

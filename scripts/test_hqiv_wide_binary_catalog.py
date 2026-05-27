"""Tests for Chae (2026) wide-binary catalog integration."""

from __future__ import annotations

import unittest

import hqiv_wide_binary as wb
import hqiv_wide_binary_catalog as cat


class TestChaeCatalog(unittest.TestCase):
    def test_catalog_loads_36_systems(self) -> None:
        catalog = cat.load_chae_catalog()
        self.assertEqual(len(catalog), 36)

    def test_reference_system_58(self) -> None:
        self.assertEqual(wb.CHAE_REFERENCE_SYSTEM, "chae2026_58")
        entry = cat.load_chae_catalog()[wb.CHAE_REFERENCE_SYSTEM]
        self.assertEqual(entry.chae_id, 58)
        self.assertAlmostEqual(entry.vobs_over_vesc, 0.35, delta=0.01)

    def test_full_treatment_reference_finite(self) -> None:
        payload = wb.full_treatment_chae(wb.CHAE_REFERENCE_SYSTEM, t_yr=0.01, dt_days=10.0)
        self.assertEqual(payload["chae_id"], 58)
        gamma = payload["instantaneous_hqiv"]["star1"]["gamma_eff"]
        self.assertGreater(gamma, 1.0)
        self.assertLess(gamma, 1.001)
        self.assertIsNotNone(payload["vis_viva"]["semi_major_au"])

    def test_projected_separation_order_of_magnitude(self) -> None:
        kin = cat.observed_relative_kinematics(cat.load_chae_catalog()[wb.CHAE_REFERENCE_SYSTEM])
        # ~10^4 AU at ~40 pc for this wide pair
        self.assertGreater(kin["separation_au"], 5000.0)
        self.assertLess(kin["separation_au"], 50000.0)

    def test_batch_all_chae(self) -> None:
        payload = wb.batch_all_chae_systems()
        self.assertEqual(payload["n_systems"], 36)
        g = payload["aggregate"]["gamma_eff_hqiv_mean_of_systems"]
        self.assertGreater(g, 1.0)
        self.assertLess(g, 1.01)


if __name__ == "__main__":
    unittest.main()

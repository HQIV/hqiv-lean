"""Tests for hqiv_observational_errors.py."""

from __future__ import annotations

import unittest

from hqiv_observational_errors import (
    flyby_literature_sigma_mm_s,
    gamma_chae_interval,
    hqiv_falsifies_chae_gamma,
)


class TestObservationalErrors(unittest.TestCase):
    def test_rosetta_sigma_matches_anderson(self) -> None:
        self.assertAlmostEqual(flyby_literature_sigma_mm_s("rosetta_2005"), 0.05)

    def test_hqiv_falsifies_high_chae_gamma(self) -> None:
        out = hqiv_falsifies_chae_gamma(
            gamma_hqiv_lo=1.000001,
            gamma_hqiv_hi=1.0015,
            gamma_chae=1.6,
            gamma_chae_lo=1.38,
            gamma_chae_hi=1.77,
        )
        self.assertEqual(out["status"], "falsified")
        self.assertTrue(out["hqiv_max_below_chae_lo"])

    def test_gamma_chae_interval_ordering(self) -> None:
        class Entry:
            gamma_chae = 0.1
            gamma_chae_err_lo = 0.05
            gamma_chae_err_hi = 0.05

        interval = gamma_chae_interval(Entry())  # type: ignore[arg-type]
        self.assertIsNotNone(interval["gamma"])
        self.assertLess(interval["gamma_lo"], interval["gamma"])  # type: ignore[operator]
        self.assertGreater(interval["gamma_hi"], interval["gamma"])  # type: ignore[operator]


if __name__ == "__main__":
    unittest.main()

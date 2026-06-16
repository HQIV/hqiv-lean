"""Tests for model_guided_zero_locator.py."""

from __future__ import annotations

import math
import unittest

from model_guided_zero_locator import (
    BALANCE_OFFSET,
    CANDIDATE_PERIOD,
    hardy_z,
    locate_zeros_near,
    model_candidates_up_to,
    model_guided_zero_locator,
    nearest_model_candidate,
)


class TestModelCandidates(unittest.TestCase):
    def test_empty_below_first_candidate(self) -> None:
        self.assertEqual(model_candidates_up_to(2.0), [])

    def test_first_candidate(self) -> None:
        cands = model_candidates_up_to(BALANCE_OFFSET)
        self.assertEqual(len(cands), 1)
        self.assertEqual(cands[0].index, 0)
        self.assertAlmostEqual(cands[0].height, BALANCE_OFFSET)

    def test_count_up_to_15(self) -> None:
        cands = model_candidates_up_to(15.0)
        heights = [c.height for c in cands]
        self.assertTrue(all(h <= 15.0 for h in heights))
        self.assertGreater(len(cands), 4)
        for k, c in enumerate(cands):
            self.assertEqual(c.index, k)
            self.assertAlmostEqual(c.height, BALANCE_OFFSET + k * CANDIDATE_PERIOD)

    def test_nearest_model_candidate(self) -> None:
        near = nearest_model_candidate(14.134725)
        self.assertIn(near.index, (4, 5))


class TestLocator(unittest.TestCase):
    def test_hardy_z_near_first_zero(self) -> None:
        z0 = hardy_z(14.134725, prec=40)
        self.assertLess(abs(z0), 1e-6)

    def test_locate_near_first_zero_candidate(self) -> None:
        cand = nearest_model_candidate(14.134725)
        roots = locate_zeros_near(cand.height, window=1.0, grid_steps=120, prec=40)
        self.assertTrue(roots)
        self.assertLess(abs(roots[0] - 14.134725), 0.05)

    def test_model_guided_finds_zeros_below_30(self) -> None:
        _, located = model_guided_zero_locator(30.0, window=1.0, grid_steps=100, prec=40)
        self.assertGreaterEqual(len(located), 3)
        for row in located:
            self.assertLess(abs(row.hardy_z_at_located), 1e-4)


if __name__ == "__main__":
    unittest.main()

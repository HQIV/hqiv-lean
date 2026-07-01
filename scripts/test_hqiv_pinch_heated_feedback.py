"""Tests for filament nodes and pinch-heated nonlinear feedback."""

from __future__ import annotations

import math
import unittest

import hqiv_pinch_heated_feedback as fb
import hqiv_plasma_pinch_filament as pinch


class TestFilamentNodes(unittest.TestCase):
    def test_node_intensity_exceeds_spine_for_n_gt_1(self) -> None:
        R, r = 1.0e6, 1.0e4
        spine = pinch.pinch_compression_ratio(R, r)
        node3 = pinch.node_localized_intensity(R, r, 3)
        node4 = pinch.node_localized_intensity(R, r, 4)
        self.assertGreater(node3, spine)
        self.assertGreater(node4, node3)

    def test_node_radius_tightens_with_n(self) -> None:
        r = 1.0e4
        r3 = pinch.node_pinch_radius(r, 3)
        r9 = pinch.node_pinch_radius(r, 9)
        self.assertLess(r3, r)
        self.assertLess(r9, r3)
        self.assertAlmostEqual(r3 / r9, math.sqrt(3.0))

    def test_filament_node_readout_collapse(self) -> None:
        out = pinch.filament_node_readout(
            1.0e-12,
            1.543e20,
            3.086e22,
            4,
            collapse_threshold=100.0,
        )
        self.assertEqual(out.n_filaments, 4)
        self.assertTrue(out.collapse_hypothesis)
        self.assertIn("junction", out.note.lower())


class TestPinchHeatedFeedback(unittest.TestCase):
    def test_local_exceeds_bulk(self) -> None:
        row = fb.pinch_heated_feedback_fixed_point(
            r_pinch_m=1.0e4,
            R_bulk_m=1.0e6,
            tube_radius_m=1.0e5,
            label="test_spine",
        )
        self.assertGreater(row.compression, 1.0)
        self.assertGreater(row.q_dot_self_local_w_m3, row.q_dot_bulk_w_m3)

    def test_node_beats_spine(self) -> None:
        spine = fb.pinch_heated_feedback_fixed_point(
            r_pinch_m=1.0e4,
            R_bulk_m=1.0e6,
            label="spine",
        )
        node = fb.pinch_heated_feedback_fixed_point(
            site="node",
            n_filaments=3,
            r_pinch_m=1.0e4,
            R_bulk_m=1.0e6,
            label="node",
        )
        self.assertGreater(node.compression, spine.compression)
        self.assertGreater(node.q_dot_self_local_w_m3, spine.q_dot_self_local_w_m3)

    def test_fixed_point_converges(self) -> None:
        row = fb.pinch_heated_feedback_fixed_point(
            site="node",
            n_filaments=3,
            r_pinch_m=1.0e4,
            R_bulk_m=1.0e6,
        )
        self.assertTrue(row.converged)
        self.assertGreater(row.iterations, 0)
        self.assertGreater(row.pinch_nonlinear_factor, 0.0)


if __name__ == "__main__":
    unittest.main()

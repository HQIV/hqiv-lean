#!/usr/bin/env python3
"""Tests for dry-wall → tribo shared factor."""

from __future__ import annotations

import unittest

import hqiv_lean_physics_primitives as lean
import hqiv_outside_contact_reduced_deltas as ocrd
import hqiv_wall_tribo_readout as wtr


class TestWallTribo(unittest.TestCase):
    def test_pristine_is_one(self) -> None:
        self.assertAlmostEqual(
            wtr.dry_wall_tribo_channel(ocrd.PRISTINE_WALL), 1.0, places=12
        )

    def test_unit_excess_dress(self) -> None:
        wall = ocrd.DryWallSpectrum(wall_coordination_excess=1.0)
        expect = 1.0 + lean.GAMMA * lean.STRONG_CHANNEL_FRACTION
        self.assertAlmostEqual(wall.dress, expect, places=12)
        self.assertGreater(wtr.dry_wall_tribo_channel(wall), 1.0)

    def test_audit_identity(self) -> None:
        audit = wtr.build_wall_tribo_audit()
        self.assertTrue(audit["all_identity_checks_pass"])


if __name__ == "__main__":
    unittest.main()

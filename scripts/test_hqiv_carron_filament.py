"""Tests for hqiv_carron_filament.py."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

import hqiv_carron_filament as carron


class TestCarronFilament(unittest.TestCase):
    def test_nearest_filament_point_from_index(self) -> None:
        index = {
            "bins": {
                "750:600": {
                    "index": 1,
                    "ra_deg": 150.0,
                    "dec_deg": 30.0,
                    "dens": 1.0,
                    "e_pos_deg": 0.1,
                    "grad_ra": 0.001,
                    "grad_de": 0.002,
                    "angle_deg": 45.0,
                    "z_low": 0.05,
                    "z_high": 0.06,
                }
            }
        }
        hit = carron.nearest_filament_point(150.05, 30.02, index)
        self.assertIsNotNone(hit)
        pt, sep = hit  # type: ignore[misc]
        self.assertAlmostEqual(pt.ra_deg, 150.0)
        self.assertLess(sep, 0.5)

    def test_load_index_roundtrip(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "idx.json"
            payload = {"bins": {}, "n_bins": 0}
            path.write_text(json.dumps(payload), encoding="utf-8")
            loaded = carron.load_block1_index(path)
            self.assertIsNotNone(loaded)


if __name__ == "__main__":
    unittest.main()

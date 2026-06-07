"""Tests for hqiv_filament_environment.py."""

from __future__ import annotations

import json
import tempfile
import unittest
from dataclasses import dataclass
from pathlib import Path

import hqiv_filament_environment as fe


@dataclass(frozen=True)
class FakeMaster:
    name: str
    hubble_type: int
    inclination_deg: float
    rdisk_kpc: float
    rhi_kpc: float
    vflat_kms: float
    distance_mpc: float


class TestFilamentEnvironment(unittest.TestCase):
    def test_load_catalog_roundtrip(self) -> None:
        payload = {
            "NGC3198": {
                "unit": [0.8, 0.6, 0.0],
                "distance_to_spine_mpc": 0.5,
                "inflow_speed_kms": 90,
                "spine_angle_deg": 37.0,
                "source": "test",
            }
        }
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "fil.json"
            path.write_text(json.dumps(payload))
            cat = fe.load_filament_catalog(path)
            self.assertIn("NGC3198", cat)
            env = cat["NGC3198"]
            self.assertAlmostEqual(env.unit_x**2 + env.unit_y**2 + env.unit_z**2, 1.0, places=6)

    def test_proxy_is_reproducible(self) -> None:
        m = FakeMaster("DDO154", 10, 64.0, 0.37, 1.5, 47.0, 4.0)
        a = fe.infer_filament_proxy(m)
        b = fe.infer_filament_proxy(m)
        self.assertEqual(a.unit(), b.unit())
        self.assertEqual(a.source, "sparc_hi_proxy")

    def test_misalignment_between_parallel_vectors_is_zero(self) -> None:
        self.assertAlmostEqual(fe.misalignment_sin((0, 0, 1), (0, 0, 1)), 0.0)

    def test_misalignment_perpendicular_is_one(self) -> None:
        self.assertAlmostEqual(fe.misalignment_sin((0, 0, 1), (1, 0, 0)), 1.0)


if __name__ == "__main__":
    unittest.main()

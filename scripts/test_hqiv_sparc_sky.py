"""Tests for hqiv_sparc_sky.py."""

from __future__ import annotations

import unittest

import hqiv_sparc_sky as sky

SIMBAD_SAMPLE = """
NGC3198
-------
Coordinates(ICRS,ep=J2000,eq=2000): 10 19 54.990  +45 32 58.88 (IR  ) C [~ ~ ] 2006AJ....131.1163S
"""


class TestSparcSky(unittest.TestCase):
    def test_parse_simbad_icrs(self) -> None:
        coords = sky.parse_simbad_icrs(SIMBAD_SAMPLE)
        self.assertIsNotNone(coords)
        ra, dec = coords  # type: ignore[misc]
        self.assertAlmostEqual(ra, 154.979125, places=3)
        self.assertAlmostEqual(dec, 45.549689, places=3)

    def test_filament_spine_unit_length(self) -> None:
        spine = sky.filament_spine_from_angle(150.0, 30.0, 45.0)
        n = spine[0] ** 2 + spine[1] ** 2 + spine[2] ** 2
        self.assertAlmostEqual(n, 1.0, places=6)

    def test_angular_separation_zero(self) -> None:
        self.assertAlmostEqual(sky.angular_separation_deg(10.0, 20.0, 10.0, 20.0), 0.0)


if __name__ == "__main__":
    unittest.main()

#!/usr/bin/env python3
"""Per-accelerator outside dressing ledger."""

from __future__ import annotations

import unittest

import hqiv_accelerator_outside_dressing as aod


class TestAcceleratorOutsideDressing(unittest.TestCase):
    def test_earth_route_unity_facility(self) -> None:
        led = aod.species_outside_ledger(
            1232.0,
            category="baryon_decuplet",
            match="tuft:(n=0, ℓ=1):parity=+",
            pdg_key="Delta+",
        )
        self.assertFalse(led.applies_accelerator_dressing)
        self.assertEqual(led.K_facility, 1.0)
        self.assertAlmostEqual(led.delta_accelerator_mev, 0.0)

    def test_charmed_baryon_gets_lhc_dressing(self) -> None:
        led = aod.species_outside_ledger(
            2286.0,
            category="baryon_charm",
            match="charmed_multiplet:lambda:n=1",
            pdg_key="Lambda_c+",
        )
        self.assertTrue(led.applies_accelerator_dressing)
        self.assertEqual(led.facility_id, "cms_lhc")
        self.assertGreater(led.K_facility, 1.0)
        self.assertGreater(led.delta_accelerator_mev, 0.0)

    def test_hidden_charm_routes_to_bes(self) -> None:
        led = aod.species_outside_ledger(
            3096.0,
            category="meson_charm",
            match="heavy:hidden_charm",
            pdg_key="Jpsi",
        )
        self.assertEqual(led.facility_id, "bes_charmonium")
        self.assertGreater(led.K_facility, 1.0)

    def test_witness_has_facility_factors(self) -> None:
        payload = aod.build_witness_payload()
        cms = payload["facilities"]["cms_lhc"]
        self.assertIn("K_facility", cms)
        self.assertGreater(cms["K_facility"], 1.0)
        earth = payload["facilities"]["earth_surface"]
        self.assertAlmostEqual(earth["K_facility"], 1.0)


if __name__ == "__main__":
    unittest.main()

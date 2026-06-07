"""Tests for hqiv_whim_filament.py."""

from __future__ import annotations

import unittest
from dataclasses import dataclass

import hqiv_whim_filament as wf


@dataclass(frozen=True)
class FakeMaster:
    name: str
    hubble_type: int
    inclination_deg: float
    rdisk_kpc: float
    sb_disk_lsun_pc2: float
    L36_e9_lsun: float
    mhi_e9_msun: float
    rhi_kpc: float
    vflat_kms: float
    distance_mpc: float


class TestWhimFilament(unittest.TestCase):
    def test_smooth_ratios_complement_at_mid_activity(self) -> None:
        a = 0.5
        s = wf.smooth_seed_ratio(a, seed_class=True)
        m = wf.smooth_active_ratio(a)
        self.assertAlmostEqual(s, 0.54, places=2)
        self.assertAlmostEqual(m, 0.5, places=6)

    def test_seed_vs_active_classification(self) -> None:
        ddo = FakeMaster("DDO154", 10, 64.0, 0.37, 12.0, 0.05, 0.08, 1.5, 47.0, 4.0)
        sb = FakeMaster("NGC3198", 5, 73.0, 3.14, 120.0, 5.0, 0.5, 0.0, 150.0, 13.8)
        self.assertTrue(wf.is_seed_galaxy(ddo))
        self.assertFalse(wf.is_seed_galaxy(sb))
        self.assertLess(wf.galaxy_activity_index(ddo), wf.galaxy_activity_index(sb))

    def test_seed_inner_phi_below_cosmic(self) -> None:
        seed = FakeMaster("DDO154", 10, 64.0, 0.37, 12.0, 0.05, 0.08, 1.5, 47.0, 4.0)
        state = wf.whim_phi_part(seed, 0.5)
        cosmic = wf.phi_cosmic_radial(0.5, seed.rdisk_kpc)
        self.assertLess(state.phi_combined_m_s2, cosmic)

    def test_active_whim_ratio_small_at_high_activity(self) -> None:
        active = FakeMaster("NGC3198", 5, 73.0, 3.14, 120.0, 5.0, 0.5, 0.0, 150.0, 13.8)
        state = wf.whim_phi_part(active, 1.0)
        self.assertLess(state.whim_seed_ratio, 0.15)
        self.assertGreater(state.whim_active_ratio, 0.85)

    def test_torque_exchange_is_equal_and_opposite(self) -> None:
        seed = FakeMaster("DDO154", 10, 64.0, 0.37, 12.0, 0.05, 0.08, 1.5, 47.0, 4.0)
        tau = wf.hqiv_torque_exchange_diagnostics(seed)
        self.assertAlmostEqual(tau.torque_on_galaxy_ppm + tau.torque_on_filament_ppm, 0.0)

    def test_no_step_discontinuity_in_phi_combined(self) -> None:
        master = FakeMaster("NGC2403", 5, 62.0, 2.0, 90.0, 2.0, 0.4, 8.0, 135.0, 3.2)
        prev = None
        for activity_scale in [i / 20 for i in range(21)]:
            # Fake varying activity by tweaking sb
            m = FakeMaster(
                master.name,
                master.hubble_type,
                master.inclination_deg,
                master.rdisk_kpc,
                20.0 + 100.0 * activity_scale,
                master.L36_e9_lsun,
                master.mhi_e9_msun,
                master.rhi_kpc,
                master.vflat_kms,
                master.distance_mpc,
            )
            val = wf.whim_phi_part(m, 2.0).phi_combined_m_s2
            if prev is not None:
                self.assertLess(abs(val - prev), wf.phi_cosmic_radial(2.0, m.rdisk_kpc) * 0.6)
            prev = val


if __name__ == "__main__":
    unittest.main()

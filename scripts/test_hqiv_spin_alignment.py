"""Tests for hqiv_spin_alignment.py."""

from __future__ import annotations

import unittest
from dataclasses import dataclass

import hqiv_spin_alignment as sa
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


class TestSpinAlignment(unittest.TestCase):
    def test_seed_alignment_fraction_positive(self) -> None:
        seed = FakeMaster("DDO154", 10, 64.0, 0.37, 12.0, 0.05, 0.08, 1.5, 47.0, 4.0)
        summary = sa.evolve_spin_alignment(seed, duration_gyr=10.0, n_steps=40)
        self.assertGreater(summary.alignment_fraction, 0.0)
        self.assertLess(summary.final_misalignment_sin, summary.initial_misalignment_sin)

    def test_active_galaxy_aligns_less(self) -> None:
        seed = FakeMaster("DDO154", 10, 64.0, 0.37, 12.0, 0.05, 0.08, 1.5, 47.0, 4.0)
        active = FakeMaster("NGC3198", 5, 73.0, 3.14, 120.0, 5.0, 0.5, 0.0, 150.0, 13.8)
        s_seed = sa.evolve_spin_alignment(seed, duration_gyr=10.0, n_steps=40)
        s_active = sa.evolve_spin_alignment(active, duration_gyr=10.0, n_steps=40)
        self.assertGreater(s_seed.alignment_fraction, s_active.alignment_fraction)

    def test_torque_stays_equal_and_opposite_in_trajectory(self) -> None:
        seed = FakeMaster("DDO154", 10, 64.0, 0.37, 12.0, 0.05, 0.08, 1.5, 47.0, 4.0)
        summary = sa.evolve_spin_alignment(seed, duration_gyr=2.0, n_steps=10)
        for state in summary.trajectory:
            self.assertAlmostEqual(
                state.torque_on_galaxy_ppm + state.torque_on_filament_ppm,
                0.0,
            )


if __name__ == "__main__":
    unittest.main()

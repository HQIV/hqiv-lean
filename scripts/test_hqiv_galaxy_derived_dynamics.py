"""Tests for hqiv_galaxy_derived_dynamics.py."""

from __future__ import annotations

import unittest
from dataclasses import dataclass

import hqiv_galaxy_derived_dynamics as d
import hqiv_galaxy_rotation as g


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
    reff_kpc: float = 0.0


class TestProtonPinCosmology(unittest.TestCase):
    def test_phi_hom_from_impedance_age(self) -> None:
        cosmo = d.proton_pin_cosmology()
        self.assertEqual(cosmo.reference_m, 4)
        self.assertAlmostEqual(cosmo.m_prop, 0.01)
        self.assertAlmostEqual(cosmo.proton_mass_mev, 938.272, places=3)
        self.assertGreater(cosmo.t_wall_gyr, 40.0)
        self.assertLess(cosmo.t_wall_gyr, 55.0)
        # Derived φ_hom is smaller than legacy apparent-age H0 bridge.
        self.assertLess(cosmo.phi_hom_m_s2, g.phi_acceleration_homogeneous_si())
        self.assertAlmostEqual(cosmo.phi_hom_m_s2, 2.0 * d.C_LIGHT * cosmo.h0_si)

    def test_xi_propagation_is_one(self) -> None:
        self.assertEqual(d.XI_PROPAGATION, 1.0)


class TestGeometryOnlyPhi(unittest.TestCase):
    def test_no_seed_class_in_state(self) -> None:
        # Diffuse dwarf would be "seed" in legacy WHIM — derived path has no such field.
        dwarf = FakeMaster("DDO154", 10, 64.0, 0.37, 12.0, 0.05, 0.08, 1.5, 47.0, 4.0)
        spiral = FakeMaster("NGC3198", 5, 73.0, 3.14, 120.0, 5.0, 0.5, 0.0, 150.0, 13.8)
        s_d = d.derived_phi_part(dwarf, 1.0)
        s_s = d.derived_phi_part(spiral, 5.0)
        self.assertNotIn("seed_class", s_d.as_dict())
        self.assertGreater(s_d.gas_fraction, s_s.gas_fraction)
        self.assertGreater(s_d.phi_combined_m_s2, 0.0)
        self.assertGreater(s_s.phi_combined_m_s2, 0.0)

    def test_gas_fraction_continuous(self) -> None:
        gas = FakeMaster("GAS", 5, 60.0, 2.0, 50.0, 1.0, 2.0, 8.0, 100.0, 10.0)
        star = FakeMaster("STAR", 5, 60.0, 2.0, 50.0, 10.0, 0.1, 8.0, 100.0, 10.0)
        self.assertGreater(d.gas_baryon_fraction(gas), 0.5)
        self.assertLess(d.gas_baryon_fraction(star), 0.1)

    def test_coherence_from_geometry_only(self) -> None:
        master = FakeMaster("NGC2403", 5, 62.0, 2.0, 90.0, 2.0, 0.4, 8.0, 135.0, 3.2)
        c, tort, mis = d.geometric_coherence(master, 2.0)
        self.assertGreater(c, 0.0)
        self.assertLessEqual(c, 1.0)
        self.assertGreaterEqual(tort, 0.0)
        self.assertGreaterEqual(mis, 0.0)
        self.assertLessEqual(mis, 1.0)

    def test_b_hom_dresses_cosmic_floor(self) -> None:
        master = FakeMaster("NGC3198", 5, 73.0, 3.14, 120.0, 5.0, 0.5, 10.0, 150.0, 13.8)
        on = d.DerivedDynamicsOptions(
            use_homogeneous_dress=True, use_whim_boundary=False, use_thermal_screen=False
        )
        off = d.DerivedDynamicsOptions(
            use_homogeneous_dress=False, use_whim_boundary=False, use_thermal_screen=False
        )
        s_on = d.derived_phi_part(master, 5.0, options=on)
        s_off = d.derived_phi_part(master, 5.0, options=off)
        self.assertEqual(s_off.b_hom, 1.0)
        self.assertGreater(s_on.gas_fraction, 0.0)
        self.assertNotEqual(s_on.b_hom, 1.0)
        self.assertAlmostEqual(
            s_on.phi_cosmic_m_s2 / max(s_off.phi_cosmic_m_s2, 1e-30),
            s_on.b_hom,
            places=6,
        )

    def test_thermal_screen_kills_hot_dwarfs(self) -> None:
        # Low-V dwarf: ℓ_th ≪ R_d → retention ≪ 1 at disk scale
        dwarf = FakeMaster("UGC07577", 10, 63.0, 0.90, 54.0, 0.05, 0.1, 2.0, 18.0, 4.0)
        spiral = FakeMaster("NGC3198", 5, 73.0, 3.14, 120.0, 5.0, 0.5, 10.0, 150.0, 13.8)
        s_d = d.derived_phi_part(dwarf, dwarf.rdisk_kpc)
        s_s = d.derived_phi_part(spiral, spiral.rdisk_kpc)
        self.assertLess(s_d.thermal_screen_retention, 0.4)
        self.assertGreater(s_s.thermal_screen_retention, 0.6)
        self.assertGreater(s_d.thermal_activity, s_s.thermal_activity)

    def test_thermal_hotter_at_centre(self) -> None:
        # Isolated disks: hot centre loses screen first; cold edge recovers.
        dwarf = FakeMaster("UGC07577", 10, 63.0, 0.90, 54.0, 0.05, 0.1, 2.0, 18.0, 4.0)
        s_in = d.derived_phi_part(dwarf, 0.1 * dwarf.rdisk_kpc)
        s_out = d.derived_phi_part(dwarf, 3.0 * dwarf.rdisk_kpc)
        self.assertLess(s_in.thermal_screen_retention, s_out.thermal_screen_retention)
        self.assertGreater(s_in.thermal_activity, s_out.thermal_activity)
        self.assertAlmostEqual(
            d.local_thermal_hotness(0.0, dwarf.rdisk_kpc), 1.0, places=10
        )
        self.assertLess(d.local_thermal_hotness(dwarf.rdisk_kpc, dwarf.rdisk_kpc), 0.6)

    def test_thermal_retention_formula(self) -> None:
        # Cool/fast: R_th ≪ ℓ_th → A₀ = 0 → full retention everywhere
        c0, _, a0, h0 = d.thermal_screen_retention(250.0e3, 0.5, 1.0)
        self.assertEqual(a0, 0.0)
        self.assertAlmostEqual(c0, 1.0)
        self.assertAlmostEqual(h0, 1.0 / (1.0 + 0.5 / 1.0), places=10)
        # Hot dwarf: A_R = A₀ · h(r); C_th = 1/(1+(γ/2)A_R)
        c, l_th, a, h = d.thermal_screen_retention(50.0e3, 1.0, 2.0)
        self.assertAlmostEqual(c, 1.0 / (1.0 + 0.5 * d.GAMMA * a), places=10)
        self.assertGreater(l_th, 0.0)
        self.assertGreater(a, 0.0)
        self.assertAlmostEqual(h, 1.0 / (1.0 + 1.0 / 2.0), places=10)

    def test_thermal_scale_uses_reff(self) -> None:
        # Extended half-light: R_th = max(R_d, R_eff) strengthens the gate.
        compact = FakeMaster(
            "C", 8, 60.0, 2.75, 300.0, 12.0, 2.0, 16.0, 0.0, 10.0, reff_kpc=2.0
        )
        extended = FakeMaster(
            "E", 8, 60.0, 2.75, 300.0, 12.0, 2.0, 16.0, 0.0, 10.0, reff_kpc=4.18
        )
        self.assertAlmostEqual(d.thermal_scale_radius_kpc(compact), 2.75)
        self.assertAlmostEqual(d.thermal_scale_radius_kpc(extended), 4.18)
        s_c = d.derived_phi_part(compact, 2.75)
        s_e = d.derived_phi_part(extended, 2.75)
        self.assertLess(s_e.thermal_screen_retention, s_c.thermal_screen_retention)


if __name__ == "__main__":
    unittest.main()

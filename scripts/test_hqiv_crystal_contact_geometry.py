"""Tests for crystal lattice contact geometry."""

from __future__ import annotations

import unittest

from hqiv_lab.crystal_geometry import (
    closed_atomic_mass_amu,
    comparison_regime_for_species,
    covalent_network_bond_length_angstrom,
    expected_contact_xi_for_crystal,
    ionic_lattice_nearest_neighbor_angstrom,
    ionic_rocksalt_lattice_dress,
    metallic_unified_nearest_neighbor_angstrom,
    rocksalt_lattice_parameter_angstrom,
)


class TestCrystalContactGeometry(unittest.TestCase):
    def test_ionic_rocksalt_dress_at_least_one(self) -> None:
        self.assertGreaterEqual(ionic_rocksalt_lattice_dress(6), 1.0)

    def test_nacl_lattice_nn_derived_not_tabulated(self) -> None:
        nn = ionic_lattice_nearest_neighbor_angstrom(11, 17)
        self.assertGreater(nn, 2.0)
        self.assertLess(nn, 3.5)
        a = rocksalt_lattice_parameter_angstrom(nn)
        self.assertAlmostEqual(a, 2.0 * nn)

    def test_nacl_regime_is_solid_lattice(self) -> None:
        self.assertEqual(
            comparison_regime_for_species("NaCl", z_i=11, z_j=17),
            "solid_lattice",
        )

    def test_h2_regime_is_gas_vapor(self) -> None:
        self.assertEqual(comparison_regime_for_species("H2", z_i=1, z_j=1), "gas_vapor")

    def test_copper_unified_nn_between_branches(self) -> None:
        from hqiv_lab.crystal_geometry import (
            metallic_lattice_nearest_neighbor_angstrom,
            metallic_phi_pack_nearest_neighbor_angstrom,
            METALLIC_CLOSE_PACK_COORD,
        )
        import hqiv_lean_physics_primitives as lean

        nested = metallic_lattice_nearest_neighbor_angstrom(
            29, n_coord=METALLIC_CLOSE_PACK_COORD
        )
        phi = metallic_phi_pack_nearest_neighbor_angstrom(
            29, n_coord=METALLIC_CLOSE_PACK_COORD
        )
        # Bare α-blend sits between branches before peel/d¹⁰ dresses.
        bare = metallic_unified_nearest_neighbor_angstrom(29, n_coord=12, packed=False)
        self.assertGreater(bare, nested)
        self.assertLess(bare, phi)
        expected = (nested ** lean.ALPHA) * (phi ** (1.0 - lean.ALPHA))
        from hqiv_lab.crystal_geometry import metallic_open_d_peel_contract

        # Cu Madelung d≥9 → peel identity; bare equals the α-blend.
        self.assertAlmostEqual(metallic_open_d_peel_contract(29), 1.0, places=9)
        self.assertAlmostEqual(bare, expected, places=6)
        packed = metallic_unified_nearest_neighbor_angstrom(29, n_coord=12, packed=True)
        self.assertLess(packed, bare)

    def test_alkali_bcc_density_uses_bravais_not_fcc(self) -> None:
        from hqiv_lab.crystal_geometry import (
            metallic_bravais_from_coordination,
            metallic_density_g_cm3,
            fcc_density_g_cm3,
        )

        n_atoms, k = metallic_bravais_from_coordination(8)
        self.assertEqual(n_atoms, 2)
        self.assertAlmostEqual(k, 2.0 / (3.0 ** 0.5), places=9)
        # Same nn: BCC density is ~8% below FCC.
        nn = 3.0
        mass = 7.0
        rho_bcc = metallic_density_g_cm3(mass, nn, n_coord=8)
        rho_fcc = fcc_density_g_cm3(mass, nn)
        self.assertLess(rho_bcc, rho_fcc)
        self.assertAlmostEqual(rho_bcc / rho_fcc, 0.9185585, places=4)

    def test_period_channel_gates_phi_without_z_set(self) -> None:
        from hqiv_lab.crystal_geometry import (
            metallic_period_channel_weight,
            metallic_phi_pack_nearest_neighbor_angstrom,
        )

        self.assertAlmostEqual(metallic_period_channel_weight(3), 1.0, places=9)
        self.assertLess(metallic_period_channel_weight(11), 0.2)
        # Li (period-2) uses homo branch; Na uses lattice max — continuous gate.
        li = metallic_phi_pack_nearest_neighbor_angstrom(3)
        na = metallic_phi_pack_nearest_neighbor_angstrom(11)
        self.assertGreater(na, li)

    def test_metallic_coordination_from_capacity_not_z_set(self) -> None:
        import hqiv_metallic_bond_network as mbn

        self.assertEqual(mbn.metallic_coordination(3), 8)   # Li
        self.assertEqual(mbn.metallic_coordination(11), 8)  # Na
        self.assertEqual(mbn.metallic_coordination(13), 12) # Al
        self.assertEqual(mbn.metallic_coordination(29), 12) # Cu
        self.assertTrue(mbn.is_metallic_element(13))
        self.assertTrue(mbn.is_metallic_element(29))
        self.assertFalse(mbn.is_metallic_element(9))   # F: cap=1 but V=7
        self.assertFalse(mbn.is_metallic_element(14))  # Si: cap=4
        self.assertFalse(mbn.is_metallic_element(32))  # Ge: outer V=4 → covalent
        self.assertTrue(mbn.is_metallic_element(31))   # Ga: outer V=3 shed metal

    def test_derive_crystal_kind_from_capacity(self) -> None:
        from hqiv_lab.crystal_geometry import derive_crystal_kind
        from hqiv_lab.species_panel import CONDENSED_SPECIES_PANEL

        self.assertEqual(derive_crystal_kind((11, 17)), "ionic")
        self.assertEqual(derive_crystal_kind((3,)), "metallic")
        self.assertEqual(derive_crystal_kind((14,)), "covalent_network")
        self.assertEqual(derive_crystal_kind((32,)), "covalent_network")
        self.assertEqual(derive_crystal_kind(()), "molecular")
        for entry in CONDENSED_SPECIES_PANEL:
            if entry.z_values:
                self.assertEqual(
                    entry.resolved_crystal_kind(),
                    entry.crystal_kind,
                    msg=entry.molecule,
                )

    def test_pblock_valence_open_helps_aluminum_not_alkali(self) -> None:
        from hqiv_lab.crystal_geometry import metallic_pblock_valence_open_dress

        self.assertAlmostEqual(metallic_pblock_valence_open_dress(3, n_coord=8), 1.0)
        self.assertAlmostEqual(metallic_pblock_valence_open_dress(29, n_coord=12), 1.0)
        self.assertGreater(metallic_pblock_valence_open_dress(13, n_coord=12), 1.0)
        self.assertGreater(metallic_pblock_valence_open_dress(12, n_coord=12), 1.0)
        # Excess-over-alkali floor: Al (cap−1=2) opens more than Mg (cap−1=1).
        self.assertGreater(
            metallic_pblock_valence_open_dress(13, n_coord=12),
            metallic_pblock_valence_open_dress(12, n_coord=12),
        )

    def test_covalent_steric_fade_identity_on_carbon(self) -> None:
        from hqiv_lab.crystal_geometry import (
            covalent_network_em_packing_dress,
            covalent_network_steric_fade_dress,
        )

        self.assertAlmostEqual(covalent_network_steric_fade_dress(1.0, 0.8), 1.0)
        dress_c = covalent_network_em_packing_dress(6, coordination=4, em_feedback=True)
        dress_si = covalent_network_em_packing_dress(14, coordination=4, em_feedback=True)
        self.assertAlmostEqual(float(dress_c["em_dress"]["steric_fade"]), 1.0, places=9)
        self.assertLess(float(dress_si["em_dress"]["steric_fade"]), 1.0)

    def test_ionic_period_channel_steric_contracts_lif(self) -> None:
        from hqiv_lab.crystal_geometry import (
            ionic_lattice_nearest_neighbor_angstrom,
            ionic_period_channel_steric_dress,
            ionic_deep_cation_open_dress,
        )

        self.assertLess(ionic_period_channel_steric_dress(3, 9), 0.99)
        self.assertGreater(ionic_period_channel_steric_dress(11, 17), 0.999)
        packed = ionic_lattice_nearest_neighbor_angstrom(3, 9, packed=True)
        bare_pack = ionic_lattice_nearest_neighbor_angstrom(3, 9, packed=False)
        self.assertLess(packed, bare_pack)
        # KCl deep-cation open; NaF (period-2 anion) identity.
        self.assertGreater(ionic_deep_cation_open_dress(19, 17), 1.0)
        self.assertAlmostEqual(ionic_deep_cation_open_dress(11, 9), 1.0, places=9)

    def test_post_d_and_peel_metallic_dresses(self) -> None:
        from hqiv_lab.crystal_geometry import (
            metallic_d10_core_elongation,
            metallic_open_d_peel_contract,
            metallic_deep_bcc_open_dress,
            metallic_alkaline_earth_open_dress,
            metallic_unified_nearest_neighbor_angstrom,
            metallic_density_g_cm3,
            closed_atomic_mass_amu,
        )

        self.assertGreater(metallic_d10_core_elongation(30), 1.1)  # Zn
        self.assertGreater(metallic_d10_core_elongation(31), 1.2)  # Ga
        self.assertAlmostEqual(metallic_d10_core_elongation(13), 1.0)  # Al
        self.assertLess(metallic_open_d_peel_contract(26), 0.97)  # Fe continuous fade
        self.assertLess(metallic_open_d_peel_contract(28), 1.0)  # Ni d=8 continuous fade
        self.assertAlmostEqual(metallic_open_d_peel_contract(29), 1.0)  # Cu d≥9
        self.assertGreater(metallic_deep_bcc_open_dress(19, n_coord=8), 1.0)  # K
        self.assertAlmostEqual(metallic_deep_bcc_open_dress(11, n_coord=8), 1.0)
        self.assertGreater(metallic_alkaline_earth_open_dress(12), 1.0)  # Mg
        self.assertAlmostEqual(metallic_alkaline_earth_open_dress(30), 1.0)  # Zn d10
        from hqiv_lab.crystal_geometry import (
            metallic_bravais_kind,
            metallic_is_hcp_candidate,
            metallic_open_d_fade,
        )

        self.assertTrue(metallic_is_hcp_candidate(12))  # Mg
        self.assertFalse(metallic_is_hcp_candidate(30))  # Zn d10 → FCC
        self.assertEqual(metallic_bravais_kind(12), "hcp")
        self.assertEqual(metallic_bravais_kind(30), "fcc")
        self.assertAlmostEqual(metallic_open_d_fade(10), 0.0)
        self.assertAlmostEqual(metallic_open_d_fade(9), 0.0)
        self.assertAlmostEqual(metallic_open_d_fade(8), 0.2)
        # Zn density near NIST after d10 elong.
        nn = metallic_unified_nearest_neighbor_angstrom(30, n_coord=12)
        rho = metallic_density_g_cm3(closed_atomic_mass_amu(30), nn, n_coord=12, z=30)
        self.assertLess(abs(rho - 7.14) / 7.14 * 100.0, 5.0)
        # Ideal HCP density equals FCC at same nn.
        rho_hcp = metallic_density_g_cm3(24.3, 3.2, n_coord=12, bravais="hcp")
        rho_fcc = metallic_density_g_cm3(24.3, 3.2, n_coord=12, bravais="fcc")
        self.assertAlmostEqual(rho_hcp, rho_fcc, places=9)

    def test_bcc_residual_opens_period2_lithium(self) -> None:
        from hqiv_lab.crystal_geometry import metallic_undercoord_open_dress

        # Period-2 (w=1) at BCC must not freeze to identity.
        self.assertGreater(metallic_undercoord_open_dress(8, period_weight=1.0), 1.0)
        # Close-pack always identity.
        self.assertAlmostEqual(
            metallic_undercoord_open_dress(12, period_weight=1.0), 1.0, places=12
        )

    def test_lif_surplus_promotes_light_cation(self) -> None:
        import hqiv_ionic_bond_network as ibn

        lif = ibn.SALTS["LIF"]
        nacl = ibn.SALTS["NACL"]
        n_c, _ = ibn.ionic_surplus_electron_counts(lif.cation, lif.anion)
        self.assertEqual(n_c, 9)
        # Promoted LiF surplus matches Na-class plateau (~210 eV) before period dress.
        self.assertGreater(abs(ibn.ionic_bond_surplus_ev(lif.cation, lif.anion)), 150.0)
        self.assertAlmostEqual(
            abs(ibn.ionic_bond_surplus_ev(lif.cation, lif.anion)),
            abs(ibn.ionic_bond_surplus_ev(nacl.cation, nacl.anion)),
            places=1,
        )

    def test_anion_period_melt_dress_identity_on_lif(self) -> None:
        import hqiv_ionic_bond_network as ibn

        # Same-period (LiF) → identity; mixed (NaF) → boost + fluoride residual.
        self.assertAlmostEqual(ibn.ionic_anion_period_melt_dress(3, 9), 1.0, places=9)
        naf = ibn.ionic_anion_period_melt_dress(11, 9)
        self.assertGreater(ibn.ionic_anion_period_melt_dress(11, 9), 1.1)
        # Fluoride residual is strictly > 1 on NaF (excess > 0, w_a = 1).
        import hqiv_lean_physics_primitives as lean

        excess = 3.0 / 2.0 - 1.0  # P_Na / P_F - 1
        residual = 1.0 + lean.STRONG_CHANNEL_FRACTION * (lean.GAMMA / 8.0) * 1.0 * excess
        self.assertGreater(residual, 1.0)
        self.assertGreater(naf, 1.0 + lean.STRONG_CHANNEL_FRACTION * lean.GAMMA * (1.0 - (2.0 / 3.0) ** 6) - 1e-9)
        # Period-1 H channel weight is capped at 1 (not (2/1)^cap).
        self.assertAlmostEqual(ibn.ionic_period_channel_weight(1), 1.0, places=12)
        from hqiv_lab.crystal_geometry import (
            ionic_is_hydride_pair,
            ionic_hydride_lattice_dress,
            ionic_lattice_nearest_neighbor_angstrom,
        )

        self.assertTrue(ionic_is_hydride_pair(3, 1))
        self.assertFalse(ionic_is_hydride_pair(3, 9))
        self.assertGreater(ionic_hydride_lattice_dress(), 1.0)
        # LiH condensed nn near ~2.0 Å (not rocksalt-over-elongated).
        self.assertLess(ionic_lattice_nearest_neighbor_angstrom(3, 1), 2.2)
        self.assertGreater(ionic_lattice_nearest_neighbor_angstrom(3, 1), 1.8)
        self.assertLess(ibn.ionic_anion_period_polarizability_softener(9), 0.9)
        self.assertGreater(ibn.ionic_anion_period_polarizability_softener(17), 0.95)
        # Cation deeper than anion (KCl) softens; same-period (NaCl) identity.
        self.assertAlmostEqual(
            ibn.ionic_cation_period_polarizability_softener(11, 17), 1.0, places=9
        )
        self.assertLess(ibn.ionic_cation_period_polarizability_softener(19, 17), 0.95)
        self.assertLess(
            ibn.ionic_period_polarizability_softener(19, 17),
            ibn.ionic_anion_period_polarizability_softener(17),
        )

    def test_si_covalent_bond_in_physical_range(self) -> None:
        bond = covalent_network_bond_length_angstrom(14, coordination=4)
        self.assertGreater(bond, 2.0)
        self.assertLess(bond, 2.6)
        # Continuous period-channel weight applies EM/nuclear dress (no hard gate).
        from hqiv_lab.crystal_geometry import covalent_network_em_packing_dress

        dress = covalent_network_em_packing_dress(14, coordination=4, em_feedback=True)
        self.assertTrue(dress["em_feedback_applied"])
        self.assertLess(float(dress["period_channel_weight"]), 0.1)
        self.assertNotAlmostEqual(
            float(dress["bond_length_angstrom"]), bond, places=3
        )

    def test_ge_covalent_bond_in_physical_range(self) -> None:
        bond = covalent_network_bond_length_angstrom(32, coordination=4)
        self.assertGreater(bond, 2.2)
        self.assertLess(bond, 2.9)
        from hqiv_lab.crystal_geometry import covalent_network_em_packing_dress

        dress = covalent_network_em_packing_dress(32, coordination=4, em_feedback=True)
        self.assertTrue(dress["em_feedback_applied"])
        # Nuclear/optical branch contracts Ge relative to bare inert-core length.
        self.assertLess(
            float(dress["bond_length_angstrom"]),
            float(dress["bond_length_bare_angstrom"]),
        )

    def test_carbon_em_open_packing_dress_activates(self) -> None:
        from hqiv_lab.crystal_geometry import covalent_network_em_packing_dress

        dress = covalent_network_em_packing_dress(6, coordination=4, em_feedback=True)
        self.assertTrue(dress["length_reliable"])
        self.assertTrue(dress["em_feedback_applied"])
        self.assertAlmostEqual(float(dress["period_channel_weight"]), 1.0, places=9)
        self.assertGreater(float(dress["network_open_channel_packing_scale"]), 1.0)
        self.assertGreater(
            float(dress["bond_length_angstrom"]),
            float(dress["bond_length_bare_angstrom"]),
        )

    def test_crystal_xi_routing(self) -> None:
        self.assertAlmostEqual(
            expected_contact_xi_for_crystal(crystal_kind="ionic", z_values=(11, 17)),
            4 + 1 / 3,
            places=3,
        )
        self.assertAlmostEqual(
            expected_contact_xi_for_crystal(crystal_kind="metallic", z_values=(29,)),
            7.0,
            places=3,
        )
        self.assertAlmostEqual(
            expected_contact_xi_for_crystal(crystal_kind="covalent_network", z_values=(14,)),
            6.0,
            places=3,
        )

    def test_si_closed_mass_reliable(self) -> None:
        from hqiv_lab.crystal_geometry import mass_reliable_for_crystal

        self.assertTrue(mass_reliable_for_crystal(14))
        self.assertTrue(mass_reliable_for_crystal(29))
        self.assertAlmostEqual(closed_atomic_mass_amu(14), 29.96, places=1)
        self.assertAlmostEqual(closed_atomic_mass_amu(29), 62.8, places=0)

    def test_nuclear_packing_dress_contracts_when_A_exceeds_2Z(self) -> None:
        from hqiv_lab.crystal_geometry import nuclear_packing_dress

        # Cu: A=63, 2Z=58 → dress < 1
        self.assertLess(nuclear_packing_dress(63, 29), 1.0)
        # A=2Z floor → unity
        self.assertAlmostEqual(nuclear_packing_dress(58, 29), 1.0, places=9)

    def test_copper_packed_nn_below_bare(self) -> None:
        bare = metallic_unified_nearest_neighbor_angstrom(29, packed=False)
        packed = metallic_unified_nearest_neighbor_angstrom(29, packed=True)
        self.assertLess(packed, bare)
        self.assertGreater(packed, 2.3)

    def test_nuclear_packing_open_identity_at_floor(self) -> None:
        from hqiv_lab.crystal_geometry import nuclear_packing_open_dress

        self.assertAlmostEqual(nuclear_packing_open_dress(1.0), 1.0, places=12)
        self.assertGreater(nuclear_packing_open_dress(0.97), 1.0)

    def test_ionic_character_lattice_identity_at_zero(self) -> None:
        from hqiv_lab.crystal_geometry import ionic_character_lattice_dress

        self.assertAlmostEqual(ionic_character_lattice_dress(0.0), 1.0, places=12)
        self.assertLess(ionic_character_lattice_dress(0.3), 1.0)


if __name__ == "__main__":
    unittest.main()

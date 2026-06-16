#!/usr/bin/env python3
"""Tests for ionic bond network spine."""

import unittest

import hqiv_curvature_contact_network as ccn
import hqiv_derived_chemistry as hdc
import hqiv_dynamic_binding_chart as chart
import hqiv_ionic_bond_network as ibn


class TestIonicBondNetwork(unittest.TestCase):
    def test_lih_ionic_bond_kind(self) -> None:
        self.assertEqual(
            ibn.classify_bond_kind("LiH", 3, 1),
            ccn.ContactKind.IONIC_BOND,
        )

    def test_hf_stays_covalent(self) -> None:
        self.assertEqual(
            ibn.classify_bond_kind("HF", 9, 1),
            ccn.ContactKind.COVALENT_BOND,
        )

    def test_lih_ionic_electron_partition(self) -> None:
        cat, an = ibn.ionic_fragments_from_neutral_pair("Li", 3, 3, "H", 1, 1)
        self.assertEqual((cat.electrons, an.electrons), (2, 2))
        self.assertEqual((cat.formal_charge, an.formal_charge), (1, -1))

    def test_nacl_formula_mass_derived(self) -> None:
        m = ibn.NACL_SALT.formula_mass_amu
        self.assertGreater(m, 50.0)
        self.assertLess(m, 70.0)

    def test_nacl_hydration_contacts_positive(self) -> None:
        self.assertGreater(ibn.derived_hydration_contact_count(ibn.NACL_SALT.cation), 0)
        self.assertGreater(ibn.derived_hydration_contact_count(ibn.NACL_SALT.anion), 0)

    def test_ionic_network_has_ionic_contact(self) -> None:
        net = ibn.build_ionic_salt_network(ibn.NACL_SALT)
        kinds = {c.kind for c in net.contacts}
        self.assertIn(ccn.ContactKind.IONIC_BOND, kinds)

    def test_lih_gmtkn55_network_ionic_edge(self) -> None:
        bench = next(b for b in chart.GMTKN55_SUITE if b.name == "LiH")
        net = ccn.build_network_from_molecule(
            bench.name, bench.fragments, bench.bonds
        )
        kinds = {c.kind for c in net.contacts}
        self.assertIn(ccn.ContactKind.IONIC_BOND, kinds)

    def test_derived_amu_h2o_order_of_magnitude(self) -> None:
        m = hdc.derived_atomic_mass_amu(8, 8)
        self.assertGreater(m, 15.0)
        self.assertLess(m, 17.0)

    def test_derived_liquid_water_near_unity(self) -> None:
        rho = hdc.derived_liquid_reference_density_g_cm3("H2O")
        self.assertGreater(rho, 0.9)
        self.assertLess(rho, 1.2)


if __name__ == "__main__":
    unittest.main()

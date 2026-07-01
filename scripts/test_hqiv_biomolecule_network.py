#!/usr/bin/env python3
"""Tests: Watson–Crick hydrogen-bond counts and peptide bond order from the HQIV spine."""

from __future__ import annotations

import unittest

import hqiv_biomolecule_network as bio


class HydrogenBondRoleTests(unittest.TestCase):
    def test_proton_bearer_is_donor(self) -> None:
        self.assertEqual(bio.hbond_role(bio.EdgeSite("N6", "N", True)), bio.HBOND_DONOR)

    def test_lone_pair_site_is_acceptor(self) -> None:
        self.assertEqual(bio.hbond_role(bio.EdgeSite("O4", "O", False)), bio.HBOND_ACCEPTOR)

    def test_roles_derived_only_from_proton_presence(self) -> None:
        # element identity (N vs O) does not change the role; the proton does
        self.assertEqual(
            bio.hbond_role(bio.EdgeSite("x", "N", True)),
            bio.hbond_role(bio.EdgeSite("y", "O", True)),
        )


class WatsonCrickCountTests(unittest.TestCase):
    def test_adenine_thymine_has_two_hydrogen_bonds(self) -> None:
        r = bio.watson_crick_pair("A", "T")
        self.assertEqual(r.hydrogen_bonds, 2)
        self.assertTrue(r.is_canonical_watson_crick)

    def test_guanine_cytosine_has_three_hydrogen_bonds(self) -> None:
        r = bio.watson_crick_pair("G", "C")
        self.assertEqual(r.hydrogen_bonds, 3)
        self.assertTrue(r.is_canonical_watson_crick)

    def test_gc_is_more_bonded_than_at(self) -> None:
        # the basis of GC-rich duplex stability — derived, not assumed
        self.assertGreater(
            bio.watson_crick_pair("G", "C").hydrogen_bonds,
            bio.watson_crick_pair("A", "T").hydrogen_bonds,
        )

    def test_uracil_pairs_like_thymine(self) -> None:
        self.assertEqual(
            bio.watson_crick_pair("A", "U").hydrogen_bonds,
            bio.watson_crick_pair("A", "T").hydrogen_bonds,
        )

    def test_mismatches_are_non_canonical(self) -> None:
        for x, y in (("G", "U"), ("A", "C"), ("A", "G")):
            self.assertFalse(bio.watson_crick_pair(x, y).is_canonical_watson_crick)

    def test_derived_partners_are_watson_crick_complements(self) -> None:
        self.assertEqual(bio.canonical_pairing_partner("G"), "C")
        self.assertEqual(bio.canonical_pairing_partner("C"), "G")
        self.assertEqual(bio.canonical_pairing_partner("T"), "A")
        self.assertIn("T", bio.canonical_pairing_partner("A"))


class PeptideBondTests(unittest.TestCase):
    def test_amide_cn_has_partial_double_character(self) -> None:
        pep = bio.peptide_bond_readout()
        self.assertGreater(pep.c_n_bond_order, 1.0)
        self.assertTrue(pep.c_n_has_partial_double)

    def test_carbonyl_is_stronger_than_amide_cn(self) -> None:
        pep = bio.peptide_bond_readout()
        self.assertGreater(pep.c_o_bond_order, pep.c_n_bond_order)

    def test_centres_are_three_coordinate_sp2(self) -> None:
        pep = bio.peptide_bond_readout()
        self.assertEqual(pep.carbonyl_c_coordination, 3)
        self.assertEqual(pep.amide_n_coordination, 3)


class AromaticRingTests(unittest.TestCase):
    def test_benzene_is_aromatic_and_planar(self) -> None:
        ring = bio.aromatic_ring_readout("benzene")
        self.assertEqual(ring.ring_size, 6)
        self.assertAlmostEqual(ring.min_ring_order, 1.5)
        self.assertAlmostEqual(ring.max_ring_order, 1.5)
        self.assertTrue(ring.all_delocalised)
        self.assertTrue(ring.planar)

    def test_n_heterocycles_are_delocalised(self) -> None:
        for name in ("pyridine", "pyrimidine", "imidazole"):
            ring = bio.aromatic_ring_readout(name)
            self.assertTrue(ring.all_delocalised, msg=f"{name} ring should be delocalised")
            self.assertTrue(ring.planar, msg=f"{name} ring should be planar")

    def test_pyrimidine_ring_is_kekule_average(self) -> None:
        # the cytosine/thymine/uracil six-ring resolves to the benzene-like 1.5
        ring = bio.aromatic_ring_readout("pyrimidine")
        self.assertAlmostEqual(ring.min_ring_order, 1.5)
        self.assertAlmostEqual(ring.max_ring_order, 1.5)


class NucleobaseTests(unittest.TestCase):
    def test_all_bases_planar_and_delocalised(self) -> None:
        for name in ("uracil", "thymine", "cytosine", "adenine", "guanine"):
            base = bio.nucleobase_readout(name)
            self.assertTrue(base.planar, msg=f"{name} framework should be planar")
            self.assertTrue(base.all_skeleton_delocalised, msg=f"{name} should be delocalised")
            self.assertGreater(base.min_ring_order, 1.0)

    def test_thymine_methyl_does_not_pucker_ring(self) -> None:
        # the 5-methyl is sp3 but pendant; the conjugated ring stays planar
        self.assertTrue(bio.nucleobase_readout("thymine").planar)

    def test_carbonyls_are_double_leaning(self) -> None:
        for name in ("uracil", "cytosine", "guanine"):
            base = bio.nucleobase_readout(name)
            self.assertTrue(base.carbonyl_orders)
            for order in base.carbonyl_orders:
                self.assertGreater(order, 1.5)

    def test_uracil_has_two_carbonyls_no_amine(self) -> None:
        base = bio.nucleobase_readout("uracil")
        self.assertEqual(len(base.carbonyl_orders), 2)
        self.assertEqual(base.exocyclic_amine_orders, ())

    def test_exocyclic_amine_is_partial_double(self) -> None:
        # cytosine/adenine/guanine NH2 conjugates into the ring → order strictly between 1 and 2
        for name in ("cytosine", "adenine", "guanine"):
            base = bio.nucleobase_readout(name)
            self.assertTrue(base.exocyclic_amine_orders)
            for order in base.exocyclic_amine_orders:
                self.assertGreater(order, 1.0)
                self.assertLess(order, 2.0)


class RingCountWidthTests(unittest.TestCase):
    def test_ring_count_is_cyclomatic_number(self) -> None:
        # pyrimidines 1 ring, purines 2 rings — from E−V+1, no table
        self.assertEqual(bio.nucleobase_ring_count("uracil"), 1)
        self.assertEqual(bio.nucleobase_ring_count("cytosine"), 1)
        self.assertEqual(bio.nucleobase_ring_count("adenine"), 2)
        self.assertEqual(bio.nucleobase_ring_count("guanine"), 2)

    def test_class_follows_from_ring_count(self) -> None:
        self.assertEqual(bio.nucleobase_class("adenine"), "purine")
        self.assertEqual(bio.nucleobase_class("uracil"), "pyrimidine")

    def test_canonical_pairs_are_purine_plus_pyrimidine(self) -> None:
        for x, y in (("A", "T"), ("G", "C")):
            w = bio.base_pair_width_readout(x, y)
            self.assertTrue(w.is_purine_pyrimidine)

    def test_uniform_helix_width_constant_ring_sum(self) -> None:
        # the isostericity: every canonical rung totals the same ring count
        at = bio.base_pair_width_readout("A", "T").total_ring_count
        gc = bio.base_pair_width_readout("G", "C").total_ring_count
        self.assertEqual(at, gc)
        self.assertEqual(at, 3)


class RingStrainTests(unittest.TestCase):
    def test_sp2_prefers_six_ring(self) -> None:
        rs = bio.ring_strain_readout("sp2")
        self.assertEqual(rs.minimal_ring_size, 6)
        self.assertAlmostEqual(rs.strain_by_size_deg[6], 0.0, places=6)

    def test_sp3_prefers_five_ring(self) -> None:
        rs = bio.ring_strain_readout("sp3")
        self.assertEqual(rs.minimal_ring_size, 5)

    def test_biological_rings_are_the_minima(self) -> None:
        # aromatic base 6-ring (sp2) and furanose sugar 5-ring (sp3) are the strain minima
        self.assertEqual(bio.ring_strain_readout("sp2").minimal_ring_size, 6)
        self.assertEqual(bio.ring_strain_readout("sp3").minimal_ring_size, 5)


class PayloadTests(unittest.TestCase):
    def test_payload_has_canonical_counts(self) -> None:
        payload = bio.build_payload()
        counts = {row["pair"]: row["hydrogen_bonds"] for row in payload["canonical_base_pairs"]}
        self.assertEqual(counts["A·T"], 2)
        self.assertEqual(counts["G·C"], 3)

    def test_spectator_contact_is_one_plus_half_gamma(self) -> None:
        self.assertAlmostEqual(bio.SPECTATOR_HALF_MONOGAMY_CONTACT, 1.2)


if __name__ == "__main__":
    unittest.main()

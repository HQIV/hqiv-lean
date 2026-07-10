"""Sparse dynamic atom-site folding witnesses."""

from __future__ import annotations

import math
import unittest

from hqiv_lab.derived_bond_geometry import (
    bound_system_participation,
    dynamic_peptide_bond_length_n_ca,
    peptide_bond_length_n_ca,
)
from hqiv_lab.miniprotein_atom_sites import (
    dress_atom_contact_targets,
    expand_atom_contacts_with_backbone,
    flat_site_list,
    tertiary_to_atom_contacts,
)
from hqiv_lab.miniprotein_backbone import (
    hqiv_peptide_bond_geometry,
    hqiv_peptide_bond_geometry_at_bound,
    peptide_bond_growth_trace,
    place_backbone_atom_state,
    ramachandran_extended_rad,
)
from hqiv_lab.miniprotein_basin import dihedrals_from_spine
from hqiv_lab.miniprotein_contacts import TertiaryContact, build_tertiary_contact_graph
from hqiv_lab.miniprotein_osh import (
    atom_contact_sse,
    build_atom_contact_network_matrix,
    prepare_atom_contacts,
)
from hqiv_lab.protein_solvent_phase import PROTEIN_FOLDING_TEMPERATURE_K


class TestDynamicBondGeometry(unittest.TestCase):
    def test_full_bound_equals_static_n_ca(self) -> None:
        n = 20
        static = peptide_bond_length_n_ca()
        dynamic_full = dynamic_peptide_bond_length_n_ca(n, n)
        self.assertAlmostEqual(static, dynamic_full, places=9)

    def test_participation_endpoint(self) -> None:
        self.assertAlmostEqual(bound_system_participation(20, 20), 1.0)
        self.assertAlmostEqual(bound_system_participation(20, 1), 0.05)

    def test_growth_trace_length(self) -> None:
        seq = "GGG"
        ext = tuple(ramachandran_extended_rad() for _ in seq)
        trace = peptide_bond_growth_trace(seq, ext)
        self.assertEqual(len(trace), 3)
        self.assertEqual(trace[-1].bound_count, 3)


class TestBackboneAtomState(unittest.TestCase):
    def test_five_sites_per_residue(self) -> None:
        seq = "ALA"
        ext = tuple(ramachandran_extended_rad() for _ in seq)
        state = place_backbone_atom_state(seq, ext)
        self.assertEqual(len(state.n_atoms), 3)
        self.assertEqual(len(state.o_atoms), 3)
        self.assertEqual(len(state.sc_centroids), 3)
        sites = flat_site_list(state)
        self.assertEqual(len(sites), 15)

    def test_backbone_bond_lengths_reasonable(self) -> None:
        seq = "GG"
        ext = tuple(ramachandran_extended_rad() for _ in seq)
        state = place_backbone_atom_state(seq, ext)
        n0, ca0, c0, o0 = state.n_atoms[0], state.ca_atoms[0], state.c_atoms[0], state.o_atoms[0]
        d_n_ca = math.dist(n0, ca0)
        d_ca_c = math.dist(ca0, c0)
        d_c_o = math.dist(c0, o0)
        g = hqiv_peptide_bond_geometry()
        self.assertAlmostEqual(d_n_ca, g.n_ca, delta=0.05)
        self.assertAlmostEqual(d_ca_c, g.ca_c, delta=0.05)
        self.assertAlmostEqual(d_c_o, g.c_o, delta=0.05)


class TestAtomContacts(unittest.TestCase):
    def test_tertiary_projects_to_ca_or_sc(self) -> None:
        contacts = (
            TertiaryContact(0, 3, 5.0, "helix_i3"),
            TertiaryContact(1, 4, 4.5, "hydrophobic"),
        )
        atom = tertiary_to_atom_contacts(contacts)
        self.assertEqual(atom[0].i.kind, "CA")
        self.assertEqual(atom[1].i.kind, "SC")

    def test_sparse_not_dense(self) -> None:
        seq = "ACDEF"
        ss_map = {"H": (1, 2, 3), "C": (4, 5)}
        topo = build_tertiary_contact_graph(seq, ss_map, include_terminus=False)
        state = place_backbone_atom_state(seq, dihedrals_from_spine(seq, ss_map))
        atom = expand_atom_contacts_with_backbone(tertiary_to_atom_contacts(topo), state)
        n_sites = len(seq) * 5
        self.assertLess(len(atom), n_sites * (n_sites - 1) // 2)

    def test_solvent_dress_scales_hydrophobic(self) -> None:
        contacts = (TertiaryContact(0, 4, 4.0, "hydrophobic"),)
        state = place_backbone_atom_state("ACDEF", dihedrals_from_spine("ACDEF", {"C": (1, 2, 3, 4, 5)}))
        raw = prepare_atom_contacts(contacts, state, temperature_k=None)
        dressed = dress_atom_contact_targets(
            tertiary_to_atom_contacts(contacts),
            temperature_k=PROTEIN_FOLDING_TEMPERATURE_K,
        )
        self.assertGreater(dressed[0].target_angstrom, raw[0].target_angstrom)


class TestOSHAtomMatrix(unittest.TestCase):
    def test_atom_network_site_count(self) -> None:
        seq = "GGGG"
        ss_map = {"C": (1, 2, 3, 4)}
        dihedrals = dihedrals_from_spine(seq, ss_map)
        state = place_backbone_atom_state(seq, dihedrals)
        contacts = build_tertiary_contact_graph(seq, ss_map, include_terminus=False)
        atom_c = prepare_atom_contacts(contacts, state)
        net = build_atom_contact_network_matrix(seq, atom_c, state)
        self.assertEqual(net.n_sites, 20)
        self.assertGreater(len(net.pairs), 0)
        sse = atom_contact_sse(state, atom_c)
        self.assertGreaterEqual(sse, 0.0)


if __name__ == "__main__":
    unittest.main()

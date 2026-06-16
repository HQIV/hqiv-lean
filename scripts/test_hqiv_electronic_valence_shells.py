#!/usr/bin/env python3
"""Electronic valence shell assignment (2s/2p/1s Compton ladder)."""

from __future__ import annotations

import math

import hqiv_electronic_valence_shells as evs
import hqiv_lean_physics_primitives as lean
from fragment_aware_bonded_horizon import BondGeometry, FragmentConfig


def test_oxygen_water_electronic_shells() -> None:
    m_s, m_p = evs.electronic_compton_shells(8)
    assert m_s == 4 and m_p == 3
    assert evs.electronic_shell_label(8, slot="s") == "2s"
    assert evs.electronic_shell_label(8, slot="p") == "2p"


def test_period3_electronic_shells() -> None:
    m_s, m_p = evs.electronic_compton_shells(17)
    assert m_s == 5 and m_p == 4
    assert evs.electronic_shell_label(16, slot="s") == "3s"
    assert evs.electronic_shell_label(16, slot="p") == "3p"


def test_nacl_compton_triplet_period3() -> None:
    frags = (FragmentConfig("Na", 11, 11), FragmentConfig("Cl", 17, 17))
    assert evs.chemistry_compton_triplet(frags) == (5, 4, 1)


def test_co_heteronuclear_triplet() -> None:
    frags = (FragmentConfig("C", 6, 6), FragmentConfig("O", 8, 8))
    assert evs.chemistry_compton_triplet(frags) == (4, 3, 4)


def test_homonuclear_bond_order() -> None:
    assert evs.homonuclear_bond_order(7) == 3
    assert evs.homonuclear_bond_order(8) == 2
    assert evs.homonuclear_bond_order(9) == 1


def test_heteronuclear_bond_order_cn_triple() -> None:
    assert evs.heteronuclear_bond_order(6, 7) == 3
    assert evs.covalent_bond_order(6, 7) == 3


def test_period3_hydride_compton_triplet() -> None:
    frags = (FragmentConfig("Cl", 17, 17), FragmentConfig("H", 1, 1))
    assert evs.chemistry_compton_triplet(frags) == (5, 4, 1)
    ph3 = (
        FragmentConfig("P", 15, 15),
        FragmentConfig("H", 1, 1),
        FragmentConfig("H", 1, 1),
        FragmentConfig("H", 1, 1),
    )
    assert evs.chemistry_compton_triplet(ph3) == (4, 3, 1)


def test_period_hydride_dissociation_dress() -> None:
    assert evs.period_hydride_dissociation_dress(9) == 1.0
    assert abs(evs.period_hydride_dissociation_dress(35) - 4 / 6) < 1e-9
    hcl = evs.period_hydride_dissociation_dress(17)
    assert abs(hcl - (4 / 5) * (1 - 0.5 / 5) * (1 - 0.5 / 9)) < 1e-9
    assert abs(evs.period_hydride_atomization_dress(15) - 0.8) < 1e-9


def test_centre_coordination_graph_dress() -> None:
    cap = lean.CONSTRUCTIVE_VALLEY_CAP
    strong = lean.STRONG_CHANNEL_FRACTION
    tri = 1.0 - 2.0 * strong / (cap * 3.0)
    tet = 1.0 + 2.0 * strong / (cap * 4.0)
    assert abs(evs.centre_coordination_graph_dress(3) - tri) < 1e-9
    assert abs(evs.centre_coordination_graph_dress(4) - tet) < 1e-9
    assert evs.centre_coordination_graph_dress(2) == 1.0


def test_homonuclear_h2_ladder_closure() -> None:
    from bonded_horizon_casimir_float import DEFAULT_UUD_ANGLES_RAD

    raw = evs.homonuclear_h2_dissociation_surplus_dimless(DEFAULT_UUD_ANGLES_RAD)
    assert raw > 0.0
    assert raw < 9.0


def test_h2s_period3_dihydride_lone_pairs() -> None:
    assert evs.centre_vsepr_lone_pair_count(16, 2) == 2
    assert evs.centre_vsepr_lone_pair_count(8, 2) == 1


def test_co_atomization_bond_order() -> None:
    assert abs(evs.heteronuclear_atomization_bond_order(6, 8) - 2.25) < 1e-9


def test_homonuclear_dissociation_open_shell_routing() -> None:
    from bonded_horizon_casimir_float import DEFAULT_UUD_ANGLES_RAD

    angles = DEFAULT_UUD_ANGLES_RAD
    n2 = evs.homonuclear_dissociation_surplus_dimless(14, 14, 7, angles)
    o2 = evs.homonuclear_dissociation_surplus_dimless(16, 16, 8, angles)
    f2 = evs.homonuclear_dissociation_surplus_dimless(18, 18, 9, angles)
    cl2 = evs.homonuclear_dissociation_surplus_dimless(34, 34, 17, angles)
    assert n2 > o2 > 0.0
    assert f2 > 0.0 and cl2 > 0.0
    assert n2 > 10.0 * f2


def test_conjugated_dress_hcn() -> None:
    frags = (
        FragmentConfig("H", 1, 1),
        FragmentConfig("C", 6, 6),
        FragmentConfig("N", 7, 7),
    )
    bonds = (
        BondGeometry(1, 0, 1.0626),
        BondGeometry(1, 2, 1.1530),
    )
    dress = evs.conjugated_heavy_heavy_surplus_dress(frags, bonds)
    assert abs(dress - 1.0 / math.sqrt(3.0)) < 1e-9


def test_conjugated_dress_c2h2_homonuclear_alkynyl() -> None:
    frags = (
        FragmentConfig("H", 1, 1),
        FragmentConfig("C", 6, 6),
        FragmentConfig("C", 6, 6),
        FragmentConfig("H", 1, 1),
    )
    bonds = (
        BondGeometry(1, 0, 1.0626),
        BondGeometry(1, 2, 1.2080),
        BondGeometry(2, 3, 1.0626),
    )
    dress = evs.conjugated_heavy_heavy_surplus_dress(frags, bonds)
    expected = (1.0 / math.sqrt(3.0)) * math.sqrt(1.0 + 1.0 / 3.0)
    assert abs(dress - expected) < 1e-9


def test_h2o_compton_triplet_and_lean_split() -> None:
    frags = (
        FragmentConfig("O", 8, 8),
        FragmentConfig("H", 1, 1),
        FragmentConfig("H", 1, 1),
    )
    assert evs.chemistry_compton_triplet(frags) == (4, 3, 1)
    assert evs.lean_atomization_horizon_split("H2O", frags) == (10, 8, 2)
    assert evs.centre_vsepr_lone_pair_count(8, 2) == 1


def test_eta_p_weights_p_slot() -> None:
    angles = (0.4, 0.2, 0.03)
    eta_mean = sum(angles) / 3 / (3.14159265 / 2)
    eta_w = evs.eta_p_s2_weighted(angles, (4, 3, 1))
    assert abs(eta_w - eta_mean) < 0.05


if __name__ == "__main__":
    test_oxygen_water_electronic_shells()
    test_period3_electronic_shells()
    test_nacl_compton_triplet_period3()
    test_co_heteronuclear_triplet()
    test_homonuclear_bond_order()
    test_heteronuclear_bond_order_cn_triple()
    test_period3_hydride_compton_triplet()
    test_period_hydride_dissociation_dress()
    test_centre_coordination_graph_dress()
    test_homonuclear_h2_ladder_closure()
    test_h2s_period3_dihydride_lone_pairs()
    test_co_atomization_bond_order()
    test_conjugated_dress_c2h2_homonuclear_alkynyl()
    test_homonuclear_dissociation_open_shell_routing()
    test_conjugated_dress_hcn()
    test_h2o_compton_triplet_and_lean_split()
    test_eta_p_weights_p_slot()
    print("test_hqiv_electronic_valence_shells: OK")

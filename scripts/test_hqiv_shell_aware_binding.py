#!/usr/bin/env python3
"""Tests for shell-aware binding readout routing."""

from __future__ import annotations

import hqiv_lean_physics_primitives as lean
import hqiv_shell_aware_binding as sab
from hqiv_dynamic_binding_chart import GMTKN55_SUITE
import hqiv_curvature_contact_network as ccn


def test_h2_covalent_dimer_uud_surplus() -> None:
    b = GMTKN55_SUITE[0]
    net = ccn.build_network_from_molecule(b.name, b.fragments, b.bonds)
    shell = sab.resolve_shell_aware_readout(
        kind=b.kind,
        fragments=b.fragments,
        compton_triplet=net.compton_triplet,
        net=net,
        molecule_name=b.name,
    )
    assert shell.compton_triplet_class == sab.ComptonTripletClass.H2_LADDER.value
    assert shell.surplus_angle_policy == sab.SurplusAnglePolicy.COVALENT_DIMER_UUD.value
    assert 0.85 < shell.curvature_feedback_weight < 0.92


def test_h2o_electronic_shell_atomization() -> None:
    b = [x for x in GMTKN55_SUITE if x.name == "H2O"][0]
    net = ccn.build_network_from_molecule(b.name, b.fragments, b.bonds)
    assert net.nodes[0].valence_s_shell == 4
    assert net.nodes[0].valence_p_shell == 3
    shell = sab.resolve_shell_aware_readout(
        kind=b.kind,
        fragments=b.fragments,
        compton_triplet=net.compton_triplet,
        net=net,
        molecule_name=b.name,
    )
    assert shell.surplus_angle_policy == sab.SurplusAnglePolicy.ELECTRONIC_COMPTON_TRIPLET.value
    assert shell.electron_split == (10, 8, 2)
    assert shell.electronic_shell_slots == ("2s", "2p", "1s")
    assert shell.surplus_dress_factor > 1.0


def test_lih_heavy_hydride_bond_surplus() -> None:
    b = GMTKN55_SUITE[1]
    net = ccn.build_network_from_molecule(b.name, b.fragments, b.bonds)
    shell = sab.resolve_shell_aware_readout(
        kind=b.kind,
        fragments=b.fragments,
        compton_triplet=net.compton_triplet,
        net=net,
        molecule_name=b.name,
    )
    assert shell.compton_triplet_m == (4, 3, 1)
    assert shell.surplus_angle_policy == sab.SurplusAnglePolicy.BOND_AVERAGED_COMPTON.value
    assert shell.curvature_feedback_weight == 1.0


if __name__ == "__main__":
    test_h2_covalent_dimer_uud_surplus()
    test_h2o_electronic_shell_atomization()
    test_lih_heavy_hydride_bond_surplus()
    print("test_hqiv_shell_aware_binding: OK")

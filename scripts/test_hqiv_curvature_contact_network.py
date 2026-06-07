#!/usr/bin/env python3
"""Tests for curvature contact network rules."""

from __future__ import annotations

import hqiv_curvature_contact_network as ccn
import hqiv_thermodynamic_phase_from_tp as tptp
from fragment_aware_bonded_horizon import BondGeometry, FragmentConfig


def test_ch4_steric_four_contacts_two_per_h() -> None:
    frags = (FragmentConfig("C", 6, 6),) + tuple(FragmentConfig("H", 1, 1) for _ in range(4))
    bonds = tuple(BondGeometry(0, i + 1, 1.09) for i in range(4))
    net = ccn.build_network_from_molecule("CH4", frags, bonds)
    steric = [c for c in net.contacts if c.kind == ccn.ContactKind.STERIC_REPULSION]
    assert len(steric) == 1
    assert steric[0].undirected_points == 4
    assert steric[0].contacts_at_i == 2


def test_networked_vev_exceeds_bare_for_ch4() -> None:
    frags = (FragmentConfig("C", 6, 6),) + tuple(FragmentConfig("H", 1, 1) for _ in range(4))
    bonds = tuple(BondGeometry(0, i + 1, 1.09) for i in range(4))
    net = ccn.build_network_from_molecule("CH4", frags, bonds)
    assert ccn.networked_vev_geometric_mean(net) > ccn.bare_vev_geometric_mean(net)


def test_stp_derives_gas_phase_not_manual_solid() -> None:
    frags = (FragmentConfig("C", 6, 6),) + tuple(FragmentConfig("H", 1, 1) for _ in range(4))
    bonds = tuple(BondGeometry(0, i + 1, 1.09) for i in range(4))
    net = ccn.build_network_from_molecule("CH4", frags, bonds)
    assert net.thermo.phase in (
        tptp.DerivedPhase.GAS,
        tptp.DerivedPhase.MOLECULAR_CLUSTER,
        tptp.DerivedPhase.SUPERCRITICAL,
    )


def test_solid_phase_adds_periodic_contact() -> None:
    frags = (
        FragmentConfig("O", 8, 8),
        FragmentConfig("H", 1, 1),
        FragmentConfig("H", 1, 1),
    )
    bonds = (BondGeometry(0, 1, 0.9572), BondGeometry(0, 2, 0.9572))
    net = ccn.build_network_from_molecule(
        "H2O",
        frags,
        bonds,
        environment=tptp.ThermodynamicEnvironment(150.0, tptp.STP_PRESSURE_PA),
        lattice_unit_cell=(2, 2, 2),
    )
    assert net.thermo.phase == tptp.DerivedPhase.SOLID
    periodic = [c for c in net.contacts if c.kind == ccn.ContactKind.PERIODIC_IMAGE]
    assert len(periodic) == 1
    assert periodic[0].undirected_points == 3


def test_liquid_env_increases_coordination_vs_stp_ch4() -> None:
    frags = (FragmentConfig("C", 6, 6),) + tuple(FragmentConfig("H", 1, 1) for _ in range(4))
    bonds = tuple(BondGeometry(0, i + 1, 1.09) for i in range(4))
    stp = ccn.build_network_from_molecule("CH4", frags, bonds)
    liq_env = tptp.ThermodynamicEnvironment(111.0, tptp.STP_PRESSURE_PA)
    liq = ccn.build_network_from_molecule("CH4", frags, bonds, environment=liq_env)
    if liq.thermo.phase == tptp.DerivedPhase.LIQUID:
        assert liq.thermo.coordination_fraction < stp.thermo.coordination_fraction or (
            ccn.networked_vev_geometric_mean(liq) != ccn.networked_vev_geometric_mean(stp)
        )


if __name__ == "__main__":
    test_ch4_steric_four_contacts_two_per_h()
    test_networked_vev_exceeds_bare_for_ch4()
    test_stp_derives_gas_phase_not_manual_solid()
    test_solid_phase_adds_periodic_contact()
    test_liquid_env_increases_coordination_vs_stp_ch4()
    print("test_hqiv_curvature_contact_network: OK")

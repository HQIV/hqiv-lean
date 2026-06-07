#!/usr/bin/env python3
"""Tests for dynamic nucleon(p,n) readout."""

from __future__ import annotations

import hqiv_dynamic_nucleon_pn as pn
import hqiv_nuclear_outside_temperature_dynamics as notd


def test_free_lockin_recovers_witness_masses() -> None:
    env = pn.NucleonEnvironment(shell=notd.REFERENCE_M, xi=notd.XI_LOCKIN, bonded=False)
    row = pn.pn_pair_readout(env)
    witness = pn._load_witness()
    assert abs(row.proton.mass_mev - float(witness["derivedProtonMass_MeV"])) < 1e-9
    assert abs(row.neutron.mass_mev - float(witness["derivedNeutronMass_MeV"])) < 1e-9


def test_gap_preserved_under_well_depth() -> None:
    env = pn.NucleonEnvironment(
        shell=notd.REFERENCE_M,
        xi=notd.XI_LOCKIN,
        well_depth_mev=5.0,
        bonded=True,
    )
    row = pn.pn_pair_readout(env)
    witness = pn._load_witness()
    assert abs(row.delta_m_mev - float(witness["derivedDeltaM_MeV"])) < 1e-9


def test_bonded_environment_lowers_both_masses_equally() -> None:
    free = pn.pn_pair_readout(
        pn.NucleonEnvironment(shell=notd.REFERENCE_M, xi=notd.XI_LOCKIN, bonded=False)
    )
    bonded = pn.pn_pair_readout(pn.caustic_environment_for_A(4))
    assert bonded.proton.mass_mev < free.proton.mass_mev
    assert bonded.neutron.mass_mev < free.neutron.mass_mev
    assert abs((free.neutron.mass_mev - free.proton.mass_mev) - bonded.delta_m_mev) < 1e-9


def test_bbn_environment_releases_some_binding() -> None:
    lock = pn.pn_pair_readout(pn.caustic_environment_for_A(4))
    bbn_xi = notd.xi_from_T_MeV(0.1)
    bbn = pn.pn_pair_readout(pn.caustic_environment_for_A(4, xi=bbn_xi))
    assert bbn.proton.mass_mev > lock.proton.mass_mev
    assert bbn.delta_m_mev == lock.delta_m_mev


def test_payload_exports_three_environments() -> None:
    payload = pn.build_payload()
    assert "free_lockin" in payload
    assert "he4_lockin_environment" in payload
    assert "he4_bbn_temperature_environment" in payload


if __name__ == "__main__":
    test_free_lockin_recovers_witness_masses()
    test_gap_preserved_under_well_depth()
    test_bonded_environment_lowers_both_masses_equally()
    test_bbn_environment_releases_some_binding()
    test_payload_exports_three_environments()
    print("test_hqiv_dynamic_nucleon_pn: OK")

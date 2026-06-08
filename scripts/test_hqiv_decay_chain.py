#!/usr/bin/env python3
"""Tests for HQIV decay-chain calculator."""

from __future__ import annotations

import math

import hqiv_decay_chain as dc
import hqiv_dynamic_beta_isotope as dbi
import hqiv_lean_physics_primitives as lean
import hqiv_tuft_global_hadron_readout as tuft


def test_neutron_beta_minus_open_at_lockin() -> None:
    n = dc.NuclearState(A=1, Z=0, label="n")
    ch = dc.evaluate_nuclear_channel(n, channel="beta_minus")
    assert ch is not None
    assert ch.kinematic_open
    assert ch.residual_open
    assert ch.channel_open
    assert ch.endpoint_q_mev is not None
    assert abs(ch.endpoint_q_mev - 0.782) < 0.02


def test_proton_beta_plus_closed_at_lockin() -> None:
    p = dc.NuclearState(A=1, Z=1, label="p")
    ch = dc.evaluate_nuclear_channel(p, channel="beta_plus")
    assert ch is not None
    assert not ch.kinematic_open or not ch.channel_open


def test_tritium_to_he3_edge() -> None:
    t = dc.NuclearState(A=3, Z=1, label="T")
    daughter = dc.beta_minus_daughter(t)
    assert daughter is not None
    assert daughter.A == 3 and daughter.Z == 2
    q = dc.endpoint_q_beta_minus(t)
    assert q is not None and q > 0.0
    edges = dc.edges_from_nuclear_state(t, residual_mode="effective")
    assert all(not e.channel.channel_open for e in edges if e.channel.tag == "beta_minus")
    tipped = dc.edges_from_nuclear_state(t, residual_mode="raw")
    beta_edges = [e for e in tipped if e.channel.tag == "beta_minus" and e.channel.channel_open]
    assert beta_edges, "T beta_minus open under raw overlap residual (EM-tipping path)"
    assert isinstance(beta_edges[0].daughter, dc.NuclearState)
    assert beta_edges[0].daughter.Z == 2


def test_he4_structurally_stable_no_open_edges() -> None:
    he4 = dc.NuclearState(A=4, Z=2, label="He4")
    edges = dc.edges_from_nuclear_state(he4)
    open_edges = [e for e in edges if e.channel.channel_open]
    assert len(open_edges) == 0


def test_branching_ratios_sum_to_one() -> None:
    n = dc.NuclearState(A=1, Z=0, label="n")
    channels = dc.open_channels_nuclear(n)
    br = dc.branching_ratios(channels)
    open_sum = sum(br[i] for i, ch in enumerate(channels) if ch.channel_open)
    if any(ch.channel_open for ch in channels):
        assert abs(open_sum - 1.0) < 1e-12


def test_chain_neutron_single_step() -> None:
    n = dc.NuclearState(A=1, Z=0, label="n")
    result = dc.expand_chain(n, max_depth=2, min_branch=1e-12)
    assert len(result.nodes) >= 2
    root = result.nodes[0]
    assert root.depth == 0
    assert len(root.children) >= 1
    child = root.children[0]
    assert isinstance(child.state, dc.NuclearState)
    assert child.state.Z == 1


def test_nucleon_gap_q_policy() -> None:
    n = dc.NuclearState(A=1, Z=0, label="n")
    q_budget = dc.endpoint_q_beta_minus(n, q_policy="mass_budget")
    q_gap = dc.endpoint_q_beta_minus(n, q_policy="nucleon_gap")
    assert q_budget is not None and q_gap is not None
    assert abs(q_budget - q_gap) < 0.05


def test_hadron_mass_budget_edge() -> None:
    parent = dc.HadronState(
        channel=tuft.TuftExcitationChannel.baryon(0, 1, pdg_key="Delta(1232)"),
        xi=lean.XI_LOCKIN,
    )
    daughter = dc.HadronState(
        channel=tuft.TuftExcitationChannel.baryon(0, 0, pdg_key="proton"),
        xi=lean.XI_LOCKIN,
    )
    m_p = dc.hadron_mass_mev(parent)
    m_d = dc.hadron_mass_mev(daughter)
    assert m_p > m_d
    edge = dc.evaluate_hadron_weak_hadron_edge(parent, daughter)
    assert edge is not None
    assert edge.channel.endpoint_q_mev > 0.0


def test_payload_structure() -> None:
    payload = dc.build_payload(max_depth=3, include_hadron_demo=True)
    assert payload["referenceM"] == 4
    assert payload["xi_lockin"] == 5.0
    assert "lean_mapping" in payload
    assert len(payload["nuclear_chains"]) >= 3
    assert len(payload["hadron_chains"]) == 1


def test_beta_valley_count_matches_lean() -> None:
    assert dbi.beta_valley_count_bound(4) == 6


def test_width_halflife_consistency() -> None:
    n = dc.NuclearState(A=1, Z=0, label="n")
    ch = dc.evaluate_nuclear_channel(n, channel="beta_minus")
    assert ch is not None and ch.channel_open
    if ch.width_per_s > 0.0 and math.isfinite(ch.half_life_s):
        expected = math.log(2.0) / ch.width_per_s
        assert abs(expected - ch.half_life_s) / ch.half_life_s < 0.05


if __name__ == "__main__":
    test_neutron_beta_minus_open_at_lockin()
    test_proton_beta_plus_closed_at_lockin()
    test_tritium_to_he3_edge()
    test_he4_structurally_stable_no_open_edges()
    test_branching_ratios_sum_to_one()
    test_chain_neutron_single_step()
    test_nucleon_gap_q_policy()
    test_hadron_mass_budget_edge()
    test_payload_structure()
    test_beta_valley_count_matches_lean()
    test_width_halflife_consistency()
    print("test_hqiv_decay_chain: OK")

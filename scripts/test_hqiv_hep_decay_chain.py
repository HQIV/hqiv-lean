#!/usr/bin/env python3
"""Tests for HQIV HEP decay-chain calculator."""

from __future__ import annotations

import math

import hqiv_hep_decay_chain as hep


def test_lhc_pp_sqrt_s() -> None:
    setup = hep.BeamTargetSetup("p", 6500.0, "p", 6500.0)
    kin = hep.collision_kinematics(setup)
    assert 13000 < kin.sqrt_s_gev < 14000


def test_fixed_target_kinematics() -> None:
    setup = hep.BeamTargetSetup("p", 400.0, "p", 0.0)
    kin = hep.collision_kinematics(setup)
    assert 27 < kin.sqrt_s_gev < 30


def test_magnetic_field_increases_weak_dressing() -> None:
    env0 = hep.ExperimentEnvironment(magnetic_field_tesla=0.0)
    env2 = hep.ExperimentEnvironment(magnetic_field_tesla=2.5)
    assert env2.weak_width_factor() > env0.weak_width_factor()


def test_collider_stream_curvature_increases_weak_dressing() -> None:
    env0 = hep.ExperimentEnvironment(magnetic_field_tesla=0.0, comoving_stream_fraction=0.0)
    env_field = hep.ExperimentEnvironment(
        magnetic_field_tesla=4.0,
        collider_reference_tesla=4.0,
        comoving_stream_fraction=0.0,
    )
    env_stream = hep.ExperimentEnvironment(magnetic_field_tesla=0.0, comoving_stream_fraction=1.0)
    assert env_field.weak_width_factor() > env0.weak_width_factor()
    assert env_stream.weak_width_factor() > env0.weak_width_factor()


def test_delta_strong_decay_to_p_pi() -> None:
    env = hep.ExperimentEnvironment()
    parent = hep.build_particle("delta_p")
    edges = hep.edges_from_particle(parent, env=env)
    assert edges
    e = edges[0]
    assert e.mode.channel == "strong"
    assert e.q_mev > 0.0
    ids = {d.species_id for d in e.daughters}
    assert "p" in ids and "pi_plus" in ids


def test_lambda_weak_chain() -> None:
    env = hep.ExperimentEnvironment()
    lam = hep.build_particle("lambda")
    root, nodes, _ = hep.expand_hep_chain(lam, env=env, max_depth=4)
    assert root.particle.species_id == "lambda"
    assert len(nodes) >= 2


def test_lhc_experiment_produces_accessible_hadrons() -> None:
    result = hep.run_experiment(
        hep.FACILITY_PRESETS["LHC_pp_13TeV"],
        max_depth=4,
    )
    assert result.kinematics.sqrt_s_gev > 10000
    assert len(result.produced) > 20
    assert len(result.root_nodes) >= 1


def test_beam_fraction_and_environment_in_payload() -> None:
    setup = hep.BeamTargetSetup("p", 400.0, "p", 0.0, beam_fraction=0.8)
    env = hep.ExperimentEnvironment(magnetic_field_tesla=1.0, lab_temperature_K=4.0)
    result = hep.run_experiment(setup, env=env, production_ids=["delta_p"], max_depth=3)
    payload = hep.build_payload(result)
    assert payload["collision"]["beam_fraction"] == 0.8
    assert payload["environment"]["magnetic_field_tesla"] == 1.0
    assert payload["environment"]["lab_temperature_K"] == 4.0


def test_branching_normalized() -> None:
    env = hep.ExperimentEnvironment()
    parent = hep.build_particle("lambda")
    edges = hep.edges_from_particle(parent, env=env)
    if len(edges) > 1:
        assert abs(sum(e.branching_ratio for e in edges) - 1.0) < 1e-9


def test_pion_charged_weak_half_life_order_of_magnitude() -> None:
    env = hep.ExperimentEnvironment()
    pi = hep.build_particle("pi_plus")
    edge = hep.edges_from_particle(pi, env=env)[0]
    assert 0.5 < edge.half_life_s / 1.803e-8 < 1.5


def test_heavy_flavor_masses_within_benchmark_band() -> None:
    for sid, ref in (
        ("D_plus", 1869.66),
        ("Jpsi", 3096.9),
        ("lambda_c", 2286.46),
        ("B_plus", 5279.34),
        ("Upsilon", 9460.3),
    ):
        m = hep.particle_mass_mev(sid)
        assert abs(m - ref) / ref <= 0.12, f"{sid} mass {m} vs {ref}"


def test_d_plus_strong_decay_channel() -> None:
    env = hep.ExperimentEnvironment()
    parent = hep.build_particle("D_plus")
    edges = hep.edges_from_particle(parent, env=env)
    hadronic = [e for e in edges if e.mode.channel == "weak" and len(e.daughters) >= 2]
    assert hadronic
    ids = {d.species_id for d in hadronic[0].daughters}
    assert "K_minus" in ids and "pi_plus" in ids


def test_lhc_heavy_roots_auto() -> None:
    result = hep.run_experiment(
        hep.FACILITY_PRESETS["LHC_pp_13TeV"],
        max_depth=3,
    )
    root_ids = {r.particle.species_id for r in result.root_nodes}
    assert "Jpsi" in root_ids or "D_plus" in root_ids


def test_belle2_upsilon_accessible() -> None:
    kin = hep.collision_kinematics(hep.FACILITY_PRESETS["Belle2_Upsilon4S"])
    ups = hep.build_particle("Upsilon")
    assert hep.production_accessible(ups, kin)


if __name__ == "__main__":
    test_lhc_pp_sqrt_s()
    test_fixed_target_kinematics()
    test_magnetic_field_increases_weak_dressing()
    test_collider_stream_curvature_increases_weak_dressing()
    test_delta_strong_decay_to_p_pi()
    test_lambda_weak_chain()
    test_lhc_experiment_produces_accessible_hadrons()
    test_beam_fraction_and_environment_in_payload()
    test_branching_normalized()
    test_pion_charged_weak_half_life_order_of_magnitude()
    test_heavy_flavor_masses_within_benchmark_band()
    test_d_plus_strong_decay_channel()
    test_lhc_heavy_roots_auto()
    test_belle2_upsilon_accessible()
    print("test_hqiv_hep_decay_chain: OK")

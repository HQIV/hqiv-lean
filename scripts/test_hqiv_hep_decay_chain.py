#!/usr/bin/env python3
"""Tests for HQIV HEP decay-chain calculator."""

from __future__ import annotations

import math

import hqiv_hep_decay_chain as hep
import hqiv_hep_multichannel_expansion as exp
import hqiv_hep_decay_readout as hdr


def test_b0_neutral_spectator_contact_kind() -> None:
    kind = exp.open_flavour_contact_kind("B0", "weak", ("D0", "pi_zero"))
    assert kind == "neutral_spectator_complement"
    assert hdr.open_flavour_contact_weight(kind) == hdr.neutral_spectator_monogamy_complement()


def test_b0_charged_spectator_uses_external_weak() -> None:
    kind = exp.open_flavour_contact_kind("B0", "weak", ("D0", "pi_plus"))
    assert kind == "bottom_external_weak"


def test_b_plus_d_pi_uses_open_charm_semileptonic_width_slot() -> None:
    """B⁺ → D⁰π⁺ must use the D-meson pole, not the pion-pole K→π slot."""
    env = hep.ExperimentEnvironment()
    parent = hep.build_particle("B_plus")
    d_pi = tuple(hep.build_particle(d) for d in ("D0", "pi_plus"))
    d_rho = tuple(hep.build_particle(d) for d in ("D0", "rho_plus"))
    w_pi = hep._hadronic_weak_width_per_s(parent, d_pi, env=env)
    w_rho = hep._hadronic_weak_width_per_s(parent, d_rho, env=env)
    assert math.isclose(w_pi, w_rho, rel_tol=1e-9)
    assert w_pi > 1e12


def test_phi_strong_branching_from_spine_discharge() -> None:
    """φ → K⁺K⁻ vs 3π: channel-independent width; spine contacts set 21/25 vs 4/25."""
    env = hep.ExperimentEnvironment()
    parent = hep.build_particle("phi")
    edges = hep.edges_from_particle(parent, env=env)
    strong = [e for e in edges if e.mode.channel == "strong"]
    by_ds = {tuple(d.species_id for d in e.daughters): e for e in strong}
    kk = by_ds[("K_plus", "K_minus")]
    leak = by_ds[("pi_plus", "pi_minus", "pi_zero")]
    assert math.isclose(kk.width_per_s, leak.width_per_s, rel_tol=1e-9)
    assert math.isclose(kk.branching_ratio, 21.0 / 25.0, rel_tol=1e-6)
    assert math.isclose(leak.branching_ratio, 4.0 / 25.0, rel_tol=1e-6)


def test_certified_strong_discharge_generalizes_vector_and_decuplet() -> None:
    """ρ⁰, ρ⁺, ω, Δ⁺ use finite Lean spans: pole width + spine topology only."""
    import hqiv_hep_decay_certificates as cert

    env = hep.ExperimentEnvironment()
    rho0 = hep.build_particle("rho_zero")
    rho0_edges = hep.edges_from_particle(rho0, env=env)
    assert len([e for e in rho0_edges if e.mode.channel == "strong"]) == 1
    assert math.isclose(rho0_edges[0].branching_ratio, 1.0, rel_tol=1e-6)

    rho_plus = hep.build_particle("rho_plus")
    rho_strong = [e for e in hep.edges_from_particle(rho_plus, env=env) if e.mode.channel == "strong"]
    assert len(rho_strong) == 1
    assert tuple(d.species_id for d in rho_strong[0].daughters) == ("pi_plus", "pi_zero")

    omega = hep.build_particle("omega_meson")
    omega_strong = [e for e in hep.edges_from_particle(omega, env=env) if e.mode.channel == "strong"]
    assert len(omega_strong) == 1
    assert tuple(d.species_id for d in omega_strong[0].daughters) == (
        "pi_plus",
        "pi_minus",
        "pi_zero",
    )

    delta = hep.build_particle("delta_p")
    delta_strong = [e for e in hep.edges_from_particle(delta, env=env) if e.mode.channel == "strong"]
    assert len(delta_strong) == 2
    widths = {tuple(d.species_id for d in e.daughters): e.width_per_s for e in delta_strong}
    assert math.isclose(widths[("p", "pi_zero")], widths[("n", "pi_plus")], rel_tol=1e-9)
    br_npi = next(
        e.branching_ratio
        for e in delta_strong
        if tuple(d.species_id for d in e.daughters) == ("n", "pi_plus")
    )
    assert math.isclose(br_npi, 0.5, rel_tol=0.02)
    assert cert.is_certified_strong_discharge_parent_id("rho_zero")
    assert hdr.certified_strong_discharge_width_scale("delta_p") == 1.0
    assert math.isclose(
        hdr.certified_strong_discharge_width_scale("rho_zero"),
        hdr.hidden_strangeness_vector_strong_width_scale(),
    )


def test_d_kaon_family_uses_double_monogamy_exclusion() -> None:
    kind = exp.open_flavour_contact_kind("D_plus", "weak", ("K_minus", "pi_plus"))
    assert kind == "double_monogamy_exclusion"
    assert hdr.open_flavour_contact_weight(kind) == hdr.double_monogamy_exclusion_factor()
    # Isospin-partner outlets keep unit seed so PDG-family rows are not uniformly scaled.
    kind_k0 = exp.open_flavour_contact_kind("D_plus", "weak", ("K0", "pi_plus"))
    assert kind_k0 == "unit_seed"


def test_lambda_c_pKpi_uses_charmed_baryon_double_monogamy() -> None:
    kind = exp.open_flavour_contact_kind("lambda_c", "weak", ("p", "K_minus", "pi_plus"))
    assert kind == "charmed_baryon_double_monogamy"
    assert hdr.open_flavour_contact_weight(kind) == hdr.charmed_baryon_double_monogamy_contact()


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
    hadronic = [
        e
        for e in edges
        if e.mode.channel == "strong"
        and e.q_mev > 0.0
        and {"p", "n"} & {d.species_id for d in e.daughters}
        and any(d.species_id.startswith("pi_") for d in e.daughters)
    ]
    assert hadronic


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
    assert any(
        {"K_minus", "pi_plus"} <= {d.species_id for d in e.daughters} for e in hadronic
    )


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

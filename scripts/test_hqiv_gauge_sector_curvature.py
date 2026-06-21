#!/usr/bin/env python3
"""Lean-aligned tests for per-gauge-sector curvature readout."""

from __future__ import annotations

import math

import hqiv_hep_decay_readout as hdr
import hqiv_lean_physics_primitives as lean


def test_strong_gauge_curvature_readout() -> None:
    assert math.isclose(hdr.strong_gauge_curvature_readout(), 14.0 / 321.0, rel_tol=1e-12)


def test_weak_confinement_aperture() -> None:
    assert math.isclose(
        hdr.weak_hadronic_strong_confinement_aperture(), 8.0 / 3.0, rel_tol=1e-12
    )


def test_weak_hopf_bridge_aperture() -> None:
    assert math.isclose(
        hdr.weak_semileptonic_hopf_bridge_aperture(), 46.0 / 45.0, rel_tol=1e-12
    )


def test_semileptonic_beats_hadronic_weak() -> None:
    had = hdr.weak_gauge_hadronic_curvature_readout()
    semi = hdr.weak_gauge_semileptonic_curvature_readout()
    assert semi > had


def test_channel_routing_semileptonic() -> None:
    mu = hdr.gauge_sector_curvature_readout("weak", daughter_ids=("mu_plus",))
    had = hdr.gauge_sector_curvature_readout("weak", daughter_ids=("pi_plus", "pi_zero"))
    assert math.isclose(mu, hdr.weak_gauge_semileptonic_curvature_readout(), rel_tol=1e-12)
    assert math.isclose(had, hdr.weak_gauge_hadronic_curvature_readout(), rel_tol=1e-12)


def test_gauge_width_factor_bs_outlets() -> None:
    phi_phi = hdr.gauge_curvature_width_factor("Bs", "weak", ("phi", "phi"))
    ds_k = hdr.gauge_curvature_width_factor("Bs", "weak", ("Ds_plus", "K_minus"))
    weak = hdr.weak_gauge_hadronic_curvature_readout()
    assert math.isclose(phi_phi, weak, rel_tol=1e-12)
    assert math.isclose(ds_k, weak, rel_tol=1e-12)


def test_gauge_width_factor_in_width_kernel_not_topology() -> None:
    import hqiv_hep_production_readout as hpr

    tw = hpr.channel_topology_weight(
        parent_id="D_plus",
        channel="weak",
        q_mev=100.0,
        parent_mass_mev=1869.0,
        n_daughters=2,
        relative_prior=1.0,
        daughter_ids=("K_minus", "pi_plus"),
    )
    assert math.isclose(tw, 1.0, rel_tol=1e-12)


def test_force_sector_fractions_sum() -> None:
    total = hdr.EM_CHANNEL_FRACTION + hdr.WEAK_CHANNEL_FRACTION + lean.STRONG_CHANNEL_FRACTION
    assert math.isclose(total, 1.0, rel_tol=1e-12)

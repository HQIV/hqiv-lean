#!/usr/bin/env python3
"""Tests for TUFT electroweak boson readout."""

from __future__ import annotations

import hqiv_tuft_electroweak_boson_readout as ew


def test_sin2_geometric_near_pdg() -> None:
    s2 = ew.sin2_theta_w_geometric_lockin()
    assert 0.22 < s2 < 0.24


def test_geometric_z_below_naive() -> None:
    m_z = ew.tuft_mz_at_xi_gev()
    assert m_z < ew.M_Z_NAIVE_GEV


def test_w_within_half_percent_of_pdg() -> None:
    m_w = ew.tuft_mw_at_xi_gev()
    ratio = m_w / ew.PDG_GEV["W"]
    assert 0.995 < ratio < 1.005


def test_z_within_half_percent_of_pdg() -> None:
    m_z = ew.tuft_mz_at_xi_gev()
    ratio = m_z / ew.PDG_GEV["Z"]
    assert 0.995 < ratio < 1.005


def test_higgs_primary_within_half_percent_of_pdg() -> None:
    m_h = ew.tuft_mh_at_xi_gev()
    ratio = m_h / ew.PDG_GEV["H"]
    assert 0.995 < ratio < 1.005


def test_higgs_primary_above_scalar_closure() -> None:
    assert ew.tuft_mh_at_xi_gev() > ew.tuft_mh_scalar_closure_at_xi_gev()


def test_w_geometric_mean_bridge() -> None:
    scale = ew.tuft_electroweak_scale_at_xi(ew.XI_LOCKIN)
    pinned = ew.tuft_mw_pinned_at_xi_gev()
    expected = scale * (ew.M_W_DERIVED_GEV * pinned) ** 0.5
    assert abs(ew.tuft_mw_at_xi_gev() - expected) < 1e-9


def test_scale_unity_at_lockin() -> None:
    assert abs(ew.tuft_electroweak_scale_at_xi(ew.XI_LOCKIN) - 1.0) < 1e-12


if __name__ == "__main__":
    test_sin2_geometric_near_pdg()
    test_geometric_z_below_naive()
    test_w_within_half_percent_of_pdg()
    test_z_within_half_percent_of_pdg()
    test_higgs_primary_within_half_percent_of_pdg()
    test_higgs_primary_above_scalar_closure()
    test_w_geometric_mean_bridge()
    test_scale_unity_at_lockin()
    print("ok")

#!/usr/bin/env python3
"""Tests for buttoned-down network binding feedback."""

from __future__ import annotations

import math

import hqiv_curvature_contact_network as ccn
import hqiv_chemistry_tuft_dynamics as ctd
from hqiv_dynamic_binding_chart import GMTKN55_SUITE
from fragment_aware_bonded_horizon import BondGeometry, FragmentConfig


def test_h2o_centre_ideal_is_dynamic_not_linear() -> None:
    frags = (
        FragmentConfig("O", 8, 8),
        FragmentConfig("H", 1, 1),
        FragmentConfig("H", 1, 1),
    )
    bonds = (
        BondGeometry(0, 1, 0.9572, bond_angle_rad=math.radians(104.5)),
        BondGeometry(0, 2, 0.9572, bond_angle_rad=math.radians(104.5)),
    )
    net = ccn.build_network_from_molecule("H2O", frags, bonds)
    geoms = ccn.covalent_bond_geometries(net)
    ideal_deg = math.degrees(geoms[0].ideal_bond_angle_rad)
    assert 108.0 < ideal_deg < 118.0
    assert abs(ideal_deg - math.degrees(ctd.dynamic_centre_angle_rad(8, 2))) < 0.01


def test_h2o_geometry_alignment_near_unity() -> None:
    b = [x for x in GMTKN55_SUITE if x.name == "H2O"][0]
    net = ccn.build_network_from_molecule(b.name, b.fragments, b.bonds)
    fb = ccn.network_binding_feedback(net, curvature_contrast_weight=1.0)
    assert fb.geometry_alignment_factor > 0.95


def test_network_feedback_product_matches_vev_times_geom_times_kappa() -> None:
    b = GMTKN55_SUITE[0]
    net = ccn.build_network_from_molecule(b.name, b.fragments, b.bonds)
    fb = ccn.network_binding_feedback(net, curvature_contrast_weight=0.9)
    assert abs(
        fb.dimless_prefactor
        - fb.networked_vev_geometric_mean
        * fb.geometry_alignment_factor
        * fb.curvature_feedback_at_xi
    ) < 1e-12


def test_h2o_gmtkn_error_within_15pct() -> None:
    from hqiv_dynamic_binding_chart import dynamic_binding_for_benchmark

    b = [x for x in GMTKN55_SUITE if x.name == "H2O"][0]
    r = dynamic_binding_for_benchmark(b)
    assert abs(r.error_pct) < 15.0


if __name__ == "__main__":
    test_h2o_centre_ideal_is_dynamic_not_linear()
    test_h2o_geometry_alignment_near_unity()
    test_network_feedback_product_matches_vev_times_geom_times_kappa()
    test_h2o_gmtkn_error_within_15pct()
    print("test_hqiv_network_binding_feedback: OK")

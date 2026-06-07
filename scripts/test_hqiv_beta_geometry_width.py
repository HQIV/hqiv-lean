#!/usr/bin/env python3
"""Tests for generic beta geometry width factors."""

from __future__ import annotations

import hqiv_dynamic_beta_isotope as dbi


def test_valley_count_bound_matches_lean() -> None:
    assert dbi.beta_valley_count_bound(1) == 0
    assert dbi.beta_valley_count_bound(3) == 4
    assert dbi.beta_valley_count_bound(4) == 6


def test_caustic_layer_count_matches_stack() -> None:
    assert dbi.beta_caustic_layer_count(1) == 0
    assert dbi.beta_caustic_layer_count(2) == 2
    assert dbi.beta_caustic_layer_count(3) == 3
    assert dbi.beta_caustic_layer_count(4) == 5


def test_width_well_between_mass_and_partner_scales() -> None:
    total = 10.0
    well = dbi.beta_width_well_depth_mev(
        3,
        1,
        cluster_total_mev=total,
        proton_mass_mev=938.0,
        neutron_mass_mev=939.0,
    )
    assert total / 3.0 < well < total / 2.0


if __name__ == "__main__":
    test_valley_count_bound_matches_lean()
    test_caustic_layer_count_matches_stack()
    test_width_well_between_mass_and_partner_scales()
    print("test_hqiv_beta_geometry_width: OK")

#!/usr/bin/env python3
"""Mass-networked TUFT vev geometric means (D/T valley propagation)."""

from __future__ import annotations

import hqiv_nuclear_curvature_binding as ncb


def test_deuteron_vev_closest_to_unity() -> None:
    v_h = ncb.tuft_vev_factor_networked_at_cluster(ncb.nucleus_curvature_shell(1), 1)
    v_d = ncb.tuft_vev_factor_networked_at_cluster(ncb.nucleus_curvature_shell(2), 2)
    v_t = ncb.tuft_vev_factor_networked_at_cluster(ncb.nucleus_curvature_shell(3), 3)
    assert abs(v_h - 1.0) < abs(v_d - 1.0)
    assert abs(v_d - 1.0) < abs(v_t - 1.0) or abs(v_d - 1.0) < 0.01


def test_valley_geomean_below_bare_shell_for_tritium() -> None:
    bare = ncb.lean.tuft_vev_factor_at_xi(float(ncb.nucleus_curvature_shell(3) + 1))
    valley = ncb.valley_network_vev_factor(3)
    assert valley < bare


def test_ch4_four_repulsive_h_h_contacts_two_per_h() -> None:
    assert ncb.peripheral_h_h_repulsive_contacts_per_hydrogen(4) == 2
    assert ncb.peripheral_h_h_repulsive_contact_points(4) == 4
    boost = ncb.hydrogen_repulsive_curvature_mass_boost(4)
    assert boost > 1.0


def test_networked_fragment_geomean_for_water() -> None:
    frags = ((8, 8), (1, 1), (1, 1))
    net = ncb.vev_geometric_mean_networked_from_fragments(frags)
    bare_triplet = ncb.vev_geometric_mean_from_triplet((4, 3, 1))
    assert net > bare_triplet * 0.98
    assert net < bare_triplet * 1.05


if __name__ == "__main__":
    test_ch4_four_repulsive_h_h_contacts_two_per_h()
    test_deuteron_vev_closest_to_unity()
    test_valley_geomean_below_bare_shell_for_tritium()
    test_networked_fragment_geomean_for_water()
    print("test_hqiv_networked_vev_geometry: OK")

#!/usr/bin/env python3
"""Electronic valence shell assignment (2s/2p/1s Compton ladder)."""

from __future__ import annotations

import hqiv_electronic_valence_shells as evs
from fragment_aware_bonded_horizon import FragmentConfig


def test_oxygen_water_electronic_shells() -> None:
    m_s, m_p = evs.electronic_compton_shells(8)
    assert m_s == 4 and m_p == 3
    assert evs.electronic_shell_label(8, slot="s") == "2s"
    assert evs.electronic_shell_label(8, slot="p") == "2p"


def test_h2o_compton_triplet_and_lean_split() -> None:
    frags = (
        FragmentConfig("O", 8, 8),
        FragmentConfig("H", 1, 1),
        FragmentConfig("H", 1, 1),
    )
    assert evs.chemistry_compton_triplet(frags) == (4, 3, 1)
    assert evs.lean_atomization_horizon_split("H2O", frags) == (10, 8, 2)
    assert evs.centre_vsepr_lone_pair_count(8, 2) == 1


def test_eta_p_weights_p_slot() -> None:
    angles = (0.4, 0.2, 0.03)
    eta_mean = sum(angles) / 3 / (3.14159265 / 2)
    eta_w = evs.eta_p_s2_weighted(angles, (4, 3, 1))
    assert abs(eta_w - eta_mean) < 0.05


if __name__ == "__main__":
    test_oxygen_water_electronic_shells()
    test_h2o_compton_triplet_and_lean_split()
    test_eta_p_weights_p_slot()
    print("test_hqiv_electronic_valence_shells: OK")

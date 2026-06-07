#!/usr/bin/env python3
"""Tests for local-curvature neutrino opacity weak-width slot."""

from __future__ import annotations

import hqiv_isotope_stability_halflife as ish
import hqiv_nuclear_outside_temperature_dynamics as notd


def test_neutrino_opacity_barn_is_oom_140_pow_four_at_lockin() -> None:
    opacity = notd.local_curvature_neutrino_opacity_barn(notd.XI_LOCKIN, 0.0)
    assert 3.0e8 <= opacity <= 4.5e8


def test_weak_width_catalysis_near_seven_percent_at_lab() -> None:
    xi = ish.xi_from_temperature_K(300.0)
    gravity = notd.local_lab_gravity_phi_epsilon("full")
    central = notd.local_curvature_weak_width_factor(xi, gravity)
    low, _, high = notd.local_curvature_weak_width_factor_band(xi, gravity)
    assert 1.06 <= central <= 1.09
    assert low < central < high
    assert 1.04 <= low <= 1.08
    assert 1.07 <= high <= 1.12


def test_qualified_neutron_half_life_in_reference_band() -> None:
    row = ish.stability_readout(1, 0, label="n", em_tipping_qualified=True, lab_temperature_K=300.0)
    assert row.half_life_seconds is not None
    ratio = row.half_life_seconds / 879.4
    assert 0.95 <= ratio <= 1.05
    low_tau = row.half_life_seconds * row.local_curvature_weak_width_factor / row.local_curvature_weak_width_factor_high
    high_tau = row.half_life_seconds * row.local_curvature_weak_width_factor / row.local_curvature_weak_width_factor_low
    assert low_tau <= 879.4 <= high_tau


if __name__ == "__main__":
    test_neutrino_opacity_barn_is_oom_140_pow_four_at_lockin()
    test_weak_width_catalysis_near_seven_percent_at_lab()
    test_qualified_neutron_half_life_in_reference_band()
    print("test_hqiv_local_curvature_neutrino_width: OK")

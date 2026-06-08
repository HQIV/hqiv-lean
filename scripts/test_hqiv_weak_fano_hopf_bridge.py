#!/usr/bin/env python3
"""Tests for weak Fano/Hopf bridge energy."""

from __future__ import annotations

import hqiv_weak_fano_hopf_bridge as bridge


def test_default_bridge_shape_is_one_fano_step_times_weak_hopf() -> None:
    assert bridge.fano_vertex_distance(0, 1) == 1
    assert bridge.fano_rotation_shape(0, 1) == 1.0 / 6.0
    assert bridge.hopf_fibration_shape(1) == 1.0 / 3.0
    assert bridge.phase_lift_shape(bridge.REFERENCE_M) == 1.0
    assert bridge.weak_bridge_shape() == 1.0 / 18.0


def test_bridge_energy_scales_with_endpoint() -> None:
    low = bridge.weak_bridge_energy_mev(1.0e-6)
    high = bridge.weak_bridge_energy_mev(2.0e-6)
    assert high == 2.0 * low


if __name__ == "__main__":
    test_default_bridge_shape_is_one_fano_step_times_weak_hopf()
    test_bridge_energy_scales_with_endpoint()
    print("test_hqiv_weak_fano_hopf_bridge: OK")

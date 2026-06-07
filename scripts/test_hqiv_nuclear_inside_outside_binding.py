#!/usr/bin/env python3
"""Tests for nuclear inside/outside curvature binding."""

from __future__ import annotations

import hqiv_nuclear_curvature_binding as ncb
import hqiv_nuclear_inside_outside_binding as niob

REFERENCE_M = ncb.REFERENCE_M


def test_inside_zero_for_single_nucleon() -> None:
    inside = niob.inside_nuclear_binding_mev(REFERENCE_M, 1, m_cluster=REFERENCE_M)
    assert inside == 0.0


def test_outside_zero_for_single_nucleon() -> None:
    outside = niob.outside_nuclear_binding_mev(REFERENCE_M, 1, m_cluster=REFERENCE_M)
    assert outside == 0.0


def test_cluster_binding_splits_inside_outside() -> None:
    m = REFERENCE_M
    A = 4
    m_cluster = ncb.nucleus_curvature_shell(A)
    total, inside, outside = niob.nuclear_cluster_binding_mev(m, A, m_cluster=m_cluster)
    assert total == inside + outside
    assert outside > 0.0
    assert total > 0.0


def test_deuteron_has_two_valley_contacts() -> None:
    assert niob.VALLEY_CONTACT_COUNT[2] == 2


def test_he4_has_six_valley_contacts() -> None:
    assert niob.VALLEY_CONTACT_COUNT[4] == 6


def test_caustic_layers_stack_for_deuteron() -> None:
    import hqiv_nuclear_caustic_binding as ncb_caustic

    m = REFERENCE_M
    trace = niob.nucleon_trace_binding_mev(m)
    layers = ncb_caustic.caustic_layers(m, 2, trace_mev=trace, geff=0.5)
    names = [layer.name for layer in layers]
    assert "sphere_pair_overlap" in names
    assert "barbell_torus" in names
    assert "tetrahedral_closure" not in names
    assert len(layers) == 2


def test_caustic_layers_include_tetra_for_he4() -> None:
    import hqiv_nuclear_caustic_binding as ncb_caustic

    m = REFERENCE_M
    trace = niob.nucleon_trace_binding_mev(m)
    layers = ncb_caustic.caustic_layers(m, 4, trace_mev=trace, geff=0.5)
    names = [layer.name for layer in layers]
    assert "tetrahedral_closure" in names
    assert len(layers) >= 4
    total = sum(layer.depth_mev for layer in layers)
    assert total > layers[0].depth_mev


def test_cumulative_caustic_deepens_with_A() -> None:
    import hqiv_nuclear_caustic_binding as ncb_caustic

    m = REFERENCE_M
    m_c = ncb.nucleus_curvature_shell(4)
    b2, _ = ncb_caustic.cumulative_caustic_binding_mev(m, 2, m_cluster=m_c)
    b4, layers4 = ncb_caustic.cumulative_caustic_binding_mev(m, 4, m_cluster=m_c)
    assert b4 > b2
    assert any(layer.name == "tetrahedral_closure" for layer in layers4)


def test_nucleus_row_carries_inside_outside() -> None:
    _, rows = ncb.molecule_phase_participation_eta(((2, 2),))
    row = rows[0]
    assert row.inside_binding_mev >= 0.0
    assert row.outside_binding_mev >= 0.0
    assert row.cluster_binding_mev == row.inside_binding_mev + row.outside_binding_mev


def test_report_light_nuclei() -> None:
    """Smoke print for D and He-4 binding (not asserted against experiment)."""
    import hqiv_nuclear_caustic_binding as ncb_caustic

    for A in (2, 4):
        m = REFERENCE_M
        m_c = ncb.nucleus_curvature_shell(A)
        total, inside, outside, layers = ncb_caustic.nuclear_cluster_binding_mev(
            m, A, m_cluster=m_c
        )
        per_a = total / A
        layer_str = ", ".join(f"{layer.name}={layer.depth_mev:.2f}" for layer in layers)
        print(
            f"A={A} B_total={total:.3f} MeV B/A={per_a:.3f} "
            f"inside={inside:.3f} outside={outside:.3f}"
        )
        print(f"    caustics: {layer_str}")


if __name__ == "__main__":
    test_inside_zero_for_single_nucleon()
    test_outside_zero_for_single_nucleon()
    test_cluster_binding_splits_inside_outside()
    test_deuteron_has_two_valley_contacts()
    test_he4_has_six_valley_contacts()
    test_caustic_layers_stack_for_deuteron()
    test_caustic_layers_include_tetra_for_he4()
    test_cumulative_caustic_deepens_with_A()
    test_nucleus_row_carries_inside_outside()
    test_report_light_nuclei()
    print("test_hqiv_nuclear_inside_outside_binding: OK")

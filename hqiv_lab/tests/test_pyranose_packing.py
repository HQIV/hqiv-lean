#!/usr/bin/env python3
"""Pyranose chair lattice — derived from ring contact graph."""

from __future__ import annotations

import hqiv_lean_physics_primitives as lean
from hqiv_lab.allotrope import preferred_allotrope
from hqiv_lab.foundation_panel import SUGAR_FOUNDATION_REFERENCES
from hqiv_lab.foundation_specs import foundation_spec
from hqiv_lab.packing import BravaisTopology, templates_for_motif
from hqiv_lab.coordination import infer_monomer_geometry
from hqiv_lab.pyranose_geometry import (
    PYRANOSE_RING_BOND_COUNT,
    has_pyranose_ring,
    pyranose_chair_diameter_factor,
    pyranose_chair_inplane_axis_factor,
    pyranose_chair_open_factor,
    pyranose_chair_short_axis_factor,
    pyranose_chair_stack_axis_factor,
    pyranose_exocyclic_oh_dress_factor,
    pyranose_molecules_per_cell,
    pyranose_ring_bond_lengths,
    pyranose_ring_contact_distance_angstrom,
    pyranose_ring_count,
    pyranose_ring_mean_bond_angstrom,
)


def test_glucose_has_six_member_ring() -> None:
    spec = foundation_spec("C6H12O6_alpha")
    lengths = pyranose_ring_bond_lengths(spec.fragments, spec.bonds)
    assert lengths is not None
    assert len(lengths) == PYRANOSE_RING_BOND_COUNT
    assert has_pyranose_ring(spec)


def test_chair_factors_match_lean_rationals() -> None:
    diam = pyranose_chair_diameter_factor()
    open_cell = pyranose_chair_open_factor()
    assert abs(diam - 17.0 / 5.0) < 1e-12
    assert abs(open_cell - 11.0 / 10.0) < 1e-12
    assert abs(pyranose_molecules_per_cell() - 4) == 0


def test_methanol_not_pyranose() -> None:
    spec = foundation_spec("CH3OH")
    assert pyranose_ring_mean_bond_angstrom(spec) is None


def test_glucose_chair_template_preferred() -> None:
    spec = foundation_spec("C6H12O6_alpha")
    mono = infer_monomer_geometry(spec)
    templates = templates_for_motif(mono.motif, spec=spec)
    assert templates[0].topology == BravaisTopology.PYRANOSE_CHAIR_Z4
    assert templates[0].molecules_per_cell == 4


def test_glucose_density_tier0_gate() -> None:
    """Solid ρ within tier-0 condensed envelope (≤ 0.1% vs NIST witness)."""
    spec = foundation_spec("C6H12O6_alpha")
    ref = next(r for r in SUGAR_FOUNDATION_REFERENCES if r.name == "C6H12O6_alpha")
    cand = preferred_allotrope(spec)
    assert cand.label == "chair"
    assert ref.reference_density_g_cm3 is not None
    err_pct = abs(cand.density_g_cm3 - ref.reference_density_g_cm3) / ref.reference_density_g_cm3 * 100.0
    assert err_pct < 0.1, f"rho err {err_pct:.4f}% pred={cand.density_g_cm3:.6f}"


def test_ring_contact_distance_positive() -> None:
    spec = foundation_spec("C6H12O6_alpha")
    mono = infer_monomer_geometry(spec)
    mean = pyranose_ring_mean_bond_angstrom(spec)
    assert mean is not None
    r = pyranose_ring_contact_distance_angstrom(mean, n_inter=mono.intermolecular_contacts)
    assert 5.0 < r < 6.5


def test_anisotropic_axes_ordering() -> None:
    """Stack axis b > in-plane a > short projection c (carbohydrate orthorhombic)."""
    a = pyranose_chair_inplane_axis_factor()
    b = pyranose_chair_stack_axis_factor()
    c = pyranose_chair_short_axis_factor()
    assert b > a > c


def test_sucrose_two_rings() -> None:
    spec = foundation_spec("C12H22O11")
    assert pyranose_ring_count(spec) == 2


if __name__ == "__main__":
    for fn in (
        test_glucose_has_six_member_ring,
        test_chair_factors_match_lean_rationals,
        test_methanol_not_pyranose,
        test_glucose_chair_template_preferred,
        test_glucose_density_tier0_gate,
        test_ring_contact_distance_positive,
        test_anisotropic_axes_ordering,
        test_sucrose_two_rings,
    ):
        fn()
    print("test_pyranose_packing: OK")

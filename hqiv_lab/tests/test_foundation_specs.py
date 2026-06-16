#!/usr/bin/env python3
"""Tests for foundation specs and derived bond geometry."""

from __future__ import annotations

from hqiv_lab.coordination import IntermolecularMotif, infer_monomer_geometry
from hqiv_lab.derived_bond_geometry import bond_length_angstrom
from hqiv_lab.foundation_specs import foundation_spec
from hqiv_lab.spec import resolve_spec


def test_foundation_specs_resolve() -> None:
    spec = resolve_spec("CH3OH")
    assert spec.name == "CH3OH"
    assert len(spec.fragments) >= 4
    assert len(spec.bonds) >= 4


def test_methanol_polyol_motif() -> None:
    mono = infer_monomer_geometry(foundation_spec("CH3OH"))
    assert mono.motif == IntermolecularMotif.POLYOL_HBOND


def test_glycylglycine_peptide_motif() -> None:
    mono = infer_monomer_geometry(foundation_spec("GlyGly"))
    assert mono.motif == IntermolecularMotif.PEPTIDE_LAYER


def test_derived_bond_lengths_positive() -> None:
    r = bond_length_angstrom("C", "O", coord_i=4, coord_j=1)
    assert 1.0 < r < 2.0


def test_glucose_pyranose_spec() -> None:
    spec = foundation_spec("C6H12O6_alpha")
    assert spec.name == "C6H12O6_alpha"
    mono = infer_monomer_geometry(spec)
    assert mono.motif == IntermolecularMotif.POLYOL_HBOND
    assert mono.intermolecular_contacts >= 5


if __name__ == "__main__":
    for fn in (
        test_foundation_specs_resolve,
        test_methanol_polyol_motif,
        test_glycylglycine_peptide_motif,
        test_derived_bond_lengths_positive,
        test_glucose_pyranose_spec,
    ):
        fn()
    print("test_foundation_specs: OK")

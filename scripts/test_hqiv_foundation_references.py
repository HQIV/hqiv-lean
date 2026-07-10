#!/usr/bin/env python3
"""Tests for foundation reference witness catalog."""

from __future__ import annotations

from pathlib import Path

import hqiv_foundation_references as fref
from hqiv_lab.foundation_panel import (
    PEPTIDE_FOLD_REFERENCES,
    SUGAR_FOUNDATION_REFERENCES,
    foundation_entry,
    peptide_fold_entry,
)


def test_foundation_json_export() -> None:
    payload = fref.build_payload()
    assert payload["comparison_policy"]
    assert "must not read reference" in payload["builder_policy"].lower()
    assert payload["summary"]["tier1_sugar_count"] == len(SUGAR_FOUNDATION_REFERENCES)
    assert payload["summary"]["tier3_peptide_fold_count"] == len(PEPTIDE_FOLD_REFERENCES)


def test_sugar_references_spec_flags() -> None:
    mono = next(r for r in SUGAR_FOUNDATION_REFERENCES if r.name == "C6H12O6_monohydrate")
    assert not mono.hqiv_spec_available
    alpha = next(r for r in SUGAR_FOUNDATION_REFERENCES if r.name == "C6H12O6_alpha")
    assert alpha.hqiv_spec_available


def test_foundation_entry_lookup() -> None:
    row = foundation_entry("C12H22O11")
    assert row.reference_density_g_cm3 == 1.587
    assert row.reference_melt_k == 462.0


def test_peptide_fold_ladder_ordering() -> None:
    names = [r.name for r in PEPTIDE_FOLD_REFERENCES]
    assert names.index("GG") < names.index("trp_cage")


def test_no_builder_imports_foundation_panel() -> None:
    """Builders must not depend on foundation_panel (witness-only module)."""
    repo = Path(__file__).resolve().parents[1]
    builder_globs = (
        list((repo / "hqiv_lab").glob("coordination.py"))
        + list((repo / "hqiv_lab").glob("packing.py"))
        + list((repo / "hqiv_lab").glob("allotrope.py"))
        + list((repo / "scripts").glob("hqiv_phase_geometry_density.py"))
        + list((repo / "scripts").glob("hqiv_dynamic_binding_chart.py"))
    )
    for path in builder_globs:
        text = path.read_text()
        assert "foundation_panel" not in text, f"{path} must not import foundation_panel"


def test_peptide_geometry_refs_are_external_only() -> None:
    row = peptide_fold_entry("GG")
    assert row.ca_rmsd_pass_angstrom == 2.0
    assert row.structure_id is not None


def test_peptide_fold_competitive_gate() -> None:
    for row in PEPTIDE_FOLD_REFERENCES:
        assert row.ca_rmsd_pass_angstrom == 2.0, row.name
    assert peptide_fold_entry("trp_cage").ca_rmsd_pass_angstrom == 2.0


if __name__ == "__main__":
    for fn in (
        test_foundation_json_export,
        test_sugar_references_spec_flags,
        test_foundation_entry_lookup,
        test_peptide_fold_ladder_ordering,
        test_no_builder_imports_foundation_panel,
        test_peptide_geometry_refs_are_external_only,
        test_peptide_fold_competitive_gate,
    ):
        fn()
    print("test_hqiv_foundation_references: OK")

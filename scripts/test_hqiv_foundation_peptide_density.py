#!/usr/bin/env python3
"""Foundation tier-1 peptide solid density gate."""

from __future__ import annotations

from hqiv_lab.allotrope import preferred_allotrope
from hqiv_lab.foundation_panel import PEPTIDE_CRYSTAL_REFERENCES
from hqiv_lab.foundation_specs import foundation_spec


def test_glygly_sheet_density_envelope() -> None:
    ref = next(r for r in PEPTIDE_CRYSTAL_REFERENCES if r.name == "GlyGly")
    spec = foundation_spec("GlyGly")
    cand = preferred_allotrope(spec)
    assert cand.label == "sheet"
    assert ref.reference_density_g_cm3 is not None
    err = abs(cand.density_g_cm3 - ref.reference_density_g_cm3) / ref.reference_density_g_cm3 * 100.0
    assert err < 2.0, f"GlyGly rho err {err:.2f}% pred={cand.density_g_cm3:.4f}"


if __name__ == "__main__":
    test_glygly_sheet_density_envelope()
    print("test_hqiv_foundation_peptide_density: OK")

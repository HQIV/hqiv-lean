#!/usr/bin/env python3
"""Foundation tier-1 optical + disaccharide density gates."""

from __future__ import annotations

import hqiv_phase_material_response as pmr
from hqiv_lab.allotrope import preferred_allotrope
from hqiv_lab.foundation_panel import POLYOL_FOUNDATION_REFERENCES, SUGAR_FOUNDATION_REFERENCES
from hqiv_lab.foundation_specs import foundation_spec
from hqiv_lab.pyranose_geometry import pyranose_ring_count


def test_glycerol_liquid_refractive_index() -> None:
    ref = next(r for r in POLYOL_FOUNDATION_REFERENCES if r.name == "C3H8O3")
    out = pmr.material_response_readout("C3H8O3", phase="liquid", temperature_k=298.15)
    assert ref.reference_refractive_index is not None
    err = abs(out["refractive_index"] - ref.reference_refractive_index) / ref.reference_refractive_index * 100.0
    assert err < 5.0, f"glycerol n err {err:.2f}% n={out['refractive_index']:.4f}"


def test_sucrose_solid_density_envelope() -> None:
    ref = next(r for r in SUGAR_FOUNDATION_REFERENCES if r.name == "C12H22O11")
    spec = foundation_spec("C12H22O11")
    assert pyranose_ring_count(spec) == 2
    cand = preferred_allotrope(spec)
    assert cand.label == "chair"
    assert ref.reference_density_g_cm3 is not None
    err = abs(cand.density_g_cm3 - ref.reference_density_g_cm3) / ref.reference_density_g_cm3 * 100.0
    assert err < 5.0, f"sucrose rho err {err:.2f}% pred={cand.density_g_cm3:.4f}"


def test_glucose_solid_refractive_index_sane() -> None:
    out = pmr.material_response_readout(
        "C6H12O6_alpha",
        allotrope="chair",
        phase="solid",
        temperature_k=414.0,
    )
    n = out["refractive_index"]
    assert 1.3 < n < 2.2, f"glucose solid n={n:.4f} outside organic crystal envelope"


if __name__ == "__main__":
    test_glycerol_liquid_refractive_index()
    test_sucrose_solid_density_envelope()
    test_glucose_solid_refractive_index_sane()
    print("test_hqiv_foundation_polyol_optical: OK")

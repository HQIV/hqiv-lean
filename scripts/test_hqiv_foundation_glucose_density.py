#!/usr/bin/env python3
"""Foundation glucose solid density gate (tier-0 envelope)."""

from __future__ import annotations

import hqiv_phase_geometry_density as pgd
from hqiv_lab.foundation_panel import SUGAR_FOUNDATION_REFERENCES


def test_glucose_alpha_solid_density_tier0_envelope() -> None:
    ref = next(r for r in SUGAR_FOUNDATION_REFERENCES if r.name == "C6H12O6_alpha")
    geom = pgd.melt_readout_with_phase_geometry(
        "C6H12O6_alpha",
        allotrope=ref.allotrope,
        temperature_at_melt_k=ref.witness_temperature_k,
    )
    pred = geom["density_g_cm3"]
    witness = ref.reference_density_g_cm3
    err_pct = abs(pred - witness) / witness * 100.0
    assert err_pct < 0.1, f"C6H12O6_alpha rho err {err_pct:.4f}% pred={pred:.6f} ref={witness}"


if __name__ == "__main__":
    test_glucose_alpha_solid_density_tier0_envelope()
    print("test_hqiv_foundation_glucose_density: OK")

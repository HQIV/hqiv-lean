#!/usr/bin/env python3
"""
Golden check: Lean lock-in numerals ↔ Python spine mirror ↔ resonance ratios.

Exits 0 when all structural checks pass. Run after `lake build HqivSpine`:

  python3 scripts/hqiv_spine_golden_check.py
"""

from __future__ import annotations

import math
import sys

import hqiv_spine_mev_discharge_bridge as bridge

MASS_UNIT = bridge.MASS_UNIT_LOCKIN
TOL = 1e-12

# Lean `LeptonAbsoluteScale` lock-in readouts (massUnit = 5)
LEAN_LOCKIN = {
    1: 3798480 / 784700,
    2: 304 / 35,
    3: 20.0,
}

# Lean `NeutrinoAbsoluteScale` lock-in absolute (m_ℓ / 140)
LEAN_NU_ABS = {
    1: 3798480 / 109858000,
    2: 304 / 4900,
    3: 1 / 7,
}


def assert_close(label: str, got: float, expected: float) -> None:
    if not math.isclose(got, expected, rel_tol=0, abs_tol=TOL):
        raise AssertionError(f"{label}: got {got}, expected {expected}")


def main() -> int:
    errors: list[str] = []

    for w, lean_val in LEAN_LOCKIN.items():
        py_val = bridge.spine_lepton_readout(w, MASS_UNIT)
        if not math.isclose(py_val, lean_val, rel_tol=0, abs_tol=TOL):
            errors.append(f"lepton winding {w}: python {py_val} != lean {lean_val}")

    mu_e = bridge.spine_lepton_readout(2) / bridge.spine_lepton_readout(1)
    tau_mu = bridge.spine_lepton_readout(3) / bridge.spine_lepton_readout(2)
    if not math.isclose(mu_e, bridge.RESONANCE_MU_OVER_E, rel_tol=0, abs_tol=TOL):
        errors.append(f"μ/e {mu_e} != {bridge.RESONANCE_MU_OVER_E}")
    if not math.isclose(tau_mu, bridge.RESONANCE_TAU_OVER_MU, rel_tol=0, abs_tol=TOL):
        errors.append(f"τ/μ {tau_mu} != {bridge.RESONANCE_TAU_OVER_MU}")

    for w, lean_val in LEAN_NU_ABS.items():
        py_val = bridge.spine_neutrino_absolute(w, MASS_UNIT)
        if not math.isclose(py_val, lean_val, rel_tol=0, abs_tol=TOL):
            errors.append(f"ν abs winding {w}: python {py_val} != lean {lean_val}")

    assert_close("ν/e", bridge.spine_neutrino_absolute(1) / bridge.spine_lepton_readout(1), 1 / 140)
    assert_close("C_A/C_F gen1", bridge.spine_quark_readout(1) / bridge.spine_lepton_readout(1), 9 / 4)
    assert_close("proton readout", bridge.spine_proton_readout(), 20.0)

    if errors:
        print("HQIV spine golden check FAILED:")
        for e in errors:
            print(f"  • {e}")
        return 1

    print("HQIV spine golden check OK")
    print(f"  lock-in μ/e = {mu_e:.6g}  (4484/2499)")
    print(f"  lock-in τ/μ = {tau_mu:.6g}  (175/76)")
    print(f"  ν suppression = {bridge.NEUTRINO_SUPPRESSION:.6g}  (1/140)")
    return 0


if __name__ == "__main__":
    sys.exit(main())

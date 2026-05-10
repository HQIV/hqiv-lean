#!/usr/bin/env python3
"""
Compare Python-side quantum-chemistry formulas against Lean-exported witnesses.

Usage:
  1) lake env lean --run scripts/export_quantum_chem_witnesses.lean
  2) python3 scripts/compare_quantum_chem_witnesses.py
"""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any, Dict, List


DATA_PATH = Path("data/quantum_chem_witnesses.json")
ABS_TOL = 1e-9


def available_modes(m: int) -> float:
    return 4.0 * (m + 2) * (m + 1)


def phi_of_shell(m: int) -> float:
    return 2.0 * (m + 1)


def lattice_full_mode_energy(m: int) -> float:
    return available_modes(m) * (phi_of_shell(m) / 2.0)


def h2_equal_shell_trace(m: int) -> float:
    return 2.0 * lattice_full_mode_energy(m)


def assert_close(label: str, got: float, expected: float, failures: List[str]) -> None:
    if not math.isclose(got, expected, rel_tol=0.0, abs_tol=ABS_TOL):
        failures.append(f"{label}: got {got}, expected {expected}")


def main() -> None:
    if not DATA_PATH.exists():
        raise SystemExit(
            f"Missing {DATA_PATH}. Run: lake env lean --run scripts/export_quantum_chem_witnesses.lean"
        )

    data: Dict[str, Any] = json.loads(DATA_PATH.read_text())
    failures: List[str] = []

    reference_m = int(data["referenceM"])
    h2_ref = float(data["h2_trace_referenceM"])
    h2_ref_expected = float(data["h2_trace_referenceM_expected"])

    # Direct witness consistency
    assert_close("h2_trace_referenceM vs expected field", h2_ref, h2_ref_expected, failures)
    assert_close(
        "h2_trace_referenceM vs python formula",
        h2_ref,
        h2_equal_shell_trace(reference_m),
        failures,
    )

    # Reference-shell site energy consistency
    site_ref = float(data["site_energy_referenceM"])
    assert_close(
        "site_energy_referenceM vs python formula",
        site_ref,
        lattice_full_mode_energy(reference_m),
        failures,
    )

    # Deterministic sweep done on Python side for quick sim sanity.
    for m in range(0, 9):
        assert_close(f"site_energy_formula(m={m})", lattice_full_mode_energy(m), 4.0 * (m + 2) * (m + 1) ** 2, failures)
        assert_close(f"h2_trace_formula(m={m})", h2_equal_shell_trace(m), 8.0 * (m + 2) * (m + 1) ** 2, failures)

    print("Quantum chemistry witness comparison")
    print("=" * 40)
    print(f"referenceM = {reference_m}")
    print(f"h2_trace_referenceM = {h2_ref}")
    print("rows_checked = 9 (python sweep m=0..8)")

    if failures:
        print("\nFAIL")
        for f in failures:
            print(f"- {f}")
        raise SystemExit(1)

    print("\nPASS: Python formulas match Lean witnesses.")


if __name__ == "__main__":
    main()

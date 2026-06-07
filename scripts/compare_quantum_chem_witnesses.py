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
import argparse
from pathlib import Path
from typing import Any, Dict, List


DATA_PATH = Path("data/quantum_chem_witnesses.json")
XI_SCAN_PATH = Path("data/quantum_chem_site_energy_xi_scan.json")
LIH_DYNAMIC_PATH = Path("data/lih_dynamic_binding.json")
ABS_TOL = 1e-9


def xi_of_shell(m: int) -> float:
    return float(m + 1)


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


# LiH Compton valence shells (Lean: `Hqiv.QuantumChemistry.LiH`)
LIH_COMPTON_M_LI_S = 4
LIH_COMPTON_M_LI_P = 3
LIH_COMPTON_M_H_S = 1


def lih_valence_sites_block() -> Dict[str, Any]:
    """Compton `(4,3,1)` triplet aligned with `lihValenceSpec` / `lihComptonUsedShells_eq_spec`."""
    return {
        "Li_s": {
            "m": LIH_COMPTON_M_LI_S,
            "xi": xi_of_shell(LIH_COMPTON_M_LI_S),
            "E_site": lattice_full_mode_energy(LIH_COMPTON_M_LI_S),
            "multiplicity": 1,
        },
        "Li_p": {
            "m": LIH_COMPTON_M_LI_P,
            "xi": xi_of_shell(LIH_COMPTON_M_LI_P),
            "E_site": lattice_full_mode_energy(LIH_COMPTON_M_LI_P),
            "multiplicity": 3,
        },
        "H_s": {
            "m": LIH_COMPTON_M_H_S,
            "xi": xi_of_shell(LIH_COMPTON_M_H_S),
            "E_site": lattice_full_mode_energy(LIH_COMPTON_M_H_S),
            "multiplicity": 1,
        },
    }


def lih_valence_trace_dimless() -> float:
    sites = lih_valence_sites_block()
    return (
        sites["Li_s"]["E_site"]
        + sites["Li_p"]["multiplicity"] * sites["Li_p"]["E_site"]
        + sites["H_s"]["E_site"]
    )


def lean_lih_bridge_witness_block() -> Dict[str, Any]:
    """
    Formal pedigree for the Compton shell triplet (local increment bridge + imprint phases).

    Lean supplies the theorems; supplying `LiHComptonOmegaKBridge` is the finite witness
    obligation (discharge via `liHComptonOmegaKBridge_from_global` when global bridge holds).
    """
    return {
        "lean_module": "Hqiv.QuantumChemistry.LiH",
        "derivation_module": "Hqiv.QuantumChemistry.LiHDerivation",
        "compton_shells_m": [LIH_COMPTON_M_LI_S, LIH_COMPTON_M_LI_P, LIH_COMPTON_M_H_S],
        "compton_shells_xi": [
            xi_of_shell(LIH_COMPTON_M_LI_S),
            xi_of_shell(LIH_COMPTON_M_LI_P),
            xi_of_shell(LIH_COMPTON_M_H_S),
        ],
        "omega_k_bridge": {
            "predicate": "lihLocalOmegaKIncrementBridge",
            "payload": "LiHComptonOmegaKBridge",
            "witnessed_in_lean": True,
            "note": (
                "Local Ωₖ increment bridge at m=4,3,1; imprint phases match on integer "
                "steps when payload is supplied (theorems "
                "lihCompton_*_imprintWeightedReadoutPhase_xi_matches)."
            ),
        },
        "imprint_phase_theorems": {
            "lihCompton_LiS_imprintWeightedReadoutPhase_xi_matches": True,
            "lihCompton_LiP_imprintWeightedReadoutPhase_xi_matches": True,
            "lihCompton_HS_imprintWeightedReadoutPhase_xi_matches": True,
            "lihCompton_imprintWeightedReadoutPhases_justified": True,
            "lihCompton_LiP_seedPotential_omega_from_discrete_imprint": True,
            "lihComptonDerivedDissociationIndicator_with_justified_readouts": True,
        },
        "used_shells_lemma": "lihComptonUsedShells_eq_spec",
    }


def site_energy_xi_rows(max_m: int) -> List[Dict[str, Any]]:
    return [
        {
            "m": m,
            "xi": xi_of_shell(m),
            "site_energy": lattice_full_mode_energy(m),
            "h2_equal_shell_trace": h2_equal_shell_trace(m),
        }
        for m in range(max_m + 1)
    ]


def main() -> None:
    parser = argparse.ArgumentParser(description="Compare Lean QC witnesses and export ξ-indexed site energies.")
    parser.add_argument("--max-m", type=int, default=8, help="largest shell to include in the Python ξ scan")
    parser.add_argument("--xi-out", type=Path, default=XI_SCAN_PATH, help="JSON path for ξ-indexed site energies")
    args = parser.parse_args()

    if args.max_m < 0:
        raise SystemExit("--max-m must be nonnegative")

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
    rows = site_energy_xi_rows(args.max_m)
    for row in rows:
        m = int(row["m"])
        assert_close(f"site_energy_formula(m={m})", lattice_full_mode_energy(m), 4.0 * (m + 2) * (m + 1) ** 2, failures)
        assert_close(f"h2_trace_formula(m={m})", h2_equal_shell_trace(m), 8.0 * (m + 2) * (m + 1) ** 2, failures)

    lih_sites = lih_valence_sites_block()
    lih_trace = lih_valence_trace_dimless()
    lean_bridge = lean_lih_bridge_witness_block()

    # Dynamic binding chart + LiH dynamic binding
    try:
        import hqiv_dynamic_binding_chart as binding_chart  # noqa: WPS433

        chart_payload = binding_chart.build_chart_payload()
        CHART_PATH = Path("data/dynamic_binding_chart.json")
        CHART_PATH.parent.mkdir(parents=True, exist_ok=True)
        CHART_PATH.write_text(json.dumps(chart_payload, indent=2) + "\n")
    except Exception as exc:  # pragma: no cover
        chart_payload = {"error": str(exc)}

    try:
        import hqiv_lih_dynamic_binding as lih_dynamic  # noqa: WPS433

        lih_dynamic_payload = lih_dynamic.build_payload()
        LIH_DYNAMIC_PATH.parent.mkdir(parents=True, exist_ok=True)
        LIH_DYNAMIC_PATH.write_text(json.dumps(lih_dynamic_payload, indent=2) + "\n")
    except Exception as exc:  # pragma: no cover - optional path during partial installs
        lih_dynamic_payload = {"error": str(exc)}

    xi_export = {
        "source": "scripts/compare_quantum_chem_witnesses.py",
        "referenceM": reference_m,
        "xi_referenceM": xi_of_shell(reference_m),
        "closed_form": {
            "xi_of_shell": "m+1",
            "site_energy_xi": "4*(xi+1)*xi^2",
            "h2_equal_shell_trace_xi": "8*(xi+1)*xi^2",
        },
        "rows": rows,
        "lih_valence_sites": lih_sites,
        "lih_valence_trace_dimless": lih_trace,
        "lean_lih_compton_bridge": lean_bridge,
        "lih_dynamic_binding": lih_dynamic_payload,
        "dynamic_binding_chart": chart_payload,
    }
    args.xi_out.parent.mkdir(parents=True, exist_ok=True)
    args.xi_out.write_text(json.dumps(xi_export, indent=2) + "\n")

    witness_out = {
        **data,
        "lih_valence_sites": lih_sites,
        "lih_valence_trace_dimless": lih_trace,
        "lean_lih_compton_bridge": lean_bridge,
        "lih_dynamic_binding": lih_dynamic_payload,
        "dynamic_binding_chart": chart_payload,
    }
    DATA_PATH.write_text(json.dumps(witness_out, indent=2) + "\n")

    print("Quantum chemistry witness comparison")
    print("=" * 40)
    print(f"referenceM = {reference_m}")
    print(f"xi_referenceM = {xi_of_shell(reference_m)}")
    print(f"h2_trace_referenceM = {h2_ref}")
    print(f"rows_checked = {len(rows)} (python sweep m=0..{args.max_m})")
    print(f"xi_scan_export = {args.xi_out}")
    print(f"witness_updated = {DATA_PATH}")
    print(f"lih_valence_trace_dimless = {lih_trace}")
    if "primary_binding_ev" in lih_dynamic_payload:
        print(
            f"lih_dynamic_binding_ev = {lih_dynamic_payload['primary_binding_ev']:.6f} "
            f"(err {lih_dynamic_payload['primary_error_pct']:+.2f}%)"
        )
        print(f"lih_dynamic_export = {LIH_DYNAMIC_PATH}")
    if "summary" in chart_payload:
        s = chart_payload["summary"]
        print(
            f"dynamic_binding_chart: n={s['count']} mean|err|={s['mean_abs_error_pct']:.2f}% "
            f"≤5%={s['within_5pct']}/{s['count']}"
        )

    if failures:
        print("\nFAIL")
        for f in failures:
            print(f"- {f}")
        raise SystemExit(1)

    print("\nPASS: Python formulas match Lean witnesses.")


if __name__ == "__main__":
    main()

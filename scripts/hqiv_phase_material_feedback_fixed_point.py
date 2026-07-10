#!/usr/bin/env python3
"""
Bounded two-way phase-material feedback witness.

Promotes the audited loop:

  phase density -> B_hom/material response -> updated phase density

The existing material-response script remains the one-way readout.  This script
wraps it with a short, clamped fixed-point trace so the feedback can be inspected
without turning it into an untracked fit.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path
from typing import Any

_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

import hqiv_phase_material_response as pmr
import hqiv_two_way_feedback_dynamics as twf

DEFAULT_JSON = _REPO_ROOT / "data" / "phase_material_feedback_fixed_point.json"


DEFAULT_CASES: tuple[dict[str, Any], ...] = (
    {"molecule": "H2O", "allotrope": "Ih", "phase": "solid", "temperature_k": 273.15},
    {"molecule": "H2O", "allotrope": None, "phase": "liquid", "temperature_k": 273.15},
    {"molecule": "CH4", "allotrope": "solid_I", "phase": "solid", "temperature_k": 90.7},
    {"molecule": "NH3", "allotrope": None, "phase": "liquid", "temperature_k": 195.0},
    {"molecule": "HF", "allotrope": None, "phase": "solid", "temperature_k": 190.0},
)


TRACKED_KEYS = (
    "refractive_index",
    "dielectric_constant",
    "thermal_conductivity_W_mK",
    "ionic_conductivity_S_m",
    "molar_heat_capacity_J_per_mol_K",
    "dynamic_viscosity_Pa_s",
    "B_hom",
)


def _delta(before: float, after: float) -> dict[str, float | None]:
    if not (math.isfinite(before) and math.isfinite(after)):
        return {"absolute": None, "percent": None}
    pct = None if abs(before) <= 1.0e-30 else 100.0 * (after - before) / before
    return {"absolute": after - before, "percent": pct}


def phase_material_fixed_point_row(
    molecule: str,
    *,
    allotrope: str | None = None,
    phase: str = "solid",
    temperature_k: float = 273.15,
    max_steps: int = 40,
    tolerance: float = 1.0e-6,
    damping: float = 1.0,
) -> dict[str, Any]:
    """One bounded material-response feedback trace."""
    base = pmr.material_response_readout(
        molecule,
        allotrope=allotrope,
        phase=phase,  # type: ignore[arg-type]
        temperature_k=temperature_k,
    )
    initial_rho = float(base["curvature_density_fraction"])

    def step(rho_curv: float) -> float:
        out = pmr.material_response_readout(
            molecule,
            allotrope=allotrope,
            phase=phase,  # type: ignore[arg-type]
            temperature_k=temperature_k,
            rho_curv=rho_curv,
        )
        return float(out["network_propagated_curvature_density_fraction"])

    trace = twf.bounded_fixed_point(
        initial_rho,
        step,
        max_steps=max_steps,
        tolerance=tolerance,
        damping=damping,
    )
    final = pmr.material_response_readout(
        molecule,
        allotrope=allotrope,
        phase=phase,  # type: ignore[arg-type]
        temperature_k=temperature_k,
        rho_curv=trace.final_state,
    )
    deltas = {
        key: _delta(float(base[key]), float(final[key]))
        for key in TRACKED_KEYS
        if key in base and key in final
    }
    return {
        "molecule": molecule,
        "phase": phase,
        "allotrope": final["allotrope"],
        "temperature_K": temperature_k,
        "feedback_policy": (
            "rho_curv starts from phase geometry; each step reads the material "
            "network-propagated curvature density and clamps it to [0,1]"
        ),
        "initial_response": {key: base[key] for key in TRACKED_KEYS if key in base},
        "fixed_point_response": {key: final[key] for key in TRACKED_KEYS if key in final},
        "response_delta": deltas,
        "trace": trace.to_dict(),
    }


def build_payload(
    cases: tuple[dict[str, Any], ...] = DEFAULT_CASES,
    *,
    max_steps: int = 40,
    tolerance: float = 1.0e-6,
    damping: float = 1.0,
) -> dict[str, Any]:
    rows = tuple(
        phase_material_fixed_point_row(
            str(case["molecule"]),
            allotrope=case.get("allotrope"),
            phase=str(case.get("phase", "solid")),
            temperature_k=float(case.get("temperature_k", 273.15)),
            max_steps=max_steps,
            tolerance=tolerance,
            damping=damping,
        )
        for case in cases
    )
    traces = tuple(
        twf.FixedPointTrace(
            initial_state=float(row["trace"]["initial_state"]),
            final_state=float(row["trace"]["final_state"]),
            converged=bool(row["trace"]["converged"]),
            tolerance=float(row["trace"]["tolerance"]),
            steps=tuple(
                twf.FixedPointStep(
                    int(step["index"]),
                    float(step["state"]),
                    float(step["next_state"]),
                    float(step["delta"]),
                )
                for step in row["trace"]["steps"]
            ),
        )
        for row in rows
    )
    return {
        "source": "scripts/hqiv_phase_material_feedback_fixed_point.py",
        "loop": "phase density -> B_hom/material response -> phase density",
        "lean_modules": [
            "Hqiv.QuantumChemistry.PhaseGeometryDensity",
            "Hqiv.QuantumChemistry.PhaseMaterialResponse",
            "Hqiv.QuantumChemistry.HomogeneousCurvatureSecondOrder",
        ],
        "max_steps": max_steps,
        "tolerance": tolerance,
        "damping": damping,
        "summary": twf.summarize_traces(traces),
        "rows": list(rows),
    }


def print_report(payload: dict[str, Any]) -> None:
    print("=== Phase-material fixed-point feedback ===")
    print(
        f"steps <= {payload['max_steps']}  damping={payload['damping']:.2f}  "
        f"tolerance={payload['tolerance']:.1e}"
    )
    summary = payload["summary"]
    print(
        f"converged {summary['converged']}/{summary['count']}  "
        f"mean |Δrho|={summary['mean_abs_shift']:.4f}  "
        f"max |Δrho|={summary['max_abs_shift']:.4f}"
    )
    print()
    for row in payload["rows"]:
        trace = row["trace"]
        print(
            f"-- {row['molecule']} {row['phase']} ({row['allotrope']}) "
            f"@ {row['temperature_K']:.2f} K"
        )
        print(
            f"   rho_curv {trace['initial_state']:.5f} -> {trace['final_state']:.5f} "
            f"({'converged' if trace['converged'] else 'bounded'})"
        )
        n_delta = row["response_delta"]["refractive_index"]
        k_delta = row["response_delta"]["thermal_conductivity_W_mK"]
        b_delta = row["response_delta"]["B_hom"]
        print(
            f"   Δn={n_delta['absolute']:+.5f}  "
            f"Δk_th={k_delta['percent']:+.2f}%  ΔB_hom={b_delta['absolute']:+.5f}"
        )
    print()


def main() -> None:
    parser = argparse.ArgumentParser(description="Bounded phase-material feedback witness.")
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    parser.add_argument("--max-steps", type=int, default=40)
    parser.add_argument("--tolerance", type=float, default=1.0e-6)
    parser.add_argument("--damping", type=float, default=1.0)
    args = parser.parse_args()

    payload = build_payload(
        max_steps=args.max_steps,
        tolerance=args.tolerance,
        damping=args.damping,
    )
    print_report(payload)
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()

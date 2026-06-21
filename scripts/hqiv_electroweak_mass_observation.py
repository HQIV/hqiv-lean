#!/usr/bin/env python3
"""
Electroweak mass observation chart: pole TUFT mass × facility outside curvature.

Mirrors `Hqiv/Physics/ElectroweakMassObservation.lean`.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal

import hqiv_hep_decay_readout as hdr
import hqiv_lean_physics_primitives as lean
import hqiv_tuft_electroweak_boson_readout as ew
import hqiv_weak_fano_hopf_bridge as wb

ElectroweakMassMethod = Literal[
    "lep_line_shape",
    "tevatron_kinematic",
    "lhc_kinematic",
    "global_ew_blend",
]

DressingChart = Literal["line_shape", "collider_universal", "collider_native"]

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OBSERVATIONS = ROOT / "data" / "electroweak_mass_observations.json"
XI_LOCKIN = lean.XI_LOCKIN
GAMMA = lean.GAMMA
KINEMATIC_COUPLING_EXPONENT_LHC = GAMMA / 5.0
KINEMATIC_COUPLING_EXPONENT_D0 = 11.0 / 125.0

# Exact mirrors of `Hqiv/Physics/ElectroweakMassObservation.lean` facility defs.
LEAN_FACILITY_PRESETS: dict[str, dict[str, Any]] = {
    "lep_line_shape": {
        "method": "lep_line_shape",
        "dressing_chart": "line_shape",
        "magnetic_field_tesla": 0.0,
        "collider_reference_tesla": 4.0,
        "comoving_stream_fraction": 0.0,
        "line_shape_stream_fraction": 0.0,
        "kinematic_coupling_exponent": 1.0,
    },
    "cdf_tevatron": {
        "method": "tevatron_kinematic",
        "dressing_chart": "collider_universal",
        "magnetic_field_tesla": 1411.0 / 1000.0,
        "collider_reference_tesla": 4.0,
        "comoving_stream_fraction": 0.0,
        "line_shape_stream_fraction": 0.0,
        "kinematic_coupling_exponent": 1.0,
    },
    "d0_tevatron": {
        "method": "tevatron_kinematic",
        "dressing_chart": "collider_native",
        "magnetic_field_tesla": 2.0,
        "collider_reference_tesla": 4.0,
        "comoving_stream_fraction": 6.0 / 100.0,
        "line_shape_stream_fraction": 0.0,
        "kinematic_coupling_exponent": KINEMATIC_COUPLING_EXPONENT_D0,
    },
    "cms_lhc": {
        "method": "lhc_kinematic",
        "dressing_chart": "collider_native",
        "magnetic_field_tesla": 38.0 / 10.0,
        "collider_reference_tesla": 4.0,
        "comoving_stream_fraction": 12.0 / 100.0,
        "line_shape_stream_fraction": 0.0,
        "kinematic_coupling_exponent": KINEMATIC_COUPLING_EXPONENT_LHC,
    },
    "atlas_lhc": {
        "method": "lhc_kinematic",
        "dressing_chart": "collider_native",
        "magnetic_field_tesla": 2.0,
        "collider_reference_tesla": 4.0,
        "comoving_stream_fraction": 12.0 / 100.0,
        "line_shape_stream_fraction": 0.0,
        "kinematic_coupling_exponent": KINEMATIC_COUPLING_EXPONENT_LHC,
    },
}


def line_shape_radiative_stack_density() -> float:
    """Lean `lineShapeRadiativeStackDensity` = 15γ/64."""
    return GAMMA / 8.0 + GAMMA / 16.0 + GAMMA / 32.0 + GAMMA / 64.0


def line_shape_mass_factor(stream_fraction: float = 0.0) -> float:
    """Lean `lineShapeMassFactor`: 1 + γ·S·(radiative_stack + stream²)."""
    s = wb.weak_bridge_shape()
    stream = max(stream_fraction, 0.0) ** 2
    return 1.0 + GAMMA * s * (line_shape_radiative_stack_density() + stream)


@dataclass(frozen=True)
class ElectroweakFacilitySetup:
    id: str
    method: ElectroweakMassMethod
    dressing_chart: DressingChart = "collider_universal"
    magnetic_field_tesla: float = 0.0
    collider_reference_tesla: float = 4.0
    comoving_stream_fraction: float = 0.0
    line_shape_stream_fraction: float = 0.0
    kinematic_coupling_exponent: float = 1.0
    sqrt_s_tev: float | None = None
    notes: str = ""

    def effective_collider_reference_tesla(self) -> float:
        if self.dressing_chart == "collider_native":
            return max(self.magnetic_field_tesla, 1e-9)
        return max(self.collider_reference_tesla, 1e-9)

    def collider_width_factor(self) -> float:
        return hdr.collider_curvature_width_factor(
            self.magnetic_field_tesla,
            self.effective_collider_reference_tesla(),
            self.comoving_stream_fraction,
            weak_bridge_shape=wb.weak_bridge_shape(),
        )

    def collider_kinematic_mass_factor(self) -> float:
        return self.collider_width_factor() ** self.kinematic_coupling_exponent

    def facility_mass_dressing_factor(self) -> float:
        if self.dressing_chart == "line_shape":
            return line_shape_mass_factor(self.line_shape_stream_fraction)
        return self.collider_kinematic_mass_factor()

    def dressing_ppm(self) -> float:
        return 1.0e6 * (self.facility_mass_dressing_factor() - 1.0)


def pole_mw_mev(xi: float = XI_LOCKIN) -> float:
    return ew.tuft_mw_at_xi_gev(xi) * 1000.0


def apparent_mw_at_facility(
    facility: ElectroweakFacilitySetup,
    *,
    xi: float = XI_LOCKIN,
) -> float:
    return pole_mw_mev(xi) * facility.facility_mass_dressing_factor()


def apparent_mw_uncertainty_mev(
    facility: ElectroweakFacilitySetup,
    *,
    xi: float = XI_LOCKIN,
    pole_sigma_mev: float = 0.0,
    dressing_sigma_ppm: float = 0.0,
) -> float:
    """Quadrature: σ_m ≈ m · sqrt((σ_pole/m)² + σ_dress_ppm²)."""
    m = apparent_mw_at_facility(facility, xi=xi)
    pole = pole_mw_mev(xi)
    rel_pole = (pole_sigma_mev / pole) if pole > 0 else 0.0
    rel_dress = dressing_sigma_ppm / 1.0e6
    return m * math.sqrt(rel_pole * rel_pole + rel_dress * rel_dress)


def facility_from_dict(row: dict[str, Any]) -> ElectroweakFacilitySetup:
    fid = str(row["id"])
    lean_row = LEAN_FACILITY_PRESETS.get(fid, {})
    sqrt_s = row.get("sqrt_s_tev")
    dressing = str(lean_row.get("dressing_chart", row.get("dressing_chart", "collider_universal")))
    exp = lean_row.get("kinematic_coupling_exponent", row.get("kinematic_coupling_exponent"))
    if exp is None and dressing == "collider_native" and fid.startswith("d0"):
        exp = KINEMATIC_COUPLING_EXPONENT_D0
    elif exp is None and dressing == "collider_native":
        exp = KINEMATIC_COUPLING_EXPONENT_LHC
    return ElectroweakFacilitySetup(
        id=fid,
        method=lean_row.get("method", row["method"]),  # type: ignore[arg-type]
        dressing_chart=dressing,  # type: ignore[arg-type]
        magnetic_field_tesla=float(
            lean_row.get("magnetic_field_tesla", row.get("magnetic_field_tesla", 0.0))
        ),
        collider_reference_tesla=float(
            lean_row.get("collider_reference_tesla", row.get("collider_reference_tesla", 4.0))
        ),
        comoving_stream_fraction=float(
            lean_row.get("comoving_stream_fraction", row.get("comoving_stream_fraction", 0.0))
        ),
        line_shape_stream_fraction=float(
            lean_row.get(
                "line_shape_stream_fraction", row.get("line_shape_stream_fraction", 0.0)
            )
        ),
        kinematic_coupling_exponent=float(exp if exp is not None else 1.0),
        sqrt_s_tev=float(sqrt_s) if sqrt_s is not None else None,
        notes=str(row.get("notes", "")),
    )


def load_facilities(observations: dict[str, Any]) -> dict[str, ElectroweakFacilitySetup]:
    return {
        str(row["id"]): facility_from_dict(row)
        for row in observations.get("facilities") or []
    }


def load_observations(path: Path | None = None) -> dict[str, Any]:
    path = path or DEFAULT_OBSERVATIONS
    return json.loads(path.read_text(encoding="utf-8"))


def sensitivity_ledger(
    observations: dict[str, Any] | None = None,
    *,
    xi: float | None = None,
) -> list[dict[str, Any]]:
    """B_ref / exponent perturbations for CDF and CMS rows."""
    observations = observations or load_observations()
    xi = float(xi if xi is not None else observations.get("pole_xi_lock", XI_LOCKIN))
    facilities = load_facilities(observations)
    rows: list[dict[str, Any]] = []
    for case in observations.get("sensitivity_checks") or []:
        base_id = str(case["facility_id"])
        base = facilities[base_id]
        variants: list[dict[str, Any]] = []
        for variant in case.get("variants") or []:
            fac = ElectroweakFacilitySetup(
                id=base.id,
                method=base.method,
                dressing_chart=base.dressing_chart,
                magnetic_field_tesla=float(
                    variant.get("magnetic_field_tesla", base.magnetic_field_tesla)
                ),
                collider_reference_tesla=float(
                    variant.get("collider_reference_tesla", base.collider_reference_tesla)
                ),
                comoving_stream_fraction=float(
                    variant.get("comoving_stream_fraction", base.comoving_stream_fraction)
                ),
                line_shape_stream_fraction=float(
                    variant.get("line_shape_stream_fraction", base.line_shape_stream_fraction)
                ),
                kinematic_coupling_exponent=float(
                    variant.get("kinematic_coupling_exponent", base.kinematic_coupling_exponent)
                ),
                sqrt_s_tev=base.sqrt_s_tev,
                notes=str(variant.get("label", "")),
            )
            variants.append(
                {
                    "label": variant.get("label", "variant"),
                    "apparent_mw_mev": apparent_mw_at_facility(fac, xi=xi),
                    "dressing_ppm": fac.dressing_ppm(),
                }
            )
        rows.append(
            {
                "case_id": case["id"],
                "facility_id": base_id,
                "central_mev": apparent_mw_at_facility(base, xi=xi),
                "variants": variants,
            }
        )
    return rows


def witness_certificate(
    observations: dict[str, Any] | None = None,
    *,
    xi: float | None = None,
) -> dict[str, Any]:
    """Machine-readable witness for papers / Zenodo."""
    observations = observations or load_observations()
    xi = float(xi if xi is not None else observations.get("pole_xi_lock", XI_LOCKIN))
    facilities = load_facilities(observations)
    pole = pole_mw_mev(xi)
    pole_sigma = float(observations.get("pole_sigma_mev", 0.0))
    dress_sigma_ppm = float(observations.get("dressing_sigma_ppm", 0.0))

    predictions = {
        fid: {
            "apparent_mw_mev": apparent_mw_at_facility(fac, xi=xi),
            "dressing_factor": fac.facility_mass_dressing_factor(),
            "dressing_ppm": fac.dressing_ppm(),
            "predicted_sigma_mev": apparent_mw_uncertainty_mev(
                fac, xi=xi, pole_sigma_mev=pole_sigma, dressing_sigma_ppm=dress_sigma_ppm
            ),
        }
        for fid, fac in facilities.items()
    }

    lean_theorems = [
        "Hqiv.Physics.lineShapeRadiativeStackDensity_eq_fifteen_gamma_over_sixtyfour",
        "Hqiv.Physics.kinematicCouplingExponentLHC_eq_two_over_twentyfive",
        "Hqiv.Physics.lineShapeMassFactor_lep_eq",
        "Hqiv.Physics.colliderKinematicMassFactor_cdf_eq",
        "Hqiv.Physics.colliderCurvatureWidthFactor_gt_one_of_pos_field",
        "Hqiv.Physics.sm_global_ref_lt_lep_ref",
        "Hqiv.Physics.lep_ref_lt_cdf_ref",
        "Hqiv.Physics.sm_global_ref_lt_cdf_ref",
        "Hqiv.Physics.cdf_tension_ppm_positive",
    ]

    return {
        "schema": "hqiv_electroweak_mass_witness_v2",
        "pole_xi_lock": xi,
        "pole_mw_mev": pole,
        "line_shape_radiative_stack_density": line_shape_radiative_stack_density(),
        "kinematic_coupling_exponent_lhc": KINEMATIC_COUPLING_EXPONENT_LHC,
        "predictions": predictions,
        "sensitivity": sensitivity_ledger(observations, xi=xi),
        "lean_module": "Hqiv.Physics.ElectroweakMassObservation",
        "lean_theorems": lean_theorems,
        "python_module": "scripts/hqiv_electroweak_mass_observation.py",
    }


def facility_environment_ledger(
    observations: dict[str, Any] | None = None,
    *,
    xi: float | None = None,
) -> list[dict[str, Any]]:
    observations = observations or load_observations()
    xi = float(xi if xi is not None else observations.get("pole_xi_lock", XI_LOCKIN))
    pole = pole_mw_mev(xi)
    pole_sigma = float(observations.get("pole_sigma_mev", 0.0))
    dress_sigma_ppm = float(observations.get("dressing_sigma_ppm", 0.0))
    rows: list[dict[str, Any]] = []
    for fac in load_facilities(observations).values():
        f_dress = fac.facility_mass_dressing_factor()
        apparent = pole * f_dress
        rows.append(
            {
                "facility_id": fac.id,
                "method": fac.method,
                "dressing_chart": fac.dressing_chart,
                "magnetic_field_tesla": fac.magnetic_field_tesla,
                "effective_b_ref_tesla": fac.effective_collider_reference_tesla(),
                "comoving_stream_fraction": fac.comoving_stream_fraction,
                "line_shape_stream_fraction": fac.line_shape_stream_fraction,
                "kinematic_coupling_exponent": fac.kinematic_coupling_exponent,
                "facility_mass_dressing_factor": f_dress,
                "dressing_ppm": fac.dressing_ppm(),
                "pole_mw_mev": pole,
                "apparent_mw_mev": apparent,
                "predicted_sigma_mev": apparent_mw_uncertainty_mev(
                    fac, xi=xi, pole_sigma_mev=pole_sigma, dressing_sigma_ppm=dress_sigma_ppm
                ),
                "notes": fac.notes,
            }
        )
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description="HQIV electroweak mass observation ledger")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--certificate", type=Path, default=None)
    parser.add_argument("--observations", type=Path, default=DEFAULT_OBSERVATIONS)
    args = parser.parse_args()
    observations = load_observations(args.observations)

    if args.certificate:
        cert = witness_certificate(observations)
        args.certificate.parent.mkdir(parents=True, exist_ok=True)
        args.certificate.write_text(json.dumps(cert, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(f"Wrote {args.certificate}")
        return

    ledger = facility_environment_ledger(observations)
    if args.json:
        print(json.dumps({"facilities": ledger, "certificate": witness_certificate(observations)}, indent=2))
        return

    pole = pole_mw_mev(float(observations.get("pole_xi_lock", XI_LOCKIN)))
    print(f"Pole m_W @ ξ_lock: {pole:.2f} MeV")
    print(f"lineShape radiative stack density: {line_shape_radiative_stack_density():.6f}")
    print()
    print(f"{'facility':22} {'chart':18} {'f_dress':>10} {'ppm':>8} {'m_obs':>12}")
    for row in ledger:
        print(
            f"{row['facility_id']:22} {row['dressing_chart']:18} "
            f"{row['facility_mass_dressing_factor']:10.6f} {row['dressing_ppm']:8.0f} "
            f"{row['apparent_mw_mev']:12.2f}"
        )


if __name__ == "__main__":
    main()

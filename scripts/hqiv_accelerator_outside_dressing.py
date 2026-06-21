#!/usr/bin/env python3
"""
Per-accelerator outside dressing for hadron mass spectroscopy ledgers.

Combines Earth-surface gravity/kinetic closure (``K_mass_chart``) with facility
kinematic charts (magnetic field, comoving stream fraction, line-shape radiative
stack) certified in ``Hqiv/Physics/ElectroweakMassObservation.lean`` and
``Hqiv/Physics/AcceleratorOutsideDressing.lean``.

Python mirror only assigns routes to species; pole/chart masses stay unchanged.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal

import hqiv_electroweak_mass_observation as emo

HadronMassFacilityRoute = Literal[
    "earth_surface",
    "cms_lhc",
    "atlas_lhc",
    "lhc_lhcb",
    "bes_charmonium",
    "lep_line_shape",
]

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_WITNESS = ROOT / "data" / "accelerator_outside_dressing.json"
EARTH_CLOSURE_JSON = ROOT / "data" / "earth_outside_closure.json"

# Extra e+e- / fixed-target presets beyond the electroweak mass chart.
EXTRA_FACILITY_PRESETS: dict[str, dict[str, Any]] = {
    "lhc_lhcb": {
        "method": "lhc_kinematic",
        "dressing_chart": "collider_native",
        "magnetic_field_tesla": 0.4,
        "collider_reference_tesla": 4.0,
        "comoving_stream_fraction": 0.08,
        "line_shape_stream_fraction": 0.0,
        "kinematic_coupling_exponent": emo.KINEMATIC_COUPLING_EXPONENT_LHC,
        "notes": "LHCb dipole-scale B and lower βγ stream proxy for bottom spectroscopy.",
    },
    "bes_charmonium": {
        "method": "lep_line_shape",
        "dressing_chart": "line_shape",
        "magnetic_field_tesla": 1.0,
        "collider_reference_tesla": 4.0,
        "comoving_stream_fraction": 0.02,
        "line_shape_stream_fraction": 0.04,
        "kinematic_coupling_exponent": 1.0,
        "notes": "BESIII / charmonium e+e- factory: line-shape radiative stack + small stream.",
    },
}

LEAN_ROUTE_MAP: dict[HadronMassFacilityRoute, str] = {
    "earth_surface": "earthSurface",
    "cms_lhc": "cmsLhc",
    "atlas_lhc": "atlasLhc",
    "lhc_lhcb": "lhcb",
    "bes_charmonium": "besCharmonium",
    "lep_line_shape": "lepLineShape",
}

# Categories that receive a non-earth facility dressing on the optional ledger.
CATEGORY_FACILITY_ROUTES: dict[str, HadronMassFacilityRoute] = {
    "baryon_charm": "cms_lhc",
    "baryon_double_charm": "cms_lhc",
    "pentaquark_charm": "cms_lhc",
    "tetraquark": "cms_lhc",
    "baryon_bottom": "lhc_lhcb",
    "meson_bottom": "lhc_lhcb",
}

# Hidden-charm / quarkonium tabulation is primarily from e+e- factories.
HIDDEN_CHARM_MATCH_PREFIXES = (
    "heavy:hidden_charm",
    "heavy:hidden_bottom",
)


@dataclass(frozen=True)
class SpeciesOutsideLedger:
    facility_route: HadronMassFacilityRoute
    facility_id: str
    applies_accelerator_dressing: bool
    K_mass_chart: float
    K_facility: float
    K_apparent: float
    delta_lab_mev: float
    delta_accelerator_mev: float
    m_apparent_mev: float
    facility_label: str
    lean_route: str


def _facility_preset(facility_id: str) -> dict[str, Any]:
    if facility_id in emo.LEAN_FACILITY_PRESETS:
        return dict(emo.LEAN_FACILITY_PRESETS[facility_id])
    if facility_id in EXTRA_FACILITY_PRESETS:
        return dict(EXTRA_FACILITY_PRESETS[facility_id])
    raise KeyError(f"unknown facility preset {facility_id!r}")


def facility_setup(facility_id: str) -> emo.ElectroweakFacilitySetup:
    row = _facility_preset(facility_id)
    return emo.ElectroweakFacilitySetup(
        id=facility_id,
        method=row["method"],
        dressing_chart=row["dressing_chart"],
        magnetic_field_tesla=float(row["magnetic_field_tesla"]),
        collider_reference_tesla=float(row["collider_reference_tesla"]),
        comoving_stream_fraction=float(row["comoving_stream_fraction"]),
        line_shape_stream_fraction=float(row.get("line_shape_stream_fraction", 0.0)),
        kinematic_coupling_exponent=float(row["kinematic_coupling_exponent"]),
        notes=str(row.get("notes", "")),
    )


def facility_mass_dressing_factor(facility_id: str) -> float:
    if facility_id == "earth_surface":
        return 1.0
    return facility_setup(facility_id).facility_mass_dressing_factor()


def k_mass_chart_from_earth_closure() -> float:
    if not EARTH_CLOSURE_JSON.is_file():
        return 1.0
    payload = json.loads(EARTH_CLOSURE_JSON.read_text(encoding="utf-8"))
    return float(payload.get("earth_default", {}).get("K_mass_chart", 1.0))


def resolve_facility_route(
    *,
    category: str,
    match: str,
    pdg_key: str | None = None,
    overrides: dict[str, str] | None = None,
    category_routes: dict[str, HadronMassFacilityRoute] | None = None,
) -> HadronMassFacilityRoute:
    _ = pdg_key
    if overrides:
        for key, route in overrides.items():
            if pdg_key == key or (pdg_key and key in pdg_key):
                return route  # type: ignore[return-value]
    if category == "meson_charm" and match.startswith(HIDDEN_CHARM_MATCH_PREFIXES):
        return "bes_charmonium"
    routes = category_routes or CATEGORY_FACILITY_ROUTES
    return routes.get(category, "earth_surface")


def species_outside_ledger(
    m_pole_mev: float,
    *,
    category: str,
    match: str,
    pdg_key: str | None = None,
    witness: dict[str, Any] | None = None,
) -> SpeciesOutsideLedger:
    """Full outside ledger for one spectroscopy row."""
    payload = witness or load_witness()
    overrides = {
        str(k): str(v) for k, v in (payload.get("species_routes", {}).get("overrides") or {}).items()
    }
    category_routes = {
        str(k): str(v)
        for k, v in (payload.get("species_routes", {}).get("by_category") or {}).items()
    }
    route = resolve_facility_route(
        category=category,
        match=match,
        pdg_key=pdg_key,
        overrides=overrides or None,
        category_routes=category_routes or None,  # type: ignore[arg-type]
    )
    facility_id = "earth_surface" if route == "earth_surface" else route
    k_gravity = k_mass_chart_from_earth_closure()
    k_facility = facility_mass_dressing_factor(facility_id)
    applies = route != "earth_surface"
    k_apparent = k_gravity * k_facility
    delta_lab = m_pole_mev * (k_gravity - 1.0)
    delta_accel = m_pole_mev * (k_facility - 1.0) if applies else 0.0
    preset = _facility_preset(facility_id) if facility_id != "earth_surface" else {}
    label = str(preset.get("notes") or facility_id)
    return SpeciesOutsideLedger(
        facility_route=route,
        facility_id=facility_id,
        applies_accelerator_dressing=applies,
        K_mass_chart=k_gravity,
        K_facility=k_facility,
        K_apparent=k_apparent,
        delta_lab_mev=delta_lab,
        delta_accelerator_mev=delta_accel,
        m_apparent_mev=m_pole_mev * k_apparent,
        facility_label=label,
        lean_route=LEAN_ROUTE_MAP[route],
    )


def load_witness(path: Path | None = None) -> dict[str, Any]:
    path = path or DEFAULT_WITNESS
    return json.loads(path.read_text(encoding="utf-8"))


def build_witness_payload() -> dict[str, Any]:
    facilities: dict[str, Any] = {
        "earth_surface": {
            "lean_route": "earthSurface",
            "K_facility": 1.0,
            "K_mass_chart": k_mass_chart_from_earth_closure(),
            "components": ["gravity_phi", "cmb_proper_motion_v_over_c"],
            "source": str(EARTH_CLOSURE_JSON.relative_to(ROOT)),
        }
    }
    all_presets = {**emo.LEAN_FACILITY_PRESETS, **EXTRA_FACILITY_PRESETS}
    for fid, preset in sorted(all_presets.items()):
        fac = facility_setup(fid)
        facilities[fid] = {
            **preset,
            "id": fid,
            "K_facility": fac.facility_mass_dressing_factor(),
            "dressing_ppm": fac.dressing_ppm(),
            "collider_width_factor": fac.collider_width_factor(),
            "effective_reference_tesla": fac.effective_collider_reference_tesla(),
        }
    return {
        "source": "scripts/hqiv_accelerator_outside_dressing.py",
        "lean_modules": [
            "Hqiv.Physics.AcceleratorOutsideDressing",
            "Hqiv.Physics.ElectroweakMassObservation",
            "Hqiv.Physics.HepDecayReadout",
        ],
        "policy": (
            "Pole/chart masses from TUFT discharge are compared to PDG tabulation at "
            "Earth-surface gravity (K_mass_chart). Optional accelerator dressing "
            "(K_facility from B-field + stream / line-shape stack) applies only to species "
            "routes listed in species_routes; it documents facility apparent mass, not a fit knob."
        ),
        "formula": {
            "m_apparent": "m_pole * K_mass_chart * K_facility",
            "delta_lab": "m_pole * (K_mass_chart - 1)",
            "delta_accelerator": "m_pole * (K_facility - 1)  [eligible species only]",
            "K_facility_collider": "colliderCurvatureWidthFactor^kinematicCouplingExponent",
            "K_facility_line_shape": "lineShapeMassFactor(streamFraction)",
        },
        "facilities": facilities,
        "species_routes": {
            "by_category": dict(CATEGORY_FACILITY_ROUTES),
            "hidden_charm_match_prefixes": list(HIDDEN_CHARM_MATCH_PREFIXES),
            "overrides": {},
        },
    }


def write_witness(path: Path | None = None) -> Path:
    path = path or DEFAULT_WITNESS
    path.write_text(json.dumps(build_witness_payload(), indent=2) + "\n", encoding="utf-8")
    return path


def main() -> None:
    path = write_witness()
    payload = json.loads(path.read_text(encoding="utf-8"))
    print(f"Wrote {path}")
    for fid, row in payload["facilities"].items():
        k = row.get("K_facility", row.get("K_mass_chart"))
        ppm = row.get("dressing_ppm")
        extra = f"  ({ppm:.1f} ppm)" if ppm is not None else ""
        print(f"  {fid:16} K={k:.8f}{extra}")


if __name__ == "__main__":
    main()

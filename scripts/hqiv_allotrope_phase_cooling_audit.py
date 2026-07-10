#!/usr/bin/env python3
"""
Allotrope phase cooling audit — T sweep with spectroscopy / material-response fingerprints.

For each panel molecule, scan temperature and report:
  • derived bulk phase (solid / liquid / gas / cluster)
  • preferred allotrope geometry (when solid)
  • per-allotrope spectroscopy profile (n, k_th, optical G_eff, unit cell)
  • phase and allotrope transition temperatures

Usage:
  PYTHONPATH=.:scripts python3 scripts/hqiv_allotrope_phase_cooling_audit.py
  PYTHONPATH=.:scripts python3 scripts/hqiv_allotrope_phase_cooling_audit.py --json data/allotrope_phase_cooling_audit.json
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

_REPO = Path(__file__).resolve().parent.parent
if str(_REPO) not in sys.path:
    sys.path.insert(0, str(_REPO))
if str(_REPO / "scripts") not in sys.path:
    sys.path.insert(0, str(_REPO / "scripts"))

import hqiv_thermodynamic_phase_from_tp as tptp
from hqiv_lab import MaterialsLab

# Default panel: small-molecule + foundation condensed witnesses.
DEFAULT_MOLECULES: tuple[str, ...] = (
    "H2O",
    "CH4",
    "NH3",
    "HF",
    "CH3OH",
    "C6H12O6",
)

_SPECTROSCOPY_KEYS = (
    "refractive_index",
    "dielectric_constant",
    "thermal_conductivity_W_mK",
    "molar_heat_capacity_J_per_mol_K",
    "latent_heat_fusion_J_per_mol",
    "optical_geff",
    "optical_contact_theta_rad",
    "B_hom",
    "curvature_density_fraction",
    "contact_xi",
)


def _temperature_grid(t_min: float, t_max: float, step_k: float) -> list[float]:
    pts: list[float] = []
    t = t_min
    while t <= t_max + 1e-9:
        pts.append(round(t, 2))
        t += step_k
    return pts


def _derived_phase_row(molecule: str, temperature_k: float) -> dict[str, Any]:
    mat = tptp.material_scales_from_network_name(molecule)
    env = tptp.ThermodynamicEnvironment(temperature_k, tptp.STP_PRESSURE_PA)
    state = tptp.derive_phase(env, mat)
    t_melt, t_boil = tptp.characteristic_temperatures_K(mat)
    return {
        "temperature_K": temperature_k,
        "derived_phase": state.phase.value,
        "T_melt_K": t_melt,
        "T_boil_K": t_boil,
        "xi": state.xi,
        "coordination_fraction": state.coordination_fraction,
        "contact_persistence": state.contact_persistence,
        "periodic_weight": state.periodic_weight,
        "notes": state.notes,
    }


def _allotrope_spectroscopy_fingerprints(
    lab: MaterialsLab,
    molecule: str,
    *,
    temperature_k: float,
    phase: str,
) -> list[dict[str, Any]]:
    """Per-allotrope geometry + condensed spectroscopy / response slots."""
    spec = lab.spec_from_name(molecule)
    mono = lab.monomer_geometry(spec)
    cands = lab.derive_allotropes(spec, temperature_k=temperature_k)
    rows: list[dict[str, Any]] = []
    resp_phase = "liquid" if phase in ("liquid", "supercritical") else "solid"
    for cand in cands:
        resp = lab.material_response(
            spec,
            allotrope_label=cand.label,
            phase=resp_phase,
            temperature_k=temperature_k,
        )
        rows.append(
            {
                "allotrope": cand.label,
                "score": cand.score,
                "motif": cand.motif,
                "density_g_cm3": cand.density_g_cm3,
                "curvature_density_fraction": cand.curvature_density_fraction,
                "intermolecular_contacts": cand.intermolecular_contacts,
                "unit_cell": cand.to_dict()["unit_cell"],
                "monomer": {
                    "mean_bond_length_angstrom": mono.mean_bond_length_angstrom,
                    "bond_angle_deg": mono.bond_angle_rad * 180.0 / 3.14159265,
                    "motif": mono.motif.value,
                },
                "spectroscopy": {k: resp.get(k) for k in _SPECTROSCOPY_KEYS if k in resp},
            }
        )
    return rows


def _detect_transitions(
    sweep: list[dict[str, Any]],
) -> dict[str, list[dict[str, Any]]]:
    phase_events: list[dict[str, Any]] = []
    allotrope_events: list[dict[str, Any]] = []
    prev_phase: str | None = None
    prev_allotrope: str | None = None
    for row in sweep:
        phase = row["derived_phase"]
        allotrope = row.get("preferred_allotrope")
        t = row["temperature_K"]
        if prev_phase is not None and phase != prev_phase:
            phase_events.append(
                {
                    "temperature_K": t,
                    "from": prev_phase,
                    "to": phase,
                }
            )
        if (
            prev_allotrope is not None
            and allotrope is not None
            and allotrope != prev_allotrope
            and phase == "solid"
        ):
            allotrope_events.append(
                {
                    "temperature_K": t,
                    "from": prev_allotrope,
                    "to": allotrope,
                }
            )
        prev_phase = phase
        if phase == "solid" and allotrope is not None:
            prev_allotrope = allotrope
    return {"phase_transitions": phase_events, "allotrope_transitions": allotrope_events}


def build_cooling_audit(
    molecules: tuple[str, ...] = DEFAULT_MOLECULES,
    *,
    t_min: float = 50.0,
    t_max: float = 400.0,
    step_k: float = 5.0,
    include_allotrope_profiles: bool = True,
    profile_on_transitions_only: bool = False,
) -> dict[str, Any]:
    lab = MaterialsLab()
    grid = _temperature_grid(t_min, t_max, step_k)
    species: dict[str, Any] = {}

    for molecule in molecules:
        spec = lab.spec_from_name(molecule)
        sweep: list[dict[str, Any]] = []
        for t_k in grid:
            phase_row = _derived_phase_row(molecule, t_k)
            preferred = None
            preferred_label = None
            if phase_row["derived_phase"] == "solid":
                best = lab.preferred_allotrope(spec, temperature_k=t_k)
                preferred_label = best.label
                preferred = best.to_dict()
            entry: dict[str, Any] = {
                **phase_row,
                "preferred_allotrope": preferred_label,
                "preferred_allotrope_detail": preferred,
            }
            sweep.append(entry)

        transitions = _detect_transitions(sweep)
        transition_temps = {e["temperature_K"] for e in transitions["phase_transitions"]}
        transition_temps |= {e["temperature_K"] for e in transitions["allotrope_transitions"]}

        profiles: list[dict[str, Any]] = []
        if include_allotrope_profiles:
            anchor_temps = sorted(transition_temps | {t_min, t_max, 273.15})
            profile_temps = anchor_temps if profile_on_transitions_only else grid
            for t_probe in profile_temps:
                row = min(sweep, key=lambda r: abs(r["temperature_K"] - t_probe))
                t_k = row["temperature_K"]
                phase = row["derived_phase"]
                profiles.append(
                    {
                        "temperature_K": t_k,
                        "probe_temperature_K": t_probe,
                        "derived_phase": phase,
                        "preferred_allotrope": row["preferred_allotrope"],
                        "allotrope_fingerprints": _allotrope_spectroscopy_fingerprints(
                            lab,
                            molecule,
                            temperature_k=t_k,
                            phase=phase,
                        ),
                    }
                )

        species[molecule] = {
            "molecule": molecule,
            "molecular_weight_amu": spec.molecular_weight_amu,
            "temperature_sweep": sweep,
            "transitions": transitions,
            "allotrope_spectroscopy_profiles": profiles,
        }

    return {
        "source": "scripts/hqiv_allotrope_phase_cooling_audit.py",
        "comparison_policy": "NIST witnesses grade readouts only; never fold inputs",
        "temperature_grid": {"T_min_K": t_min, "T_max_K": t_max, "step_K": step_k},
        "molecules": list(molecules),
        "species": species,
    }


def print_report(payload: dict[str, Any]) -> None:
    print("HQIV allotrope phase cooling audit")
    print("=" * 72)
    for name, block in payload["species"].items():
        print(f"\n{name}  (MW={block['molecular_weight_amu']:.2f} amu)")
        trans = block["transitions"]
        if trans["phase_transitions"]:
            print("  Phase transitions:")
            for e in trans["phase_transitions"]:
                print(f"    T={e['temperature_K']:6.1f} K  {e['from']} → {e['to']}")
        else:
            print("  Phase transitions: (none in range)")
        if trans["allotrope_transitions"]:
            print("  Allotrope switches (solid):")
            for e in trans["allotrope_transitions"]:
                print(f"    T={e['temperature_K']:6.1f} K  {e['from']} → {e['to']}")
        # Snapshot at cryo, melt, room
        for t_probe in (100.0, 273.15, 310.0):
            row = next(
                (r for r in block["temperature_sweep"] if r["temperature_K"] == t_probe),
                None,
            )
            if row is None:
                continue
            allot = row["preferred_allotrope"] or "—"
            print(
                f"  T={t_probe:6.1f} K  phase={row['derived_phase']:18s}  "
                f"allotrope={allot}"
            )


def main() -> int:
    parser = argparse.ArgumentParser(description="Allotrope phase cooling audit")
    parser.add_argument(
        "--json",
        type=Path,
        default=_REPO / "data" / "allotrope_phase_cooling_audit.json",
    )
    parser.add_argument("--molecules", nargs="*", default=list(DEFAULT_MOLECULES))
    parser.add_argument("--t-min", type=float, default=50.0)
    parser.add_argument("--t-max", type=float, default=400.0)
    parser.add_argument("--step-k", type=float, default=5.0)
    parser.add_argument(
        "--transitions-only-profiles",
        action="store_true",
        help="Emit full allotrope spectroscopy only at transition T (+ anchors)",
    )
    parser.add_argument("--no-profiles", action="store_true")
    args = parser.parse_args()

    payload = build_cooling_audit(
        tuple(args.molecules),
        t_min=args.t_min,
        t_max=args.t_max,
        step_k=args.step_k,
        include_allotrope_profiles=not args.no_profiles,
        profile_on_transitions_only=args.transitions_only_profiles,
    )
    print_report(payload)
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        print(f"\nWrote {args.json}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

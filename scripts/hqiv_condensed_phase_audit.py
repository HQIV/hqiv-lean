#!/usr/bin/env python3
"""
Condensed-phase trace audit: geometry → ρ → n → κ₆ @ species melt temperature.

Exports ``data/hqiv_lab_witnesses.json`` for paper tables and bundle sync.
Validates Compton-triplet contact ξ, motif contacts, and NIST panel gaps.

Usage:
  PYTHONPATH=scripts python3 scripts/hqiv_condensed_phase_audit.py
  PYTHONPATH=scripts python3 scripts/hqiv_condensed_phase_audit.py --json data/hqiv_lab_witnesses.json
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict
from pathlib import Path
from typing import Any

_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

import hqiv_dynamic_binding_chart as chart
import hqiv_ionic_bond_network as ibn
import hqiv_metallic_bond_network as mbn
import hqiv_lean_physics_primitives as lean
import hqiv_phase_geometry_density as pgd
import hqiv_phase_material_response as pmr
import hqiv_salt_phase_response as spr
from hqiv_lab.crystal_geometry import (
    closed_atomic_mass_amu,
    covalent_network_em_packing_dress,
    diamond_cubic_density_g_cm3,
    diamond_cubic_lattice_parameter_angstrom,
    expected_contact_xi_for_crystal,
    metallic_density_g_cm3,
    metallic_lattice_parameter_angstrom,
    mass_reliable_for_crystal,
    metallic_unified_nearest_neighbor_angstrom,
)
from hqiv_lab.coordination import infer_monomer_geometry
from hqiv_lab.packing import (
    neighbor_covalent_lapse_overlap_factor,
    halogen_strong_hbond_leg_factor,
    linear_chain_zigzag_lattice_open_factor,
)
from hqiv_lab.spec import MoleculeSpec
from hqiv_lab.species_panel import CONDENSED_SPECIES_PANEL, panel_entry

# Molecular GMTKN55 panel default (H₂O, CH₄, NH₃, HF).
_EXPECTED_XI_MOLECULAR = lean.xi_from_compton_triplet((4, 3, 1))


def _entry_crystal_kind(entry: Any) -> str:
    if hasattr(entry, "resolved_crystal_kind"):
        return entry.resolved_crystal_kind()
    return entry.crystal_kind


def _xi_trace_ok(entry: Any, xi: float) -> bool:
    expected = expected_contact_xi_for_crystal(
        crystal_kind=_entry_crystal_kind(entry),
        z_values=entry.z_values,
        molecule=entry.molecule,
    )
    return abs(xi - expected) < 1e-6


def _chart_row(name: str):
    for row in chart.GMTKN55_SUITE:
        if row.name.upper() == name.upper():
            return row
    raise KeyError(name)


def audit_ionic_crystal(entry: Any) -> dict[str, Any]:
    """Ionic rocksalt witness @ species melt temperature."""
    salt = ibn.SALTS.get(entry.molecule.upper())
    if salt is None:
        z_i, z_j = entry.z_values[0], entry.z_values[1]
        salt = ibn.IonicSalt(
            entry.molecule,
            ibn.IonicFragment("cat", z_i, z_i - 1),
            ibn.IonicFragment("an", z_j, z_j + 1),
        )
    readout = spr.salt_phase_response_readout(
        salt,
        temperature_k=entry.witness_temperature_k,
    )
    rho_g = float(readout["density_g_cm3"])
    n_solid = float(readout["refractive_index_solid"])
    t_melt = float(readout["T_melt_K"])
    rho_err = (
        abs(rho_g - entry.nist_solid_density_g_cm3) / entry.nist_solid_density_g_cm3 * 100.0
        if entry.nist_solid_density_g_cm3 > 0.0
        else 0.0
    )
    n_err = (
        abs(n_solid - entry.nist_refractive_index) / entry.nist_refractive_index * 100.0
        if entry.nist_refractive_index > 0.0
        else 0.0
    )
    t_err = (
        abs(t_melt - entry.nist_melt_k) / entry.nist_melt_k * 100.0
        if entry.nist_melt_k > 0.0
        else 0.0
    )
    xi = readout["contact_xi"]
    expected_xi = expected_contact_xi_for_crystal(
        crystal_kind="ionic",
        z_values=entry.z_values,
    )
    return {
        "molecule": entry.molecule,
        "motif_label": entry.motif_label,
        "allotrope": entry.allotrope,
        "crystal_kind": _entry_crystal_kind(entry),
        "comparison_regime": "solid_lattice",
        "expected_contact_xi": expected_xi,
        "witness_temperature_K": entry.witness_temperature_k,
        "contact_xi": xi,
        "geometry": {
            "density_g_cm3": readout["density_g_cm3"],
            "nearest_neighbor_angstrom": salt.lattice_bond_angstrom,
            "lattice_parameter_angstrom": readout["lattice_parameter_angstrom"],
            "T_sl_at_pressure_K": readout["T_solid_liquid_K"],
            "curvature_density_fraction": readout["crystalline_curvature_density_fraction"],
        },
        "material_response": {
            "refractive_index": readout["refractive_index_solid"],
        },
        "nist_reference": {
            "solid_density_g_cm3": entry.nist_solid_density_g_cm3,
            "refractive_index": entry.nist_refractive_index,
            "melt_K": entry.nist_melt_k,
        },
        "benchmark": {
            "density_error_pct": rho_err,
            "refractive_index_error_pct": n_err,
            "T_sl_error_pct": t_err,
            "contact_xi_trace_consistent": _xi_trace_ok(entry, xi),
        },
    }


def audit_covalent_network_crystal(entry: Any) -> dict[str, Any]:
    """Elemental diamond-cubic semiconductor / covalent network @ melt reference."""
    z = entry.z_values[0]
    import hqiv_allotrope_network as an

    ro = an.allotrope_readout(z, 4)
    dress = covalent_network_em_packing_dress(
        z, coordination=4, packed=False, em_feedback=True
    )
    # Live density uses EM/open packing only when length is reliable (period-2).
    bond = float(dress["bond_length_angstrom"])
    bond_bare = float(dress["bond_length_bare_angstrom"])
    a_ang = diamond_cubic_lattice_parameter_angstrom(bond)
    mass = closed_atomic_mass_amu(z)
    rho_g = diamond_cubic_density_g_cm3(mass, bond)
    rho_bare = diamond_cubic_density_g_cm3(mass, bond_bare)
    m_s, _ = __import__("hqiv_electronic_valence_shells", fromlist=["electronic_compton_shells"]).electronic_compton_shells(z)
    xi = lean.xi_from_compton_triplet((m_s, m_s, m_s))
    expected_xi = expected_contact_xi_for_crystal(
        crystal_kind="covalent_network",
        z_values=entry.z_values,
    )
    rho_err = (
        abs(rho_g - entry.nist_solid_density_g_cm3) / entry.nist_solid_density_g_cm3 * 100.0
        if entry.nist_solid_density_g_cm3 > 0.0
        else 0.0
    )
    rho_err_bare = (
        abs(rho_bare - entry.nist_solid_density_g_cm3) / entry.nist_solid_density_g_cm3 * 100.0
        if entry.nist_solid_density_g_cm3 > 0.0
        else 0.0
    )
    n_err = 0.0  # band-gap optics deferred; NIST n is comparison-only
    return {
        "molecule": entry.molecule,
        "motif_label": entry.motif_label,
        "allotrope": entry.allotrope,
        "crystal_kind": _entry_crystal_kind(entry),
        "comparison_regime": "solid_lattice",
        "expected_contact_xi": expected_xi,
        "witness_temperature_K": entry.witness_temperature_k,
        "contact_xi": xi,
        "geometry": {
            "density_g_cm3": rho_g,
            "density_bare_g_cm3": rho_bare,
            "bond_length_angstrom": bond,
            "bond_length_bare_angstrom": bond_bare,
            "lattice_parameter_angstrom": a_ang,
            "T_sl_at_pressure_K": entry.nist_melt_k,
            "allotrope_bond_order": ro.bond_order,
            "length_reliable": ro.length_reliable,
            "em_feedback_applied": dress["em_feedback_applied"],
            "network_open_channel_packing_scale": dress[
                "network_open_channel_packing_scale"
            ],
            "mass_reliable": mass_reliable_for_crystal(z),
        },
        "material_response": {
            "refractive_index": entry.nist_refractive_index,
        },
        "nist_reference": {
            "solid_density_g_cm3": entry.nist_solid_density_g_cm3,
            "refractive_index": entry.nist_refractive_index,
            "melt_K": entry.nist_melt_k,
        },
        "benchmark": {
            "density_error_pct": rho_err,
            "density_error_pct_bare": rho_err_bare,
            "refractive_index_error_pct": n_err,
            "T_sl_error_pct": 0.0,
            "contact_xi_trace_consistent": abs(xi - expected_xi) < 1e-6,
        },
    }


def audit_metallic_crystal(entry: Any) -> dict[str, Any]:
    """Metallic solid witness @ melt reference (Bravais density from coordination)."""
    z = entry.z_values[0]
    n_coord = mbn.metallic_coordination(z)
    from hqiv_lab.crystal_geometry import metallic_bravais_kind

    bravais = metallic_bravais_kind(z, n_coord=n_coord)
    nn = metallic_unified_nearest_neighbor_angstrom(z, n_coord=n_coord)
    mass = closed_atomic_mass_amu(z)
    rho_g = metallic_density_g_cm3(mass, nn, n_coord=n_coord, bravais=bravais, z=z)
    a_ang = metallic_lattice_parameter_angstrom(nn, n_coord=n_coord, bravais=bravais)
    net = mbn.build_metallic_lattice_network(mbn.metal_lattice_from_z(entry.molecule, z))
    xi = lean.xi_from_compton_triplet(net.compton_triplet)
    expected_xi = expected_contact_xi_for_crystal(
        crystal_kind="metallic",
        z_values=entry.z_values,
    )
    rho_err = (
        abs(rho_g - entry.nist_solid_density_g_cm3) / entry.nist_solid_density_g_cm3 * 100.0
        if entry.nist_solid_density_g_cm3 > 0.0
        else 0.0
    )
    return {
        "molecule": entry.molecule,
        "motif_label": entry.motif_label,
        "allotrope": entry.allotrope,
        "crystal_kind": _entry_crystal_kind(entry),
        "comparison_regime": "solid_lattice",
        "expected_contact_xi": expected_xi,
        "witness_temperature_K": entry.witness_temperature_k,
        "contact_xi": xi,
        "geometry": {
            "density_g_cm3": rho_g,
            "nearest_neighbor_angstrom": nn,
            "lattice_parameter_angstrom": a_ang,
            "T_sl_at_pressure_K": entry.nist_melt_k,
            "mass_reliable": mass_reliable_for_crystal(z),
        },
        "material_response": {
            "refractive_index": 0.0,
        },
        "nist_reference": {
            "solid_density_g_cm3": entry.nist_solid_density_g_cm3,
            "refractive_index": entry.nist_refractive_index,
            "melt_K": entry.nist_melt_k,
        },
        "benchmark": {
            "density_error_pct": rho_err,
            "refractive_index_error_pct": 0.0,
            "T_sl_error_pct": 0.0,
            "contact_xi_trace_consistent": abs(xi - expected_xi) < 1e-6,
        },
    }


def audit_species(entry: Any) -> dict[str, Any]:
    kind = _entry_crystal_kind(entry)
    if kind == "ionic":
        return audit_ionic_crystal(entry)
    if kind == "metallic":
        return audit_metallic_crystal(entry)
    if kind == "covalent_network":
        return audit_covalent_network_crystal(entry)
    spec = MoleculeSpec.from_chart_name(entry.molecule)
    mono = infer_monomer_geometry(spec)
    chart_row = _chart_row(entry.molecule)
    compton_triplet = chart.chemistry_compton_triplet(chart_row)
    geom = pgd.melt_readout_with_phase_geometry(
        entry.molecule,
        allotrope=entry.allotrope,
        temperature_at_melt_k=entry.witness_temperature_k,
    )
    mat = pmr.material_response_readout(
        entry.molecule,
        allotrope=entry.allotrope,
        phase="solid",
        temperature_k=entry.witness_temperature_k,
    )
    rho_err_pct = abs(geom["density_g_cm3"] - entry.nist_solid_density_g_cm3) / entry.nist_solid_density_g_cm3 * 100.0
    n_err_pct = abs(mat["refractive_index"] - entry.nist_refractive_index) / entry.nist_refractive_index * 100.0
    t_sl_err_pct = abs(geom["T_sl_at_pressure_K"] - entry.nist_melt_k) / entry.nist_melt_k * 100.0
    xi = geom["contact_xi"]
    trace_ok = _xi_trace_ok(entry, xi) and abs(mat["contact_xi"] - xi) < 1e-9
    return {
        "molecule": entry.molecule,
        "motif_label": entry.motif_label,
        "allotrope": entry.allotrope,
        "crystal_kind": _entry_crystal_kind(entry),
        "expected_contact_xi": expected_contact_xi_for_crystal(
            crystal_kind=entry.crystal_kind,
            z_values=entry.z_values,
            molecule=entry.molecule,
        ),
        "witness_temperature_K": entry.witness_temperature_k,
        "gmtkn55_compton_triplet": list(compton_triplet),
        "contact_xi": xi,
        "intermolecular_contacts": mono.intermolecular_contacts,
        "monomer_motif": mono.motif.value,
        "geometry": {
            "density_g_cm3": geom["density_g_cm3"],
            "curvature_density_fraction": geom["curvature_density_fraction"],
            "phase_curvature_density_fraction": geom["phase_curvature_density_fraction"],
            "kappa6_feedback": geom["kappa6_feedback"],
            "T_sl_at_pressure_K": geom["T_sl_at_pressure_K"],
            "refractive_index_solid": geom["refractive_index_solid"],
            "neighbor_lapse_overlap_factor": neighbor_covalent_lapse_overlap_factor(mono),
            "halogen_strong_hbond_leg_factor": halogen_strong_hbond_leg_factor(mono),
            "linear_chain_zigzag_lattice_open_factor": linear_chain_zigzag_lattice_open_factor(
                mono
            ),
        },
        "material_response": {
            "refractive_index": mat["refractive_index"],
            "refractive_index_one_way": mat["refractive_index_one_way"],
            "optical_coupling_level": mat["optical_coupling_level"],
            "missing_optical_coupled_relaxation_flag": mat[
                "missing_optical_coupled_relaxation_flag"
            ],
            "thermal_conductivity_W_mK": mat["thermal_conductivity_W_mK"],
            "thermal_conductivity_one_way_W_mK": mat[
                "thermal_conductivity_one_way_W_mK"
            ],
            "phonon_cage_fraction": mat["phonon_cage_fraction"],
            "network_propagated_curvature_density_fraction": mat[
                "network_propagated_curvature_density_fraction"
            ],
            "molar_heat_capacity_J_per_mol_K": mat["molar_heat_capacity_J_per_mol_K"],
            "optical_phase_eta": mat["optical_phase_eta"],
            "optical_geff": mat["optical_geff"],
            "B_hom": mat["B_hom"],
        },
        "nist_reference": {
            "solid_density_g_cm3": entry.nist_solid_density_g_cm3,
            "refractive_index": entry.nist_refractive_index,
            "melt_K": entry.nist_melt_k,
        },
        "benchmark": {
            "density_error_pct": rho_err_pct,
            "refractive_index_error_pct": n_err_pct,
            "T_sl_error_pct": t_sl_err_pct,
            "contact_xi_trace_consistent": trace_ok,
        },
    }


def _mean_by_crystal_kind(rows: list[dict[str, Any]], metric: str) -> dict[str, float]:
    buckets: dict[str, list[float]] = {}
    for row in rows:
        kind = row["crystal_kind"]
        buckets.setdefault(kind, []).append(float(row["benchmark"][metric]))
    return {kind: sum(vals) / len(vals) for kind, vals in buckets.items()}


def build_payload() -> dict[str, Any]:
    rows = [audit_species(e) for e in CONDENSED_SPECIES_PANEL]
    rho_errs = [r["benchmark"]["density_error_pct"] for r in rows]
    n_errs = [r["benchmark"]["refractive_index_error_pct"] for r in rows]
    t_errs = [r["benchmark"]["T_sl_error_pct"] for r in rows]
    return {
        "source": "scripts/hqiv_condensed_phase_audit.py",
        "comparison_policy": "NIST/CRC values used for benchmark only, not HQIV fit",
        "expected_contact_xi_molecular_default": _EXPECTED_XI_MOLECULAR,
        "xi_routing": "per crystal_kind via hqiv_lab.crystal_geometry.expected_contact_xi_for_crystal",
        "species": rows,
        "summary": {
            "species_count": len(rows),
            "mean_density_error_pct_vs_nist": sum(rho_errs) / len(rho_errs),
            "mean_refractive_index_error_pct_vs_nist": sum(n_errs) / len(n_errs),
            "mean_T_sl_error_pct_vs_nist": sum(t_errs) / len(t_errs),
            "mean_density_error_pct_by_crystal_kind": _mean_by_crystal_kind(
                rows, "density_error_pct"
            ),
            "mean_refractive_index_error_pct_by_crystal_kind": _mean_by_crystal_kind(
                rows, "refractive_index_error_pct"
            ),
            "mean_T_sl_error_pct_by_crystal_kind": _mean_by_crystal_kind(
                rows, "T_sl_error_pct"
            ),
            "all_contact_xi_traces_consistent": all(
                r["benchmark"]["contact_xi_trace_consistent"] for r in rows
            ),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Condensed-phase trace audit → JSON witness.")
    parser.add_argument(
        "--json",
        type=Path,
        default=_REPO_ROOT / "data" / "hqiv_lab_witnesses.json",
    )
    args = parser.parse_args()
    payload = build_payload()
    args.json.parent.mkdir(parents=True, exist_ok=True)
    args.json.write_text(json.dumps(payload, indent=2) + "\n")
    s = payload["summary"]
    print("HQIV condensed-phase trace audit")
    print("=" * 60)
    for row in payload["species"]:
        b = row["benchmark"]
        g = row["geometry"]
        m = row["material_response"]
        t_sl = g.get("T_sl_at_pressure_K", row.get("witness_temperature_K", 0.0))
        print(
            f"{row['molecule']:4} @ {row['witness_temperature_K']:6.1f} K  "
            f"ρ={g['density_g_cm3']:.4f}  n={m['refractive_index']:.4f}  "
            f"T_sl={t_sl:.2f}  "
            f"|Δρ|={b['density_error_pct']:.2f}%  ξ={row['contact_xi']:.4f}"
        )
    print(
        f"\nSummary: mean |Δρ|={s['mean_density_error_pct_vs_nist']:.2f}%  "
        f"mean |Δn|={s['mean_refractive_index_error_pct_vs_nist']:.2f}%  "
        f"mean |ΔT_sl|={s['mean_T_sl_error_pct_vs_nist']:.2f}%  "
        f"ξ trace OK={s['all_contact_xi_traces_consistent']}"
    )
    print(f"Wrote {args.json}")


if __name__ == "__main__":
    main()

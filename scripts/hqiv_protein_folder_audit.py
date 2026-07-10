#!/usr/bin/env python3
"""
Protein-folder audit — spine chemistry manifest + miniprotein fold + biomolecule network.

Grades HQIV-derived protein readouts against PDB/COD witnesses (comparison only).

Usage:
  PYTHONPATH=.:scripts python3 scripts/hqiv_protein_folder_audit.py
  PYTHONPATH=.:scripts python3 scripts/hqiv_protein_folder_audit.py --json data/protein_folder_audit.json
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

import hqiv_biomolecule_network as bio
import hqiv_spine_chemistry as sc
from hqiv_lab.protein import (
    peptide_shell_dress_manifest,
    run_baseline_folds,
    spine_chemistry_manifest,
)
from hqiv_lab.phase_diagram import (
    HOH_ANGLE_GAS_REFERENCE_DEG,
    WATER_HOH_ANGLE_OBSERVATIONS,
    hoh_angle_witness_row,
    low_density_liquid_fraction,
    material_scales_for_spec,
)
from hqiv_lab.protein_solvent_phase import (
    CRYO_CRYSTALLOGRAPHY_TEMPERATURE_K,
    PROTEIN_FOLDING_TEMPERATURE_K,
    aqueous_angle_pivot_dress_factor,
    aqueous_bulk_curvature_at_t,
    aqueous_bulk_pivot_at_contact,
    bulk_low_density_fraction,
    local_low_density_fraction_at_interface,
)
from hqiv_lab.spec import resolve_spec
import hqiv_thermodynamic_phase_from_tp as tptp

from hqiv_miniprotein_fold_audit import build_dual_temperature_comparison, build_payload


def _biomolecule_panel() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for pair in ("AT", "GC", "GU"):
        x, y = pair[0], pair[1]
        r = bio.watson_crick_pair(x, y)
        rows.append(
            {
                "pair": r.pair,
                "hydrogen_bonds": r.hydrogen_bonds,
                "canonical": r.is_canonical_watson_crick,
                "spine_expected": sc.CANONICAL_WC_HBOND_COUNTS.get(pair),
            }
        )
    return rows


def _aqueous_solvent_witness() -> dict[str, Any]:
    """Bulk + interface aqueous readouts at protein-folding temperature (comparison quarantine on θ_ref)."""
    mat = material_scales_for_spec(resolve_spec("H2O"), bulk=True)
    f_cytosol = low_density_liquid_fraction(
        PROTEIN_FOLDING_TEMPERATURE_K, tptp.STP_PRESSURE_PA, mat
    )
    f_super_bulk = bulk_low_density_fraction(200.0)
    return {
        "fold_temperature_K": PROTEIN_FOLDING_TEMPERATURE_K,
        "cryo_temperature_K": CRYO_CRYSTALLOGRAPHY_TEMPERATURE_K,
        "bulk_rho_curv_cytosol": aqueous_bulk_curvature_at_t(PROTEIN_FOLDING_TEMPERATURE_K),
        "bulk_rho_curv_cryo": aqueous_bulk_curvature_at_t(CRYO_CRYSTALLOGRAPHY_TEMPERATURE_K),
        "f_ldl_bulk_cytosol": f_cytosol,
        "f_ldl_hydrophobic_interface_200K": local_low_density_fraction_at_interface(
            f_super_bulk, "hydrophobic"
        ),
        "f_ldl_hydrophilic_interface_200K": local_low_density_fraction_at_interface(
            f_super_bulk, "hydrophilic"
        ),
        "hoh_angle_cytosol_310K_1atm": hoh_angle_witness_row(f_cytosol),
        "hoh_angle_gas_reference_deg": HOH_ANGLE_GAS_REFERENCE_DEG,
        "hoh_angle_observations": list(WATER_HOH_ANGLE_OBSERVATIONS),
        "hb_pivot_dress_hydrophobic_cytosol": aqueous_angle_pivot_dress_factor(
            PROTEIN_FOLDING_TEMPERATURE_K, "hydrophobic"
        ),
        "hb_pivot_angstrom_hydrophobic_cytosol": aqueous_bulk_pivot_at_contact(
            "hydrophobic", temperature_k=PROTEIN_FOLDING_TEMPERATURE_K
        ),
        "hb_pivot_dress_hydrophilic_cytosol": aqueous_angle_pivot_dress_factor(
            PROTEIN_FOLDING_TEMPERATURE_K, "hydrophilic"
        ),
    }


def build_protein_folder_audit(
    witness_path: Path,
    *,
    include_network: bool = False,
    dual_temperature: bool = True,
) -> dict[str, Any]:
    fold_payload = build_payload(witness_path, include_network=include_network)
    baseline = run_baseline_folds(include_network=include_network)
    dual_t_payload = None
    if dual_temperature:
        dual_t_payload = build_dual_temperature_comparison(
            witness_path,
            include_network=include_network,
        )
    return {
        "source": "scripts/hqiv_protein_folder_audit.py",
        "comparison_policy": "PDB/COD witnesses grade HQIV fold readouts only",
        "spine_chemistry": spine_chemistry_manifest(),
        "peptide_shell_dress": peptide_shell_dress_manifest(),
        "biomolecule_watson_crick": _biomolecule_panel(),
        "fold_audit": fold_payload,
        "dual_temperature_fold_comparison": dual_t_payload,
        "baseline_folds_no_witness": {
            name: {
                "n_residues": f.n_residues,
                "strategy": f.strategy,
                "network_contacts": f.network_contacts,
                "tertiary_contacts": f.tertiary_contacts,
                "bond_geometry_angstrom": f.bond_geometry,
            }
            for name, f in baseline.items()
        },
        "aqueous_solvent_witness": _aqueous_solvent_witness(),
        "summary": {
            **fold_payload.get("summary", {}),
            "spine_h2_site_energy": sc.h2_site_energy_same_shell(sc.REFERENCE_M),
            "fold_temperature_K": PROTEIN_FOLDING_TEMPERATURE_K,
            "cryo_crystallography_temperature_K": CRYO_CRYSTALLOGRAPHY_TEMPERATURE_K,
            "trp_cage_rg_angstrom": None,  # filled below
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="HQIV protein-folder spine audit")
    parser.add_argument(
        "--json",
        type=Path,
        default=_REPO / "data" / "protein_folder_audit.json",
    )
    parser.add_argument(
        "--witnesses",
        type=Path,
        default=_REPO / "data" / "miniprotein_witnesses.json",
    )
    parser.add_argument("--full-network", action="store_true")
    parser.add_argument(
        "--no-dual-temperature",
        action="store_true",
        help="Skip cryo vs cytosol comparison on curvature-weighted targets",
    )
    args = parser.parse_args()

    payload = build_protein_folder_audit(
        args.witnesses,
        include_network=args.full_network,
        dual_temperature=not args.no_dual_temperature,
    )
    for row in payload["fold_audit"].get("folds", []):
        if row.get("name") == "trp_cage":
            payload["summary"]["trp_cage_rg_angstrom"] = row.get("predicted_radius_of_gyration_A")

    args.json.parent.mkdir(parents=True, exist_ok=True)
    args.json.write_text(json.dumps(payload, indent=2) + "\n")

    print("HQIV protein-folder audit (spine chemistry + fold + biomolecule)")
    print("=" * 64)
    m = payload["spine_chemistry"]
    print(f"  Slater same/adj/deep: {m['slater_same_shell']}/{m['slater_adjacent_shell']}/{m['slater_deep_shell']}")
    print(f"  H₂ site energy @ m=4: {m['h2_site_energy_reference_m']:.0f}")
    print(f"  C 2p Z_eff (spine):   {m['carbon_zeff_spine']:.2f}")
    for row in payload["biomolecule_watson_crick"]:
        exp = row.get("spine_expected")
        ok = exp is None or row["hydrogen_bonds"] == exp
        tag = "OK" if ok else "MISMATCH"
        print(f"  WC {row['pair']:4s}  H-bonds={row['hydrogen_bonds']}  {tag}")
    print("-" * 64)
    for row in payload["fold_audit"].get("folds", []):
        rmsd = row.get("ca_rmsd_angstrom")
        rmsd_s = f"{rmsd:.2f}" if rmsd is not None else "n/a"
        status = "PASS" if row.get("passed") else "FAIL" if row.get("passed") is False else "n/a"
        print(f"  {row['name']:10s}  RMSD={rmsd_s} Å  {status}")
    s = payload["summary"]
    print(f"Summary: mean Cα RMSD={s.get('mean_ca_rmsd_angstrom', 0):.2f} Å  passed={s.get('passed')}/{s.get('targets')}")
    dual = payload.get("dual_temperature_fold_comparison")
    if dual is not None:
        print("-" * 64)
        print(
            f"Dual-T curvature-weighted folds "
            f"(cryo {dual['cryo_temperature_K']:.0f} K vs cytosol {dual['cytosol_temperature_K']:.0f} K)"
        )
        print(
            f"  bulk ρ: cryo={aqueous_bulk_curvature_at_t(dual['cryo_temperature_K']):.3f}  "
            f"cytosol={aqueous_bulk_curvature_at_t(dual['cytosol_temperature_K']):.3f}"
        )
        for row in dual.get("comparisons", []):
            cyto = row["cytosol"]["ca_rmsd_angstrom"]
            cryo = row["cryo"]["ca_rmsd_angstrom"]
            delta = row.get("ca_rmsd_delta_cryo_minus_cytosol_A")
            delta_s = f"{delta:+.2f}" if delta is not None else "n/a"
            closer = "cryo" if row.get("cryo_closer_to_witness") else "cytosol"
            print(
                f"  {row['name']:16s}  cytosol={cyto:.2f} Å  cryo={cryo:.2f} Å  "
                f"Δ={delta_s} Å  closer={closer}"
            )
        ds = dual.get("summary", {})
        mean_d = ds.get("mean_ca_rmsd_delta_cryo_minus_cytosol_A")
        if mean_d is not None:
            print(
                f"  mean Δ(cryo−cytosol)={mean_d:+.2f} Å  "
                f"cryo closer: {ds.get('cryo_closer_count', 0)}/{ds.get('targets', 0)}"
            )
    print(f"Wrote {args.json}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

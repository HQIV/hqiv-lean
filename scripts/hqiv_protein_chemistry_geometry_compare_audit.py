#!/usr/bin/env python3
"""
Protein vs general bond-geometry comparative audit.

Same shell / feedback language on both sides:

  shell_anchor_projection → em^(α·length_share) → (1+base·open²)

Compares mean treatment factors and quarantined accuracy:

* Chemistry SOTA: spectral diatomic panel + carbon network packing
* Protein: peptide backbone bonds + tertiary register packing + fold ladder

Laboratory constants (NIST/CRC/Engh–Huber/PDB) are comparison quarantine only.

Usage:
  PYTHONPATH=.:scripts python3 scripts/hqiv_protein_chemistry_geometry_compare_audit.py
  PYTHONPATH=.:scripts python3 scripts/hqiv_protein_chemistry_geometry_compare_audit.py --refresh-fold
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

import hqiv_chemistry_panel_accuracy as cpa
import hqiv_lean_physics_primitives as lean
import hqiv_two_way_feedback_dynamics as twf
from hqiv_lab.derived_bond_geometry import (
    peptide_bond_length_c_n,
    peptide_bond_length_c_o,
    peptide_bond_length_ca_c,
    peptide_bond_length_n_ca,
)
from hqiv_lab.miniprotein_fold import COMPETITIVE_CA_RMSD_PASS_ANGSTROM
from hqiv_lab.peptide_shell_dress import (
    REGISTER_OCCUPANCY,
    peptide_bond_dress_cached,
    peptide_shell_dress_manifest,
    tertiary_contact_packing_scale,
)

DEFAULT_JSON = _REPO_ROOT / "data" / "protein_chemistry_geometry_compare_audit.json"
PROTEIN_FOLDER_JSON = _REPO_ROOT / "data" / "protein_folder_audit.json"

# Engh–Huber / Ideal peptide bond lengths — COMPARISON QUARANTINE ONLY.
PEPTIDE_BOND_COMPARISON_ANGSTROM: dict[str, float] = {
    "N_CA": 1.458,
    "CA_C": 1.525,
    "C_N": 1.329,
    "C_O": 1.231,
}


def _err_pct(pred: float, ref: float) -> float:
    return 100.0 * (pred - ref) / ref


def _geo_mean_abs_pct(errors: list[float]) -> float:
    factors = [1.0 + abs(e) / 100.0 for e in errors if math.isfinite(e)]
    if not factors:
        return float("nan")
    return 100.0 * (twf.geometric_mean_positive(factors) - 1.0)


def _mean(xs: list[float]) -> float:
    return sum(xs) / len(xs) if xs else float("nan")


def chemistry_side() -> dict[str, Any]:
    panel = cpa.build_payload()
    spectral = panel["spectral"]
    carbon = panel["carbon"]

    # Mean shell treatment on the spectral panel (from live spectral rows).
    import hqiv_spectral_scale_anchor_feedback as ssa

    spectral_full = ssa.build_payload()
    length_shares: list[float] = []
    ems: list[float] = []
    packings: list[float] = []
    energy_shares: list[float] = []
    for row in spectral_full["rows"]:
        if not row.get("geometry_reliable", True):
            continue
        shell = row["pin"]["shell_projection"]
        length_shares.append(float(shell["length_share"]))
        ems.append(float(row["pin"]["em_star"]))
        packings.append(float(shell["network_open_channel_packing_scale"]))
        energy_shares.append(float(shell["energy_share"]))

    carbon_errs = [abs(float(r["error_pct"])) for r in carbon["rows"] if r.get("error_pct") is not None]
    bond_errs = [
        abs(float(r["bond_error_pct"]))
        for r in carbon["rows"]
        if r.get("bond_error_pct") is not None
    ]

    return {
        "panel": "general_bond_geometry",
        "status": "SOTA chemistry stack",
        "spectral": {
            "count": spectral["count"],
            "reliable_count": spectral["reliable_count"],
            "geometric_mean_error_pct": spectral["geometric_mean_error_pct"],
            "rows": spectral["rows"],
        },
        "carbon": {
            "count": carbon["count"],
            "rows": carbon["rows"],
            "mean_abs_density_error_pct": _mean(carbon_errs),
            "mean_abs_bond_error_pct": _mean(bond_errs),
        },
        "mean_treatment": {
            "length_share": _mean(length_shares),
            "em": _mean(ems),
            "network_open_channel_packing_scale": _mean(packings),
            "energy_share": _mean(energy_shares),
            "length_dress_em_alpha_share": _mean(
                [
                    max(em, 1.0e-30) ** (lean.ALPHA * ls)
                    for em, ls in zip(ems, length_shares)
                ]
            ),
            "n_rows": len(length_shares),
        },
        "accuracy_headline": {
            "r_e_geo_mean_pct": spectral["geometric_mean_error_pct"]["r_e"],
            "D_e_geo_mean_pct": spectral["geometric_mean_error_pct"]["D_e"],
            "B_e_geo_mean_pct": spectral["geometric_mean_error_pct"]["B_e"],
            "carbon_density_mean_abs_pct": _mean(carbon_errs),
            "carbon_bond_mean_abs_pct": _mean(bond_errs),
        },
        "feedback_stack": [
            "shell_anchor_projection (occupancy / open / polarity)",
            "em^(α·length_share) spectral length dress",
            "1+base·open² covalent-network packing",
            "ω* spectral scale pin (quarantine comparison elsewhere)",
            "phase–material two-way fixed point (5/5)",
        ],
    }


def protein_bond_geometry_side() -> dict[str, Any]:
    preds = {
        "N_CA": peptide_bond_length_n_ca(),
        "CA_C": peptide_bond_length_ca_c(),
        "C_N": peptide_bond_length_c_n(),
        "C_O": peptide_bond_length_c_o(),
    }
    rows: list[dict[str, Any]] = []
    length_shares: list[float] = []
    ems: list[float] = []
    packings_available: list[float] = []
    energy_shares: list[float] = []
    length_scales: list[float] = []
    errors: list[float] = []
    gas_errors: list[float] = []

    for slot, pred in preds.items():
        dress = peptide_bond_dress_cached(slot, environment="aqueous")
        gas = peptide_bond_dress_cached(slot, environment="gas")
        ref = PEPTIDE_BOND_COMPARISON_ANGSTROM[slot]
        err = _err_pct(pred, ref)
        # Reconstruct gas-dressed length for comparison.
        bare = pred / max(dress.length_scale, 1.0e-30)
        gas_pred = bare * gas.length_scale
        gas_err = _err_pct(gas_pred, ref)
        errors.append(err)
        gas_errors.append(gas_err)
        shell = dress.projection.to_dict()
        length_shares.append(float(shell["length_share"]))
        ems.append(dress.em)
        packings_available.append(float(shell["network_open_channel_packing_scale"]))
        energy_shares.append(float(shell["energy_share"]))
        length_scales.append(dress.length_scale)
        rows.append(
            {
                "slot": slot,
                "pred_angstrom": pred,
                "engh_huber_angstrom": ref,
                "error_pct": err,
                "gas_em_pred_angstrom": gas_pred,
                "gas_em_error_pct": gas_err,
                "length_scale": dress.length_scale,
                "em": dress.em,
                "length_share": shell["length_share"],
                "open_channel_fraction": shell["open_channel_fraction"],
                "network_packing_available": shell["network_open_channel_packing_scale"],
                "packing_applied_on_backbone": False,
                "environment": "aqueous",
                "note": (
                    "aqueous: diamond-node + thermal γ/16 (no gas EM); "
                    "gas EM shown only as counterfactual"
                ),
            }
        )

    register_rows = []
    reg_packings: list[float] = []
    outside_scales: list[float] = []
    from hqiv_lab.protein_solvent_phase import aqueous_outside_geometry_scale

    for kind, occ in REGISTER_OCCUPANCY.items():
        pack = tertiary_contact_packing_scale(kind, aqueous=True)
        outside = aqueous_outside_geometry_scale(contact_kind=kind)
        reg_packings.append(pack)
        outside_scales.append(outside["scale"])
        register_rows.append(
            {
                "register": kind,
                "occupancy": occ,
                "open_channel_fraction": 1.0 - occ,
                "packing_scale": pack,
                "outside_geometry_scale": outside["scale"],
                "outside_bulk": outside["bulk"],
                "outside_local": outside["local_defect"],
                "outside_thermal": outside["thermal"],
                "phase_contact_weight": outside["phase_contact_weight"],
            }
        )

    return {
        "panel": "peptide_backbone_and_registers",
        "comparison_policy": (
            "Engh–Huber / Ideal peptide bond lengths are comparison quarantine only; "
            "aqueous protein uses outside density/curvature on tertiary scales, not gas EM on σ bonds"
        ),
        "backbone_bonds": rows,
        "tertiary_registers": register_rows,
        "shell_manifest": peptide_shell_dress_manifest(environment="aqueous"),
        "mean_treatment": {
            "length_share": _mean(length_shares),
            "em": _mean(ems),
            "network_open_channel_packing_scale_available": _mean(packings_available),
            "network_open_channel_packing_applied_on_backbone": 1.0,
            "tertiary_packing_scale": _mean(reg_packings),
            "tertiary_outside_geometry_scale": _mean(outside_scales),
            "energy_share": _mean(energy_shares),
            "length_dress_em_alpha_share": _mean(length_scales),
            "n_bond_slots": len(rows),
            "n_registers": len(register_rows),
        },
        "accuracy_headline": {
            "bond_geo_mean_abs_pct": _geo_mean_abs_pct(errors),
            "bond_mean_abs_pct": _mean([abs(e) for e in errors]),
            "bond_signed_mean_pct": _mean(errors),
            "gas_em_counterfactual_geo_mean_abs_pct": _geo_mean_abs_pct(gas_errors),
        },
        "feedback_stack": [
            "aqueous σ bonds: diamond-node + thermal γ/16 (gas EM off)",
            "tertiary: 1+base·open² with aqueous phase_contact_weight",
            "tertiary: outsideBulk(foldXi)×local×thermal from OutsideContactLedger",
            "LDL/HDL interface dress + directional solvent ρ",
            "competitive fold gate: Cα RMSD < 2 Å (all lengths)",
            "gas em^(α·length_share) retained only as spectroscopy counterfactual",
        ],
    }


def protein_fold_side(*, refresh_fold: bool) -> dict[str, Any]:
    if refresh_fold or not PROTEIN_FOLDER_JSON.is_file():
        from hqiv_protein_folder_audit import build_protein_folder_audit

        payload = build_protein_folder_audit(
            PROTEIN_FOLDER_JSON.parent / "miniprotein_witnesses.json",
            include_network=False,
            dual_temperature=False,
        )
        PROTEIN_FOLDER_JSON.write_text(json.dumps(payload, indent=2) + "\n")
    else:
        payload = json.loads(PROTEIN_FOLDER_JSON.read_text())

    folds = payload.get("fold_audit", {}).get("folds", [])
    rmsds = [float(f["ca_rmsd_angstrom"]) for f in folds if f.get("ca_rmsd_angstrom") is not None]
    passed = sum(1 for f in folds if f.get("passed") is True)
    failed = sum(1 for f in folds if f.get("passed") is False)
    return {
        "panel": "protein_fold_ladder",
        "source_json": str(PROTEIN_FOLDER_JSON.relative_to(_REPO_ROOT)),
        "refreshed": refresh_fold,
        "competitive_gate_angstrom": COMPETITIVE_CA_RMSD_PASS_ANGSTROM,
        "pass_rule": "strict Cα RMSD < 2 Å (AlphaFold-class; all lengths)",
        "targets": len(folds),
        "passed": passed,
        "failed": failed,
        "mean_ca_rmsd_angstrom": _mean(rmsds),
        "rows": [
            {
                "name": f["name"],
                "n_residues": f["n_residues"],
                "ca_rmsd_angstrom": f.get("ca_rmsd_angstrom"),
                "ca_rmsd_pass_angstrom": f.get("ca_rmsd_pass_angstrom"),
                "passed": f.get("passed"),
            }
            for f in folds
        ],
        "trp_cage_rmsd_angstrom": next(
            (f.get("ca_rmsd_angstrom") for f in folds if f.get("name") == "trp_cage"),
            None,
        ),
    }


def compare_mean_treatment(chem: dict[str, Any], prot: dict[str, Any]) -> dict[str, Any]:
    ct = chem["mean_treatment"]
    pt = prot["mean_treatment"]
    return {
        "shared_language": (
            "shell_anchor_projection → em^(α·length_share) → 1+base·open²"
        ),
        "chemistry": ct,
        "protein": pt,
        "deltas_protein_minus_chemistry": {
            "length_share": pt["length_share"] - ct["length_share"],
            "em": pt["em"] - ct["em"],
            "length_dress_em_alpha_share": (
                pt["length_dress_em_alpha_share"] - ct["length_dress_em_alpha_share"]
            ),
            "energy_share": pt["energy_share"] - ct["energy_share"],
            "packing_note": (
                "chemistry applies open² on covalent networks; "
                "protein applies open² on tertiary registers only "
                f"(mean tertiary packing={pt['tertiary_packing_scale']:.4f}, "
                f"backbone-available but unused mean={pt['network_open_channel_packing_scale_available']:.4f})"
            ),
        },
        "accuracy_gap": {
            "chemistry_r_e_geo_mean_pct": chem["accuracy_headline"]["r_e_geo_mean_pct"],
            "protein_bond_geo_mean_abs_pct": prot["accuracy_headline"]["bond_geo_mean_abs_pct"],
            "chemistry_carbon_density_mean_abs_pct": chem["accuracy_headline"][
                "carbon_density_mean_abs_pct"
            ],
            "note": (
                "Bond-length % errors are the closest like-for-like geometry metric; "
                "fold Cα RMSD is a tertiary-structure metric, not a bond-length %."
            ),
        },
    }


def build_payload(*, refresh_fold: bool = False) -> dict[str, Any]:
    chem = chemistry_side()
    prot_bonds = protein_bond_geometry_side()
    fold = protein_fold_side(refresh_fold=refresh_fold)
    return {
        "source": "scripts/hqiv_protein_chemistry_geometry_compare_audit.py",
        "role": (
            "Fresh side-by-side audit: protein fold/peptide geometry vs SOTA "
            "general bond-geometry chemistry stack under shared shell feedback"
        ),
        "comparison_policy": (
            "NIST/CRC/Engh–Huber/PDB are quarantine only; never derivation inputs"
        ),
        "chemistry": chem,
        "protein_geometry": prot_bonds,
        "protein_fold": fold,
        "mean_treatment_compare": compare_mean_treatment(chem, prot_bonds),
        "verdict": {
            "chemistry_geometry": (
                f"spectral r_e geo-mean {chem['accuracy_headline']['r_e_geo_mean_pct']:.2f}%, "
                f"carbon density mean |err| {chem['accuracy_headline']['carbon_density_mean_abs_pct']:.2f}%"
            ),
            "protein_bonds": (
                f"peptide bond geo-mean |err| "
                f"{prot_bonds['accuracy_headline']['bond_geo_mean_abs_pct']:.2f}% "
                f"vs Engh–Huber quarantine"
            ),
            "protein_fold": (
                f"{fold['passed']}/{fold['targets']} clear Cα < "
                f"{fold['competitive_gate_angstrom']} Å; "
                f"mean RMSD {fold['mean_ca_rmsd_angstrom']:.2f} Å; "
                f"Trp-cage {fold['trp_cage_rmsd_angstrom']:.2f} Å"
                if fold["trp_cage_rmsd_angstrom"] is not None
                else f"{fold['passed']}/{fold['targets']} competitive passes"
            ),
            "treatment_parity": (
                "Same shell projection language; chemistry uses gas-phase EM + open² "
                "on network lengths (NIST assay). Protein aqueous path: backbone σ "
                "bonds = diamond-node + γ/16 (no gas EM); tertiary Cα = packing × "
                "outsideBulk(B_hom(foldXi),ρ)×local×thermal."
            ),
        },
    }


def print_report(payload: dict[str, Any]) -> None:
    chem = payload["chemistry"]
    prot = payload["protein_geometry"]
    fold = payload["protein_fold"]
    cmp_ = payload["mean_treatment_compare"]
    ct = cmp_["chemistry"]
    pt = cmp_["protein"]

    print("=== Protein vs chemistry bond-geometry audit ===")
    print(
        "Shared language: shell_anchor_projection; gas EM on NIST spectral; "
        "aqueous outsideBulk×packing on protein tertiary"
    )
    print("Laboratory constants are comparison quarantine only.")
    print()
    print("-- Mean shell / feedback treatment")
    print(
        f"{'quantity':<40} {'chemistry':>12} {'protein':>12} {'Δ(p−c)':>10}"
    )
    for key, label in (
        ("length_share", "length_share"),
        ("em", "em"),
        ("length_dress_em_alpha_share", "em^(α·length_share)"),
        ("energy_share", "energy_share"),
    ):
        c, p = ct[key], pt[key]
        print(f"{label:<40} {c:12.4f} {p:12.4f} {p-c:+10.4f}")
    print(
        f"{'open² packing (applied)':<40} "
        f"{ct['network_open_channel_packing_scale']:12.4f} "
        f"{pt['tertiary_packing_scale']:12.4f} "
        f"{'tertiary':>10}"
    )
    print(
        f"{'open² available on backbone (unused)':<40} "
        f"{'—':>12} {pt['network_open_channel_packing_scale_available']:12.4f}"
    )
    print()
    print("-- Accuracy (quarantine comparisons)")
    ah = chem["accuracy_headline"]
    ph = prot["accuracy_headline"]
    print(
        f"  Chemistry spectral geo-mean |err|%:  "
        f"r_e {ah['r_e_geo_mean_pct']:.2f}  "
        f"D_e {ah['D_e_geo_mean_pct']:.2f}  "
        f"B_e {ah['B_e_geo_mean_pct']:.2f}"
    )
    print(
        f"  Chemistry carbon mean |err|%:        "
        f"density {ah['carbon_density_mean_abs_pct']:.2f}  "
        f"bond {ah['carbon_bond_mean_abs_pct']:.2f}"
    )
    print(
        f"  Protein peptide bonds vs Engh–Huber: "
        f"geo-mean |err| {ph['bond_geo_mean_abs_pct']:.2f}%  "
        f"mean |err| {ph['bond_mean_abs_pct']:.2f}%  "
        f"signed mean {ph['bond_signed_mean_pct']:+.2f}%  "
        f"(gas-EM counterfactual {ph.get('gas_em_counterfactual_geo_mean_abs_pct', float('nan')):.2f}%)"
    )
    print(
        f"  Protein tertiary outside scale (mean): "
        f"{pt.get('tertiary_outside_geometry_scale', float('nan')):.4f}  "
        f"packing {pt['tertiary_packing_scale']:.4f}"
    )
    print(
        f"  Protein fold competitive (<{fold['competitive_gate_angstrom']} Å): "
        f"{fold['passed']}/{fold['targets']}  "
        f"mean Cα RMSD {fold['mean_ca_rmsd_angstrom']:.2f} Å  "
        f"Trp-cage {fold['trp_cage_rmsd_angstrom']:.2f} Å"
    )
    print()
    print("-- Peptide bond rows")
    print(f"{'slot':<8} {'pred':>8} {'EH':>8} {'err%':>8} {'len×':>8} {'em':>8}")
    for row in prot["backbone_bonds"]:
        print(
            f"{row['slot']:<8} {row['pred_angstrom']:8.4f} "
            f"{row['engh_huber_angstrom']:8.4f} {row['error_pct']:+8.2f} "
            f"{row['length_scale']:8.4f} {row['em']:8.4f}"
        )
    print()
    print("-- Spectral panel (chemistry)")
    print(f"{'name':<6} {'r_e':>8} {'err%':>8} {'D_e err%':>10} {'B_e err%':>10}")
    for row in chem["spectral"]["rows"]:
        print(
            f"{row['name']:<6} {row['r_e_angstrom']:8.4f} "
            f"{row['r_e_error_pct']:+8.2f} "
            f"{row['D_e_error_pct']:+10.2f} "
            f"{row['B_e_error_pct']:+10.2f}"
        )
    print()
    print("-- Verdict")
    for k, v in payload["verdict"].items():
        print(f"  {k}: {v}")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Compare protein vs SOTA chemistry bond-geometry under shared shell feedback."
    )
    parser.add_argument(
        "--json-out",
        type=Path,
        default=DEFAULT_JSON,
        help=f"JSON output path (default {DEFAULT_JSON})",
    )
    parser.add_argument(
        "--refresh-fold",
        action="store_true",
        help="Re-run the full protein fold ladder (slow); else reuse protein_folder_audit.json",
    )
    parser.add_argument(
        "--no-json",
        action="store_true",
        help="Print only; do not write JSON",
    )
    args = parser.parse_args()

    payload = build_payload(refresh_fold=args.refresh_fold)
    print_report(payload)
    if not args.no_json:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2) + "\n")
        print(f"\nwrote {args.json_out}")


if __name__ == "__main__":
    main()

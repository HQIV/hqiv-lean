#!/usr/bin/env python3
"""
Miniprotein fold audit — HQIV secondary-structure spine vs PDB Cα witnesses.

Literature coordinates grade readouts only; they are never imported as fold targets.

Usage:
  PYTHONPATH=scripts:. python3 scripts/hqiv_miniprotein_fold_audit.py
  PYTHONPATH=scripts:. python3 scripts/hqiv_miniprotein_fold_audit.py --refresh-witnesses
"""

from __future__ import annotations

import argparse
import json
import sys
import urllib.request
from pathlib import Path
from typing import Any

_REPO = Path(__file__).resolve().parent.parent
if str(_REPO) not in sys.path:
    sys.path.insert(0, str(_REPO))
if str(_REPO / "scripts") not in sys.path:
    sys.path.insert(0, str(_REPO / "scripts"))

from hqiv_lab.foundation_panel import peptide_fold_entry
from hqiv_lab.miniprotein_fold import (
    MiniproteinFoldResult,
    CURVATURE_WEIGHTED_FOLD_TARGETS,
    FRAGMENT_FOLD_SPECS,
    fold_fragment_by_name,
    fold_glycylglycine,
    fold_miniprotein_fragment,
    fold_trp_cage,
    hydrophobic_contact_pairs,
    radius_of_gyration,
    run_ladder_with_engine,
)
from hqiv_lab.protein_solvent_phase import (
    CRYO_CRYSTALLOGRAPHY_TEMPERATURE_K,
    PROTEIN_FOLDING_TEMPERATURE_K,
    aqueous_bulk_curvature_at_t,
)


def _fetch_gg_ca_from_cod() -> list[list[float]]:
    """Cα proxy atoms C1, C3 from COD:2100438 (Moggach gly–gly crystal)."""
    url = "https://www.crystallography.net/cod/2100438.cif"
    text = urllib.request.urlopen(url, timeout=90).read().decode("utf-8", errors="replace")
    cell: dict[str, float] = {}
    frac: dict[str, tuple[float, float, float]] = {}
    in_atom = False
    for line in text.splitlines():
        if line.startswith("_cell_length_a"):
            cell["a"] = float(line.split()[1].split("(")[0])
        elif line.startswith("_cell_length_b"):
            cell["b"] = float(line.split()[1].split("(")[0])
        elif line.startswith("_cell_length_c"):
            cell["c"] = float(line.split()[1].split("(")[0])
        elif line.startswith("_cell_angle_beta"):
            cell["beta"] = float(line.split()[1].split("(")[0])
        elif line.startswith("_atom_site_type_symbol"):
            in_atom = True
            continue
        elif in_atom and line.startswith("loop_"):
            in_atom = False
        elif in_atom and line.startswith("C ") and len(line.split()) >= 5:
            parts = line.split()
            label = parts[1]
            if label in ("C1", "C3"):
                fx = float(parts[2].split("(")[0])
                fy = float(parts[3].split("(")[0])
                fz = float(parts[4].split("(")[0])
                frac[label] = (fx, fy, fz)
    if "C1" not in frac or "C3" not in frac:
        raise RuntimeError("COD 2100438: C1/C3 alpha carbons not found")
    import math

    beta = math.radians(cell["beta"])
    a, b, c = cell["a"], cell["b"], cell["c"]
    c_vec = (c * math.cos(beta), 0.0, c * math.sin(beta))

    def to_cart(frac_xyz: tuple[float, float, float]) -> list[float]:
        x, y, z = frac_xyz
        return [
            a * x + c_vec[0] * z,
            b * y + c_vec[1] * z,
            c_vec[2] * z,
        ]

    return [to_cart(frac["C1"]), to_cart(frac["C3"])]


def _fetch_trp_cage_ca_from_pdb() -> list[list[float]]:
    url = "https://files.rcsb.org/download/1L2Y.pdb"
    text = urllib.request.urlopen(url, timeout=60).read().decode("utf-8", errors="replace")
    in_model = False
    coords: list[list[float]] = []
    for line in text.splitlines():
        if line.startswith("MODEL"):
            in_model = line.split()[1] == "1"
            continue
        if line.startswith("ENDMDL") and in_model:
            break
        if not in_model or not line.startswith("ATOM"):
            continue
        if line[12:16].strip() != "CA" or line[21] != "A":
            continue
        coords.append([float(line[30:38]), float(line[38:46]), float(line[46:54])])
    if len(coords) != 20:
        raise RuntimeError(f"expected 20 Cα from 1L2Y model 1, got {len(coords)}")
    return coords


def _fetch_pdb_ca_slice(
  pdb_id: str,
  *,
  chain: str = "A",
  model: int = 1,
  res_start: int,
  res_end: int,
) -> list[list[float]]:
    """Inclusive 1-based residue Cα slice from wwPDB (model 1 default)."""
    url = f"https://files.rcsb.org/download/{pdb_id}.pdb"
    text = urllib.request.urlopen(url, timeout=60).read().decode("utf-8", errors="replace")
    in_model = False
    by_res: dict[int, list[float]] = {}
    for line in text.splitlines():
        if line.startswith("MODEL"):
            in_model = int(line.split()[1]) == model
            continue
        if line.startswith("ENDMDL") and in_model:
            break
        if not in_model or not line.startswith("ATOM"):
            continue
        if line[12:16].strip() != "CA" or line[21] != chain:
            continue
        res = int(line[22:26])
        if res_start <= res <= res_end:
            by_res[res] = [float(line[30:38]), float(line[38:46]), float(line[46:54])]
    missing = [r for r in range(res_start, res_end + 1) if r not in by_res]
    if missing:
        raise RuntimeError(f"{pdb_id} chain {chain}: missing Cα for residues {missing}")
    return [by_res[r] for r in range(res_start, res_end + 1)]


def load_witnesses(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text())
    return payload.get("witnesses", payload)


def save_witnesses(path: Path, witnesses: dict[str, Any]) -> None:
    payload = {
        "source": str(path.relative_to(_REPO)) if path.is_relative_to(_REPO) else str(path),
        "comparison_policy": "PDB/COD Cα traces grade HQIV fold readouts only — never fold inputs",
        "witnesses": witnesses,
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n")


def _witness_ca(entry: dict[str, Any]) -> list[tuple[float, float, float]] | None:
    raw = entry.get("ca_angstrom")
    if raw is None:
        return None
    return [tuple(float(x) for x in row) for row in raw]


def _end_to_end(ca: list[tuple[float, float, float]]) -> float | None:
    if len(ca) < 2:
        return None
    import math

    a, b = ca[0], ca[-1]
    return math.sqrt(sum((a[i] - b[i]) ** 2 for i in range(3)))


def audit_fold(
    fold: MiniproteinFoldResult,
    *,
    witness_rg: float | None = None,
) -> dict[str, Any]:
    pred_rg = radius_of_gyration(list(fold.ca_trace))
    row: dict[str, Any] = {
        "name": fold.name,
        "sequence": fold.sequence,
        "n_residues": fold.n_residues,
        "strategy": fold.strategy,
        "network_contacts": fold.network_contacts,
        "bond_geometry_angstrom": fold.bond_geometry,
        "predicted_radius_of_gyration_A": pred_rg,
        "witness_radius_of_gyration_A": witness_rg,
        "ca_rmsd_angstrom": fold.ca_rmsd_angstrom,
        "ca_rmsd_pass_angstrom": fold.ca_rmsd_pass_angstrom,
        "passed": fold.passed,
    }
    if witness_rg is not None and witness_rg > 0:
        row["radius_of_gyration_error_pct"] = abs(pred_rg - witness_rg) / witness_rg * 100.0
    return row


def _fold_curvature_weighted_target(
    name: str,
    witnesses: dict[str, Any],
    *,
    temperature_k: float,
    include_network: bool,
    closure_engine: str,
) -> MiniproteinFoldResult:
    raw = witnesses.get(name, {}).get("ca_angstrom")
    witness_ca = [tuple(row) for row in raw] if raw is not None else None
    if witness_ca is None:
        raise RuntimeError(f"{name} witness Cα missing — run with --refresh-witnesses")
    if name == "trp_cage":
        from hqiv_lab.foundation_panel import peptide_fold_entry

        return fold_trp_cage(
            witness_ca=list(witness_ca),
            pass_a=peptide_fold_entry("trp_cage").ca_rmsd_pass_angstrom,
            include_network=include_network,
            closure_engine=closure_engine,
            temperature_k=temperature_k,
        )
    return fold_fragment_by_name(
        name,
        witness_ca=list(witness_ca),
        include_network=include_network,
        closure_engine=closure_engine,
        temperature_k=temperature_k,
    )


def build_dual_temperature_comparison(
    witness_path: Path,
    *,
    cytosol_k: float = PROTEIN_FOLDING_TEMPERATURE_K,
    cryo_k: float = CRYO_CRYSTALLOGRAPHY_TEMPERATURE_K,
    include_network: bool = False,
    closure_engine: str = "nerf",
) -> dict[str, Any]:
    """
    Cryo vs cytosol fold comparison on curvature-weighted tertiary targets.

    Witness PDB coordinates are fixed; only bulk aqueous ρ and closure dress change with T.
    """
    witnesses = load_witnesses(witness_path)
    rows: list[dict[str, Any]] = []
    for name in CURVATURE_WEIGHTED_FOLD_TARGETS:
        cytosol_fold = _fold_curvature_weighted_target(
            name,
            witnesses,
            temperature_k=cytosol_k,
            include_network=include_network,
            closure_engine=closure_engine,
        )
        cryo_fold = _fold_curvature_weighted_target(
            name,
            witnesses,
            temperature_k=cryo_k,
            include_network=include_network,
            closure_engine=closure_engine,
        )
        r_cyto = cytosol_fold.ca_rmsd_angstrom
        r_cryo = cryo_fold.ca_rmsd_angstrom
        delta = None
        if r_cyto is not None and r_cryo is not None:
            delta = r_cryo - r_cyto
        rows.append(
            {
                "name": name,
                "cytosol_temperature_K": cytosol_k,
                "cryo_temperature_K": cryo_k,
                "aqueous_bulk_curvature_cytosol": aqueous_bulk_curvature_at_t(cytosol_k),
                "aqueous_bulk_curvature_cryo": aqueous_bulk_curvature_at_t(cryo_k),
                "cytosol": audit_fold(cytosol_fold),
                "cryo": audit_fold(cryo_fold),
                "ca_rmsd_delta_cryo_minus_cytosol_A": delta,
                "cryo_closer_to_witness": (
                    r_cryo < r_cyto if r_cyto is not None and r_cryo is not None else None
                ),
            }
        )
    deltas = [
        r["ca_rmsd_delta_cryo_minus_cytosol_A"]
        for r in rows
        if r["ca_rmsd_delta_cryo_minus_cytosol_A"] is not None
    ]
    return {
        "source": "scripts/hqiv_miniprotein_fold_audit.py",
        "comparison_policy": (
            "Same PDB witnesses; T dresses bulk aqueous ρ only (ξ lock-in at contact horizon)"
        ),
        "closure_engine": closure_engine,
        "targets": list(CURVATURE_WEIGHTED_FOLD_TARGETS),
        "cytosol_temperature_K": cytosol_k,
        "cryo_temperature_K": cryo_k,
        "comparisons": rows,
        "summary": {
            "targets": len(rows),
            "mean_ca_rmsd_delta_cryo_minus_cytosol_A": (
                sum(deltas) / len(deltas) if deltas else None
            ),
            "cryo_closer_count": sum(1 for r in rows if r.get("cryo_closer_to_witness") is True),
            "cytosol_closer_count": sum(1 for r in rows if r.get("cryo_closer_to_witness") is False),
        },
    }


def build_payload(
    witness_path: Path,
    *,
    include_network: bool = False,
    closure_engine: str = "nerf",
) -> dict[str, Any]:
    witnesses = load_witnesses(witness_path)
    rows: list[dict[str, Any]] = []

    gg_ref = peptide_fold_entry("GG")
    gg_w = witnesses.get("GG", {})
    gg_ca = _witness_ca(gg_w)
    gg_fold = fold_glycylglycine(
        witness_ca=list(gg_ca) if gg_ca else None,
        pass_a=gg_ref.ca_rmsd_pass_angstrom,
        include_network=include_network,
    )
    rows.append(audit_fold(gg_fold))

    for spec in FRAGMENT_FOLD_SPECS:
        entry = witnesses.get(spec.name, {})
        frag_ca = _witness_ca(entry)
        if frag_ca is None:
            raise RuntimeError(f"{spec.name} witness Cα missing — run with --refresh-witnesses")
        frag_fold = fold_miniprotein_fragment(
            spec,
            witness_ca=list(frag_ca),
            include_network=include_network,
            closure_engine=closure_engine,
        )
        rows.append(audit_fold(frag_fold))

    tc_ref = peptide_fold_entry("trp_cage")
    tc_w = witnesses.get("trp_cage", {})
    tc_ca = _witness_ca(tc_w)
    if tc_ca is None:
        raise RuntimeError("trp_cage witness Cα missing — run with --refresh-witnesses")
    tc_witness_rg = radius_of_gyration(list(tc_ca))
    tc_fold = fold_trp_cage(
        witness_ca=list(tc_ca),
        pass_a=tc_ref.ca_rmsd_pass_angstrom,
        include_network=include_network,
        closure_engine=closure_engine,
    )
    tc_row = audit_fold(tc_fold, witness_rg=tc_witness_rg)
    tc_row["tertiary_contacts"] = tc_fold.tertiary_contacts
    tc_row["hydrophobic_pairs"] = len(hydrophobic_contact_pairs(tc_fold.sequence))
    tc_row["diagnostics"] = {
        "witness_end_to_end_ca_A": _end_to_end(list(tc_ca)),
        "predicted_end_to_end_ca_A": _end_to_end(list(tc_fold.ca_trace)),
        "notes": (
            "Tertiary graph: helix i±3/4, sheet i+2, helix–sheet register, "
            "hydrophobic, compact terminus — staged closure (SS → hydro → terminus). "
            "All targets from derived peptide geometry (no PDB inputs)."
        ),
    }
    rows.append(tc_row)

    return {
        "source": "scripts/hqiv_miniprotein_fold_audit.py",
        "closure_engine": closure_engine,
        "comparison_policy": "PDB Cα witnesses grade HQIV fold readouts only",
        "folds": rows,
        "summary": {
            "targets": len(rows),
            "passed": sum(1 for r in rows if r.get("passed") is True),
            "mean_ca_rmsd_angstrom": sum(
                r["ca_rmsd_angstrom"] for r in rows if r.get("ca_rmsd_angstrom") is not None
            )
            / max(1, sum(1 for r in rows if r.get("ca_rmsd_angstrom") is not None)),
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Miniprotein fold foundation audit")
    parser.add_argument(
        "--json",
        type=Path,
        default=_REPO / "data" / "miniprotein_fold_audit.json",
    )
    parser.add_argument(
        "--witnesses",
        type=Path,
        default=_REPO / "data" / "miniprotein_witnesses.json",
    )
    parser.add_argument(
        "--refresh-witnesses",
        action="store_true",
        help="Re-fetch 1L2Y + COD:2100438 Cα witnesses from wwPDB/COD",
    )
    parser.add_argument(
        "--closure-engine",
        choices=("nerf", "osh"),
        default="nerf",
        help="Tertiary closure backend (osh = OSHoracle contact matrix + carrier)",
    )
    parser.add_argument(
        "--compare-osh",
        action="store_true",
        help="Print NeRF vs OSH RMSD side-by-side (witness ladder)",
    )
    parser.add_argument(
        "--full-network",
        action="store_true",
        help="Build full curvature contact network (slow; default uses O(1) scaffold count)",
    )
    args = parser.parse_args()

    if args.compare_osh:
        witnesses = load_witnesses(args.witnesses)
        nerf = run_ladder_with_engine("nerf", witnesses=witnesses, include_network=args.full_network)
        osh = run_ladder_with_engine("osh", witnesses=witnesses, include_network=args.full_network)
        print("NeRF vs OSH closure (Cα RMSD vs witnesses)")
        print("=" * 60)
        for name in nerf:
            rn = nerf[name].ca_rmsd_angstrom
            ro = osh[name].ca_rmsd_angstrom
            rn_s = f"{rn:.2f}" if rn is not None else "n/a"
            ro_s = f"{ro:.2f}" if ro is not None else "n/a"
            print(f"  {name:16s}  nerf={rn_s} Å  osh={ro_s} Å")
        return 0

    if args.refresh_witnesses:
        witnesses = load_witnesses(args.witnesses)
        witnesses.setdefault("trp_cage", {})["ca_angstrom"] = _fetch_trp_cage_ca_from_pdb()
        witnesses["trp_cage"]["sequence"] = "NLYIQWLKDGGPSSGRPPPS"
        witnesses["trp_cage"]["pdb_id"] = "1L2Y"
        witnesses.setdefault("GG", {})["ca_angstrom"] = _fetch_gg_ca_from_cod()
        witnesses["GG"]["sequence"] = "GG"
        witnesses["GG"]["structure_id"] = "COD:2100438"
        fragment_slices = {
            spec.name: spec.pdb_residue_range
            for spec in FRAGMENT_FOLD_SPECS
            if spec.pdb_residue_range is not None
        }
        for name, (start, end) in fragment_slices.items():
            spec = next(s for s in FRAGMENT_FOLD_SPECS if s.name == name)
            witnesses.setdefault(name, {})
            witnesses[name]["ca_angstrom"] = _fetch_pdb_ca_slice(
                "1L2Y", res_start=start, res_end=end
            )
            witnesses[name]["sequence"] = spec.sequence
            witnesses[name]["pdb_id"] = "1L2Y"
            witnesses[name]["residue_range"] = [start, end]
        save_witnesses(args.witnesses, witnesses)
        print(f"Refreshed GG, fragments, and trp_cage witnesses → {args.witnesses}")

    payload = build_payload(
        args.witnesses,
        include_network=args.full_network,
        closure_engine=args.closure_engine,
    )
    args.json.parent.mkdir(parents=True, exist_ok=True)
    args.json.write_text(json.dumps(payload, indent=2) + "\n")

    print("HQIV miniprotein fold audit (predict vs PDB Cα witness)")
    print("=" * 60)
    for row in payload["folds"]:
        rmsd = row.get("ca_rmsd_angstrom")
        rmsd_s = f"{rmsd:.2f}" if rmsd is not None else "n/a"
        passed = row.get("passed")
        if passed is True:
            status = "PASS"
        elif passed is False:
            status = "FAIL"
        else:
            status = "n/a"
        rg_e = row.get("radius_of_gyration_error_pct")
        rg_s = f"  Rg err={rg_e:.1f}%" if rg_e is not None else ""
        print(
            f"  {row['name']:10s}  n={row['n_residues']:2d}  "
            f"RMSD={rmsd_s} Å  threshold={row.get('ca_rmsd_pass_angstrom')}  {status}{rg_s}"
        )
        print(f"             strategy={row['strategy']}  contacts={row['network_contacts']}")
    s = payload["summary"]
    print(f"Summary: mean Cα RMSD={s['mean_ca_rmsd_angstrom']:.2f} Å  passed={s['passed']}/{s['targets']}")
    print(f"Wrote {args.json}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

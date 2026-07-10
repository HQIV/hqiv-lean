#!/usr/bin/env python3
"""
Fold the HQIV miniprotein bench through PROtien ribosome tunnel + staged NeRF.

Uses lab ladder sequences / SS maps / competitive <2 Å gate, and grades against
``data/miniprotein_witnesses.json`` (comparison quarantine only).

Requires sibling PROtien + HQIV_LEAN on PYTHONPATH:

  HQIV_LEAN_ROOT=/path/to/HQIV_LEAN \\
  PYTHONPATH=.:scripts:/path/to/PROtien/src:$HQIV_LEAN_ROOT:$HQIV_LEAN_ROOT/scripts \\
  python3 scripts/hqiv_tunnel_nerf_bench_audit.py
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
from pathlib import Path
from typing import Any

import numpy as np

_REPO = Path(__file__).resolve().parents[1]
_DEFAULT_PROTIEN = _REPO.parent / "PROtien" / "src"


def _ensure_paths(protien_src: Path, hqiv_root: Path) -> None:
    for p in (str(_REPO), str(_REPO / "scripts"), str(protien_src), str(hqiv_root), str(hqiv_root / "scripts")):
        if p not in sys.path:
            sys.path.insert(0, p)
    os.environ.setdefault("HQIV_LEAN_ROOT", str(hqiv_root))


def _load_witnesses(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text())
    return payload.get("witnesses", payload)


def _witness_ca(entry: dict[str, Any] | None) -> list[tuple[float, float, float]] | None:
    if not entry:
        return None
    raw = entry.get("ca_angstrom")
    if raw is None:
        return None
    return [tuple(float(x) for x in row) for row in raw]


def _ss_map_to_string(n: int, ss_map: dict[str, tuple[int, ...]]) -> str:
    chars = ["C"] * n
    for kind, idxs in ss_map.items():
        for i in idxs:
            if 1 <= i <= n:
                chars[i - 1] = kind
    return "".join(chars)


def _bench_targets() -> list[dict[str, Any]]:
    from hqiv_lab.miniprotein_fold import (
        COMPETITIVE_CA_RMSD_PASS_ANGSTROM,
        FRAGMENT_FOLD_SPECS,
        TRP_CAGE_SECONDARY_STRUCTURE,
        TRP_CAGE_SEQUENCE,
        TRP_CAGE_STAGED_FINAL_ROUNDS,
        TRP_CAGE_STAGED_TERMINUS_ROUNDS,
    )

    targets: list[dict[str, Any]] = [
        {
            "name": "GG",
            "sequence": "GG",
            "ss_map": {"C": (1, 2)},
            "pass_a": COMPETITIVE_CA_RMSD_PASS_ANGSTROM,
            "final_rounds": 4,
            "terminus_rounds": 2,
            "include_terminus": False,
        }
    ]
    for spec in FRAGMENT_FOLD_SPECS:
        targets.append(
            {
                "name": spec.name,
                "sequence": spec.sequence,
                "ss_map": dict(spec.ss_map),
                "pass_a": float(spec.pass_a),
                "final_rounds": int(
                    spec.staged_final_rounds
                    if spec.staged_final_rounds is not None
                    else (16 if spec.staged_closure else 8)
                ),
                "terminus_rounds": int(
                    spec.staged_terminus_rounds
                    if spec.staged_terminus_rounds is not None
                    else 8
                ),
                "include_terminus": len(spec.sequence) >= 8,
                "curvature_weights": bool(spec.curvature_weights or spec.staged_closure),
            }
        )
    targets.append(
        {
            "name": "trp_cage",
            "sequence": TRP_CAGE_SEQUENCE,
            "ss_map": dict(TRP_CAGE_SECONDARY_STRUCTURE),
            "pass_a": COMPETITIVE_CA_RMSD_PASS_ANGSTROM,
            "final_rounds": TRP_CAGE_STAGED_FINAL_ROUNDS,
            "terminus_rounds": TRP_CAGE_STAGED_TERMINUS_ROUNDS,
            "include_terminus": True,
            "curvature_weights": True,
        }
    )
    return targets


def fold_target_tunnel_nerf(
    target: dict[str, Any],
    *,
    temperature_k: float,
    quick: bool,
    seed_mode: str,
    tunnel_weight: float,
    handedness_bias: float,
) -> dict[str, Any]:
    from horizon_physics.proteins.full_protein_minimizer import minimize_full_chain
    from horizon_physics.proteins.post_tunnel_hqiv_nerf import (
        mean_signed_handedness,
        refine_ca_post_tunnel_nerf_staged,
    )
    from hqiv_lab.miniprotein_backbone import kabsch_rmsd

    seq = target["sequence"]
    ss_map = target["ss_map"]
    t0 = time.perf_counter()

    # 1) Tunnel extrusion only (null cone + lip + optional handedness bias).
    raw = minimize_full_chain(
        seq,
        simulate_ribosome_tunnel=True,
        post_extrusion_refine=False,
        fast_pass_steps_per_connection=0,
        min_pass_iter_per_connection=0,
        kappa_dihedral=0.0,
        quick=quick,
        tunnel_handedness_bias_weight=float(handedness_bias),
        tunnel_handedness_target=0.4,
        tunnel_handedness_sign=1.0,
        refinement_temperature_k=float(temperature_k),
    )
    ca_tunnel = np.asarray(raw["ca_min"], dtype=float)
    hand_tunnel = mean_signed_handedness(ca_tunnel)

    # 2) Staged NeRF polish with lab SS map (not predict_ss).
    final_rounds = int(target["final_rounds"])
    terminus_rounds = int(target["terminus_rounds"])
    if quick:
        final_rounds = min(final_rounds, 6)
        terminus_rounds = min(terminus_rounds, 4)

    ca_nerf, nerf_info = refine_ca_post_tunnel_nerf_staged(
        ca_tunnel,
        seq,
        temperature_k=float(temperature_k),
        seed_mode=seed_mode,
        tunnel_dihedral_weight=float(tunnel_weight),
        structure_rounds=4 if quick else 8,
        hydrophobic_rounds=4 if quick else 8,
        terminus_rounds=terminus_rounds,
        final_rounds=final_rounds,
        curvature_weights=bool(target.get("curvature_weights", True)),
        macro_ricci_soft=True,
        atom_sites=not quick and len(seq) >= 8,
        include_terminus=bool(target.get("include_terminus", False)),
        ss_map=ss_map,
        align_to_tunnel_frame=True,
        quick=quick,
    )
    elapsed = time.perf_counter() - t0

    ca_list = [tuple(map(float, row)) for row in ca_nerf]
    return {
        "name": target["name"],
        "sequence": seq,
        "n_residues": len(seq),
        "ss_string": _ss_map_to_string(len(seq), ss_map),
        "strategy": (
            "ribosome_tunnel+hqiv_lab_nerf"
            f"+seed_{seed_mode}"
            f"+T{temperature_k:.2f}K"
        ),
        "ca_trace": ca_list,
        "ca_tunnel": [tuple(map(float, row)) for row in ca_tunnel],
        "elapsed_s": elapsed,
        "handedness_tunnel": hand_tunnel,
        "nerf_info": {
            k: v
            for k, v in nerf_info.items()
            if k
            not in (
                "message",
            )
        },
        "pass_a": float(target["pass_a"]),
    }


def grade_row(
    row: dict[str, Any],
    witness_ca: list[tuple[float, float, float]] | None,
    *,
    free_fold_rmsd: float | None = None,
) -> dict[str, Any]:
    from hqiv_lab.miniprotein_backbone import kabsch_rmsd

    out = {
        "name": row["name"],
        "sequence": row["sequence"],
        "n_residues": row["n_residues"],
        "strategy": row["strategy"],
        "ss_string": row["ss_string"],
        "elapsed_s": row["elapsed_s"],
        "handedness_tunnel": row["handedness_tunnel"],
        "handedness_mean_after": row["nerf_info"].get("handedness_mean_after"),
        "handedness_sign_preserved": row["nerf_info"].get("handedness_sign_preserved"),
        "mean_abs_dpsi_from_tunnel_rad": row["nerf_info"].get(
            "mean_abs_dpsi_from_tunnel_rad"
        ),
        "n_contacts": row["nerf_info"].get("n_contacts"),
        "ca_rmsd_pass_angstrom": row["pass_a"],
        "free_fold_ca_rmsd_angstrom": free_fold_rmsd,
    }
    if witness_ca is None:
        out["ca_rmsd_angstrom"] = None
        out["passed"] = None
        return out
    rmsd = kabsch_rmsd(row["ca_trace"], witness_ca)
    out["ca_rmsd_angstrom"] = rmsd
    out["passed"] = rmsd < float(row["pass_a"])
    if free_fold_rmsd is not None:
        out["delta_vs_free_fold_angstrom"] = rmsd - free_fold_rmsd
    return out


def _free_fold_rmsd_table(path: Path | None) -> dict[str, float]:
    if path is None or not path.is_file():
        return {}
    payload = json.loads(path.read_text())
    folds = payload.get("fold_audit", {}).get("folds") or payload.get("folds") or []
    out: dict[str, float] = {}
    for row in folds:
        name = row.get("name")
        rmsd = row.get("ca_rmsd_angstrom")
        if name and rmsd is not None:
            out[str(name)] = float(rmsd)
    return out


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--witnesses",
        type=Path,
        default=_REPO / "data" / "miniprotein_witnesses.json",
    )
    ap.add_argument(
        "--out",
        type=Path,
        default=_REPO / "data" / "tunnel_nerf_bench_audit.json",
    )
    ap.add_argument(
        "--free-fold-audit",
        type=Path,
        default=_REPO / "data" / "protein_folder_audit.json",
        help="Optional free-fold audit for ΔRMSD column",
    )
    ap.add_argument("--protien-src", type=Path, default=_DEFAULT_PROTIEN)
    ap.add_argument("--hqiv-root", type=Path, default=_REPO)
    ap.add_argument("--temperature-k", type=float, default=310.15)
    ap.add_argument("--seed-mode", choices=("blend", "tunnel", "spine"), default="blend")
    ap.add_argument("--tunnel-weight", type=float, default=0.55)
    ap.add_argument("--handedness-bias", type=float, default=0.03)
    ap.add_argument("--quick", action="store_true", help="Reduced NeRF rounds")
    ap.add_argument(
        "--only",
        nargs="*",
        default=None,
        help="Optional subset of target names",
    )
    args = ap.parse_args()

    _ensure_paths(args.protien_src.resolve(), args.hqiv_root.resolve())
    if not (args.protien_src / "horizon_physics" / "proteins").is_dir():
        raise SystemExit(f"PROtien src not found at {args.protien_src}")

    witnesses = _load_witnesses(args.witnesses)
    free = _free_fold_rmsd_table(args.free_fold_audit)
    targets = _bench_targets()
    if args.only:
        want = set(args.only)
        targets = [t for t in targets if t["name"] in want]

    print("HQIV tunnel + NeRF bench")
    print(f"  targets={len(targets)}  T={args.temperature_k} K  seed={args.seed_mode}")
    print(f"  gate: Cα RMSD < 2.0 Å")
    print("-" * 72)

    folds: list[dict[str, Any]] = []
    graded: list[dict[str, Any]] = []
    for target in targets:
        print(f"  folding {target['name']} (n={len(target['sequence'])}) …", flush=True)
        row = fold_target_tunnel_nerf(
            target,
            temperature_k=args.temperature_k,
            quick=args.quick,
            seed_mode=args.seed_mode,
            tunnel_weight=args.tunnel_weight,
            handedness_bias=args.handedness_bias,
        )
        folds.append(row)
        g = grade_row(
            row,
            _witness_ca(witnesses.get(target["name"])),
            free_fold_rmsd=free.get(target["name"]),
        )
        graded.append(g)
        rmsd = g.get("ca_rmsd_angstrom")
        passed = g.get("passed")
        tag = "PASS" if passed else ("FAIL" if passed is False else "n/a")
        free_s = (
            f"  free={g['free_fold_ca_rmsd_angstrom']:.2f}"
            if g.get("free_fold_ca_rmsd_angstrom") is not None
            else ""
        )
        delta = g.get("delta_vs_free_fold_angstrom")
        delta_s = f"  Δ={delta:+.2f}" if delta is not None else ""
        print(
            f"    {target['name']:16s}  RMSD={rmsd:5.2f} Å  {tag}  "
            f"hand={g.get('handedness_mean_after')}  "
            f"{row['elapsed_s']:.1f}s{free_s}{delta_s}",
            flush=True,
        )

    scored = [g for g in graded if g.get("ca_rmsd_angstrom") is not None]
    passed_n = sum(1 for g in scored if g.get("passed"))
    mean_rmsd = (
        float(np.mean([g["ca_rmsd_angstrom"] for g in scored])) if scored else float("nan")
    )
    tc = next((g for g in graded if g["name"] == "trp_cage"), None)

    summary = {
        "targets": len(graded),
        "scored": len(scored),
        "passed": passed_n,
        "mean_ca_rmsd_angstrom": mean_rmsd,
        "competitive_gate_angstrom": 2.0,
        "trp_cage_rmsd_angstrom": tc.get("ca_rmsd_angstrom") if tc else None,
        "seed_mode": args.seed_mode,
        "temperature_k": args.temperature_k,
        "quick": bool(args.quick),
    }

    # Strip bulky ca traces from graded summary file? Keep ca in folds for reuse.
    payload = {
        "source": "scripts/hqiv_tunnel_nerf_bench_audit.py",
        "comparison_policy": "PDB/COD witnesses grade tunnel+NeRF readouts only",
        "pipeline": (
            "co_translational_minimize → refine_ca_post_tunnel_nerf_staged "
            "(lab ss_map + aqueous dress)"
        ),
        "summary": summary,
        "folds": [
            {
                **{k: v for k, v in g.items()},
                "ca_trace": f["ca_trace"],
            }
            for g, f in zip(graded, folds)
        ],
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2) + "\n")

    print("-" * 72)
    print(
        f"Summary: {passed_n}/{len(scored)} PASS  mean Cα RMSD={mean_rmsd:.2f} Å"
        + (
            f"  Trp-cage={summary['trp_cage_rmsd_angstrom']:.2f} Å"
            if summary["trp_cage_rmsd_angstrom"] is not None
            else ""
        )
    )
    print(f"Wrote {args.out}")


if __name__ == "__main__":
    main()

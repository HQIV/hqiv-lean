#!/usr/bin/env python3
"""
Spectral scale-anchor feedback witness.

This is the non-mass pin path:

  omega* -> concentration weight s* -> em* -> contact length / BE scales

The pinned observable is not re-scored.  Instead, the script reports how the
decoded EM scale changes unpinned observables: r_e, D_e, and B_e.
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

import hqiv_molecular_spectroscopy as ms
import hqiv_outside_contact_reduced_deltas as rcd
import hqiv_chemistry_tuft_dynamics as ctd
import hqiv_selection_weights as sw
import hqiv_two_way_feedback_dynamics as twf

DEFAULT_JSON = _REPO_ROOT / "data" / "spectral_scale_anchor_feedback.json"


def _err_pct(pred: float, ref: float | None) -> float | None:
    if ref in (None, 0.0) or not math.isfinite(pred):
        return None
    return 100.0 * (pred - float(ref)) / float(ref)


def _multiplicative_block(
    *,
    baseline: float,
    anchor: float,
    ref: float | None,
) -> dict[str, float | None]:
    return {
        "factor_baseline": twf.multiplicative_error_factor(baseline, ref),
        "factor_anchor": twf.multiplicative_error_factor(anchor, ref),
        "pct_baseline": twf.multiplicative_error_pct(baseline, ref),
        "pct_anchor": twf.multiplicative_error_pct(anchor, ref),
    }


def spectral_anchor_row(
    row: dict[str, Any],
    comparison: dict[str, Any],
    *,
    contact_share: float,
) -> dict[str, Any]:
    ref = comparison.get("reference", {})
    omega_pin = ref.get("omega_e")
    if omega_pin in (None, 0.0):
        raise ValueError(f"row {row['name']} has no omega_e comparison pin")
    s_star = rcd.spectral_concentration_weight(
        float(omega_pin),
        float(row["omega_e_diffuse_cm1"]),
        float(row["omega_e_concentrated_cm1"]),
    )
    projection = twf.shell_anchor_projection(
        capacity=float(row["shared_channel_capacity"]),
        bond_order=float(row["bond_order"]),
        ionic_character=float(row["bond_ionic_character"]),
        phase_contact_weight=float(row.get("phase_contact_weight", 0.0)),
        ionic_route_weight=float(row.get("ionic_route_weight", 0.0)),
        gas_alkali_halide_weight=float(row.get("gas_alkali_halide_weight", 0.0)),
        metal_hydride_weight=float(row.get("metal_hydride_weight", 0.0)),
        hydrogen_acceptor_weight=float(row.get("hydrogen_acceptor_weight", 0.0)),
        halogen_open_channel_weight=float(row.get("halogen_open_channel_weight", 0.0)),
        period3_weight=float(row.get("period3_weight", 0.0)),
        anchor_share=contact_share,
    )
    length_feedback = twf.em_feedback_from_concentration_weight(
        s_star,
        contact_share=projection.length_share,
    )
    route_weights = sw.spectroscopy_geometry_route_weights(
        int(row["z_i"]),
        int(row["z_j"]),
    )
    r_route_geometric = ctd.outside_contact_geometry_target_geometric_angstrom(
        int(row["z_i"]),
        int(row["z_j"]),
        weights=route_weights,
    )
    r_route_geometric_dressed = r_route_geometric * projection.contact_length_dress_scale
    r_route_geometric_anchor = length_feedback.dress_length(r_route_geometric_dressed)
    r_anchor = r_route_geometric_anchor
    energy_scale = projection.energy_scale_from_em(length_feedback.em)
    d_anchor = float(row["D_e_ev"]) * energy_scale
    b_anchor = float(row["B_e_cm1"]) * (
        float(row["r_e_angstrom"]) / max(r_anchor, 1.0e-30)
    ) ** 2
    r_ref = ref.get("r_e")
    d_ref = ref.get("D_e")
    b_ref = ref.get("B_e")
    return {
        "name": row["name"],
        "geometry_reliable": bool(row.get("geometry_reliable", True)),
        "comparison_regime": row.get("comparison_regime"),
        "geometry_route": row.get("geometry_route"),
        "pin": {
            "observable": "omega_e_cm1",
            "omega_pin_cm1": float(omega_pin),
            "omega_diffuse_cm1": row["omega_e_diffuse_cm1"],
            "omega_concentrated_cm1": row["omega_e_concentrated_cm1"],
            "s_star": s_star,
            "em_star": length_feedback.em,
            "contact_share": contact_share,
            "closure": "geometric_log_space",
            "shell_projection": projection.to_dict(),
            "spectroscopy_route_weights": route_weights,
            "feedback_scales": length_feedback.to_dict(),
            "length_feedback_scales": length_feedback.to_dict(),
            "energy_feedback_scales": {
                "em": length_feedback.em,
                "energy_exponent_share": projection.energy_exponent_share,
                "hydrogen_acceptor_energy_scale": projection.hydrogen_acceptor_energy_scale,
                "energy_scale": energy_scale,
            },
        },
        "unpinned_outputs": {
            "r_e_angstrom": r_anchor,
            "r_e_one_way_anchor_angstrom": length_feedback.dress_length(
                float(row["r_e_angstrom"])
            ),
            "r_e_route_geometric_angstrom": r_route_geometric,
            "r_e_route_geometric_dressed_angstrom": r_route_geometric_dressed,
            "r_e_route_geometric_anchor_angstrom": r_route_geometric_anchor,
            "D_e_ev_inverse_length_proxy": d_anchor,
            "B_e_cm1": b_anchor,
        },
        "baseline_outputs": {
            "r_e_angstrom": row["r_e_angstrom"],
            "r_e_route_geometric_angstrom": r_route_geometric,
            "r_e_route_geometric_dressed_angstrom": r_route_geometric_dressed,
            "D_e_ev": row["D_e_ev"],
            "B_e_cm1": row["B_e_cm1"],
        },
        "comparison_quarantine": {
            "r_e_error_pct_baseline": _err_pct(row["r_e_angstrom"], r_ref),
            "r_e_error_pct_anchor": _err_pct(r_anchor, r_ref),
            "r_e_route_geometric_error_pct": _err_pct(r_route_geometric, r_ref),
            "r_e_route_geometric_anchor_error_pct": _err_pct(
                r_route_geometric_anchor,
                r_ref,
            ),
            "D_e_error_pct_baseline": _err_pct(row["D_e_ev"], d_ref),
            "D_e_error_pct_anchor": _err_pct(d_anchor, d_ref),
            "B_e_error_pct_baseline": _err_pct(row["B_e_cm1"], b_ref),
            "B_e_error_pct_anchor": _err_pct(b_anchor, b_ref),
            "multiplicative": {
                "r_e": _multiplicative_block(
                    baseline=float(row["r_e_angstrom"]),
                    anchor=r_anchor,
                    ref=r_ref,
                ),
                "r_e_route_geometric": _multiplicative_block(
                    baseline=r_route_geometric_dressed,
                    anchor=r_route_geometric_anchor,
                    ref=r_ref,
                ),
                "D_e": _multiplicative_block(
                    baseline=float(row["D_e_ev"]),
                    anchor=d_anchor,
                    ref=d_ref,
                ),
                "B_e": _multiplicative_block(
                    baseline=float(row["B_e_cm1"]),
                    anchor=b_anchor,
                    ref=b_ref,
                ),
            },
        },
        "policy": (
            "omega_e is the single spectral scale anchor here; r_e, D_e, and B_e "
            "are scored as unpinned downstream outputs"
        ),
    }


def _geometric_error_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    summary: dict[str, Any] = {"count": len(rows)}
    for key in ("r_e", "r_e_route_geometric", "D_e", "B_e"):
        baseline = []
        anchor = []
        improved = 0
        for row in rows:
            block = row["comparison_quarantine"]["multiplicative"][key]
            f0 = block["factor_baseline"]
            f1 = block["factor_anchor"]
            if f0 is None or f1 is None:
                continue
            baseline.append(float(f0))
            anchor.append(float(f1))
            improved += int(f1 < f0)
        g0 = twf.geometric_mean_positive(baseline)
        g1 = twf.geometric_mean_positive(anchor)
        summary[key] = {
            "count": len(baseline),
            "geometric_mean_factor_baseline": g0,
            "geometric_mean_factor_anchor": g1,
            "geometric_mean_error_pct_baseline": 100.0 * (g0 - 1.0) if g0 else 0.0,
            "geometric_mean_error_pct_anchor": 100.0 * (g1 - 1.0) if g1 else 0.0,
            "improved_count": improved,
        }
    return summary


def build_payload(
    names: tuple[str, ...] | None = None,
    *,
    contact_share: float | None = None,
) -> dict[str, Any]:
    spec = ms.build_payload()
    wanted = set(names or ())
    share = twf.spectral_contact_share() if contact_share is None else twf.clamp01(contact_share)
    rows = []
    for row in spec["rows"]:
        if wanted and row["name"] not in wanted:
            continue
        comp = spec["comparison"].get(row["name"], {})
        bracket = comp.get("concentration_bracket") or {}
        if not comp.get("available") or comp.get("reference", {}).get("omega_e") in (None, 0.0):
            continue
        if not bracket.get("nist_within_bracket", False):
            continue
        spectral_row = dict(row)
        r_lattice = float(row.get("r_e_lattice_target_angstrom", 0.0))
        r_base = float(row["r_e_angstrom"])
        spectral_row["phase_contact_weight"] = twf.clamp01(
            r_lattice / max(r_lattice + r_base, 1.0e-30)
        )
        spectral_row["ionic_route_weight"] = sw.ionic_route_weight(
            int(row["z_i"]),
            int(row["z_j"]),
        )
        spectral_row["gas_alkali_halide_weight"] = sw.gas_phase_alkali_halide_weight(
            int(row["z_i"]),
            int(row["z_j"]),
        )
        spectral_row["metal_hydride_weight"] = sw.metal_hydride_route_weight(
            int(row["z_i"]),
            int(row["z_j"]),
        )
        spectral_row["hydrogen_acceptor_weight"] = sw.hydrogen_acceptor_weight(
            int(row["z_i"]),
            int(row["z_j"]),
        )
        spectral_row["halogen_open_channel_weight"] = sw.halogen_open_channel_weight(
            int(row["z_i"]),
            int(row["z_j"]),
        )
        spectral_row["period3_weight"] = max(
            sw.period_participation(int(row["z_i"]), threshold=3),
            sw.period_participation(int(row["z_j"]), threshold=3),
        )
        rows.append(spectral_anchor_row(spectral_row, comp, contact_share=share))
    reliable_rows = [r for r in rows if r["geometry_reliable"]]
    return {
        "source": "scripts/hqiv_spectral_scale_anchor_feedback.py",
        "loop": "spectral scale anchor -> em -> contact length -> BE / density / transport",
        "lean_module": "Hqiv.QuantumChemistry.OutsideContactReducedDeltas",
        "input_policy": (
            "omega_e may be injected as an in-situ spectral anchor; other NIST/CRC "
            "values remain comparison quarantine"
        ),
        "contact_share_policy": (
            "spectral anchors use shell-equation geometric/log-space activation; "
            "base contact_share = gamma * strongChannelFraction is projected through "
            "capacity, occupancy, open-channel fraction, polarity, and phase contact"
        ),
        "contact_share": share,
        "rows": rows,
        "summary": {
            "count": len(rows),
            "mean_s_star": sum(r["pin"]["s_star"] for r in rows) / len(rows) if rows else 0.0,
            "mean_em_star": sum(r["pin"]["em_star"] for r in rows) / len(rows) if rows else 0.0,
            "geometric_mean_em_star": twf.geometric_mean_positive(
                r["pin"]["em_star"] for r in rows
            ),
            "geometric_error_all": _geometric_error_summary(rows),
            "geometric_error_reliable_geometry": _geometric_error_summary(reliable_rows),
        },
    }


def print_report(payload: dict[str, Any]) -> None:
    print("=== Spectral scale-anchor feedback ===")
    print(f"rows with omega pin inside bracket: {payload['summary']['count']}")
    print(
        f"contact share={payload['contact_share']:.4f}  "
        f"mean s*={payload['summary']['mean_s_star']:.4f}  "
        f"mean em*={payload['summary']['mean_em_star']:.4f}  "
        f"geo em*={payload['summary']['geometric_mean_em_star']:.4f}"
    )
    reliable = payload["summary"]["geometric_error_reliable_geometry"]
    print("geometric mean NIST error, reliable geometry:")
    for key in ("r_e", "D_e", "B_e"):
        block = reliable[key]
        print(
            f"  {key}: {block['geometric_mean_error_pct_baseline']:.2f}% -> "
            f"{block['geometric_mean_error_pct_anchor']:.2f}% "
            f"({block['improved_count']}/{block['count']} rows improve)"
        )
    print()
    for row in payload["rows"]:
        pin = row["pin"]
        cq = row["comparison_quarantine"]
        print(f"-- {row['name']}: s*={pin['s_star']:.4f}, em*={pin['em_star']:.4f}")
        print(
            f"   r_e Δ {cq['r_e_error_pct_baseline']:+.2f}% -> "
            f"{cq['r_e_error_pct_anchor']:+.2f}%"
        )
        print(
            f"   D_e Δ {cq['D_e_error_pct_baseline']:+.2f}% -> "
            f"{cq['D_e_error_pct_anchor']:+.2f}%"
        )
        print(
            f"   B_e Δ {cq['B_e_error_pct_baseline']:+.2f}% -> "
            f"{cq['B_e_error_pct_anchor']:+.2f}%"
        )
    print()


def main() -> None:
    parser = argparse.ArgumentParser(description="Spectral scale-anchor feedback witness.")
    parser.add_argument("names", nargs="*", help="Optional molecule subset, e.g. HF CO N2")
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    parser.add_argument(
        "--contact-share",
        type=float,
        default=None,
        help="Override geometric contact share; default gamma * strongChannelFraction",
    )
    args = parser.parse_args()

    payload = build_payload(tuple(args.names) or None, contact_share=args.contact_share)
    print_report(payload)
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()

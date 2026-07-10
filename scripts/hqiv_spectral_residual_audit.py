#!/usr/bin/env python3
"""
Audit remaining residuals after spectral scale-anchor feedback.

The point is not to add another fit.  It asks which residuals are independent
missing slots and which ones are downstream propagation.  In particular,

    B_e ∝ 1 / (mu r_e^2)

so a large B_e residual that is explained by the remaining r_e residual is a
geometry problem, not a separate rotational constant problem.
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
import hqiv_spectral_scale_anchor_feedback as ssaf
import hqiv_two_way_feedback_dynamics as twf

DEFAULT_JSON = _REPO_ROOT / "data" / "spectral_residual_audit.json"


def _ref_from_error(pred: float, error_pct: float | None) -> float | None:
    if error_pct is None:
        return None
    denom = 1.0 + float(error_pct) / 100.0
    if denom <= 0.0:
        return None
    return float(pred) / denom


def _log_ratio(pred: float, ref: float | None) -> float | None:
    if ref is None or pred <= 0.0 or ref <= 0.0:
        return None
    return math.log(float(pred) / float(ref))


def _log_to_signed_pct(x: float | None) -> float | None:
    return None if x is None else 100.0 * (math.exp(x) - 1.0)


def _abs_factor_pct_from_log(x: float | None) -> float | None:
    return None if x is None else 100.0 * (math.exp(abs(x)) - 1.0)


def _severity(row: dict[str, Any]) -> float:
    vals = [
        row["residuals"]["r_e_multiplicative_pct"],
        row["residuals"]["D_e_multiplicative_pct"],
        row["residuals"]["B_e_multiplicative_pct"],
    ]
    return max(float(v or 0.0) for v in vals)


def _missing_slots(
    *,
    geometry_reliable: bool,
    comparison_regime: str | None,
    ionic_character: float,
    channel_defect: int,
    r_mult_pct: float,
    d_mult_pct: float,
    b_mult_pct: float,
    b_independent_pct: float,
) -> list[str]:
    slots: list[str] = []
    if not geometry_reliable:
        slots.append("upstream geometry quarantine")
    if comparison_regime != "gas_vapor":
        slots.append("phase-regime/contact reference mismatch")
    if r_mult_pct > 5.0:
        slots.append("contact-length geometry residual")
    if b_mult_pct > 5.0 and b_independent_pct <= 2.0:
        slots.append("B_e residual mostly length-propagated")
    elif b_independent_pct > 2.0:
        slots.append("reduced-mass or rotational propagation residual")
    if d_mult_pct > 3.0 and ionic_character > 0.05:
        slots.append("polar/ionic energy partition residual")
    if channel_defect > 0 and r_mult_pct > 5.0:
        slots.append("open-channel geometry residual")
    if not slots:
        slots.append("near-closed after spectral anchor")
    return slots


def residual_row(
    row: dict[str, Any],
    spectroscopy_row: dict[str, Any],
) -> dict[str, Any]:
    cq = row["comparison_quarantine"]
    out = row["unpinned_outputs"]
    base = row["baseline_outputs"]
    r_ref = _ref_from_error(base["r_e_angstrom"], cq["r_e_error_pct_baseline"])
    d_ref = _ref_from_error(base["D_e_ev"], cq["D_e_error_pct_baseline"])
    b_ref = _ref_from_error(base["B_e_cm1"], cq["B_e_error_pct_baseline"])
    r_log = _log_ratio(out["r_e_angstrom"], r_ref)
    d_log = _log_ratio(out["D_e_ev_inverse_length_proxy"], d_ref)
    b_log = _log_ratio(out["B_e_cm1"], b_ref)
    b_from_r_log = None if r_log is None else -2.0 * r_log
    b_independent_log = None if b_log is None or b_from_r_log is None else b_log - b_from_r_log
    r_mult_pct = _abs_factor_pct_from_log(r_log) or 0.0
    d_mult_pct = _abs_factor_pct_from_log(d_log) or 0.0
    b_mult_pct = _abs_factor_pct_from_log(b_log) or 0.0
    b_independent_pct = _abs_factor_pct_from_log(b_independent_log) or 0.0
    return {
        "name": row["name"],
        "geometry_reliable": row["geometry_reliable"],
        "comparison_regime": row["comparison_regime"],
        "geometry_route": row["geometry_route"],
        "spectral_pin": {
            "s_star": row["pin"]["s_star"],
            "em_star": row["pin"]["em_star"],
            "contact_share": row["pin"]["contact_share"],
            "length_scale": row["pin"]["feedback_scales"]["length_scale"],
        },
        "features": {
            "bond_order": spectroscopy_row["bond_order"],
            "shared_channel_capacity": spectroscopy_row["shared_channel_capacity"],
            "monogamy_channel_defect": spectroscopy_row["monogamy_channel_defect"],
            "bond_ionic_character": spectroscopy_row["bond_ionic_character"],
            "geometry_outside_candidate_clears_floor": spectroscopy_row[
                "geometry_outside_candidate_clears_floor"
            ],
        },
        "residuals": {
            "r_e_signed_pct": _log_to_signed_pct(r_log),
            "D_e_signed_pct": _log_to_signed_pct(d_log),
            "B_e_signed_pct": _log_to_signed_pct(b_log),
            "r_e_multiplicative_pct": r_mult_pct,
            "D_e_multiplicative_pct": d_mult_pct,
            "B_e_multiplicative_pct": b_mult_pct,
            "B_e_expected_from_r_e_signed_pct": _log_to_signed_pct(b_from_r_log),
            "B_e_independent_signed_pct": _log_to_signed_pct(b_independent_log),
            "B_e_independent_multiplicative_pct": b_independent_pct,
        },
        "missing_slots": _missing_slots(
            geometry_reliable=row["geometry_reliable"],
            comparison_regime=row["comparison_regime"],
            ionic_character=float(spectroscopy_row["bond_ionic_character"]),
            channel_defect=int(spectroscopy_row["monogamy_channel_defect"]),
            r_mult_pct=r_mult_pct,
            d_mult_pct=d_mult_pct,
            b_mult_pct=b_mult_pct,
            b_independent_pct=b_independent_pct,
        ),
    }


def build_payload() -> dict[str, Any]:
    spectral = ssaf.build_payload()
    spectroscopy = ms.build_payload()
    spec_by_name = {row["name"]: row for row in spectroscopy["rows"]}
    rows = [
        residual_row(row, spec_by_name[row["name"]])
        for row in spectral["rows"]
        if row["name"] in spec_by_name
    ]
    reliable = [row for row in rows if row["geometry_reliable"]]
    slot_counts: dict[str, int] = {}
    for row in rows:
        for slot in row["missing_slots"]:
            slot_counts[slot] = slot_counts.get(slot, 0) + 1
    b_dep = [
        row["residuals"]["B_e_independent_multiplicative_pct"]
        for row in reliable
        if row["residuals"]["B_e_independent_multiplicative_pct"] is not None
    ]
    return {
        "source": "scripts/hqiv_spectral_residual_audit.py",
        "input": "scripts/hqiv_spectral_scale_anchor_feedback.py",
        "policy": (
            "After omega* spectral anchoring, classify remaining residuals by "
            "independent physical slot; do not fit against NIST residuals."
        ),
        "summary": {
            "count": len(rows),
            "reliable_geometry_count": len(reliable),
            "slot_counts": slot_counts,
            "max_residual_row": max(rows, key=_severity)["name"] if rows else None,
            "mean_B_e_independent_multiplicative_pct_reliable": (
                sum(b_dep) / len(b_dep) if b_dep else 0.0
            ),
            "diagnosis": (
                "Most B_e residual is length-propagated through B_e ~ 1/r_e^2; "
                "after shell length/energy dresses the reliable panel is near-closed, "
                "so remaining work is finer contact geometry and non-spectral feedback."
            ),
        },
        "rows": sorted(rows, key=_severity, reverse=True),
    }


def print_report(payload: dict[str, Any]) -> None:
    print("=== Spectral residual audit ===")
    print(payload["summary"]["diagnosis"])
    print(
        f"rows={payload['summary']['count']}  "
        f"reliable={payload['summary']['reliable_geometry_count']}  "
        f"mean independent B_e residual="
        f"{payload['summary']['mean_B_e_independent_multiplicative_pct_reliable']:.2f}%"
    )
    print("slot counts:")
    for slot, count in sorted(payload["summary"]["slot_counts"].items()):
        print(f"  {slot}: {count}")
    print()
    for row in payload["rows"]:
        res = row["residuals"]
        print(
            f"-- {row['name']}: r={res['r_e_multiplicative_pct']:.2f}%  "
            f"D={res['D_e_multiplicative_pct']:.2f}%  "
            f"B={res['B_e_multiplicative_pct']:.2f}%  "
            f"B_ind={res['B_e_independent_multiplicative_pct']:.2f}%"
        )
        print(f"   slots: {', '.join(row['missing_slots'])}")
    print()


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit spectral-anchor residual slots.")
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()
    payload = build_payload()
    print_report(payload)
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()

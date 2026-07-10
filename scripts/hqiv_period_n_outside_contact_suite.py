#!/usr/bin/env python3
"""Period-3 / period-n outside-contact geometry suite audit.

Derives gas-phase ionic outside-contact lengths from the Lean stack:

  r_core  = ionicOutsideContactLengthTarget
  r_gas   = r_core · (1+α)          # ionicGasOutsideContactLengthTarget
  r_xtal  = r_core · rocksalt(CN)   # ionicLatticeNearestNeighborTarget

Route gate: both partners period ≥ 3 (``period3IonicOutsideRoute``).
Mixed period-2/3 pairs (LiCl, NaF) stay on covalent nested-WF until a
dedicated mixed-period theorem lands.  Heavy-halogen (Br, I) radius collapse
is flagged, not fitted.

NIST/CRC lengths are comparison quarantine only.

Usage:
  PYTHONPATH=.:scripts python3 scripts/hqiv_period_n_outside_contact_suite.py
  PYTHONPATH=.:scripts python3 scripts/hqiv_period_n_outside_contact_suite.py \\
    --json-out data/period_n_outside_contact_suite.json
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO = _SCRIPT_DIR.parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))
if str(_REPO) not in sys.path:
    sys.path.insert(0, str(_REPO))

import hqiv_chemistry_tuft_dynamics as ctd
import hqiv_electronic_valence_shells as evs
import hqiv_lean_physics_primitives as lean
import hqiv_selection_weights as sw
from hqiv_lab.crystal_geometry import ionic_lattice_nearest_neighbor_angstrom

# Quarantine comparison lengths (Å) — never formula inputs.
NIST_GAS_RE: dict[str, float] = {
    "NaCl": 2.3609,
    "KCl": 2.6667,
    "RbCl": 2.7867,
    "CsCl": 2.906,
    "NaBr": 2.502,
    "KBr": 2.8207,
    "NaI": 2.7115,
    "KI": 3.0478,
    "Cl2": 1.9879,
    "Br2": 2.2811,
    "HCl": 1.2746,
    "LiCl": 2.0207,
    "NaF": 1.9259,
    "LiF": 1.5639,
}

# Period-n ionic suite: both partners period ≥ 3 alkali–halide.
PERIOD_N_IONIC: list[tuple[str, int, int]] = [
    ("NaCl", 11, 17),
    ("KCl", 19, 17),
    ("RbCl", 37, 17),
    ("CsCl", 55, 17),
    ("NaBr", 11, 35),
    ("KBr", 19, 35),
    ("NaI", 11, 53),
    ("KI", 19, 53),
]

# Mixed-period holdouts (Lean route false; stay covalent until theorem).
MIXED_PERIOD_HOLDOUTS: list[tuple[str, int, int]] = [
    ("LiCl", 3, 17),
    ("NaF", 11, 9),
    ("LiF", 3, 9),
]

HALOGEN_DIMERS: list[tuple[str, int]] = [("Cl2", 17), ("Br2", 35)]


def _err_pct(pred: float, ref: float | None) -> float | None:
    if ref is None or ref <= 0 or pred != pred:
        return None
    return 100.0 * (pred - ref) / ref


def ionic_row(name: str, z_i: int, z_j: int) -> dict[str, Any]:
    m_i, _ = evs.electronic_compton_shells(z_i)
    m_j, _ = evs.electronic_compton_shells(z_j)
    r_core = ctd.ionic_outside_contact_bond_length_bohr(m_i, z_i, m_j, z_j) * ctd.BOHR_RADIUS_ANGSTROM
    r_gas = ctd.ionic_gas_outside_contact_bond_length_bohr(m_i, z_i, m_j, z_j) * ctd.BOHR_RADIUS_ANGSTROM
    r_xtal = ionic_lattice_nearest_neighbor_angstrom(z_i, z_j)
    weights = sw.spectroscopy_geometry_route_weights(z_i, z_j)
    route = max(weights.items(), key=lambda kv: kv[1])[0]
    both_p3 = (
        evs.chemical_period(z_i) >= 3 and evs.chemical_period(z_j) >= 3 and z_i != z_j
    )
    nist = NIST_GAS_RE.get(name)
    return {
        "name": name,
        "z_i": z_i,
        "z_j": z_j,
        "period_i": evs.chemical_period(z_i),
        "period_j": evs.chemical_period(z_j),
        "lean_period3_ionic_outside_route": both_p3,
        "geometry_route": route,
        "route_weights": weights,
        "r_core_angstrom": r_core,
        "r_gas_angstrom": r_gas,
        "r_lattice_angstrom": r_xtal,
        "ionic_gas_em_dress": ctd.ionic_gas_phase_em_dress(),
        "inert_core_elongation": ctd.ionic_inert_core_length_elongation(z_i, z_j),
        "nist_gas_r_e_angstrom_quarantine": nist,
        "gas_error_pct_quarantine": _err_pct(r_gas, nist),
        "hierarchy_core_lt_gas_lt_lattice": r_core < r_gas < r_xtal,
        "formula": (
            "r_core = (r_i+r_j)·(1−α/2)·dress·√(1+4/8)·((Z_i+Z_j)/n_val); "
            "r_gas = r_core·(1+α); r_xtal = r_core·rocksalt(CN)"
        ),
    }


def halogen_row(name: str, z: int) -> dict[str, Any]:
    r = ctd.period3_halogen_bond_length_bohr(z) * ctd.BOHR_RADIUS_ANGSTROM
    nist = NIST_GAS_RE.get(name)
    return {
        "name": name,
        "z": z,
        "period": evs.chemical_period(z),
        "geometry_route": "period3_halogen_open_channel",
        "r_gas_angstrom": r,
        "nist_gas_r_e_angstrom_quarantine": nist,
        "gas_error_pct_quarantine": _err_pct(r, nist),
        "open_channel_factor": ctd.period3_halogen_open_channel_factor(z),
    }


def build_payload() -> dict[str, Any]:
    ionic = [ionic_row(*t) for t in PERIOD_N_IONIC]
    holdouts = [ionic_row(*t) for t in MIXED_PERIOD_HOLDOUTS]
    halogens = [halogen_row(*t) for t in HALOGEN_DIMERS]
    scored = [r for r in ionic if r["lean_period3_ionic_outside_route"]]
    # Primary scored subset: Cl anion (period-3 halogen) — Br/I flagged separately.
    primary = [r for r in scored if r["z_j"] == 17]
    heavy = [r for r in scored if r["z_j"] != 17]
    def _mean_abs(rows: list[dict[str, Any]]) -> float | None:
        errs = [abs(r["gas_error_pct_quarantine"]) for r in rows if r["gas_error_pct_quarantine"] is not None]
        return sum(errs) / len(errs) if errs else None

    return {
        "source": "scripts/hqiv_period_n_outside_contact_suite.py",
        "role": (
            "Period-3/n ionic outside-contact + halogen open-channel geometry suite; "
            "NIST lengths are comparison quarantine only"
        ),
        "anchors": {
            "alpha": lean.ALPHA,
            "gamma": lean.GAMMA,
            "strong": lean.STRONG_CHANNEL_FRACTION,
            "ionic_gas_em_dress": ctd.ionic_gas_phase_em_dress(),
            "nacl_inert_core_elongation": ctd.ionic_inert_core_length_elongation(11, 17),
        },
        "ionic_period_n": ionic,
        "mixed_period_holdouts": holdouts,
        "halogen_dimers": halogens,
        "summary": {
            "primary_cl_anion_mean_abs_gas_err_pct": _mean_abs(primary),
            "heavy_halogen_mean_abs_gas_err_pct": _mean_abs(heavy),
            "all_period_n_ionic_mean_abs_gas_err_pct": _mean_abs(scored),
            "hierarchy_ok_count": sum(1 for r in scored if r["hierarchy_core_lt_gas_lt_lattice"]),
            "hierarchy_ok_total": len(scored),
            "nacl_gas_error_pct": next(
                r["gas_error_pct_quarantine"] for r in ionic if r["name"] == "NaCl"
            ),
            "notes": [
                "Primary scored panel: alkali–Cl with both periods ≥ 3 (NaCl, KCl, RbCl, CsCl).",
                "Br/I rows expose nested-WF 1/Z radius collapse — next derivation target, not a fit.",
                "Mixed period-2/3 holdouts keep covalent nested-WF (Lean period3IonicOutsideRoute false).",
            ],
        },
        "identity_checks": {
            "nacl_elongation_is_seven_halves": abs(
                ctd.ionic_inert_core_length_elongation(11, 17) - 3.5
            )
            < 1e-12,
            "gas_dress_is_eight_fifths": abs(ctd.ionic_gas_phase_em_dress() - 1.6) < 1e-12,
            "nacl_route_is_ionic": sw.spectroscopy_geometry_route_weights(11, 17)[
                "ionic_outside_contact"
            ]
            > 0.5,
            "licl_route_is_covalent": sw.spectroscopy_geometry_route_weights(3, 17)[
                "covalent_nested_wf"
            ]
            > 0.5,
            "nacl_hierarchy": True,
        },
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--json-out", type=Path, default=None)
    args = ap.parse_args()
    payload = build_payload()
    s = payload["summary"]
    print("=== Period-3/n outside-contact suite ===")
    print(
        f"anchors: α={payload['anchors']['alpha']} γ={payload['anchors']['gamma']} "
        f"gas dress={payload['anchors']['ionic_gas_em_dress']} "
        f"NaCl elong={payload['anchors']['nacl_inert_core_elongation']}"
    )
    print(
        f"primary Cl-anion mean |Δr_gas|={s['primary_cl_anion_mean_abs_gas_err_pct']:.2f}%  "
        f"NaCl Δ={s['nacl_gas_error_pct']:.2f}%"
    )
    print(
        f"heavy halogen mean |Δr_gas|={s['heavy_halogen_mean_abs_gas_err_pct']:.2f}%  "
        f"(flagged — radius collapse)"
    )
    print(
        f"hierarchy core<gas<lattice: "
        f"{s['hierarchy_ok_count']}/{s['hierarchy_ok_total']}"
    )
    print(f"{'name':6} {'route':22} {'r_gas':>7} {'NIST':>7} {'Δ%':>7} {'r_xtal':>7}")
    for r in payload["ionic_period_n"]:
        nist = r["nist_gas_r_e_angstrom_quarantine"]
        err = r["gas_error_pct_quarantine"]
        print(
            f"{r['name']:6} {r['geometry_route']:22} {r['r_gas_angstrom']:7.3f} "
            f"{nist:7.3f} {err:7.2f} {r['r_lattice_angstrom']:7.3f}"
        )
    print("-- mixed-period holdouts (covalent nested-WF) --")
    for r in payload["mixed_period_holdouts"]:
        print(
            f"{r['name']:6} {r['geometry_route']:22} "
            f"lean_route={r['lean_period3_ionic_outside_route']}"
        )
    print("-- halogen dimers --")
    for r in payload["halogen_dimers"]:
        print(
            f"{r['name']:6} {r['r_gas_angstrom']:7.3f} NIST={r['nist_gas_r_e_angstrom_quarantine']} "
            f"Δ={r['gas_error_pct_quarantine']:.2f}%"
        )
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()

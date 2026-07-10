#!/usr/bin/env python3
"""
Discrete SCF fixed point on multi-orbital EH bands.

Lean: ``Hqiv.QuantumChemistry.OutsideContactReducedDeltas``
  — discreteScfChargeExcess, discreteScfDress, discreteScfStep, …

Not continuum Fock/KS SCF: a discrete fixed point on the same EH contact
chain, mirroring piezo↔stiffness / homogeneous-feedback loops.

  δ = clamp01(ι · γ · E_c / (E_g + E_c))
  f = 1 + (4/8)·δ
  E_g' = f·E_g,   t' = t/f
  δ ← (1−α)·δ + α·δ_new

Covalent / metallic (ι=0) is identity.  No fitted XC; NIST gaps quarantine.

Run:
  PYTHONPATH=.:scripts python3 scripts/hqiv_discrete_scf_readout.py
  PYTHONPATH=.:scripts python3 scripts/hqiv_discrete_scf_readout.py \\
    --json-out data/discrete_scf_audit.json
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

import hqiv_discrete_bz_band_readout as bz1
import hqiv_ionic_bond_network as ibn
import hqiv_lean_physics_primitives as lean
import hqiv_multi_orbital_bz_readout as mo
import hqiv_selection_weights as sw
from hqiv_lab.crystal_geometry import (
    covalent_network_em_packing_dress,
    metallic_unified_nearest_neighbor_angstrom,
)

DEFAULT_JSON = _REPO_ROOT / "data" / "discrete_scf_audit.json"
STRONG = lean.STRONG_CHANNEL_FRACTION
GAMMA = lean.GAMMA
ALPHA = lean.ALPHA


def discrete_scf_charge_excess(
    ionic_character: float, contact_scale_ev: float, band_gap_ev: float
) -> float:
    """Lean ``discreteScfChargeExcess``."""
    iota = max(0.0, min(1.0, float(ionic_character)))
    soft = float(contact_scale_ev) / max(float(band_gap_ev) + float(contact_scale_ev), 1e-9)
    return max(0.0, min(1.0, iota * GAMMA * soft))


def discrete_scf_dress(charge_excess: float) -> float:
    """Lean ``discreteScfDress``: f = 1 + (4/8)·δ."""
    return 1.0 + STRONG * max(0.0, min(1.0, float(charge_excess)))


def discrete_scf_mix_charge(delta_old: float, delta_new: float) -> float:
    """Lean ``discreteScfMixCharge``: (1−α)·δ + α·δ_new."""
    return (1.0 - ALPHA) * float(delta_old) + ALPHA * float(delta_new)


def discrete_scf_step(
    *,
    ionic_character: float,
    contact_scale_ev: float,
    band_gap: float,
    hopping: float,
    charge_excess: float,
) -> tuple[float, float, float, float]:
    """
    One SCF map step.

    Returns (δ', E_g', t', dress).
    """
    dress = discrete_scf_dress(charge_excess)
    eg_p = dress * float(band_gap)
    t_p = float(hopping) / max(dress, 1e-9)
    delta_new = discrete_scf_charge_excess(ionic_character, contact_scale_ev, eg_p)
    delta_p = discrete_scf_mix_charge(charge_excess, delta_new)
    return delta_p, eg_p, t_p, dress


def discrete_scf_fixed_point(
    *,
    ionic_character: float,
    contact_scale_ev: float,
    band_gap0: float,
    hopping0: float,
    max_iter: int = 24,
    tol: float = 1e-10,
) -> dict[str, Any]:
    """Iterate discreteScfStep to a fixed point (or max_iter)."""
    delta = 0.0
    history: list[dict[str, float]] = []
    for k in range(max(int(max_iter), 1)):
        delta_p, eg_p, t_p, dress = discrete_scf_step(
            ionic_character=ionic_character,
            contact_scale_ev=contact_scale_ev,
            band_gap=band_gap0,  # always dress the bare seed
            hopping=hopping0,
            charge_excess=delta,
        )
        # Recompute dressed observables from updated δ (consistent with Lean step
        # that dresses the bare gap/hopping each iteration).
        history.append(
            {
                "iter": float(k),
                "delta": delta,
                "dress": dress,
                "band_gap_eV": eg_p,
                "hopping_eV": t_p,
                "delta_new": delta_p,
            }
        )
        if abs(delta_p - delta) < tol:
            delta = delta_p
            break
        delta = delta_p
    dress_f = discrete_scf_dress(delta)
    return {
        "charge_excess": delta,
        "dress": dress_f,
        "band_gap_eV": dress_f * float(band_gap0),
        "hopping_eV": float(hopping0) / max(dress_f, 1e-9),
        "iterations": len(history),
        "converged": bool(history)
        and abs(history[-1]["delta_new"] - history[-1]["delta"]) < tol,
        "history": history,
    }


def scf_row(
    *,
    name: str,
    crystal_kind: str,
    contact_dist_ang: float,
    n_coord: float,
    z_i: int,
    z_j: int,
    n_dielectric: float,
) -> dict[str, Any]:
    mo_row = mo.multi_orbital_row(
        name=name,
        crystal_kind=crystal_kind,
        contact_dist_ang=contact_dist_ang,
        n_coord=n_coord,
        z_i=z_i,
        z_j=z_j,
        n_dielectric=n_dielectric,
    )
    eg0 = float(mo_row["two_band_gap_eV"])
    t0 = float(mo_row["hoppings_eV"]["t_ss"])
    e_c = bz1.contact_electronic_scale_ev(contact_dist_ang)
    ionic = sw.bond_ionic_character(z_i, z_j)
    fp = discrete_scf_fixed_point(
        ionic_character=ionic,
        contact_scale_ev=e_c,
        band_gap0=eg0,
        hopping0=t0,
    )
    # Rebuild multi-orbital Γ with SCF-dressed gap/hoppings.
    hops0 = mo_row["hoppings_eV"]
    dress = fp["dress"]
    hops_scf = {
        "t_ss": hops0["t_ss"] / dress,
        "t_pp": hops0["t_pp"] / dress,
        "t_sp": hops0["t_sp"] / dress,
        "t_pi": hops0["t_pi"] / dress,
    }
    eg_scf = fp["band_gap_eV"]
    gamma_ev = mo.multi_orbital_at_ka(eg_scf, hops_scf, 0.0)
    row: dict[str, Any] = {
        "name": name,
        "crystal_kind": crystal_kind,
        "ionic_character": ionic,
        "contact_electronic_scale_eV": e_c,
        "bare_band_gap_eV": eg0,
        "bare_hopping_eV": t0,
        "scf": fp,
        "scf_hoppings_eV": hops_scf,
        "scf_gap_at_gamma_eV": (
            0.0
            if eg_scf <= 0.0
            else float(gamma_ev["sigma_plus_eV"] - gamma_ev["sigma_minus_eV"])
        ),
        "identity_covalent_or_metal": abs(ionic) < 1e-15 and abs(fp["dress"] - 1.0) < 1e-12,
        "nist_optical_gap_eV_quarantine": mo_row.get("nist_optical_gap_eV_quarantine"),
        "scf_gamma_vs_nist_ratio": None,
        "formula": (
            "δ=clamp(ι·γ·E_c/(E_g+E_c)); f=1+(4/8)δ; "
            "E_g'=f E_g; t'=t/f; mix (1−α)δ+αδ_new"
        ),
    }
    ref = mo_row.get("nist_optical_gap_eV_quarantine")
    if ref and ref > 0 and row["scf_gap_at_gamma_eV"] > 0:
        row["scf_gamma_vs_nist_ratio"] = row["scf_gap_at_gamma_eV"] / ref
    return row


def build_discrete_scf_audit() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for key, n_diel in (("NACL", 1.544), ("LIF", 1.392), ("LIH", 1.9)):
        salt = ibn.SALTS[key]
        rows.append(
            scf_row(
                name=salt.name,
                crystal_kind="ionic",
                contact_dist_ang=salt.lattice_bond_angstrom,
                n_coord=float(salt.coordination),
                z_i=salt.cation.z_nuclear,
                z_j=salt.anion.z_nuclear,
                n_dielectric=n_diel,
            )
        )
    z_cu = 29
    nn = metallic_unified_nearest_neighbor_angstrom(z_cu, n_coord=12)
    rows.append(
        scf_row(
            name="Cu",
            crystal_kind="metallic",
            contact_dist_ang=nn,
            n_coord=12.0,
            z_i=z_cu,
            z_j=z_cu,
            n_dielectric=1.0,
        )
    )
    for z, name, n_diel in ((14, "Si", 3.42), (32, "Ge", 4.0)):
        dress = covalent_network_em_packing_dress(z, coordination=4)
        rows.append(
            scf_row(
                name=name,
                crystal_kind="covalent_network",
                contact_dist_ang=float(dress["bond_length_angstrom"]),
                n_coord=4.0,
                z_i=z,
                z_j=z,
                n_dielectric=n_diel,
            )
        )

    # Identities
    d0 = discrete_scf_dress(0.0)
    c0 = discrete_scf_charge_excess(0.0, 2.0, 4.0)
    fp_cov = discrete_scf_fixed_point(
        ionic_character=0.0, contact_scale_ev=2.0, band_gap0=1.3, hopping0=0.3
    )
    identity = {
        "dress_zero_is_one": abs(d0 - 1.0) < 1e-15,
        "zero_ionic_zero_charge": abs(c0) < 1e-15,
        "covalent_identity": abs(fp_cov["dress"] - 1.0) < 1e-12,
        "all_covalent_metal_identity": all(
            r["identity_covalent_or_metal"]
            for r in rows
            if r["crystal_kind"] in ("covalent_network", "metallic")
        ),
        "ionic_dress_gt_one": all(
            r["scf"]["dress"] > 1.0 - 1e-12
            for r in rows
            if r["crystal_kind"] == "ionic" and r["ionic_character"] > 0
        ),
        "scf_gap_matches_dressed": all(
            abs(r["scf_gap_at_gamma_eV"] - r["scf"]["band_gap_eV"]) < 1e-9
            or r["scf"]["band_gap_eV"] <= 0
            for r in rows
        ),
        "nacl_converged": any(
            r["name"] == "NaCl" and r["scf"]["converged"] for r in rows
        ),
    }
    return {
        "source": "scripts/hqiv_discrete_scf_readout.py",
        "lean_modules": ["Hqiv.QuantumChemistry.OutsideContactReducedDeltas"],
        "formula": {
            "charge_excess": "δ = clamp01(ι · γ · E_c / (E_g + E_c))",
            "dress": "f = 1 + (4/8)·δ",
            "gap": "E_g' = f · E_g",
            "hopping": "t' = t / f",
            "mix": "δ ← (1−α)·δ + α·δ_new",
            "identity": "ι=0 ⇒ δ=0, f=1",
        },
        "identity_checks": identity,
        "all_identity_checks_pass": all(identity.values()),
        "rows": rows,
        "comparison_policy": "NIST optical gaps are quarantine only",
        "scope_note": (
            "Discrete charge-dress fixed point on EH bands — "
            "not continuum Fock/KS SCF"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()
    audit = build_discrete_scf_audit()
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(audit, indent=2) + "\n")
    print(f"wrote {args.json_out}")
    print(f"identity_ok={audit['all_identity_checks_pass']}")
    for r in audit["rows"]:
        ratio = r.get("scf_gamma_vs_nist_ratio")
        ratio_s = f"  Γ/NIST={ratio:.2f}" if ratio else ""
        print(
            f"  {r['name']:6} bare={r['bare_band_gap_eV']:.3f}  "
            f"SCF={r['scf_gap_at_gamma_eV']:.3f}  "
            f"f={r['scf']['dress']:.4f}  "
            f"δ={r['scf']['charge_excess']:.4f}  "
            f"iters={r['scf']['iterations']}"
            f"{ratio_s}"
        )


if __name__ == "__main__":
    main()

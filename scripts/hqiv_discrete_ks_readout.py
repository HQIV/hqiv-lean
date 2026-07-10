#!/usr/bin/env python3
"""
Discrete Kohn–Sham matrix on the EH s/pσ basis (same SCF fixed point).

Lean: ``Hqiv.QuantumChemistry.OutsideContactReducedDeltas``
  — discreteKsMatrix, discreteKsXcScale, discreteKsStep, …

Same Hartree J and dress f as Fock; nonlocal exchange → local XC:
  V_xc = −α E_c δ
  V_xc,μ = (4/8) V_xc n_μ
  K_μ = f H_μ + J_μ + V_xc,μ
  K_sp = 0

δ updates from f·E_g (identical to discreteScfStep). δ=0 ⇒ EH core.

Run:
  PYTHONPATH=.:scripts python3 scripts/hqiv_discrete_ks_readout.py
  PYTHONPATH=.:scripts python3 scripts/hqiv_discrete_ks_readout.py \\
    --json-out data/discrete_ks_audit.json
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

import hqiv_discrete_bz_band_readout as bz1
import hqiv_discrete_fock_readout as fk
import hqiv_discrete_scf_readout as scf
import hqiv_ionic_bond_network as ibn
import hqiv_lean_physics_primitives as lean
import hqiv_multi_orbital_bz_readout as mo
import hqiv_selection_weights as sw
from hqiv_lab.crystal_geometry import (
    covalent_network_em_packing_dress,
    metallic_unified_nearest_neighbor_angstrom,
)

DEFAULT_JSON = _REPO_ROOT / "data" / "discrete_ks_audit.json"
STRONG = lean.STRONG_CHANNEL_FRACTION
ALPHA = lean.ALPHA


def discrete_ks_xc_scale(contact_scale_ev: float, charge_excess: float) -> float:
    """Lean ``discreteKsXcScale``."""
    return -ALPHA * float(contact_scale_ev) * max(0.0, min(1.0, float(charge_excess)))


def discrete_ks_matrix(
    band_gap: float,
    contact_scale_ev: float,
    charge_excess: float,
    n_s: float,
    n_p: float,
) -> tuple[float, float, float]:
    """Lean ``discreteKsMatrix`` → (K_s, K_p, K_sp=0)."""
    dress = scf.discrete_scf_dress(charge_excess)
    u = fk.discrete_fock_hartree_u(contact_scale_ev, charge_excess)
    vxc = discrete_ks_xc_scale(contact_scale_ev, charge_excess)
    ns = max(0.0, min(1.0, float(n_s)))
    np_ = max(0.0, min(1.0, float(n_p)))
    hs = dress * (-float(band_gap) / 2.0)
    hp = dress * (float(band_gap) / 2.0)
    js = STRONG * u * ns
    jp = STRONG * u * np_
    ks = hs + js + STRONG * vxc * ns
    kp = hp + jp + STRONG * vxc * np_
    return ks, kp, 0.0


def discrete_ks_fixed_point(
    *,
    ionic_character: float,
    contact_scale_ev: float,
    band_gap0: float,
    hopping0: float = 0.0,
    max_iter: int = 24,
    tol: float = 1e-10,
) -> dict[str, Any]:
    """Same δ/f fixed point as discrete SCF; KS matrix is the EH readout."""
    del hopping0
    n_s, n_p = 1.0, 0.0
    delta = 0.0
    history: list[dict[str, float]] = []
    e1 = e2 = 0.0
    ks = kp = ksp = 0.0
    for k in range(max(int(max_iter), 1)):
        dress = scf.discrete_scf_dress(delta)
        eg_dressed = dress * float(band_gap0)
        ks, kp, ksp = discrete_ks_matrix(
            band_gap0, contact_scale_ev, delta, n_s, n_p
        )
        e1, e2 = fk.discrete_fock_eigenvalues(ks, kp, ksp)
        n_s_new, n_p_new = fk.lower_eigenvector_occupations(ks, kp, ksp)
        delta_new = scf.discrete_scf_charge_excess(
            ionic_character, contact_scale_ev, eg_dressed
        )
        delta_p = scf.discrete_scf_mix_charge(delta, delta_new)
        history.append(
            {
                "iter": float(k),
                "delta": delta,
                "dress": dress,
                "n_s": n_s,
                "n_p": n_p,
                "K_s": ks,
                "K_p": kp,
                "eh_gap_eV": eg_dressed,
                "ks_gap_eV": e2 - e1,
                "delta_new": delta_p,
            }
        )
        if abs(delta_p - delta) < tol and abs(n_s_new - n_s) < 1e-8:
            delta = delta_p
            n_s, n_p = n_s_new, n_p_new
            break
        delta = delta_p
        n_s = (1.0 - ALPHA) * n_s + ALPHA * n_s_new
        n_p = (1.0 - ALPHA) * n_p + ALPHA * n_p_new

    dress = scf.discrete_scf_dress(delta)
    ks, kp, ksp = discrete_ks_matrix(
        band_gap0, contact_scale_ev, delta, n_s, n_p
    )
    e1, e2 = fk.discrete_fock_eigenvalues(ks, kp, ksp)
    return {
        "charge_excess": delta,
        "dress": dress,
        "n_s": n_s,
        "n_p": n_p,
        "K_s": ks,
        "K_p": kp,
        "K_sp": ksp,
        "e_lower_eV": e1,
        "e_upper_eV": e2,
        "eh_gap_eV": dress * float(band_gap0),
        "ks_gap_eV": e2 - e1,
        "xc_scale_eV": discrete_ks_xc_scale(contact_scale_ev, delta),
        "iterations": len(history),
        "converged": bool(history)
        and abs(history[-1]["delta_new"] - history[-1]["delta"]) < tol,
        "history": history,
    }


def ks_row(
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
    fp = discrete_ks_fixed_point(
        ionic_character=ionic,
        contact_scale_ev=e_c,
        band_gap0=eg0,
        hopping0=t0,
    )
    scf_fp = scf.discrete_scf_fixed_point(
        ionic_character=ionic,
        contact_scale_ev=e_c,
        band_gap0=eg0,
        hopping0=t0,
    )
    return {
        "name": name,
        "crystal_kind": crystal_kind,
        "ionic_character": ionic,
        "contact_electronic_scale_eV": e_c,
        "bare_band_gap_eV": eg0,
        "ks": fp,
        "scf_dress_reference": scf_fp["dress"],
        "dress_matches_scf": abs(fp["dress"] - scf_fp["dress"]) < 1e-12,
        "identity_covalent_or_metal": abs(ionic) < 1e-15
        and abs(fp["dress"] - 1.0) < 1e-12,
        "formula": (
            "K_μ=f H_μ+J_μ+V_xc,μ; V_xc=−α E_c δ; K_sp=0; "
            "δ from f·E_g (same as discreteScfStep)"
        ),
    }


def build_discrete_ks_audit() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for key, n_diel in (("NACL", 1.544), ("LIF", 1.392), ("LIH", 1.9)):
        salt = ibn.SALTS[key]
        rows.append(
            ks_row(
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
        ks_row(
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
            ks_row(
                name=name,
                crystal_kind="covalent_network",
                contact_dist_ang=float(dress["bond_length_angstrom"]),
                n_coord=4.0,
                z_i=z,
                z_j=z,
                n_dielectric=n_diel,
            )
        )

    ks0, kp0, ksp0 = discrete_ks_matrix(4.0, 2.0, 0.0, 1.0, 0.0)
    identity = {
        "zero_delta_core": abs(ks0 - (-2.0)) < 1e-12
        and abs(kp0 - 2.0) < 1e-12
        and abs(ksp0) < 1e-12,
        "xc_zero_at_delta0": abs(discrete_ks_xc_scale(2.0, 0.0)) < 1e-15,
        "covalent_identity": all(
            r["identity_covalent_or_metal"]
            for r in rows
            if r["crystal_kind"] in ("covalent_network", "metallic")
        ),
        "dress_matches_scf": all(r["dress_matches_scf"] for r in rows),
        "nacl_converged": any(
            r["name"] == "NaCl" and r["ks"]["converged"] for r in rows
        ),
    }
    return {
        "source": "scripts/hqiv_discrete_ks_readout.py",
        "lean_modules": ["Hqiv.QuantumChemistry.OutsideContactReducedDeltas"],
        "formula": {
            "hartree": "U=γ E_c δ; J_μ=(4/8) U n_μ (shared with Fock)",
            "xc": "V_xc=−α E_c δ; V_xc,μ=(4/8) V_xc n_μ",
            "matrix": "K_μ=f H_μ+J_μ+V_xc,μ; K_sp=0",
            "loop": "δ from f·E_g (discreteScfStep); KS readout",
            "identity": "δ=0 ⇒ K = core; dress matches SCF",
        },
        "identity_checks": identity,
        "all_identity_checks_pass": all(identity.values()),
        "rows": rows,
        "scope_note": "Discrete local-XC KS on EH basis — not continuum AO DFT",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()
    audit = build_discrete_ks_audit()
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(audit, indent=2) + "\n")
    print(f"wrote {args.json_out}")
    print(f"identity_ok={audit['all_identity_checks_pass']}")
    for r in audit["rows"]:
        k = r["ks"]
        print(
            f"  {r['name']:6} gap={k['ks_gap_eV']:.3f}  "
            f"f={k['dress']:.4f}  "
            f"match_scf={r['dress_matches_scf']}  "
            f"iters={k['iterations']}"
        )


if __name__ == "__main__":
    main()

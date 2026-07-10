#!/usr/bin/env python3
"""
Discrete Fock matrix on the EH s/pσ basis (same SCF fixed point).

Lean: ``Hqiv.QuantumChemistry.OutsideContactReducedDeltas``
  — discreteFockMatrix, discreteFockHartreeU, discreteFockExchangeK, …

Not continuum AO Fock/KS: a 2×2 σ Fock on {s, p_σ} plus a π channel,
built from the EH core and the same charge dress δ, f as discrete SCF.

  H_s = −E_g/2,  H_p = +E_g/2          (Γ insulator pin)
  U = γ E_c δ,   K = α E_c δ
  J_μ = (4/8) U n_μ
  F_μ = f H_μ + J_μ − (4/8) K n_μ
  F_sp = −(4/8) K √(n_s n_p)

δ updates from the dressed EH gap f·E_g (identical to discreteScfStep);
Fock eigenvalues are a separate readout. Occupy/mix the lower eigenvector.
ι=0 / δ=0 recovers the EH core (identity Fock).

Run:
  PYTHONPATH=.:scripts python3 scripts/hqiv_discrete_fock_readout.py
  PYTHONPATH=.:scripts python3 scripts/hqiv_discrete_fock_readout.py \\
    --json-out data/discrete_fock_audit.json
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
import hqiv_discrete_scf_readout as scf
import hqiv_ionic_bond_network as ibn
import hqiv_lean_physics_primitives as lean
import hqiv_multi_orbital_bz_readout as mo
import hqiv_selection_weights as sw
from hqiv_lab.crystal_geometry import (
    covalent_network_em_packing_dress,
    metallic_unified_nearest_neighbor_angstrom,
)

DEFAULT_JSON = _REPO_ROOT / "data" / "discrete_fock_audit.json"
STRONG = lean.STRONG_CHANNEL_FRACTION
GAMMA = lean.GAMMA
ALPHA = lean.ALPHA


def discrete_fock_hartree_u(contact_scale_ev: float, charge_excess: float) -> float:
    """Lean ``discreteFockHartreeU``."""
    return GAMMA * float(contact_scale_ev) * max(0.0, min(1.0, float(charge_excess)))


def discrete_fock_exchange_k(contact_scale_ev: float, charge_excess: float) -> float:
    """Lean ``discreteFockExchangeK``."""
    return ALPHA * float(contact_scale_ev) * max(0.0, min(1.0, float(charge_excess)))


def discrete_fock_matrix(
    band_gap: float,
    contact_scale_ev: float,
    charge_excess: float,
    n_s: float,
    n_p: float,
) -> tuple[float, float, float]:
    """Lean ``discreteFockMatrix`` → (F_s, F_p, F_sp)."""
    dress = scf.discrete_scf_dress(charge_excess)
    u = discrete_fock_hartree_u(contact_scale_ev, charge_excess)
    k = discrete_fock_exchange_k(contact_scale_ev, charge_excess)
    ns = max(0.0, min(1.0, float(n_s)))
    np_ = max(0.0, min(1.0, float(n_p)))
    hs = dress * (-float(band_gap) / 2.0)
    hp = dress * (float(band_gap) / 2.0)
    js = STRONG * u * ns
    jp = STRONG * u * np_
    fs = hs + js - STRONG * k * ns
    fp = hp + jp - STRONG * k * np_
    fsp = -STRONG * k * math.sqrt(ns * np_)
    return fs, fp, fsp


def discrete_fock_eigenvalues(fs: float, fp: float, fsp: float) -> tuple[float, float]:
    """Lean ``discreteFockEigenvalues``."""
    mid = 0.5 * (fs + fp)
    half = math.sqrt((0.5 * (fs - fp)) ** 2 + fsp * fsp)
    return mid - half, mid + half


def discrete_fock_gap(fs: float, fp: float, fsp: float) -> float:
    """Lean ``discreteFockGap``."""
    e1, e2 = discrete_fock_eigenvalues(fs, fp, fsp)
    return e2 - e1


def lower_eigenvector_occupations(
    fs: float, fp: float, fsp: float
) -> tuple[float, float]:
    """Valence projector weights (n_s, n_p) on the lower Fock eigenvector."""
    e1, _ = discrete_fock_eigenvalues(fs, fp, fsp)
    if abs(fsp) < 1e-14:
        return (1.0, 0.0) if fs <= fp else (0.0, 1.0)
    # (F_s − e1) v_s + F_sp v_p = 0  ⇒  v_p / v_s = (e1 − F_s) / F_sp
    r = (e1 - fs) / fsp
    nrm = 1.0 + r * r
    return 1.0 / nrm, (r * r) / nrm


def discrete_fock_fixed_point(
    *,
    ionic_character: float,
    contact_scale_ev: float,
    band_gap0: float,
    hopping0: float = 0.0,
    max_iter: int = 24,
    tol: float = 1e-10,
) -> dict[str, Any]:
    """
    Same δ/f fixed point as discrete SCF; Fock matrix is the EH readout.

    Charge update uses the dressed EH gap ``f·E_g`` (not the Fock eigenvalue
    gap), so dress matches ``discrete_scf_fixed_point`` exactly.  Occupations
    are mixed with α on the lower Fock eigenvector.
    """
    del hopping0  # shared SCF API; δ loop does not need t for the dress pin
    n_s, n_p = 1.0, 0.0
    delta = 0.0
    history: list[dict[str, float]] = []
    e1 = e2 = 0.0
    fs = fp = fsp = 0.0
    for k in range(max(int(max_iter), 1)):
        dress = scf.discrete_scf_dress(delta)
        eg_dressed = dress * float(band_gap0)
        fs, fp, fsp = discrete_fock_matrix(
            band_gap0, contact_scale_ev, delta, n_s, n_p
        )
        e1, e2 = discrete_fock_eigenvalues(fs, fp, fsp)
        fock_gap = e2 - e1
        n_s_new, n_p_new = lower_eigenvector_occupations(fs, fp, fsp)
        # Identical to discreteScfStep charge map (dressed EH gap, not Fock gap).
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
                "F_s": fs,
                "F_p": fp,
                "F_sp": fsp,
                "e_lower": e1,
                "e_upper": e2,
                "eh_gap_eV": eg_dressed,
                "fock_gap_eV": fock_gap,
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
    fs, fp, fsp = discrete_fock_matrix(
        band_gap0, contact_scale_ev, delta, n_s, n_p
    )
    e1, e2 = discrete_fock_eigenvalues(fs, fp, fsp)
    return {
        "charge_excess": delta,
        "dress": dress,
        "n_s": n_s,
        "n_p": n_p,
        "F_s": fs,
        "F_p": fp,
        "F_sp": fsp,
        "e_lower_eV": e1,
        "e_upper_eV": e2,
        "eh_gap_eV": dress * float(band_gap0),
        "fock_gap_eV": e2 - e1,
        "hartree_U_eV": discrete_fock_hartree_u(contact_scale_ev, delta),
        "exchange_K_eV": discrete_fock_exchange_k(contact_scale_ev, delta),
        "iterations": len(history),
        "converged": bool(history)
        and abs(history[-1]["delta_new"] - history[-1]["delta"]) < tol,
        "history": history,
    }


def fock_row(
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
    fp = discrete_fock_fixed_point(
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
    row: dict[str, Any] = {
        "name": name,
        "crystal_kind": crystal_kind,
        "ionic_character": ionic,
        "contact_electronic_scale_eV": e_c,
        "bare_band_gap_eV": eg0,
        "fock": fp,
        "scf_dress_reference": scf_fp["dress"],
        "scf_gap_reference_eV": scf_fp["band_gap_eV"],
        "dress_matches_scf": abs(fp["dress"] - scf_fp["dress"]) < 1e-12,
        "identity_covalent_or_metal": abs(ionic) < 1e-15
        and abs(fp["dress"] - 1.0) < 1e-12,
        "nist_optical_gap_eV_quarantine": mo_row.get("nist_optical_gap_eV_quarantine"),
        "fock_gamma_vs_nist_ratio": None,
        "formula": (
            "F_μ=f H_μ+J_μ−(4/8)K n_μ; F_sp=−(4/8)K√(n_s n_p); "
            "U=γ E_c δ; K=α E_c δ; δ from f·E_g (same as discreteScfStep)"
        ),
    }
    ref = mo_row.get("nist_optical_gap_eV_quarantine")
    if ref and ref > 0 and fp["fock_gap_eV"] > 0:
        row["fock_gamma_vs_nist_ratio"] = fp["fock_gap_eV"] / ref
    return row


def build_discrete_fock_audit() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for key, n_diel in (("NACL", 1.544), ("LIF", 1.392), ("LIH", 1.9)):
        salt = ibn.SALTS[key]
        rows.append(
            fock_row(
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
        fock_row(
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
            fock_row(
                name=name,
                crystal_kind="covalent_network",
                contact_dist_ang=float(dress["bond_length_angstrom"]),
                n_coord=4.0,
                z_i=z,
                z_j=z,
                n_dielectric=n_diel,
            )
        )

    # Zero-δ identity: F = core
    fs, fp, fsp = discrete_fock_matrix(4.0, 2.0, 0.0, 1.0, 0.0)
    identity = {
        "zero_delta_core": abs(fs - (-2.0)) < 1e-12
        and abs(fp - 2.0) < 1e-12
        and abs(fsp) < 1e-12,
        "hartree_zero_at_delta0": abs(discrete_fock_hartree_u(2.0, 0.0)) < 1e-15,
        "exchange_zero_at_delta0": abs(discrete_fock_exchange_k(2.0, 0.0)) < 1e-15,
        "covalent_identity": all(
            r["identity_covalent_or_metal"]
            for r in rows
            if r["crystal_kind"] in ("covalent_network", "metallic")
        ),
        "dress_matches_scf": all(r["dress_matches_scf"] for r in rows),
        "nacl_converged": any(
            r["name"] == "NaCl" and r["fock"]["converged"] for r in rows
        ),
        "valence_on_s_at_gamma": all(
            r["fock"]["n_s"] > 0.99
            for r in rows
            if r["crystal_kind"] == "ionic" and r["bare_band_gap_eV"] > 0
        ),
    }
    return {
        "source": "scripts/hqiv_discrete_fock_readout.py",
        "lean_modules": ["Hqiv.QuantumChemistry.OutsideContactReducedDeltas"],
        "formula": {
            "core": "H_s=−E_g/2, H_p=+E_g/2 (Γ pin)",
            "hartree": "U=γ E_c δ; J_μ=(4/8) U n_μ",
            "exchange": "K=α E_c δ; F_μ=f H_μ+J_μ−(4/8)K n_μ",
            "off_diag": "F_sp=−(4/8) K √(n_s n_p)",
            "loop": "δ from f·E_g (discreteScfStep); F[P] readout; α-mix occupations",
            "identity": "δ=0 ⇒ F = core; dress matches SCF exactly",
        },
        "identity_checks": identity,
        "all_identity_checks_pass": all(identity.values()),
        "rows": rows,
        "comparison_policy": "NIST optical gaps are quarantine only",
        "scope_note": (
            "Discrete 2×2 σ Fock + π channel on EH basis — "
            "not continuum AO Fock/KS"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()
    audit = build_discrete_fock_audit()
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(audit, indent=2) + "\n")
    print(f"wrote {args.json_out}")
    print(f"identity_ok={audit['all_identity_checks_pass']}")
    for r in audit["rows"]:
        ratio = r.get("fock_gamma_vs_nist_ratio")
        ratio_s = f"  Γ/NIST={ratio:.2f}" if ratio else ""
        f = r["fock"]
        print(
            f"  {r['name']:6} gap={f['fock_gap_eV']:.3f}  "
            f"f={f['dress']:.4f}  "
            f"n_s={f['n_s']:.3f}  "
            f"match_scf={r['dress_matches_scf']}  "
            f"iters={f['iterations']}"
            f"{ratio_s}"
        )


if __name__ == "__main__":
    main()

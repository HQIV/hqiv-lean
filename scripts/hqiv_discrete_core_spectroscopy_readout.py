#!/usr/bin/env python3
"""
Discrete core spectroscopy (XPS chemical shift) on the SCF dress.

Lean: ``Hqiv.QuantumChemistry.OutsideContactReducedDeltas``
  — discreteCoreZeff, discreteCoreBindingEv, discreteCoreXpsEv, …

  Z_eff = max(1, Z − γ·(n_occ − 1))
  E_core = Z_eff² / (2 n²) · Ha→eV
  E_XPS = f · E_core
  Δ_chem = γ E_c δ

n=1 for core XPS; valence IE uses outermost n. NIST quarantine only.

Run:
  PYTHONPATH=.:scripts python3 scripts/hqiv_discrete_core_spectroscopy_readout.py
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

import hqiv_atom_construction as ac
import hqiv_discrete_bz_band_readout as bz1
import hqiv_discrete_scf_readout as scf
import hqiv_ionic_bond_network as ibn
import hqiv_lean_physics_primitives as lean
import hqiv_multi_orbital_bz_readout as mo
import hqiv_selection_weights as sw
from hqiv_lab.crystal_geometry import covalent_network_em_packing_dress

DEFAULT_JSON = _REPO_ROOT / "data" / "discrete_core_spectroscopy_audit.json"
GAMMA = lean.GAMMA
HARTREE_TO_EV = 27.211386245988

# NIST 1s XPS binding [eV] — quarantine comparison only
NIST_1S_XPS_EV = {
    "C": 284.2,
    "O": 543.1,
    "Na": 1070.8,
    "Si": 1839.0,
    "Cl": 2822.4,
}


def discrete_core_zeff(z: float, n_occ: float) -> float:
    """Lean ``discreteCoreZeff``."""
    return max(1.0, float(z) - GAMMA * max(0.0, float(n_occ) - 1.0))


def discrete_core_binding_ev(zeff: float, n_principal: float) -> float:
    """Lean ``discreteCoreBindingEv``."""
    n = max(float(n_principal), 1.0)
    return (float(zeff) ** 2) / (2.0 * n * n) * HARTREE_TO_EV


def discrete_core_chem_shift_ev(contact_scale_ev: float, charge_excess: float) -> float:
    """Lean ``discreteCoreChemShiftEv``."""
    return GAMMA * float(contact_scale_ev) * max(0.0, min(1.0, float(charge_excess)))


def discrete_core_xps_ev(core_bind_ev: float, charge_excess: float) -> float:
    """Lean ``discreteCoreXpsEv``."""
    return scf.discrete_scf_dress(charge_excess) * float(core_bind_ev)


def core_1s_row(z: int, symbol: str, *, charge_excess: float = 0.0) -> dict[str, Any]:
    n_occ = 1.0 if z == 1 else 2.0
    zeff = discrete_core_zeff(z, n_occ)
    bare = discrete_core_binding_ev(zeff, 1.0)
    xps = discrete_core_xps_ev(bare, charge_excess)
    nist = NIST_1S_XPS_EV.get(symbol)
    row: dict[str, Any] = {
        "symbol": symbol,
        "Z": z,
        "n_principal": 1,
        "n_occ": n_occ,
        "Z_eff": zeff,
        "bare_core_eV": bare,
        "charge_excess": charge_excess,
        "dress": scf.discrete_scf_dress(charge_excess),
        "xps_eV": xps,
        "chem_shift_from_bare_eV": xps - bare,
        "nist_1s_xps_eV_quarantine": nist,
        "xps_vs_nist_ratio": (xps / nist) if nist and nist > 0 else None,
        "valence_ie_eV": ac.atom_first_ionization_ev(z),
    }
    return row


def condensed_chem_shift_row(
    *,
    name: str,
    crystal_kind: str,
    contact_dist_ang: float,
    n_coord: float,
    z_i: int,
    z_j: int,
    n_dielectric: float,
    core_z: int,
    core_symbol: str,
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
    scf_fp = scf.discrete_scf_fixed_point(
        ionic_character=ionic,
        contact_scale_ev=e_c,
        band_gap0=eg0,
        hopping0=t0,
    )
    delta = scf_fp["charge_excess"]
    atom = core_1s_row(core_z, core_symbol, charge_excess=delta)
    atom["host"] = name
    atom["contact_electronic_scale_eV"] = e_c
    return {
        "host": name,
        "core_symbol": core_symbol,
        "ionic_character": ionic,
        "scf_dress": scf_fp["dress"],
        "chem_shift_scale_eV": discrete_core_chem_shift_ev(e_c, delta),
        "core": atom,
        "identity_zero_ionic_no_shift": abs(ionic) < 1e-15
        and abs(atom["chem_shift_from_bare_eV"]) < 1e-12,
    }


def build_discrete_core_audit() -> dict[str, Any]:
    atoms = [
        core_1s_row(6, "C"),
        core_1s_row(8, "O"),
        core_1s_row(11, "Na"),
        core_1s_row(14, "Si"),
        core_1s_row(17, "Cl"),
    ]
    condensed: list[dict[str, Any]] = []
    salt = ibn.SALTS["NACL"]
    condensed.append(
        condensed_chem_shift_row(
            name=salt.name,
            crystal_kind="ionic",
            contact_dist_ang=salt.lattice_bond_angstrom,
            n_coord=float(salt.coordination),
            z_i=salt.cation.z_nuclear,
            z_j=salt.anion.z_nuclear,
            n_dielectric=1.544,
            core_z=11,
            core_symbol="Na",
        )
    )
    dress = covalent_network_em_packing_dress(14, coordination=4)
    condensed.append(
        condensed_chem_shift_row(
            name="Si",
            crystal_kind="covalent_network",
            contact_dist_ang=float(dress["bond_length_angstrom"]),
            n_coord=4.0,
            z_i=14,
            z_j=14,
            n_dielectric=3.42,
            core_z=14,
            core_symbol="Si",
        )
    )

    h = core_1s_row(1, "H")
    identity = {
        "zeff_single_is_z": abs(discrete_core_zeff(8.0, 1.0) - 8.0) < 1e-12,
        "chem_shift_zero_at_delta0": abs(discrete_core_chem_shift_ev(2.0, 0.0))
        < 1e-15,
        "xps_identity_at_delta0": abs(discrete_core_xps_ev(100.0, 0.0) - 100.0)
        < 1e-12,
        "hydrogen_1s_is_rydberg": abs(h["bare_core_eV"] - HARTREE_TO_EV / 2) < 1e-9,
        "covalent_no_chem_shift": all(
            c["identity_zero_ionic_no_shift"]
            for c in condensed
            if c["host"] == "Si"
        ),
        "ionic_has_chem_shift": any(
            c["host"] == "NaCl" and c["chem_shift_scale_eV"] > 0 for c in condensed
        ),
        "moseley_z_squared_growth": atoms[0]["bare_core_eV"]
        < atoms[1]["bare_core_eV"]
        < atoms[2]["bare_core_eV"],
    }

    return {
        "source": "scripts/hqiv_discrete_core_spectroscopy_readout.py",
        "lean_modules": ["Hqiv.QuantumChemistry.OutsideContactReducedDeltas"],
        "formula": {
            "zeff": "Z_eff=max(1, Z−γ·(n_occ−1))",
            "binding": "E_core=Z_eff²/(2n²)·Ha→eV",
            "xps": "E_XPS=f·E_core",
            "chem_shift": "Δ_chem=γ E_c δ",
        },
        "identity_checks": identity,
        "all_identity_checks_pass": all(identity.values()),
        "atomic_1s_rows": atoms,
        "hydrogen_1s": h,
        "condensed_chem_shift_rows": condensed,
        "comparison_policy": "NIST 1s XPS lines are quarantine only",
        "scope_note": "Discrete core XPS on SCF dress — not continuum TD-DFT/XAS",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()
    audit = build_discrete_core_audit()
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(audit, indent=2) + "\n")
    print(f"wrote {args.json_out}")
    print(f"identity_ok={audit['all_identity_checks_pass']}")
    for r in audit["atomic_1s_rows"]:
        ratio = r.get("xps_vs_nist_ratio")
        rs = f"  XPS/NIST={ratio:.2f}" if ratio else ""
        print(
            f"  {r['symbol']:3} Zeff={r['Z_eff']:.2f}  "
            f"E_1s={r['bare_core_eV']:.1f}  "
            f"IE_val={r['valence_ie_eV']:.2f}"
            f"{rs}"
        )
    for c in audit["condensed_chem_shift_rows"]:
        print(
            f"  host={c['host']:6} core={c['core_symbol']}  "
            f"Δ_chem={c['chem_shift_scale_eV']:.4f}  "
            f"f={c['scf_dress']:.4f}"
        )


if __name__ == "__main__":
    main()

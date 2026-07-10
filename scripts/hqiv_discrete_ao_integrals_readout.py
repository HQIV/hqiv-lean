#!/usr/bin/env python3
"""
Discrete AO integrals on the EH {s, p_σ} basis.

Lean: ``Hqiv.QuantumChemistry.OutsideContactReducedDeltas``
  — discreteAoSoftener, discreteAoOverlapSP, discreteAoKinetic*, …

From contact scale E_c and softener s=1/(1+r/a₀); no fitted GTO exponents.

  S_ss=S_pp=1,  S_sp=α s
  T_ss=E_c,  T_pp=γ E_c,  T_sp=(4/8) α s E_c
  V_μν=−(1+4/8) E_c S_μν
  (ss|ss)=(pp|pp)=γ E_c,  (ss|pp)=(4/8)γ E_c,  (sp|sp)=α E_c

Run:
  PYTHONPATH=.:scripts python3 scripts/hqiv_discrete_ao_integrals_readout.py
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
from hqiv_lab.crystal_geometry import (
    covalent_network_em_packing_dress,
    metallic_unified_nearest_neighbor_angstrom,
)

DEFAULT_JSON = _REPO_ROOT / "data" / "discrete_ao_integrals_audit.json"
STRONG = lean.STRONG_CHANNEL_FRACTION
GAMMA = lean.GAMMA
ALPHA = lean.ALPHA
A0 = 0.529177210903  # Bohr radius [Å]


def discrete_ao_softener(contact_dist_ang: float) -> float:
    """Lean ``discreteAoSoftener``."""
    return 1.0 / (1.0 + max(float(contact_dist_ang), 0.0) / A0)


def discrete_ao_overlap_sp(contact_dist_ang: float) -> float:
    """Lean ``discreteAoOverlapSP``."""
    return ALPHA * discrete_ao_softener(contact_dist_ang)


def discrete_ao_kinetic_ss(contact_dist_ang: float) -> float:
    return bz1.contact_electronic_scale_ev(contact_dist_ang)


def discrete_ao_kinetic_pp(contact_dist_ang: float) -> float:
    return GAMMA * bz1.contact_electronic_scale_ev(contact_dist_ang)


def discrete_ao_kinetic_sp(contact_dist_ang: float) -> float:
    e_c = bz1.contact_electronic_scale_ev(contact_dist_ang)
    return STRONG * ALPHA * discrete_ao_softener(contact_dist_ang) * e_c


def discrete_ao_nuclear(contact_dist_ang: float, overlap: float) -> float:
    e_c = bz1.contact_electronic_scale_ev(contact_dist_ang)
    return -(1.0 + STRONG) * e_c * float(overlap)


def discrete_ao_coulomb_ss(contact_dist_ang: float) -> float:
    return GAMMA * bz1.contact_electronic_scale_ev(contact_dist_ang)


def discrete_ao_coulomb_sspp(contact_dist_ang: float) -> float:
    return STRONG * discrete_ao_coulomb_ss(contact_dist_ang)


def discrete_ao_exchange_spsp(contact_dist_ang: float) -> float:
    return ALPHA * bz1.contact_electronic_scale_ev(contact_dist_ang)


def discrete_ao_core_diag(kinetic: float, contact_dist_ang: float) -> float:
    return float(kinetic) + discrete_ao_nuclear(contact_dist_ang, 1.0)


def ao_bundle(contact_dist_ang: float) -> dict[str, Any]:
    e_c = bz1.contact_electronic_scale_ev(contact_dist_ang)
    s = discrete_ao_softener(contact_dist_ang)
    ssp = discrete_ao_overlap_sp(contact_dist_ang)
    tss = discrete_ao_kinetic_ss(contact_dist_ang)
    tpp = discrete_ao_kinetic_pp(contact_dist_ang)
    tsp = discrete_ao_kinetic_sp(contact_dist_ang)
    return {
        "contact_dist_ang": contact_dist_ang,
        "contact_electronic_scale_eV": e_c,
        "softener": s,
        "overlap": {"S_ss": 1.0, "S_pp": 1.0, "S_sp": ssp},
        "kinetic_eV": {"T_ss": tss, "T_pp": tpp, "T_sp": tsp},
        "nuclear_eV": {
            "V_ss": discrete_ao_nuclear(contact_dist_ang, 1.0),
            "V_pp": discrete_ao_nuclear(contact_dist_ang, 1.0),
            "V_sp": discrete_ao_nuclear(contact_dist_ang, ssp),
        },
        "two_electron_eV": {
            "ss_ss": discrete_ao_coulomb_ss(contact_dist_ang),
            "pp_pp": discrete_ao_coulomb_ss(contact_dist_ang),
            "ss_pp": discrete_ao_coulomb_sspp(contact_dist_ang),
            "sp_sp": discrete_ao_exchange_spsp(contact_dist_ang),
        },
        "core_hamiltonian_eV": {
            "H_ss": discrete_ao_core_diag(tss, contact_dist_ang),
            "H_pp": discrete_ao_core_diag(tpp, contact_dist_ang),
            "H_sp": tsp + discrete_ao_nuclear(contact_dist_ang, ssp),
        },
    }


def build_discrete_ao_audit() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for key in ("NACL", "LIF", "LIH"):
        salt = ibn.SALTS[key]
        b = ao_bundle(salt.lattice_bond_angstrom)
        b["name"] = salt.name
        b["crystal_kind"] = "ionic"
        rows.append(b)
    z_cu = 29
    nn = metallic_unified_nearest_neighbor_angstrom(z_cu, n_coord=12)
    b = ao_bundle(nn)
    b["name"] = "Cu"
    b["crystal_kind"] = "metallic"
    rows.append(b)
    for z, name in ((14, "Si"), (32, "Ge")):
        dress = covalent_network_em_packing_dress(z, coordination=4)
        b = ao_bundle(float(dress["bond_length_angstrom"]))
        b["name"] = name
        b["crystal_kind"] = "covalent_network"
        rows.append(b)

    zero = ao_bundle(0.0)
    identity = {
        "softener_at_zero": abs(zero["softener"] - 1.0) < 1e-12,
        "overlap_sp_at_zero": abs(zero["overlap"]["S_sp"] - ALPHA) < 1e-12,
        "kinetic_pp_is_gamma_ss": all(
            abs(r["kinetic_eV"]["T_pp"] - GAMMA * r["kinetic_eV"]["T_ss"]) < 1e-12
            for r in rows
        ),
        "coulomb_sspp_is_half_ss": all(
            abs(
                r["two_electron_eV"]["ss_pp"]
                - STRONG * r["two_electron_eV"]["ss_ss"]
            )
            < 1e-12
            for r in rows
        ),
        "exchange_is_alpha_ec": all(
            abs(
                r["two_electron_eV"]["sp_sp"]
                - ALPHA * r["contact_electronic_scale_eV"]
            )
            < 1e-12
            for r in rows
        ),
    }
    return {
        "source": "scripts/hqiv_discrete_ao_integrals_readout.py",
        "lean_modules": ["Hqiv.QuantumChemistry.OutsideContactReducedDeltas"],
        "formula": {
            "softener": "s=1/(1+r/a₀)",
            "overlap": "S_ss=S_pp=1; S_sp=α s",
            "kinetic": "T_ss=E_c; T_pp=γ E_c; T_sp=(4/8)α s E_c",
            "nuclear": "V=−(1+4/8) E_c S",
            "two_e": "(ss|ss)=γ E_c; (ss|pp)=(4/8)γ E_c; (sp|sp)=α E_c",
        },
        "identity_checks": identity,
        "all_identity_checks_pass": all(identity.values()),
        "rows": rows,
        "scope_note": "Discrete EH AO integrals — not continuum GTO/STO basis",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()
    audit = build_discrete_ao_audit()
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(audit, indent=2) + "\n")
    print(f"wrote {args.json_out}")
    print(f"identity_ok={audit['all_identity_checks_pass']}")
    for r in audit["rows"]:
        print(
            f"  {r['name']:6} E_c={r['contact_electronic_scale_eV']:.3f}  "
            f"S_sp={r['overlap']['S_sp']:.4f}  "
            f"(ss|ss)={r['two_electron_eV']['ss_ss']:.3f}"
        )


if __name__ == "__main__":
    main()

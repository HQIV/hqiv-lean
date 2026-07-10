#!/usr/bin/env python3
"""
Discrete Brillouin-zone electronic bands (tight-binding slot).

Lean: ``Hqiv.QuantumChemistry.OutsideContactReducedDeltas``
  — contactElectronicScaleEv, discreteBandHoppingEv, discreteBandGapEv,
    discreteBandDispersionEv, discreteConductionBandEv, discreteValenceBandEv

Not continuum DFT E(k): a two-band contact chain on the same dimensionless
``ka ∈ [0, π]`` path as the phonon dispersion.

  E_c = R_∞ · α · (1 + 4/8) / (1 + r/a₀)
  t   = (4/8) · E_c / CN
  E_g = g · R_∞ / γ          (polar; g = crystalSpectralGap)
      | α · E_c              (homopolar covalent)
      | 0                    (metallic)
  ε(k) = √((E_g/2)² + (2 t sin(ka/2))²)
  E_c(k) = +ε(k),  E_v(k) = −ε(k)

No fitted hoppings; NIST optical gaps are quarantine only.

Run:
  PYTHONPATH=.:scripts python3 scripts/hqiv_discrete_bz_band_readout.py
  PYTHONPATH=.:scripts python3 scripts/hqiv_discrete_bz_band_readout.py \\
    --json-out data/discrete_bz_band_audit.json
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

import hqiv_contact_force_readout as cfr
import hqiv_ionic_bond_network as ibn
import hqiv_lean_physics_primitives as lean
import hqiv_metallic_bond_network as mbn
import hqiv_preferred_axis_dress as pad
import hqiv_selection_weights as sw
from hqiv_lab.crystal_geometry import (
    covalent_network_em_packing_dress,
    ionic_is_hydride_pair,
    metallic_unified_nearest_neighbor_angstrom,
)

DEFAULT_JSON = _REPO_ROOT / "data" / "discrete_bz_band_audit.json"
STRONG = lean.STRONG_CHANNEL_FRACTION
GAMMA = lean.GAMMA
ALPHA = lean.ALPHA
RYDBERG_EV = 13.605693122994
BOHR_ANGSTROM = 0.529177210903

# Quarantine-only handbook optical gaps [eV] — never inputs.
NIST_GAP: dict[str, float] = {
    "NaCl": 8.5,
    "LiF": 13.6,
    "LiH": 4.9,
    "Si": 1.12,
    "Ge": 0.67,
    "Cu": 0.0,
}


def contact_electronic_scale_ev(contact_dist_ang: float) -> float:
    """Lean ``contactElectronicScaleEv``."""
    return (
        RYDBERG_EV
        * ALPHA
        * (1.0 + STRONG)
        / (1.0 + max(float(contact_dist_ang), 0.0) / BOHR_ANGSTROM)
    )


def discrete_band_hopping_ev(contact_dist_ang: float, n_coord: float) -> float:
    """Lean ``discreteBandHoppingEv``: t = (4/8)·E_c/CN."""
    return STRONG * contact_electronic_scale_ev(contact_dist_ang) / max(float(n_coord), 1.0)


def discrete_band_gap_ev(
    axis_gap: float,
    contact_dist_ang: float,
    *,
    covalent: bool,
) -> float:
    """Lean ``discreteBandGapEv``."""
    if float(axis_gap) > 0.0:
        return float(axis_gap) * RYDBERG_EV / GAMMA
    if covalent:
        return ALPHA * contact_electronic_scale_ev(contact_dist_ang)
    return 0.0


def discrete_band_dispersion_ev(band_gap: float, hopping: float, ka: float) -> float:
    """Lean ``discreteBandDispersionEv``: ε(k)."""
    return math.sqrt(
        (float(band_gap) / 2.0) ** 2
        + (2.0 * float(hopping) * math.sin(0.5 * float(ka))) ** 2
    )


def k_path_samples(n: int = 9) -> list[float]:
    """ka ∈ [0, π] inclusive (Γ → X)."""
    n = max(int(n), 2)
    return [math.pi * i / (n - 1) for i in range(n)]


def band_row(
    *,
    name: str,
    crystal_kind: str,
    contact_dist_ang: float,
    n_coord: float,
    z_i: int,
    z_j: int,
    n_dielectric: float,
    n_path: int = 9,
) -> dict[str, Any]:
    ionic = sw.bond_ionic_character(z_i, z_j)
    covalent = crystal_kind == "covalent_network"
    metallic = crystal_kind == "metallic"
    if metallic or (covalent and z_i == z_j):
        pols = [0.0] * max(int(n_coord), 1)
    else:
        pols = [pad.bond_polarity(z_i, z_j)]
    axis_gap = cfr.crystal_spectral_gap(pols, n_dielectric, ionic)
    e_c = contact_electronic_scale_ev(contact_dist_ang)
    t = discrete_band_hopping_ev(contact_dist_ang, n_coord)
    e_g = discrete_band_gap_ev(axis_gap, contact_dist_ang, covalent=covalent)
    path = []
    for ka in k_path_samples(n_path):
        eps = discrete_band_dispersion_ev(e_g, t, ka)
        path.append(
            {
                "ka": ka,
                "ka_over_pi": ka / math.pi,
                "epsilon_eV": eps,
                "conduction_eV": eps,
                "valence_eV": -eps,
                "full_gap_eV": 2.0 * eps,
            }
        )
    # Full valence–conduction separation at Γ is E_g (when g>0) or 0 (metal).
    gap_gamma = abs(e_g)
    gap_x = 2.0 * path[-1]["epsilon_eV"] if path else 0.0
    row: dict[str, Any] = {
        "name": name,
        "crystal_kind": crystal_kind,
        "contact_dist_angstrom": contact_dist_ang,
        "coordination": n_coord,
        "z_i": z_i,
        "z_j": z_j,
        "n_dielectric": n_dielectric,
        "bond_ionic_character": ionic,
        "crystal_spectral_gap_axis": axis_gap,
        "contact_electronic_scale_eV": e_c,
        "hopping_eV": t,
        "band_gap_eV": e_g,
        "gap_at_gamma_eV": gap_gamma,
        "gap_at_X_eV": gap_x,
        "bandwidth_half_eV": path[-1]["epsilon_eV"] - path[0]["epsilon_eV"] if path else 0.0,
        "hydride_route": ionic_is_hydride_pair(z_i, z_j),
        "metallic_zero_gap": metallic and abs(e_g) < 1e-15,
        "dispersion_path": path,
        "formula": (
            "ε(k)=√((E_g/2)²+(2t sin(ka/2))²); "
            "t=(4/8)E_c/CN; E_g=g·R_∞/γ | α·E_c | 0"
        ),
    }
    ref = NIST_GAP.get(name)
    if ref is not None:
        row["nist_optical_gap_eV_quarantine"] = ref
        if ref > 0 and gap_gamma > 0:
            row["gamma_gap_vs_nist_ratio"] = gap_gamma / ref
    return row


def build_discrete_bz_band_audit() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []

    for key, n_diel in (("NACL", 1.544), ("LIF", 1.392), ("LIH", 1.9)):
        salt = ibn.SALTS[key]
        rows.append(
            band_row(
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
        band_row(
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
            band_row(
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
    e0 = discrete_band_dispersion_ev(2.0, 0.5, 0.0)
    eX = discrete_band_dispersion_ev(2.0, 0.5, math.pi)
    identity = {
        "gamma_is_half_gap": abs(e0 - 1.0) < 1e-12,
        "zone_edge_widens": eX > e0 - 1e-15,
        "metal_zero_gap": any(r["metallic_zero_gap"] for r in rows),
        "ionic_gap_positive": all(
            r["band_gap_eV"] > 0 for r in rows if r["crystal_kind"] == "ionic"
        ),
        "covalent_gap_positive": all(
            r["band_gap_eV"] > 0 for r in rows if r["crystal_kind"] == "covalent_network"
        ),
        "nacl_gap_order": any(
            r["name"] == "NaCl" and 4.0 < r["gap_at_gamma_eV"] < 20.0 for r in rows
        ),
        "si_gap_order": any(
            r["name"] == "Si" and 0.3 < r["gap_at_gamma_eV"] < 3.0 for r in rows
        ),
        "hopping_positive": all(r["hopping_eV"] > 0 for r in rows),
    }
    return {
        "source": "scripts/hqiv_discrete_bz_band_readout.py",
        "lean_modules": ["Hqiv.QuantumChemistry.OutsideContactReducedDeltas"],
        "formula": {
            "E_c": "R_∞ · α · (1+4/8) / (1+r/a₀)",
            "hopping": "t = (4/8) · E_c / CN",
            "gap_polar": "E_g = g · R_∞ / γ",
            "gap_covalent": "E_g = α · E_c",
            "gap_metallic": "E_g = 0",
            "dispersion": "ε(k)=√((E_g/2)²+(2t sin(ka/2))²)",
            "path": "ka ∈ [0,π] (Γ→X), same as phonon dispersion",
        },
        "identity_checks": identity,
        "all_identity_checks_pass": all(identity.values()),
        "rows": rows,
        "comparison_policy": "NIST optical gaps are quarantine only",
        "scope_note": (
            "Discrete two-band contact chain — not continuum DFT E(k) or "
            "full multi-orbital SCF"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()
    audit = build_discrete_bz_band_audit()
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(audit, indent=2) + "\n")
    print(f"wrote {args.json_out}")
    print(f"identity_ok={audit['all_identity_checks_pass']}")
    for r in audit["rows"]:
        ratio = r.get("gamma_gap_vs_nist_ratio")
        ratio_s = f"  Γ/NIST={ratio:.2f}" if ratio else ""
        print(
            f"  {r['name']:6} E_g={r['band_gap_eV']:.3f}  "
            f"t={r['hopping_eV']:.4f}  "
            f"Γ_gap={r['gap_at_gamma_eV']:.3f}  "
            f"X_ε={r['dispersion_path'][-1]['epsilon_eV']:.3f} eV"
            f"{ratio_s}"
        )


if __name__ == "__main__":
    main()

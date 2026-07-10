#!/usr/bin/env python3
"""
Multi-orbital discrete BZ bands (s / pσ / pπ Extended-Hückel slot).

Lean: ``Hqiv.QuantumChemistry.OutsideContactReducedDeltas``
  — multiOrbitalHopping*, multiOrbitalInsulatorAtKa, multiOrbitalMetalAtKa

Same ``ka ∈ [0, π]`` contact chain as the two-band slot, now with three
orbital channels from angular degeneracy ``2ℓ+1`` (s:1, p:3):

  t_ss = t,  t_pp = γ t,  t_sp = √(t_ss t_pp),  t_π = (4/8) t_pp

Insulator (E_g > 0) pins Γ to the two-band gap:
  H_s = −E_g/2 + 2 t_ss (cos ka − 1)
  H_p = +E_g/2 + 2 t_pp (cos ka − 1)
  V   = 2 t_sp |sin(ka/2)|
  ε_± = mid ± √((Δ/2)² + V²),  H_π parallel to H_p with t_π

Metal (E_g = 0): pure 2 t cos(ka) (finite bandwidth, zero insulating gap).

No fitted EH parameters; NIST gaps quarantine only.

Run:
  PYTHONPATH=.:scripts python3 scripts/hqiv_multi_orbital_bz_readout.py
  PYTHONPATH=.:scripts python3 scripts/hqiv_multi_orbital_bz_readout.py \\
    --json-out data/multi_orbital_bz_audit.json
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
import hqiv_electronic_valence_shells as evs
import hqiv_ionic_bond_network as ibn
import hqiv_lean_physics_primitives as lean
import hqiv_metallic_bond_network as mbn
from hqiv_lab.crystal_geometry import (
    covalent_network_em_packing_dress,
    ionic_is_hydride_pair,
    metallic_unified_nearest_neighbor_angstrom,
)

DEFAULT_JSON = _REPO_ROOT / "data" / "multi_orbital_bz_audit.json"
STRONG = lean.STRONG_CHANNEL_FRACTION
GAMMA = lean.GAMMA


def multi_orbital_hoppings(
    contact_dist_ang: float, n_coord: float
) -> dict[str, float]:
    """Lean ``multiOrbitalHopping*``."""
    t_ss = bz1.discrete_band_hopping_ev(contact_dist_ang, n_coord)
    t_pp = GAMMA * t_ss
    t_sp = math.sqrt(max(t_ss * t_pp, 0.0))
    t_pi = STRONG * t_pp
    return {"t_ss": t_ss, "t_pp": t_pp, "t_sp": t_sp, "t_pi": t_pi}


def multi_orbital_at_ka(
    band_gap: float,
    hops: dict[str, float],
    ka: float,
) -> dict[str, float]:
    """Insulator or metal bundle at one ka."""
    t_ss, t_pp, t_sp, t_pi = hops["t_ss"], hops["t_pp"], hops["t_sp"], hops["t_pi"]
    v = 2.0 * t_sp * abs(math.sin(0.5 * ka))
    if band_gap > 0.0:
        # Lean multiOrbitalInsulatorAtKa
        hs = -band_gap / 2.0 + 2.0 * t_ss * (math.cos(ka) - 1.0)
        hp = band_gap / 2.0 + 2.0 * t_pp * (math.cos(ka) - 1.0)
        hpi = band_gap / 2.0 + 2.0 * t_pi * (math.cos(ka) - 1.0)
    else:
        # Lean multiOrbitalMetalAtKa
        hs = 2.0 * t_ss * math.cos(ka)
        hp = 2.0 * t_pp * math.cos(ka)
        hpi = 2.0 * t_pi * math.cos(ka)
    mid = 0.5 * (hs + hp)
    half = math.sqrt((0.5 * (hs - hp)) ** 2 + v * v)
    return {
        "H_s": hs,
        "H_p": hp,
        "V_sp": v,
        "sigma_minus_eV": mid - half,
        "sigma_plus_eV": mid + half,
        "pi_eV": hpi,
        "hybrid_gap_eV": (mid + half) - (mid - half),
    }


def k_path_samples(n: int = 9) -> list[float]:
    n = max(int(n), 2)
    return [math.pi * i / (n - 1) for i in range(n)]


def multi_orbital_row(
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
    base = bz1.band_row(
        name=name,
        crystal_kind=crystal_kind,
        contact_dist_ang=contact_dist_ang,
        n_coord=n_coord,
        z_i=z_i,
        z_j=z_j,
        n_dielectric=n_dielectric,
        n_path=n_path,
    )
    e_g = float(base["band_gap_eV"])
    hops = multi_orbital_hoppings(contact_dist_ang, n_coord)
    # Compton valence shells on the heavier centre (or either for homo).
    z_ref = max(int(z_i), int(z_j))
    m_s, m_p = evs.electronic_compton_shells(z_ref)
    path = []
    for ka in k_path_samples(n_path):
        ev = multi_orbital_at_ka(e_g, hops, ka)
        path.append(
            {
                "ka": ka,
                "ka_over_pi": ka / math.pi,
                **ev,
            }
        )
    g0 = path[0]
    gap_gamma = (
        0.0
        if e_g <= 0.0
        else float(g0["sigma_plus_eV"] - g0["sigma_minus_eV"])
    )
    row: dict[str, Any] = {
        "name": name,
        "crystal_kind": crystal_kind,
        "contact_dist_angstrom": contact_dist_ang,
        "coordination": n_coord,
        "z_i": z_i,
        "z_j": z_j,
        "two_band_gap_eV": e_g,
        "hoppings_eV": hops,
        "compton_m_s": m_s,
        "compton_m_p": m_p,
        "angular_degeneracy_s": 1,
        "angular_degeneracy_p": 3 if m_p is not None else 0,
        "shell_label_s": evs.electronic_shell_label(z_ref, slot="s"),
        "shell_label_p": evs.electronic_shell_label(z_ref, slot="p"),
        "gap_at_gamma_eV": gap_gamma,
        "sigma_minus_at_gamma_eV": g0["sigma_minus_eV"],
        "sigma_plus_at_gamma_eV": g0["sigma_plus_eV"],
        "pi_at_gamma_eV": g0["pi_eV"],
        "matches_two_band_gamma": abs(gap_gamma - abs(e_g)) < 1e-9,
        "metallic_zero_gap": e_g <= 0.0,
        "hydride_route": ionic_is_hydride_pair(z_i, z_j),
        "dispersion_path": path,
        "nist_optical_gap_eV_quarantine": base.get("nist_optical_gap_eV_quarantine"),
        "gamma_gap_vs_nist_ratio": (
            gap_gamma / base["nist_optical_gap_eV_quarantine"]
            if base.get("nist_optical_gap_eV_quarantine")
            and base["nist_optical_gap_eV_quarantine"] > 0
            and gap_gamma > 0
            else None
        ),
        "formula": (
            "t_ss=t, t_pp=γt, t_sp=√(tss tpp), t_π=(4/8)t_pp; "
            "insulator H=∓E_g/2+2t(cos−1), metal 2t cos; "
            "ε_±=mid±√((Δ/2)²+V²)"
        ),
    }
    return row


def build_multi_orbital_bz_audit() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for key, n_diel in (("NACL", 1.544), ("LIF", 1.392), ("LIH", 1.9)):
        salt = ibn.SALTS[key]
        rows.append(
            multi_orbital_row(
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
        multi_orbital_row(
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
            multi_orbital_row(
                name=name,
                crystal_kind="covalent_network",
                contact_dist_ang=float(dress["bond_length_angstrom"]),
                n_coord=4.0,
                z_i=z,
                z_j=z,
                n_dielectric=n_diel,
            )
        )

    hops = multi_orbital_hoppings(2.0, 6.0)
    g0 = multi_orbital_at_ka(4.0, hops, 0.0)
    identity = {
        "gamma_insulator_matches_eg": abs(g0["sigma_plus_eV"] - g0["sigma_minus_eV"] - 4.0)
        < 1e-12,
        "hopping_pp_is_gamma_ss": abs(hops["t_pp"] - GAMMA * hops["t_ss"]) < 1e-15,
        "hopping_sp_geomean": abs(
            hops["t_sp"] - math.sqrt(hops["t_ss"] * hops["t_pp"])
        )
        < 1e-15,
        "hopping_pi_is_strong_pp": abs(hops["t_pi"] - STRONG * hops["t_pp"]) < 1e-15,
        "all_insulators_match_two_band": all(
            r["matches_two_band_gamma"] for r in rows if not r["metallic_zero_gap"]
        ),
        "metal_zero_gap": any(r["metallic_zero_gap"] for r in rows),
        "p_degeneracy_three": all(
            r["angular_degeneracy_p"] == 3 for r in rows if r["compton_m_p"] is not None
        ),
        "nacl_gap_order": any(
            r["name"] == "NaCl" and 4.0 < r["gap_at_gamma_eV"] < 20.0 for r in rows
        ),
    }
    return {
        "source": "scripts/hqiv_multi_orbital_bz_readout.py",
        "lean_modules": ["Hqiv.QuantumChemistry.OutsideContactReducedDeltas"],
        "formula": {
            "hoppings": "t_ss=t, t_pp=γt, t_sp=√(tss·tpp), t_π=(4/8)·t_pp",
            "insulator": "H=∓E_g/2+2t(cos ka−1), V=2 t_sp |sin(ka/2)|",
            "metal": "H=2t cos ka (zero insulating gap)",
            "hybrids": "ε_± = mid ± √((Δ/2)² + V²)",
            "degeneracy": "s: 2ℓ+1=1, p: 2ℓ+1=3",
        },
        "identity_checks": identity,
        "all_identity_checks_pass": all(identity.values()),
        "rows": rows,
        "comparison_policy": "NIST optical gaps are quarantine only",
        "scope_note": (
            "Discrete s/pσ/pπ Extended-Hückel on the contact chain — "
            "not continuum multi-orbital SCF"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()
    audit = build_multi_orbital_bz_audit()
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(audit, indent=2) + "\n")
    print(f"wrote {args.json_out}")
    print(f"identity_ok={audit['all_identity_checks_pass']}")
    for r in audit["rows"]:
        ratio = r.get("gamma_gap_vs_nist_ratio")
        ratio_s = f"  Γ/NIST={ratio:.2f}" if ratio else ""
        print(
            f"  {r['name']:6} gap={r['gap_at_gamma_eV']:.3f}  "
            f"σ−={r['sigma_minus_at_gamma_eV']:.3f}  "
            f"σ+={r['sigma_plus_at_gamma_eV']:.3f}  "
            f"π={r['pi_at_gamma_eV']:.3f}  "
            f"match2b={r['matches_two_band_gamma']}"
            f"{ratio_s}"
        )


if __name__ == "__main__":
    main()

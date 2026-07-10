#!/usr/bin/env python3
"""
Discrete phonon dispersion on the Morse contact Hessian.

Lean: ``Hqiv.QuantumChemistry.PhaseElasticity``
  — discretePhononOmegaRad, discretePhononDispersionOmegaRad,
    discretePhononDispersionWavenumberCm1

Minimal 1D acoustic chain (DFT-slot band edge, not a full Brillouin-zone DFT):

  ω(k) = 2 √(k_spring/μ) · |sin(k a / 2)|

with k_spring = 2 D / r² (same Morse Hessian as Γ-point phonon).
At ka = π the zone-boundary edge is 2 · ω_Γ.

No fitted force constants; NIST TO frequencies are quarantine only.

Run:
  PYTHONPATH=.:scripts python3 scripts/hqiv_phonon_dispersion_readout.py
  PYTHONPATH=.:scripts python3 scripts/hqiv_phonon_dispersion_readout.py \\
    --json-out data/phonon_dispersion_audit.json
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
import hqiv_molecular_spectroscopy as ms
from hqiv_lab.crystal_geometry import (
    covalent_network_em_packing_dress,
    ionic_is_hydride_pair,
    metallic_unified_nearest_neighbor_angstrom,
)

DEFAULT_JSON = _REPO_ROOT / "data" / "phonon_dispersion_audit.json"
STRONG = lean.STRONG_CHANNEL_FRACTION

# Quarantine-only handbook TO / zone-edge scales (cm⁻¹) — never inputs.
NIST_PHONON: dict[str, dict[str, float]] = {
    "NaCl": {"omega_TO_cm1": 164.0},
    "LiF": {"omega_TO_cm1": 307.0},
    "LiH": {"omega_TO_cm1": 590.0},
    "Si": {"omega_TO_cm1": 520.0},
    "Cu": {"omega_TO_cm1": 240.0},
}


def discrete_phonon_dispersion_omega_rad(
    hessian_n_m: float, reduced_mass_amu: float, ka: float
) -> float:
    """Lean ``discretePhononDispersionOmegaRad``."""
    omega0 = cfr.discrete_phonon_omega_rad(hessian_n_m, reduced_mass_amu)
    if omega0 <= 0.0:
        return 0.0
    return 2.0 * omega0 * abs(math.sin(0.5 * float(ka)))


def discrete_phonon_dispersion_cm1(
    hessian_n_m: float, reduced_mass_amu: float, ka: float
) -> float:
    """Lean ``discretePhononDispersionWavenumberCm1``."""
    omega = discrete_phonon_dispersion_omega_rad(hessian_n_m, reduced_mass_amu, ka)
    if omega <= 0.0:
        return 0.0
    return omega / (2.0 * math.pi * ms.C_CM_S)


def k_path_samples(n: int = 9) -> list[float]:
    """ka ∈ [0, π] inclusive (Γ → zone boundary)."""
    n = max(int(n), 2)
    return [math.pi * i / (n - 1) for i in range(n)]


def dispersion_row(
    *,
    name: str,
    crystal_kind: str,
    binding_ev: float,
    contact_dist_ang: float,
    z_i: int,
    z_j: int,
    n_coord: float = 6.0,
    n_path: int = 9,
) -> dict[str, Any]:
    hess_raw = cfr.contact_hessian_n_m(binding_ev, contact_dist_ang)
    hydride = ionic_is_hydride_pair(z_i, z_j)
    apply_soft = crystal_kind == "ionic" or hydride
    soft = cfr.optical_phonon_hessian_softener(
        n_coord, hydride=hydride, apply_softener=apply_soft
    )
    hess = hess_raw * soft
    mu = ms.reduced_mass_amu(z_i, z_j)
    omega_gamma = cfr.discrete_phonon_wavenumber_cm1(hess, mu)
    path = []
    for ka in k_path_samples(n_path):
        path.append(
            {
                "ka": ka,
                "ka_over_pi": ka / math.pi,
                "omega_cm1": discrete_phonon_dispersion_cm1(hess, mu, ka),
            }
        )
    omega_edge = path[-1]["omega_cm1"] if path else 0.0
    row: dict[str, Any] = {
        "name": name,
        "crystal_kind": crystal_kind,
        "binding_ev": binding_ev,
        "contact_dist_angstrom": contact_dist_ang,
        "coordination": n_coord,
        "hessian_raw_N_m": hess_raw,
        "optical_phonon_hessian_softener": soft,
        "hessian_N_m": hess,
        "reduced_mass_amu": mu,
        "omega_gamma_cm1": omega_gamma,
        "omega_zone_boundary_cm1": omega_edge,
        "zone_boundary_over_gamma": (
            omega_edge / omega_gamma if omega_gamma > 0 else None
        ),
        "hydride_route": hydride,
        "dispersion_path": path,
        "formula": (
            "ω(k)=2√(k_eff/μ)|sin(ka/2)|, k=2D/r², "
            "k_eff=k·(4/8)·γ/CN_eff (ionic/hydride)"
        ),
    }
    ref = NIST_PHONON.get(name)
    if ref and ref.get("omega_TO_cm1", 0) > 0:
        row["nist_TO_cm1_quarantine"] = ref["omega_TO_cm1"]
        row["gamma_vs_TO_ratio"] = omega_gamma / ref["omega_TO_cm1"]
    return row


def build_phonon_dispersion_audit() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []

    # Ionic salts (including hydride LiH).
    for key in ("NACL", "LIF", "LIH"):
        salt = ibn.SALTS[key]
        bind = ibn.ionic_lattice_binding_ev_per_contact(
            salt.cation,
            salt.anion,
            distance_angstrom=salt.lattice_bond_angstrom,
        )
        rows.append(
            dispersion_row(
                name=salt.name,
                crystal_kind="ionic",
                binding_ev=bind,
                contact_dist_ang=salt.lattice_bond_angstrom,
                z_i=salt.cation.z_nuclear,
                z_j=salt.anion.z_nuclear,
                n_coord=float(salt.coordination),
            )
        )

    # Metallic Cu.
    z_cu = 29
    nn = metallic_unified_nearest_neighbor_angstrom(z_cu, n_coord=12)
    frag = mbn.MetalFragment("Cu", z_cu, z_cu)
    bind_cu = mbn.metallic_lattice_binding_ev_per_contact(
        frag,
        distance_angstrom=nn,
        coordination=mbn.metallic_coordination(z_cu),
    )
    rows.append(
        dispersion_row(
            name="Cu",
            crystal_kind="metallic",
            binding_ev=bind_cu,
            contact_dist_ang=nn,
            z_i=z_cu,
            z_j=z_cu,
            n_coord=12.0,
        )
    )

    # Covalent Si.
    dress = covalent_network_em_packing_dress(14, coordination=4)
    r_si = float(dress["bond_length_angstrom"])
    bind_si = cfr.covalent_network_binding_ev(14, r_si, coordination=4)
    rows.append(
        dispersion_row(
            name="Si",
            crystal_kind="covalent_network",
            binding_ev=bind_si,
            contact_dist_ang=r_si,
            z_i=14,
            z_j=14,
            n_coord=4.0,
        )
    )

    identity = {
        "zone_boundary_is_2_gamma": all(
            abs((r.get("zone_boundary_over_gamma") or 0) - 2.0) < 1e-9 for r in rows
        ),
        "gamma_positive": all(r["omega_gamma_cm1"] > 0 for r in rows),
        "hydride_lih": any(r["name"] == "LiH" and r["hydride_route"] for r in rows),
        "ionic_softener_applied": all(
            r["optical_phonon_hessian_softener"] < 1.0
            for r in rows
            if r["crystal_kind"] == "ionic"
        ),
        "covalent_metal_identity_softener": all(
            abs(r["optical_phonon_hessian_softener"] - 1.0) < 1e-15
            for r in rows
            if r["crystal_kind"] in ("metallic", "covalent_network")
        ),
    }
    return {
        "source": "scripts/hqiv_phonon_dispersion_readout.py",
        "lean_modules": ["Hqiv.QuantumChemistry.PhaseElasticity"],
        "formula": {
            "hessian": "k = 2 D / r²",
            "optical_softener": "s = (4/8)·γ / CN_eff (ionic/hydride; CN_eff=1 for Z=1 anion)",
            "omega_gamma": "√(k·s/μ) / (2π c)",
            "dispersion": "ω(k) = 2 √(k·s/μ) |sin(ka/2)|",
            "zone_boundary": "ka=π → ω = 2 ω_Γ",
        },
        "identity_checks": identity,
        "all_identity_checks_pass": all(identity.values()),
        "rows": rows,
        "comparison_policy": "NIST TO frequencies are quarantine only",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()
    audit = build_phonon_dispersion_audit()
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(audit, indent=2) + "\n")
    print(f"wrote {args.json_out}")
    print(f"identity_ok={audit['all_identity_checks_pass']}")
    for r in audit["rows"]:
        ratio = r.get("gamma_vs_TO_ratio")
        ratio_s = f"  Γ/TO={ratio:.2f}" if ratio else ""
        print(
            f"  {r['name']:6} Γ={r['omega_gamma_cm1']:.1f}  "
            f"X={r['omega_zone_boundary_cm1']:.1f} cm⁻¹"
            f"{ratio_s}"
        )


if __name__ == "__main__":
    main()

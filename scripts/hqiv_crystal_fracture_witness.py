#!/usr/bin/env python3
"""
Crystal fracture-scale candidate witnesses from lattice contact binding.

Lean: ``Hqiv.QuantumChemistry.PhaseElasticity``.
No tabulated K_IC or Young's modulus inputs.

Ethics scope: these are **contact-network scale witnesses**, not handbook fracture
toughness predictions.  Crystal anisotropy, crack-tip shape, grain boundaries,
plasticity, and defect statistics are intentionally quarantined until a richer
mechanics spine exists.

Run:
  PYTHONPATH=scripts python3 scripts/hqiv_crystal_fracture_witness.py
  PYTHONPATH=scripts python3 scripts/hqiv_crystal_fracture_witness.py --json-out data/crystal_fracture_witnesses.json
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

import hqiv_ionic_bond_network as ibn
import hqiv_metallic_bond_network as mbn
import hqiv_salt_phase_response as spr
from hqiv_lab.crystal_geometry import closed_atomic_mass_amu, fcc_density_g_cm3

EV_J = 1.602176634e-19
DEFAULT_JSON = _REPO_ROOT / "data" / "crystal_fracture_witnesses.json"


def contact_binding_stiffness_pa(binding_ev: float, contact_dist_ang: float) -> float:
    """Lean ``contactBindingStiffnessPa``."""
    if contact_dist_ang <= 0.0:
        return 0.0
    d_m = contact_dist_ang * 1e-10
    return binding_ev * EV_J / max(d_m**3, 1e-36)


def bulk_modulus_proxy_pa(binding_ev: float, contact_dist_ang: float, n_coord: float) -> float:
    return contact_binding_stiffness_pa(binding_ev, contact_dist_ang) * max(n_coord, 1.0)


def young_modulus_proxy_pa(binding_ev: float, contact_dist_ang: float, n_coord: float) -> float:
    return 3.0 * bulk_modulus_proxy_pa(binding_ev, contact_dist_ang, n_coord)


def griffith_cohesive_energy_release_j_m2(
    binding_ev: float, contact_dist_ang: float, n_coord: float
) -> float:
    """Lean ``griffithCohesiveEnergyReleaseJPerM2``."""
    if contact_dist_ang <= 0.0:
        return 0.0
    return binding_ev * EV_J * max(n_coord, 1.0) / (contact_dist_ang * 1e-10)


def fracture_toughness_candidate_pa_sqrt_m(
    binding_ev: float, contact_dist_ang: float, n_coord: float
) -> float:
    """Lean ``fractureToughnessCandidatePaSqrtM``; interpreted as a K-scale witness."""
    e_y = young_modulus_proxy_pa(binding_ev, contact_dist_ang, n_coord)
    g_c = griffith_cohesive_energy_release_j_m2(binding_ev, contact_dist_ang, n_coord)
    return math.sqrt(max(2.0 * e_y * g_c, 0.0))


def acoustic_velocity_proxy_m_s(young_pa: float, density_g_cm3: float) -> float:
    """Longitudinal speed scale ``sqrt(E/ρ)`` from the contact stiffness proxy."""
    rho_kg_m3 = density_g_cm3 * 1000.0
    if young_pa <= 0.0 or rho_kg_m3 <= 0.0:
        return 0.0
    return math.sqrt(young_pa / rho_kg_m3)


def contact_length_from_strain(r0_ang: float, strain: float) -> float:
    """Lean ``contactLengthFromStrain``."""
    return float(r0_ang) * (1.0 + float(strain))


def stiffness_ratio_from_strain(strain: float) -> float:
    """Lean ``stiffnessRatioFromStrain``: ``(r₀/r)³``."""
    return (1.0 / max(1.0 + float(strain), 1e-12)) ** 3


def piezo_stiffness_equilibrium_strain(
    r0_ang: float,
    binding_ev: float,
    n_coord: float,
    stress_pa: float,
    *,
    thermal_strain: float = 0.0,
    max_steps: int = 8,
    tolerance: float = 1.0e-9,
) -> dict[str, Any]:
    """
    Strain ↔ stiffness fixed point (Lean ``strainFromStressStiffness`` loop).

    ``ε' = clamp01(thermal + (1−thermal)·strong·σ/k(r(ε)))``.
    Zero external stress recovers the thermal / Lindemann seed.  No residual-inferred
    strain; no molecule case.
    """
    import hqiv_lean_physics_primitives as lean
    import hqiv_two_way_feedback_dynamics as twf

    k0 = bulk_modulus_proxy_pa(binding_ev, r0_ang, n_coord)
    eps0 = twf.clamp01(thermal_strain)

    def step(eps: float) -> float:
        k = k0 * stiffness_ratio_from_strain(eps)
        mech = twf.clamp01(
            float(stress_pa) / max(k, 1e-30) * lean.STRONG_CHANNEL_FRACTION
        )
        return twf.clamp01(eps0 + (1.0 - eps0) * mech)

    trace = twf.bounded_fixed_point(
        eps0, step, max_steps=max_steps, tolerance=tolerance
    )
    eps = float(trace.final_state)
    r = contact_length_from_strain(r0_ang, eps)
    return {
        "thermal_strain": eps0,
        "external_stress_Pa": float(stress_pa),
        "equilibrium_strain": eps,
        "contact_length_angstrom": r,
        "stiffness_ratio": stiffness_ratio_from_strain(eps),
        "bulk_modulus_proxy_Pa": k0 * stiffness_ratio_from_strain(eps),
        "converged": trace.converged,
        "fixed_point": trace.to_dict(),
    }


def cleavage_localization_index(contact_lock: float, carrier_count: float) -> float:
    """
    Dimensionless brittle-cleavage proxy.

    Strongly locked contacts with few delocalized carriers localize fracture; metals
    with mobile carriers lower the index.
    """
    return max(contact_lock, 0.0) / max(carrier_count, 1.0)


def ductile_carrier_score(contact_lock: float, carrier_count: float) -> float:
    """Dimensionless delocalization score: mobile carriers not locked to one contact."""
    return max(carrier_count, 0.0) * max(0.0, 1.0 - max(0.0, min(contact_lock, 1.0)))


def ionic_fracture_row(salt: ibn.IonicSalt) -> dict[str, Any]:
    bind = ibn.ionic_lattice_binding_ev_per_contact(
        salt.cation,
        salt.anion,
        distance_angstrom=salt.lattice_bond_angstrom,
    )
    n_coord = float(salt.coordination)
    d = salt.lattice_bond_angstrom
    lock = ibn.ionic_lattice_contact_lock(salt)
    density = spr.salt_crystal_density_g_cm3(salt, coordination=salt.coordination)
    young = young_modulus_proxy_pa(bind, d, n_coord)
    g_c = griffith_cohesive_energy_release_j_m2(bind, d, n_coord)
    k_scale = fracture_toughness_candidate_pa_sqrt_m(bind, d, n_coord)
    carrier_count = 1.0
    return {
        "name": salt.name,
        "crystal_kind": "ionic",
        "nearest_neighbor_angstrom": d,
        "coordination": salt.coordination,
        "density_g_cm3": density,
        "binding_ev_per_contact": bind,
        "contact_lock": lock,
        "bulk_modulus_proxy_Pa": bulk_modulus_proxy_pa(bind, d, n_coord),
        "young_modulus_proxy_Pa": young,
        "griffith_G_c_J_m2": g_c,
        "K_scale_candidate_Pa_sqrt_m": k_scale,
        "sound_speed_proxy_m_s": acoustic_velocity_proxy_m_s(young, density),
        "cleavage_localization_index": cleavage_localization_index(lock, carrier_count),
        "ductile_carrier_score": ductile_carrier_score(lock, carrier_count),
        "carrier_count": carrier_count,
        "interpretation": "ionic brittle-scale witness; no handbook K_IC input",
    }


def metallic_fracture_row(lattice: mbn.MetallicLattice) -> dict[str, Any]:
    bind = mbn.metallic_lattice_binding_ev_per_contact(
        lattice.metal,
        distance_angstrom=lattice.nearest_neighbor_angstrom,
        coordination=lattice.coordination,
    )
    n_coord = float(lattice.coordination)
    d = lattice.nearest_neighbor_angstrom
    lock = mbn.metallic_lattice_contact_lock(lattice)
    density = fcc_density_g_cm3(closed_atomic_mass_amu(lattice.metal.z_nuclear), d)
    young = young_modulus_proxy_pa(bind, d, n_coord)
    g_c = griffith_cohesive_energy_release_j_m2(bind, d, n_coord)
    k_scale = fracture_toughness_candidate_pa_sqrt_m(bind, d, n_coord)
    carrier_count = float(lattice.metal.n_bulk)
    return {
        "name": lattice.name,
        "crystal_kind": "metallic",
        "nearest_neighbor_angstrom": d,
        "coordination": lattice.coordination,
        "density_g_cm3": density,
        "binding_ev_per_contact": bind,
        "contact_lock": lock,
        "bulk_modulus_proxy_Pa": bulk_modulus_proxy_pa(bind, d, n_coord),
        "young_modulus_proxy_Pa": young,
        "griffith_G_c_J_m2": g_c,
        "K_scale_candidate_Pa_sqrt_m": k_scale,
        "sound_speed_proxy_m_s": acoustic_velocity_proxy_m_s(young, density),
        "cleavage_localization_index": cleavage_localization_index(lock, carrier_count),
        "ductile_carrier_score": ductile_carrier_score(lock, carrier_count),
        "carrier_count": carrier_count,
        "interpretation": "metallic delocalized-carrier scale witness; plasticity not yet modeled",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Crystal fracture candidate witnesses.")
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()
    rows = [
        ionic_fracture_row(ibn.NACL_SALT),
        metallic_fracture_row(mbn.CU_LATTICE),
        metallic_fracture_row(mbn.AL_LATTICE),
    ]
    payload = {
        "lean_module": "Hqiv.QuantumChemistry.PhaseElasticity",
        "policy": (
            "Griffith-scale candidates from contact binding only; handbook K_IC, "
            "Young's modulus, crack geometry, and plasticity are quarantined"
        ),
        "ethics": {
            "no_tabulated_moduli": True,
            "no_tabulated_fracture_toughness": True,
            "not_a_handbook_prediction": True,
            "open_terms": [
                "anisotropic elastic tensor",
                "plastic zone and dislocation mobility",
                "grain boundaries",
                "crack-tip shape statistics",
            ],
        },
        "witnesses": rows,
    }
    for row in rows:
        k = row["K_scale_candidate_Pa_sqrt_m"]
        print(
            f"{row['name']:4s} E_proxy={row['young_modulus_proxy_Pa']:.3e} Pa  "
            f"K_scale~={k:.3e} Pa·√m  "
            f"cleave={row['cleavage_localization_index']:.3f}  "
            f"ductile={row['ductile_carrier_score']:.3f}"
        )
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(payload, indent=2) + "\n")
    print(f"Wrote {args.json_out}")


if __name__ == "__main__":
    main()

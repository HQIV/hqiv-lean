#!/usr/bin/env python3
"""
Aqueous electrolyte readouts on the ionic-bond + H₂O host spine.

Uses ``hqiv_ionic_bond_network`` (no tabulated masses, hydration shells, or AMU tables):
  • ``IonicSalt`` stoichiometry and derived formula mass
  • Hydration contacts from ion–H₂O cluster VSEPR
  • σ from solvation-hop Eyring on ion contacts
  • Colligative ΔT_f from host melt spine

Run:
  PYTHONPATH=scripts python3 scripts/hqiv_electrolyte_solution.py
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

import hqiv_homogeneous_curvature_feedback as hcf
import hqiv_ionic_bond_network as ibn
import hqiv_phase_geometry_density as pgd
import hqiv_phase_material_response as pmr

AVOGADRO = pgd.AVOGADRO
FARADAY = 96485.33212
H2O_MW_G_MOL = 18.015  # from derived H2O spec below

# Benchmark only — not HQIV inputs.
NIST_SEAWATER_35PSU = {
    "salinity_g_per_kg": 35.0,
    "density_g_cm3": 1.023,
    "refractive_index": 1.34,
    "conductivity_S_m": 5.0,
    "freezing_point_depression_K": 1.9,
}


def _h2o_mw_g_mol() -> float:
    from hqiv_lab.spec import MoleculeSpec

    return MoleculeSpec.from_chart_name("H2O").molecular_weight_amu


def molality_mol_per_kg(salinity_g_per_kg: float, salt: ibn.IonicSalt) -> float:
    return max(salinity_g_per_kg, 0.0) / salt.formula_mass_amu


def solution_density_g_cm3(salinity_g_per_kg: float, salt: ibn.IonicSalt) -> float:
    return (1000.0 + salinity_g_per_kg) / 1000.0


def ion_molarity_mol_per_l(salinity_g_per_kg: float, salt: ibn.IonicSalt) -> float:
    m = molality_mol_per_kg(salinity_g_per_kg, salt)
    rho = solution_density_g_cm3(salinity_g_per_kg, salt)
    denom = 1.0 + m * salt.formula_mass_amu / 1000.0
    return m * rho / max(denom, 1e-12)


def hydration_curvature_perturbation(
    salinity_g_per_kg: float,
    salt: ibn.IonicSalt,
    *,
    host_rho_curv: float,
) -> tuple[float, float]:
    import hqiv_lean_physics_primitives as lean

    m = molality_mol_per_kg(salinity_g_per_kg, salt)
    n_water = 1000.0 / _h2o_mw_g_mol()
    particle_frac = m * salt.dissolved_particles / max(n_water, 1e-12)
    coord_excess = particle_frac * (lean.GAMMA / 2.0)
    headroom = max(1.0 - host_rho_curv, 0.0)
    return min(host_rho_curv + coord_excess * headroom, 1.0), coord_excess


def cryoscopic_constant_K_kg_mol(host: str = "H2O", *, t_melt_k: float = 273.15) -> float:
    l_fusion = pmr.latent_heat_fusion_j_per_mol(host)
    return 8.314462618 * (t_melt_k**2) * _h2o_mw_g_mol() / (1000.0 * max(l_fusion, 1.0))


def colligative_freezing_depression_K(
    salinity_g_per_kg: float,
    salt: ibn.IonicSalt,
    *,
    host: str = "H2O",
    t_melt_k: float = 273.15,
) -> float:
    m = molality_mol_per_kg(salinity_g_per_kg, salt)
    return salt.dissolved_particles * m * cryoscopic_constant_K_kg_mol(host, t_melt_k=t_melt_k)


def ionic_conductivity_s_m(
    salinity_g_per_kg: float,
    salt: ibn.IonicSalt,
    *,
    host: str = "H2O",
    temperature_k: float,
    rho_curv: float,
) -> float:
    c = ion_molarity_mol_per_l(salinity_g_per_kg, salt)
    c_m3 = c * 1000.0
    mu_cat = ibn.eyring_ion_mobility_m2_per_vs(
        salt.cation, host=host, temperature_k=temperature_k, rho_curv=rho_curv
    )
    mu_an = ibn.eyring_ion_mobility_m2_per_vs(
        salt.anion, host=host, temperature_k=temperature_k, rho_curv=rho_curv
    )
    return FARADAY * (
        abs(salt.cation.formal_charge) * c_m3 * mu_cat
        + abs(salt.anion.formal_charge) * c_m3 * mu_an
    )


def salt_water_response_readout(
    *,
    salt: ibn.IonicSalt = ibn.NACL_SALT,
    salinity_g_per_kg: float = 35.0,
    host: str = "H2O",
    temperature_k: float = 298.15,
) -> dict[str, Any]:
    rho_g = solution_density_g_cm3(salinity_g_per_kg, salt)
    host_base = pmr.material_response_readout(
        host, phase="liquid", temperature_k=temperature_k, carrier_fraction=0.0
    )
    rho_curv_host = pgd.melt_comparison_curvature_density_fraction()
    rho_curv, coord_excess = hydration_curvature_perturbation(
        salinity_g_per_kg, salt, host_rho_curv=rho_curv_host
    )
    xi = host_base["contact_xi"]
    b_hom = hcf.homogeneous_curvature_budget_at_xi(xi, rho_curv)
    b_hom += (
        hcf.binding_curvature_feedback_second_order_homogeneous(
            xi, rho_curv, coordination_excess=coord_excess
        )
        - 1.0
    )

    coord_div = pmr.clausius_mossotti_local_field_divisor(host, "liquid")
    alpha_host = pmr.hqiv_polarizability_angstrom3(host, rho_curv, xi)
    c_ion = ion_molarity_mol_per_l(salinity_g_per_kg, salt)
    cm_raw = pmr.clausius_mossotti_ratio(
        rho_g, _h2o_mw_g_mol(), alpha_host, coordination_divisor=coord_div
    )
    n = pmr.refractive_index_from_clausius_mossotti(cm_raw * max(b_hom, 1.0))
    sigma = ionic_conductivity_s_m(
        salinity_g_per_kg, salt, host=host, temperature_k=temperature_k, rho_curv=rho_curv
    )
    delta_t_f = colligative_freezing_depression_K(salinity_g_per_kg, salt, host=host)

    witness = ibn.salt_witness(salt)
    benchmark: dict[str, Any] = {}
    if abs(salinity_g_per_kg - 35.0) < 0.5:
        nist = NIST_SEAWATER_35PSU
        benchmark = {
            "density_error_pct": abs(rho_g - nist["density_g_cm3"]) / nist["density_g_cm3"] * 100.0,
            "refractive_index_error_pct": abs(n - nist["refractive_index"]) / nist["refractive_index"] * 100.0,
            "conductivity_error_pct": abs(sigma - nist["conductivity_S_m"]) / nist["conductivity_S_m"] * 100.0,
            "freezing_depression_error_pct": abs(delta_t_f - nist["freezing_point_depression_K"])
            / nist["freezing_point_depression_K"]
            * 100.0,
        }

    return {
        "system": f"{salt.name}(aq)",
        "host": host,
        "salinity_g_per_kg": salinity_g_per_kg,
        "molality_mol_per_kg": molality_mol_per_kg(salinity_g_per_kg, salt),
        "ion_molarity_mol_per_l": c_ion,
        "temperature_K": temperature_k,
        "density_g_cm3": rho_g,
        "curvature_density_fraction": rho_curv,
        "hydration_coordination_excess": coord_excess,
        "B_hom_electrolyte": b_hom,
        "refractive_index": n,
        "ionic_conductivity_S_m": sigma,
        "freezing_point_depression_K": delta_t_f,
        "freezing_point_K": 273.15 - delta_t_f,
        "ionic_lattice_witness": witness,
        "host_baseline": {
            "refractive_index": host_base["refractive_index"],
            "dynamic_viscosity_Pa_s": host_base["dynamic_viscosity_Pa_s"],
        },
        "benchmark_vs_nist_35psu": benchmark,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Aqueous electrolyte on ionic-bond spine.")
    parser.add_argument("--salinity-g-kg", type=float, default=35.0)
    parser.add_argument("--temperature-K", type=float, default=298.15)
    parser.add_argument("--json-out", type=Path, default=None)
    args = parser.parse_args()
    out = salt_water_response_readout(
        salinity_g_per_kg=args.salinity_g_kg,
        temperature_k=args.temperature_K,
    )
    print(f"{out['system']} @ {out['temperature_K']:.2f} K")
    print(f"  ρ={out['density_g_cm3']:.4f}  n={out['refractive_index']:.4f}  σ={out['ionic_conductivity_S_m']:.3f} S/m")
    print(f"  ΔT_f={out['freezing_point_depression_K']:.2f} K")
    if args.json_out:
        args.json_out.write_text(json.dumps(out, indent=2) + "\n")


if __name__ == "__main__":
    main()

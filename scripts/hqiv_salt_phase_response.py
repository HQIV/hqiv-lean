#!/usr/bin/env python3
"""
Salt melting point and refractive index on the ionic-bond contact-network spine.

Same machinery as covalent ``CurvatureContactNetwork`` + ``PhaseMaterialResponse``:
  • ``ionicBondSurplus`` → lattice binding per contact
  • ``ionic_lattice`` intermolecular motif → ``ionic_lattice_melt_cohesive_ev``
  • Clausius–Mossotti → solid refractive index n

Lean mirrors:
  • ``Hqiv.Geometry.BondedHorizonCasimir`` — ``ionicBondSurplus``
  • ``Hqiv.QuantumChemistry.CurvatureContactNetwork`` — ``ionicBond``, ``ionSolvation``
  • ``Hqiv.QuantumChemistry.PhaseMaterialResponse`` — ``refractiveIndexFromCM``

Run:
  PYTHONPATH=scripts python3 scripts/hqiv_salt_phase_response.py
  PYTHONPATH=scripts python3 scripts/hqiv_salt_phase_response.py --salt NaCl --json-out data/salt_phase_witness.json
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
import hqiv_lean_physics_primitives as lean
import hqiv_phase_geometry_density as pgd
import hqiv_phase_material_response as pmr
import hqiv_thermodynamic_phase_from_tp as tptp

AVOGADRO = pgd.AVOGADRO

# Laboratory validation anchors (not HQIV inputs).
NIST_SALT_BENCHMARKS = {
    "NACL": {
        "T_melt_K": 1074.0,
        "refractive_index_solid": 1.544,
        "density_g_cm3": 2.17,
        "coordination": 6,
    },
    "LIH": {
        "T_melt_K": 958.0,
        "refractive_index_solid": 1.45,
        "density_g_cm3": 0.82,
        "coordination": 6,
    },
    "KCL": {
        "T_melt_K": 1045.0,
        "refractive_index_solid": 1.490,
        "density_g_cm3": 1.98,
        "coordination": 6,
    },
    "LIF": {
        "T_melt_K": 1121.0,
        "refractive_index_solid": 1.392,
        "density_g_cm3": 2.64,
        "coordination": 6,
    },
    "NAF": {
        "T_melt_K": 1266.0,
        "refractive_index_solid": 1.325,
        "density_g_cm3": 2.56,
        "coordination": 6,
    },
}


def rocksalt_lattice_parameter_angstrom(nearest_neighbor_ang: float) -> float:
    """Rocksalt FCC: cell edge a = 2 × nearest-neighbor M–X contact."""
    return 2.0 * float(nearest_neighbor_ang)


def salt_crystal_density_g_cm3(
    salt: ibn.IonicSalt,
    *,
    coordination: int = 6,
) -> float:
    """
    ρ from rocksalt unit cell: 4 formula units per a³ (geometry witness, not a table).
    """
    a_ang = rocksalt_lattice_parameter_angstrom(salt.lattice_bond_angstrom)
    a_cm = a_ang * 1e-8
    vol_cm3 = a_cm**3
    mass_g = 4.0 * salt.formula_mass_amu / AVOGADRO
    return float(mass_g / max(vol_cm3, 1e-30))


def material_scales_for_ionic_salt(
    salt: ibn.IonicSalt,
    *,
    coordination: int = 6,
) -> tptp.MaterialThermodynamicScales:
    """Thermodynamic scales from ionic lattice contacts (not tetrahedral bulk_condensed)."""
    from hqiv_lab.crystal_geometry import ionic_hydride_melt_dress

    bind = ibn.ionic_lattice_binding_ev_per_contact(
        salt.cation,
        salt.anion,
        distance_angstrom=salt.lattice_bond_angstrom,
    )
    # Hydride melt dress (anion Z=1): (1+α)/γ² on the cohesive scale.
    bind *= ionic_hydride_melt_dress(salt.anion.z_nuclear)
    net = ibn.build_ionic_salt_network(salt)
    xi = lean.xi_from_compton_triplet(net.compton_triplet)
    rho_g = salt_crystal_density_g_cm3(salt, coordination=coordination)
    rho_frac = pgd.crystalline_curvature_density_fraction(
        rho_g,
        motif="ionic_lattice",
        n_coord=coordination,
        salt=salt,
    )
    return tptp.MaterialThermodynamicScales(
        name=salt.name,
        characteristic_binding_ev=float(bind),
        contact_points=int(coordination),
        molecular_weight_amu=salt.formula_mass_amu,
        intermolecular_contacts=int(coordination),
        contact_xi=float(xi),
        bulk_condensed=False,
        medium_density_fraction=float(rho_frac),
        intermolecular_motif="ionic_lattice",
        z_heavy=max(salt.cation.z_nuclear, salt.anion.z_nuclear),
    )


def salt_solid_refractive_index(
    salt: ibn.IonicSalt,
    material: tptp.MaterialThermodynamicScales,
    *,
    coordination: int = 6,
    temperature_k: float | None = None,
) -> float:
    """Clausius–Mossotti n for ionic crystal at derived ρ and B_hom(ξ, ρ)."""
    import hqiv_selection_weights as sw
    import hqiv_voltage_generation_ledger as vgl

    rho_g = salt_crystal_density_g_cm3(salt, coordination=coordination)
    xi = material.contact_xi
    rho_curv = float(material.medium_density_fraction or 0.0)
    b_hom = hcf.homogeneous_curvature_budget_at_xi(xi, rho_curv)
    # Optical gap: surplus × α²·γ/n_coord, softened by ionic character and
    # Lindemann piezo strain — E_opt / ((1+(4/8)·γ·δ²)·(1+(4/8)·ε·δ²)).
    ionic = float(
        sw.bond_ionic_character(salt.cation.z_nuclear, salt.anion.z_nuclear)
    )
    t_melt, _ = tptp.characteristic_temperatures_K(material)
    t_use = float(temperature_k) if temperature_k is not None else float(t_melt)
    eps = vgl.lindemann_thermal_strain(t_use, t_melt)
    soft = vgl.ionic_optical_gap_softener_with_piezo(ionic, eps)
    e_soft = max(tptp.ionic_lattice_optical_gap_ev(material) * soft, 1e-4)
    span = float(salt.lattice_bond_angstrom)
    r_ratio = span / pmr.BOHR_RADIUS_ANGSTROM
    alpha = (
        lean.ALPHA
        * lean.STRONG_CHANNEL_FRACTION
        * (r_ratio**3)
        * (pmr.RYDBERG_EV / e_soft)
        * b_hom
        * ibn.ionic_period_polarizability_softener(
            salt.cation.z_nuclear, salt.anion.z_nuclear
        )
    )
    coord_div = 3.0 if coordination >= 6 else float(coordination)
    cm = pmr.clausius_mossotti_ratio(
        rho_g,
        salt.formula_mass_amu,
        alpha,
        coordination_divisor=coord_div,
    )
    cm = min(float(cm), 0.35)
    return pmr.refractive_index_from_clausius_mossotti(cm)


def salt_phase_response_readout(
    salt: ibn.IonicSalt,
    *,
    coordination: int = 6,
    temperature_k: float = 298.15,
    pressure_pa: float = tptp.STP_PRESSURE_PA,
) -> dict[str, Any]:
    """
    Full salt witness: T_melt, T_boil, solid n, ρ, phase @ (T,P), ionic network slot.
    """
    mat = material_scales_for_ionic_salt(salt, coordination=coordination)
    t_melt, t_boil = tptp.characteristic_temperatures_K(mat)
    t_sl = tptp.solid_liquid_transition_temperature_K(mat, pressure_Pa=pressure_pa)
    n_solid = salt_solid_refractive_index(
        salt, mat, coordination=coordination, temperature_k=temperature_k
    )
    rho_g = salt_crystal_density_g_cm3(salt, coordination=coordination)
    env = tptp.ThermodynamicEnvironment(temperature_k, pressure_pa)
    phase_state = tptp.derive_phase(env, mat)
    witness = ibn.salt_witness(salt)

    bench: dict[str, Any] = {}
    key = salt.name.upper()
    if key in NIST_SALT_BENCHMARKS:
        ref = NIST_SALT_BENCHMARKS[key]
        bench = {
            "T_melt_error_pct": abs(t_melt - ref["T_melt_K"]) / ref["T_melt_K"] * 100.0,
            "refractive_index_error_pct": abs(n_solid - ref["refractive_index_solid"])
            / ref["refractive_index_solid"]
            * 100.0,
            "density_error_pct": abs(rho_g - ref["density_g_cm3"]) / ref["density_g_cm3"] * 100.0,
            "reference": ref,
        }

    return {
        "salt": salt.name,
        "coordination": coordination,
        "density_g_cm3": rho_g,
        "lattice_parameter_angstrom": rocksalt_lattice_parameter_angstrom(
            salt.lattice_bond_angstrom
        ),
        "T_melt_K": t_melt,
        "T_boil_K": t_boil,
        "T_solid_liquid_K": t_sl,
        "refractive_index_solid": n_solid,
        "ionic_melt_cohesive_ev": tptp.ionic_lattice_melt_cohesive_ev(mat),
        "contact_xi": mat.contact_xi,
        "medium_density_fraction": mat.medium_density_fraction,
        "melt_reference_g_cm3": pgd.derived_melt_reference_density_g_cm3(
            rho_g,
            motif="ionic_lattice",
            n_coord=coordination,
            salt=salt,
        ),
        "crystalline_melt_density_ratio": pgd.resolve_crystalline_melt_density_ratio(
            motif="ionic_lattice",
            n_coord=coordination,
            salt=salt,
        )[0],
        "crystalline_curvature_density_fraction": mat.medium_density_fraction,
        "phase_at_T_P": phase_state.phase.value,
        "ionic_lattice_witness": witness,
        "benchmark_vs_nist": bench,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Salt melt + refractive index witnesses.")
    parser.add_argument(
        "--salt",
        default="NaCl",
        choices=("LiH", "NaCl", "KCl", "LiF", "NaF", "all"),
    )
    parser.add_argument("--json-out", type=Path, default=None)
    args = parser.parse_args()
    keys = list(ibn.SALTS) if args.salt.lower() == "all" else [args.salt.upper()]
    rows = [salt_phase_response_readout(ibn.SALTS[k]) for k in keys]
    for row in rows:
        print(
            f"{row['salt']}: T_melt={row['T_melt_K']:.1f} K  "
            f"n_solid={row['refractive_index_solid']:.4f}  "
            f"ρ={row['density_g_cm3']:.3f} g/cm³"
        )
        if row.get("benchmark_vs_nist"):
            b = row["benchmark_vs_nist"]
            print(
                f"  vs NIST: ΔT_melt={b['T_melt_error_pct']:.1f}%  "
                f"Δn={b['refractive_index_error_pct']:.1f}%  "
                f"Δρ={b['density_error_pct']:.1f}%"
            )
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps({"salts": rows}, indent=2) + "\n")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
Phase geometry → mass density → curvature density ρ → melt / κ₆ feedback.

Uses data already in the stack (formula weight, bond lengths). Allotropes are
**derived** via ``hqiv_lab`` (VSEPR motif → packing templates); this script is the
legacy CLI bridge. No fitted potentials: ρ = Z·M/(N_A·V).

Example (H₂O ice Ih at 273 K):
  input H2O + allotrope Ih → ρ_solid ≈ 0.917 g/cm³ → ρ_curvature vs liquid water → T_melt.

Run:
  python3 scripts/hqiv_phase_geometry_density.py H2O
  python3 scripts/hqiv_phase_geometry_density.py CH4 --allotrope solid
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

import hqiv_dynamic_binding_chart as chart
import hqiv_homogeneous_curvature_feedback as hcf
import hqiv_lean_physics_primitives as lean
import hqiv_thermodynamic_phase_from_tp as tptp

AVOGADRO = 6.022_140_76e23
ANGSTROM_TO_CM = 1.0e-8

# Monomer MW from chart fragment labels (no extra tables).
_ELEMENT_AMU: dict[str, float] = {
    "H": 1.008,
    "Li": 6.94,
    "C": 12.011,
    "N": 14.007,
    "O": 15.999,
    "F": 18.998,
}


@dataclass(frozen=True)
class PhaseUnitCell:
    """Crystalline unit cell for density (geometry witness, not DFT)."""

    allotrope: str
    molecules_per_cell: int
    molecular_weight_amu: float
    # Hexagonal: a=b, c; cubic: a only; orthorhombic: a,b,c
    a_angstrom: float
    b_angstrom: float | None = None
    c_angstrom: float | None = None
    crystal_system: str = "hexagonal"  # hexagonal | cubic | orthorhombic

    @property
    def volume_cm3(self) -> float:
        a = self.a_angstrom * ANGSTROM_TO_CM
        b = (self.b_angstrom if self.b_angstrom is not None else self.a_angstrom) * ANGSTROM_TO_CM
        c = (self.c_angstrom if self.c_angstrom is not None else self.a_angstrom) * ANGSTROM_TO_CM
        if self.crystal_system == "hexagonal":
            return (math.sqrt(3.0) / 2.0) * a * a * c
        if self.crystal_system == "cubic":
            return a * a * a
        return a * b * c


def density_g_cm3(cell: PhaseUnitCell) -> float:
    """ρ = Z·M / (N_A·V) with M in g/mol."""
    mass_g = cell.molecules_per_cell * cell.molecular_weight_amu / AVOGADRO
    return mass_g / cell.volume_cm3


def liquid_reference_density_g_cm3(molecule: str) -> float:
    """Reference liquid density at melt comparison (water = 1.0 g/cm³ scale)."""
    refs = {
        "H2O": 1.0,
        "CH4": 0.423,  # boiling liquid CH4 @ 112 K order-of-magnitude
        "NH3": 0.682,
    }
    return refs.get(molecule.upper(), 1.0)


def _lab_cell_to_legacy(cell: Any) -> PhaseUnitCell:
    from hqiv_lab.unit_cell import PhaseUnitCell as LabCell

    assert isinstance(cell, LabCell)
    return PhaseUnitCell(
        allotrope=cell.allotrope,
        molecules_per_cell=cell.molecules_per_cell,
        molecular_weight_amu=cell.molecular_weight_amu,
        a_angstrom=cell.a_angstrom,
        b_angstrom=cell.b_angstrom,
        c_angstrom=cell.c_angstrom,
        crystal_system=cell.crystal.value,
    )


def preferred_allotrope(molecule: str, *, temperature_k: float = 273.15) -> str:
    """Derived preferred allotrope at (T, P) via ``hqiv_lab``."""
    from hqiv_lab import MaterialsLab

    return MaterialsLab().preferred_allotrope(
        MaterialsLab().spec_from_name(molecule),
        temperature_k=temperature_k,
    ).label


def phase_unit_cell(
    molecule: str,
    allotrope: str | None = None,
    *,
    temperature_k: float = 273.15,
) -> PhaseUnitCell:
    """Unit cell from derived allotrope (``hqiv_lab``), not a static table."""
    from hqiv_lab import MaterialsLab

    lab = MaterialsLab()
    spec = lab.spec_from_name(molecule)
    cell = lab.unit_cell(spec, allotrope, temperature_k=temperature_k)
    return _lab_cell_to_legacy(cell)


def covalent_span_angstrom(name: str) -> float:
    """Sum of chart bond lengths (geometry span for polarizability / stiffness)."""
    for bench in chart.GMTKN55_SUITE:
        if bench.name.upper() == name.upper():
            if bench.bonds:
                return sum(b.distance_angstrom for b in bench.bonds)
    return 1.0


def curvature_density_fraction(
    rho_solid_g_cm3: float,
    molecule: str,
) -> float:
    """ρ_curvature ∈ [0,1]: solid geometry density vs liquid reference at melt."""
    ref = liquid_reference_density_g_cm3(molecule)
    if ref <= 0.0:
        return 0.0
    return min(1.0, max(0.0, rho_solid_g_cm3 / ref))


def clausius_mossotti_from_refractive_index(n: float) -> float:
    """(n² − 1)/(n² + 2) — optical curvature participation (CM ratio)."""
    n2 = n * n
    return (n2 - 1.0) / (n2 + 2.0)


def optical_curvature_density_fraction(n: float) -> float:
    """ρ_opt ∈ [0,1] from solid n; n = 1 is the dilute/gas limit."""
    if n <= 1.0:
        return 0.0
    return min(1.0, max(0.0, clausius_mossotti_from_refractive_index(n)))


def phase_curvature_density_fraction(rho_geom: float, n_solid: float) -> float:
    """
    Unified ρ for κ₆ feedback: geometric packing × optical phase dress.

    Lean mirror: ``phaseCurvatureDensityFraction`` in ``PhaseGeometryDensity``.
    """
    rho_opt = optical_curvature_density_fraction(n_solid)
    dressed = rho_geom * (1.0 + lean.ALPHA * rho_opt)
    return min(1.0, max(0.0, dressed))


def kappa6_feedback_from_phase_curvature(
    xi: float,
    rho_geom: float,
    n_solid: float,
    *,
    coordination_excess: float = 0.0,
) -> float:
    """κ₆ second-order feedback from unified phase curvature (geometry + n)."""
    rho_kappa = phase_curvature_density_fraction(rho_geom, n_solid)
    return hcf.binding_curvature_feedback_second_order_homogeneous(
        xi,
        rho_kappa,
        coordination_excess=coordination_excess,
    )


def material_scales_with_phase_geometry(
    molecule: str,
    *,
    allotrope: str | None = None,
    bulk: bool = True,
    temperature_k: float = 273.15,
) -> tptp.MaterialThermodynamicScales:
    """Bulk material scales with ρ_geom + solid n for κ₆ curvature closure."""
    from hqiv_lab.coordination import infer_monomer_geometry
    from hqiv_lab.spec import MoleculeSpec

    import hqiv_phase_material_response as pmr

    cell = phase_unit_cell(molecule, allotrope, temperature_k=temperature_k)
    rho_g = density_g_cm3(cell)
    rho_geom = curvature_density_fraction(rho_g, molecule)
    base = tptp.material_scales_from_network_name(molecule)
    mono = infer_monomer_geometry(MoleculeSpec.from_chart_name(molecule))
    inter = mono.intermolecular_contacts
    n_solid = pmr.refractive_index_solid_readout(
        molecule, cell, allotrope=cell.allotrope
    )
    return tptp.MaterialThermodynamicScales(
        name=f"{molecule}_bulk" if bulk else molecule,
        characteristic_binding_ev=base.characteristic_binding_ev,
        contact_points=inter,
        molecular_weight_amu=cell.molecular_weight_amu,
        intermolecular_contacts=inter,
        contact_xi=base.contact_xi,
        bulk_condensed=bulk,
        medium_density_fraction=rho_geom,
        refractive_index_solid=n_solid,
        intermolecular_motif=mono.motif.value,
        z_heavy=mono.z_heavy,
    )


# --- Orbital phase geometry (Lean: PhaseGeometryDensity orbital section) ----------------

G_NEWTON_SI = 6.67430e-11
EARTH_MASS_KG = 5.9722e24
EARTH_RADIUS_M = 6.378137e6
SOLAR_SYSTEM_PROP_XI = 1.0  # xiOfShell(0) = 1


@dataclass(frozen=True)
class OrbitalPhaseWitness:
    """Planetary geometry witness: mass, radius, encounter distance [m]."""

    label: str
    central_mass_kg: float
    radius_m: float
    encounter_radius_m: float


def orbital_bulk_dominance_weight(r_bulk: float, r_encounter: float) -> float:
    """Lean ``orbitalBulkDominanceWeight`` (bulk-dominated limit)."""
    if r_bulk <= 0.0:
        return 0.0
    return 1.0 / (1.0 + (r_encounter / r_bulk) ** 2)


def orbital_local_curvature_fraction(r_bulk: float, r_encounter: float) -> float:
    """Lean ``orbitalLocalCurvatureFraction``: clamp((R/r)²)."""
    if r_encounter <= 0.0:
        return 0.0
    return min(1.0, max(0.0, (r_bulk / r_encounter) ** 2))


def orbital_curvature_density_fraction(w: OrbitalPhaseWitness) -> float:
    """Lean ``orbitalCurvatureDensityFraction``: w_bulk + (1−w_bulk)·ρ_local."""
    w_bulk = orbital_bulk_dominance_weight(w.radius_m, w.encounter_radius_m)
    rho_local = orbital_local_curvature_fraction(w.radius_m, w.encounter_radius_m)
    return min(1.0, max(0.0, w_bulk + (1.0 - w_bulk) * rho_local))


def orbital_phase_witness_from_body(
    *,
    label: str,
    gm: float,
    radius_m: float,
    encounter_radius_m: float,
) -> OrbitalPhaseWitness:
    """Build witness from SI GM and equatorial radius."""
    mass_kg = gm / G_NEWTON_SI if G_NEWTON_SI > 0.0 else 0.0
    return OrbitalPhaseWitness(label, mass_kg, radius_m, encounter_radius_m)


def orbital_phase_witness_earth(encounter_radius_m: float) -> OrbitalPhaseWitness:
    return OrbitalPhaseWitness("Earth", EARTH_MASS_KG, EARTH_RADIUS_M, encounter_radius_m)


def homogeneous_curvature_budget_from_orbital(
    xi: float,
    witness: OrbitalPhaseWitness,
) -> float:
    """Lean ``homogeneousCurvatureBudgetFromOrbital``."""
    rho = orbital_curvature_density_fraction(witness)
    return hcf.homogeneous_curvature_budget_at_xi(xi, rho)


def orbital_curvature_mass_delta_fraction(
    xi: float,
    witness: OrbitalPhaseWitness,
) -> float:
    """Lean ``orbitalCurvatureMassDeltaFraction``: B_hom − 1."""
    return homogeneous_curvature_budget_from_orbital(xi, witness) - 1.0


def flyby_dynamic_kappa_phi_from_phase(
    witness: OrbitalPhaseWitness,
    gate: float,
    *,
    xi: float = SOLAR_SYSTEM_PROP_XI,
) -> float:
    """Lean ``flybyDynamicKappaPhiFromPhase``: 1 + gate·(B_hom − 1)."""
    g = max(0.0, min(1.0, float(gate)))
    b_hom = homogeneous_curvature_budget_from_orbital(xi, witness)
    return 1.0 + g * (b_hom - 1.0)


def orbital_flyby_readout(
    *,
    label: str = "Earth",
    gm: float,
    radius_m: float,
    encounter_radius_m: float,
    xi: float = SOLAR_SYSTEM_PROP_XI,
) -> dict[str, Any]:
    """Full orbital phase-geometry witness for flyby diagnostics."""
    w = orbital_phase_witness_from_body(
        label=label,
        gm=gm,
        radius_m=radius_m,
        encounter_radius_m=encounter_radius_m,
    )
    rho = orbital_curvature_density_fraction(w)
    b_hom = homogeneous_curvature_budget_from_orbital(xi, w)
    return {
        "witness": asdict(w),
        "propagation_xi": xi,
        "curvature_density_fraction": rho,
        "B_hom": b_hom,
        "curvature_mass_delta_fraction": b_hom - 1.0,
        "w_bulk": orbital_bulk_dominance_weight(w.radius_m, w.encounter_radius_m),
        "rho_local": orbital_local_curvature_fraction(w.radius_m, w.encounter_radius_m),
    }


def melt_readout_with_phase_geometry(
    molecule: str,
    *,
    allotrope: str | None = None,
    pressure_pa: float = tptp.STP_PRESSURE_PA,
    temperature_at_melt_k: float = 273.15,
) -> dict[str, Any]:
    """Full witness: geometry → ρ_geom + n → κ₆(ρ) → T_sl @ pressure."""
    cell = phase_unit_cell(molecule, allotrope, temperature_k=temperature_at_melt_k)
    rho_g = density_g_cm3(cell)
    rho_geom = curvature_density_fraction(rho_g, molecule)
    mat = material_scales_with_phase_geometry(
        molecule,
        allotrope=allotrope,
        bulk=True,
        temperature_k=temperature_at_melt_k,
    )
    n_solid = mat.refractive_index_solid or 1.0
    rho_kappa = phase_curvature_density_fraction(rho_geom, n_solid)
    rho_opt = optical_curvature_density_fraction(n_solid)
    xi = mat.contact_xi
    fb = kappa6_feedback_from_phase_curvature(xi, rho_geom, n_solid)
    motif_scale = tptp.melt_motif_relative_scale_for_material(mat)
    t_melt, t_boil = tptp.characteristic_temperatures_K(mat)
    env = tptp.ThermodynamicEnvironment(temperature_at_melt_k, pressure_pa)
    phase = tptp.derive_phase(env, mat)
    return {
        "molecule": molecule,
        "allotrope": cell.allotrope,
        "unit_cell": asdict(cell),
        "density_g_cm3": rho_g,
        "liquid_reference_g_cm3": liquid_reference_density_g_cm3(molecule),
        "curvature_density_fraction": rho_geom,
        "optical_curvature_density_fraction": rho_opt,
        "phase_curvature_density_fraction": rho_kappa,
        "refractive_index_solid": n_solid,
        "contact_xi": xi,
        "kappa6_feedback": fb,
        "melt_motif_relative_scale": motif_scale,
        "T_melt_K": t_melt,
        "T_boil_K": t_boil,
        "T_sl_at_pressure_K": tptp.solid_liquid_transition_temperature_K(mat, pressure_Pa=pressure_pa),
        "phase_at_melt": phase.phase.value,
        "B_eff": hcf.effective_curvature_budget(xi, rho_kappa),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Phase geometry → density → melt / orbital curvature.")
    parser.add_argument("molecule", nargs="?", default="H2O")
    parser.add_argument("--allotrope", default=None)
    parser.add_argument("--orbital", action="store_true", help="Earth flyby witness at --encounter-r RE")
    parser.add_argument("--encounter-r", type=float, default=2.0, help="Encounter radius in body radii")
    parser.add_argument("--json-out", type=Path, default=None)
    args = parser.parse_args()
    if args.orbital:
        r_m = args.encounter_r * EARTH_RADIUS_M
        out = orbital_flyby_readout(
            gm=3.986004418e14,
            radius_m=EARTH_RADIUS_M,
            encounter_radius_m=r_m,
        )
        print(f"Earth orbital witness @ r = {args.encounter_r:.2f} R⊕")
        print(f"  ρ_orb = {out['curvature_density_fraction']:.4f}")
        print(f"  B_hom = {out['B_hom']:.4f}  δm fraction = {out['curvature_mass_delta_fraction']:.6f}")
    else:
        out = melt_readout_with_phase_geometry(args.molecule, allotrope=args.allotrope)
        print(f"{out['molecule']} allotrope {out['allotrope']}")
        print(f"  ρ_solid = {out['density_g_cm3']:.4f} g/cm³  →  ρ_curvature = {out['curvature_density_fraction']:.4f}")
        print(f"  T_melt ≈ {out['T_sl_at_pressure_K']:.2f} K @ 1 atm  (phase @ 273.15 K: {out['phase_at_melt']})")
        print(f"  κ₆ feedback = {out['kappa6_feedback']:.4f}")
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(out, indent=2) + "\n")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
Phase geometry → material response targets (no fitted potentials).

Extends ``hqiv_phase_geometry_density`` with readouts already implied by the stack:

  • Clausius–Mossotti / refractive index n (binding-softness polarizability + ρ)
  • Dielectric constant ε_r ≈ n²
  • Phonon thermal conductivity k_th (stiffness from binding, ρ_curv, G_eff contact)
  • Ionic conductivity slot σ (activation from contact binding; carriers explicit)
  • Molar heat capacity C_p (contact-mode DOF × B_hom)
  • Latent heat L_fusion (melt cohesive × tetrahedral shell release)
  • Dynamic viscosity η (liquid Arrhenius from contact binding; solid → ∞)
  • Ice Ih birefringence Δn (hexagonal a,c anisotropy in CM)

Run:
  python3 scripts/hqiv_phase_material_response.py H2O --allotrope Ih
  python3 scripts/hqiv_phase_material_response.py H2O --phase liquid
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import asdict
from pathlib import Path
from typing import Any, Literal

_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

import hqiv_chemistry_tuft_dynamics as ctd
import hqiv_curvature_bond_state as cbs
import hqiv_dynamic_binding_chart as chart
import hqiv_electronic_valence_shells as evs
import hqiv_homogeneous_curvature_feedback as hcf
import hqiv_lean_physics_primitives as lean
import hqiv_phase_geometry_density as pgd
import hqiv_s2_binding_geometry as s2bg
import hqiv_thermodynamic_phase_from_tp as tptp
from hqiv_lab.coordination import IntermolecularMotif, infer_monomer_geometry
from hqiv_lab.spec import MoleculeSpec

AVOGADRO = pgd.AVOGADRO
BOHR_RADIUS_ANGSTROM = 0.529177210903
RYDBERG_EV = 13.605693122994
EV_TO_J = 1.602176634e-19
K_B = 1.380649e-23
AMU_KG = 1.66053906660e-27
ANGSTROM3_TO_CM3 = 1.0e-24

PhaseKind = Literal["solid", "liquid"]


def phase_lift_coeff(m: int) -> float:
    """Lean ``phaseLiftCoeff m = φ(m)/6 = 2(m+1)/6``."""
    return 2.0 * (max(m, 0) + 1) / 6.0


def _spec_for_molecule(molecule: str) -> MoleculeSpec:
    return MoleculeSpec.from_chart_name(molecule)


def optical_contact_theta_rad(molecule: str) -> float:
    """
    Contact phase θ for Clausius–Mossotti / G_eff optical slot.

    Uses TUFT ``dynamicCentreAngleRad`` (VSEPR bent-centre) — the same θ₀-normalized
    phase that enters ``phaseParticipationEta`` on the Compton IR window spine.
    """
    spec = _spec_for_molecule(molecule)
    mono = infer_monomer_geometry(spec)
    return ctd.dynamic_centre_angle_rad(mono.z_heavy, mono.n_bonds_at_heavy)


def optical_phase_eta(molecule: str) -> float:
    """η = θ/θ₀ — Lean ``phaseParticipationEta`` (drop-in for local-field slots)."""
    return s2bg.phase_participation_eta(optical_contact_theta_rad(molecule))


def optical_geff(molecule: str) -> float:
    """G_eff(η) = η^α on the optical contact."""
    return cbs.g_eff(optical_phase_eta(molecule))


def steric_domain_count(molecule: str) -> int:
    spec = _spec_for_molecule(molecule)
    mono = infer_monomer_geometry(spec)
    return max(mono.intermolecular_contacts, mono.n_bonds_at_heavy + mono.lone_pair_count)


def coordination_domain_count(molecule: str) -> int:
    """Domains entering Clausius–Mossotti local-field slots (may differ from steric winding)."""
    spec = _spec_for_molecule(molecule)
    mono = infer_monomer_geometry(spec)
    if mono.motif == IntermolecularMotif.LINEAR_CHAIN:
        return mono.intermolecular_contacts
    return steric_domain_count(molecule)


def intermolecular_motif(molecule: str) -> IntermolecularMotif:
    return infer_monomer_geometry(_spec_for_molecule(molecule)).motif


def optical_molecular_span_angstrom(molecule: str) -> float:
    """
    Characteristic polarizability span [Å].

    Linear H-bond chains use nn contact scale; others use covalent span sum.
    """
    spec = _spec_for_molecule(molecule)
    mono = infer_monomer_geometry(spec)
    cov = pgd.covalent_span_angstrom(molecule)
    if mono.motif == IntermolecularMotif.LINEAR_CHAIN:
        from hqiv_lab.packing import intermolecular_contact_distance_angstrom

        r_nn = intermolecular_contact_distance_angstrom(mono)
        dipole_span = r_nn / (1.0 + lean.ALPHA)
        core = math.sqrt(max(cov, 1e-6) * dipole_span)
        halogen_dress = 1.0 + lean.GAMMA * (mono.z_heavy / 8.0)
        return core * halogen_dress
    return cov


def binding_softness_ev(molecule: str) -> float:
    """Covalent gap scale for polarizability (softer for single-bond chains)."""
    e_bond = binding_ev_per_covalent_bond(molecule)
    if intermolecular_motif(molecule) == IntermolecularMotif.LINEAR_CHAIN:
        return e_bond / (1.0 + lean.ALPHA)
    return e_bond


def hqiv_polarizability_angstrom3(
    molecule: str,
    rho_curv: float,
    xi: float,
) -> float:
    """
    HQIV molecular polarizability volume [Å³].

    α ∝ α_lattice · (r_span/a₀)³ · (E_Ryd / E_bond) · B_hom(ξ, ρ_curv) · G_eff(η).
    """
    span = optical_molecular_span_angstrom(molecule)
    e_bond = binding_softness_ev(molecule)
    r_ratio = span / BOHR_RADIUS_ANGSTROM
    alpha_dim = (
        lean.ALPHA
        * lean.STRONG_CHANNEL_FRACTION
        * (r_ratio**3)
        * (RYDBERG_EV / max(e_bond, 0.05))
    )
    motif = intermolecular_motif(molecule)
    geff = optical_geff(molecule)
    if motif in (
        IntermolecularMotif.TETRAHEDRAL_HBOND,
        IntermolecularMotif.PYRAMIDAL_HBOND,
    ):
        m_wind = max(steric_domain_count(molecule) - 1, 1)
        lift = phase_lift_coeff(m_wind)
        alpha_dim *= 1.0 + (lift - 1.0) * geff
    elif motif == IntermolecularMotif.LINEAR_CHAIN:
        alpha_dim *= geff * (1.0 + lean.GAMMA / 4.0)
    else:
        alpha_dim *= geff / math.sqrt(max(steric_domain_count(molecule), 1))
    return alpha_dim * (1.0 + rho_curv * lean.ALPHA) * (BOHR_RADIUS_ANGSTROM**3)


def binding_ev_per_covalent_bond(molecule: str) -> float:
    """Characteristic covalent gap from GMTKN55 atomization / dissociation reference."""
    for bench in chart.GMTKN55_SUITE:
        if bench.name.upper() == molecule.upper():
            n_bonds = max(len(bench.bonds), 1)
            return bench.reference_ev / n_bonds
    return 5.0


def intermolecular_binding_ev_per_contact(molecule: str) -> float:
    """Cohesive scale per intermolecular contact (bulk H₂O: 4 contacts)."""
    mat = pgd.material_scales_with_phase_geometry(molecule, bulk=True)
    inter = max(mat.intermolecular_contacts, 1)
    return mat.characteristic_binding_ev / inter


def clausius_mossotti_ratio(
    rho_g_cm3: float,
    molecular_weight_amu: float,
    alpha_mol_angstrom3: float,
    *,
    coordination_divisor: float,
) -> float:
    """
    (n² − 1)/(n² + 2) from number density and molecular polarizability.

    Local-field divisor encodes preferred phase orientation (H-bond vs isotropic liquid).
    """
    alpha_cm3 = alpha_mol_angstrom3 * ANGSTROM3_TO_CM3
    raw = (rho_g_cm3 / molecular_weight_amu) * AVOGADRO * alpha_cm3 / 3.0
    return raw / max(coordination_divisor, 1e-6)


def refractive_index_from_clausius_mossotti(cm: float) -> float:
    """Solve n from CM ratio; CM must stay below 1."""
    cm_clamped = min(max(cm, 0.0), 0.99)
    n_sq = (1.0 + 2.0 * cm_clamped) / (1.0 - cm_clamped)
    return math.sqrt(max(1.0, n_sq))


def dielectric_constant_from_refractive_index(n: float) -> float:
    return n * n


def fragment_atom_count(molecule: str) -> int:
    for bench in chart.GMTKN55_SUITE:
        if bench.name.upper() == molecule.upper():
            return len(bench.fragments)
    return 1


def phonon_thermal_conductivity_w_mk(
    molecule: str,
    cell: pgd.PhaseUnitCell,
    rho_curv: float,
    xi: float,
    *,
    temperature_k: float = 273.15,
) -> float:
    """
    k_th ≈ (1/3) ρ c_spec v_s ℓ · G_eff(θ_contact) · B_hom.

    v_s from intermolecular binding stiffness / mass density;
    ℓ ~ lattice spacing × order parameter (1 − ρ_curv/2).
    """
    rho_kg_m3 = pgd.density_g_cm3(cell) * 1000.0
    lattice_m = cell.a_angstrom * 1e-10
    vol_m3 = cell.volume_cm3 * 1e-6 / max(cell.molecules_per_cell, 1)
    e_contact_j = intermolecular_binding_ev_per_contact(molecule) * EV_TO_J
    stiffness = e_contact_j / max(vol_m3, 1e-36)
    v_s = math.sqrt(stiffness / max(rho_kg_m3, 1e-12))
    n_atoms = fragment_atom_count(molecule)
    mw_kg = cell.molecular_weight_amu * AMU_KG
    c_spec = 3.0 * K_B * n_atoms / max(mw_kg, 1e-30)
    ell = lattice_m * (1.0 - 0.5 * rho_curv)
    theta_contact = optical_contact_theta_rad(molecule)
    geff = cbs.outside_contact_coupling(theta_contact)
    b_hom = hcf.homogeneous_curvature_budget_at_xi(xi, rho_curv)
    return (1.0 / 3.0) * rho_kg_m3 * c_spec * v_s * ell * geff * b_hom


def ionic_conductivity_s_m(
    molecule: str,
    rho_curv: float,
    temperature_k: float,
    *,
    carrier_fraction: float = 0.0,
) -> float:
    """
    σ_ionic ∝ n_carrier · exp(−E_a/kT) · ρ_curv · G_eff.

    Pure neutral media: carrier_fraction = 0 → σ ≈ 0 (ultra-pure limit).
    """
    if carrier_fraction <= 0.0 or temperature_k <= 0.0:
        return 0.0
    e_a = intermolecular_binding_ev_per_contact(molecule) * EV_TO_J
    geff = cbs.g_eff(rho_curv)
    mobility_scale = 1.0e-7  # geometry slot [m²/(V·s)] — not a half-life fit
    n_carrier = carrier_fraction * pgd.AVOGADRO * 1.0e3  # mol-scale placeholder
    boltz = math.exp(-e_a / (K_B * temperature_k))
    return n_carrier * mobility_scale * boltz * rho_curv * geff


def clausius_mossotti_local_field_divisor(
    molecule: str,
    phase: PhaseKind,
) -> float:
    """
    Clausius–Mossotti local-field divisor from η = θ/θ₀ and motif.

    Liquid: tetrahedral ``1−c_R·η``; pyramidal ``·n²/4``; apolar ``·(1+(n−1)sc)``.
    Solid: Onsager ``n·φ(m)/6/G_eff`` (apolar/pyramidal); chain ``n/(2G_eff)``.
    """
    eta = optical_phase_eta(molecule)
    motif = intermolecular_motif(molecule)
    n_dom = max(coordination_domain_count(molecule), 1)
    geff = max(optical_geff(molecule), 1e-6)
    base = max(1.0 - lean.C_RINDLER_SHARED * eta, 1e-6)

    if phase == "liquid":
        if motif == IntermolecularMotif.TETRAHEDRAL_HBOND:
            return base
        if motif == IntermolecularMotif.PYRAMIDAL_HBOND:
            return max(base * n_dom * n_dom / 4.0, 1e-6)
        if motif == IntermolecularMotif.LINEAR_CHAIN:
            return max(base * (1.0 + lean.STRONG_CHANNEL_FRACTION), 1e-6)
        return max(base * (1.0 + (n_dom - 1) * lean.STRONG_CHANNEL_FRACTION), 1e-6)

    if motif == IntermolecularMotif.LINEAR_CHAIN:
        return max(n_dom / (2.0 * geff), 1e-6)
    if motif in (
        IntermolecularMotif.APOLAR_CLOSE_PACK,
        IntermolecularMotif.PYRAMIDAL_HBOND,
        IntermolecularMotif.DIATOMIC,
    ):
        return n_dom * phase_lift_coeff(n_dom - 1) / geff
    return 1.0


def phase_orientation_cm_factor(
    molecule: str,
    phase: PhaseKind,
    allotrope: str | None,
    *,
    rho_curv: float = 0.0,
) -> float:
    """
    Oriented bulk CM multiplier from η and steric winding (replaces per-species tables).

    Ice Ih / H-bond solids: ``phaseLiftCoeff(n_domains−1) · G_eff(η)``.
    """
    if phase != "solid":
        return 1.0
    motif = intermolecular_motif(molecule)
    geff = optical_geff(molecule)
    n_dom = max(steric_domain_count(molecule), 1)
    lift = phase_lift_coeff(n_dom - 1)
    if motif == IntermolecularMotif.TETRAHEDRAL_HBOND:
        al = (allotrope or "Ih").upper()
        if al in ("IH", "ICE_IH", "I_H"):
            return lift * geff * (1.0 + lean.GAMMA / 4.0)
        return geff
    if motif == IntermolecularMotif.LINEAR_CHAIN:
        return 1.0 + (lift - 1.0) * geff
    if motif == IntermolecularMotif.PYRAMIDAL_HBOND:
        return 1.0 + (lift - 1.0) * geff * (1.0 + lean.GAMMA / 4.0)
    return geff


def coordination_local_field_divisor(molecule: str, phase: PhaseKind) -> float:
    """Backward-compatible alias for the θ-derived local-field divisor."""
    return clausius_mossotti_local_field_divisor(molecule, phase)


def molar_heat_capacity_j_per_mol_k(
    molecule: str,
    rho_curv: float,
    xi: float,
    *,
    phase: PhaseKind,
) -> float:
    """
    C_p,mol ≈ (3 × n_atoms) R × B_hom; solids add α lattice phonon channel.
    """
    n_atoms = fragment_atom_count(molecule)
    dof = 3.0 * n_atoms
    if phase == "solid":
        dof *= 1.0 + lean.ALPHA
    c_mol = dof * K_B * AVOGADRO
    b_hom = hcf.homogeneous_curvature_budget_at_xi(xi, rho_curv)
    return c_mol * b_hom


def latent_heat_fusion_j_per_mol(
    molecule: str,
    *,
    allotrope: str | None = None,
) -> float:
    """
    L_f ≈ E_melt × N_A × n_inter × (φ(3)/6)² / (1+α).

    Melt cohesive from thermodynamic spine; squared shell-opening for network release.
    """
    mat = pgd.material_scales_with_phase_geometry(molecule, allotrope=allotrope, bulk=True)
    e_melt_ev = tptp.melt_cohesive_ev(mat)
    inter = max(mat.intermolecular_contacts, 1)
    shell_release = lean.PHASE_LIFT_3**2 / (1.0 + lean.ALPHA)
    return e_melt_ev * EV_TO_J * AVOGADRO * inter * shell_release


def dynamic_viscosity_pas(
    molecule: str,
    rho_curv: float,
    *,
    phase: PhaseKind,
    temperature_k: float,
    allotrope: str | None = None,
) -> float:
    """
    Eyring slot: η ≈ τ · σ with τ = (ℏ/kT) exp(E_melt/kT), σ from contact stiffness / span³.

    E_melt is the same cohesive scale as T_sl (not a separate fit). Solid → ∞.
    """
    if phase == "solid" or temperature_k <= 0.0:
        return float("inf")
    mat = pgd.material_scales_with_phase_geometry(
        molecule, allotrope=allotrope, bulk=(phase == "solid")
    )
    e_rearrange = tptp.melt_cohesive_ev(mat) * EV_TO_J
    hbar = 1.054571817e-34
    span_m = pgd.covalent_span_angstrom(molecule) * 1e-10
    tau = (hbar / (K_B * temperature_k)) * math.exp(
        e_rearrange / (K_B * temperature_k)
    )
    stress_scale = (
        intermolecular_binding_ev_per_contact(molecule) * EV_TO_J / max(span_m**3, 1e-36)
    )
    return tau * stress_scale * cbs.g_eff(rho_curv) / (6.0 * math.pi)


def hexagonal_optical_cm_factors(cell: pgd.PhaseUnitCell) -> tuple[float, float]:
    """
    Small uniaxial CM split from c/a ratio (ice Ih birefringence ~10⁻³).

    Returns (f_ordinary_basal, f_extraordinary_axial) multipliers on isotropic CM.
    """
    c_a = (cell.c_angstrom or cell.a_angstrom) / max(cell.a_angstrom, 1e-6)
    split = (c_a - 1.0) * lean.C_RINDLER_SHARED / 20.0
    return 1.0 + split, max(1.0 - split, 1e-6)


def birefringent_refractive_indices(
    molecule: str,
    cell: pgd.PhaseUnitCell,
    rho_curv: float,
    xi: float,
    *,
    allotrope: str | None = None,
) -> tuple[float, float, float]:
    """
    Uniaxial ice Ih: n_o (ordinary, basal) and n_e (extraordinary, c-axis).

    Returns (n_ordinary, n_extraordinary, delta_n).
    """
    rho_g = pgd.density_g_cm3(cell)
    alpha = hqiv_polarizability_angstrom3(molecule, rho_curv, xi)
    coord_div = coordination_local_field_divisor(molecule, "solid")
    cm_iso = clausius_mossotti_ratio(
        rho_g, cell.molecular_weight_amu, alpha, coordination_divisor=coord_div
    )
    cm_iso *= phase_orientation_cm_factor(molecule, "solid", allotrope, rho_curv=rho_curv)
    f_basal, f_axial = hexagonal_optical_cm_factors(cell)
    n_o = refractive_index_from_clausius_mossotti(cm_iso * f_basal)
    n_e = refractive_index_from_clausius_mossotti(cm_iso * f_axial)
    return n_o, n_e, abs(n_o - n_e)


def refractive_index_solid_readout(
    molecule: str,
    cell: pgd.PhaseUnitCell,
    *,
    allotrope: str | None = None,
) -> float:
    """Solid n from CM + η orientation without re-entering melt / allotrope scoring."""
    import hqiv_thermodynamic_phase_from_tp as tptp

    al = allotrope or cell.allotrope
    rho_g = pgd.density_g_cm3(cell)
    rho_curv = pgd.curvature_density_fraction(rho_g, molecule)
    xi = tptp.material_scales_from_network_name(molecule).contact_xi
    coord_div = coordination_local_field_divisor(molecule, "solid")
    alpha = hqiv_polarizability_angstrom3(molecule, rho_curv, xi)
    cm_raw = clausius_mossotti_ratio(
        rho_g, cell.molecular_weight_amu, alpha, coordination_divisor=coord_div
    )
    cm = cm_raw * phase_orientation_cm_factor(molecule, "solid", al, rho_curv=rho_curv)
    return refractive_index_from_clausius_mossotti(cm)


def material_response_readout(
    molecule: str,
    *,
    allotrope: str | None = None,
    phase: PhaseKind = "solid",
    temperature_k: float = 273.15,
    carrier_fraction: float = 0.0,
) -> dict[str, Any]:
    """Full response witness: n, ε_r, k_th, σ slot."""
    import hqiv_thermodynamic_phase_from_tp as tptp

    if allotrope is None:
        allotrope = pgd.preferred_allotrope(molecule, temperature_k=temperature_k)
    cell = pgd.phase_unit_cell(molecule, allotrope, temperature_k=temperature_k)
    if phase == "liquid":
        rho_g = pgd.liquid_reference_density_g_cm3(molecule)
        rho_curv = pgd.curvature_density_fraction(rho_g, molecule)
    else:
        rho_g = pgd.density_g_cm3(cell)
        rho_curv = pgd.curvature_density_fraction(rho_g, molecule)
    xi = tptp.material_scales_from_network_name(molecule).contact_xi
    coord_div = coordination_local_field_divisor(molecule, phase)
    alpha = hqiv_polarizability_angstrom3(molecule, rho_curv, xi)
    cm_raw = clausius_mossotti_ratio(
        rho_g, cell.molecular_weight_amu, alpha, coordination_divisor=coord_div
    )
    cm = cm_raw * phase_orientation_cm_factor(molecule, phase, allotrope, rho_curv=rho_curv)
    n = refractive_index_from_clausius_mossotti(cm)
    eps_r = dielectric_constant_from_refractive_index(n)
    k_th = phonon_thermal_conductivity_w_mk(
        molecule, cell, rho_curv, xi, temperature_k=temperature_k
    )
    sigma = ionic_conductivity_s_m(
        molecule, rho_curv, temperature_k, carrier_fraction=carrier_fraction
    )
    c_p = molar_heat_capacity_j_per_mol_k(molecule, rho_curv, xi, phase=phase)
    l_fusion = latent_heat_fusion_j_per_mol(molecule, allotrope=allotrope)
    eta = dynamic_viscosity_pas(
        molecule,
        rho_curv,
        phase=phase,
        temperature_k=temperature_k,
        allotrope=allotrope,
    )
    n_o, n_e, delta_n = (float("nan"), float("nan"), 0.0)
    if (
        phase == "solid"
        and molecule.upper() == "H2O"
        and cell.crystal_system == "hexagonal"
    ):
        n_o, n_e, delta_n = birefringent_refractive_indices(
            molecule, cell, rho_curv, xi, allotrope=allotrope
        )
    return {
        "molecule": molecule,
        "phase": phase,
        "allotrope": cell.allotrope,
        "temperature_K": temperature_k,
        "density_g_cm3": rho_g,
        "curvature_density_fraction": rho_curv,
        "contact_xi": xi,
        "optical_contact_theta_rad": optical_contact_theta_rad(molecule),
        "optical_phase_eta": optical_phase_eta(molecule),
        "optical_geff": optical_geff(molecule),
        "coordination_divisor": coord_div,
        "polarizability_angstrom3": alpha,
        "clausius_mossotti_ratio": cm,
        "clausius_mossotti_ratio_raw": cm_raw,
        "phase_orientation_cm_factor": phase_orientation_cm_factor(
            molecule, phase, allotrope, rho_curv=rho_curv
        ),
        "refractive_index": n,
        "dielectric_constant": eps_r,
        "thermal_conductivity_W_mK": k_th,
        "ionic_conductivity_S_m": sigma,
        "molar_heat_capacity_J_per_mol_K": c_p,
        "latent_heat_fusion_J_per_mol": l_fusion,
        "dynamic_viscosity_Pa_s": eta,
        "refractive_index_ordinary": n_o,
        "refractive_index_extraordinary": n_e,
        "birefringence_delta_n": delta_n,
        "B_hom": hcf.homogeneous_curvature_budget_at_xi(xi, rho_curv),
        "unit_cell": asdict(cell),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Phase geometry material response readout.")
    parser.add_argument("molecule", nargs="?", default="H2O")
    parser.add_argument(
        "--allotrope",
        default=None,
        help="Derived allotrope label (default: species preferred at --temperature-K)",
    )
    parser.add_argument("--phase", choices=("solid", "liquid"), default="solid")
    parser.add_argument("--temperature-K", type=float, default=273.15)
    parser.add_argument("--json-out", type=Path, default=None)
    args = parser.parse_args()
    out = material_response_readout(
        args.molecule,
        allotrope=args.allotrope,
        phase=args.phase,
        temperature_k=args.temperature_K,
    )
    print(f"{out['molecule']} {out['phase']} ({out['allotrope']}) @ {out['temperature_K']:.2f} K")
    print(f"  n = {out['refractive_index']:.4f}   ε_r = {out['dielectric_constant']:.4f}")
    print(f"  k_th = {out['thermal_conductivity_W_mK']:.4f} W/(m·K)")
    print(f"  σ_ionic = {out['ionic_conductivity_S_m']:.3e} S/m")
    print(f"  C_p,mol = {out['molar_heat_capacity_J_per_mol_K']:.1f} J/(mol·K)")
    print(f"  L_fusion = {out['latent_heat_fusion_J_per_mol']:.2e} J/mol")
    if out["phase"] == "liquid" and math.isfinite(out["dynamic_viscosity_Pa_s"]):
        print(f"  η = {out['dynamic_viscosity_Pa_s']:.3e} Pa·s")
    if out["birefringence_delta_n"] > 0.0:
        print(
            f"  birefringence Δn = {out['birefringence_delta_n']:.5f}  "
            f"(n_o={out['refractive_index_ordinary']:.4f}, n_e={out['refractive_index_extraordinary']:.4f})"
        )
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(out, indent=2) + "\n")


if __name__ == "__main__":
    main()

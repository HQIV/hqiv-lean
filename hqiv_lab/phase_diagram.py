"""
Generalized HQIV phase diagrams: (T, P) → phase, end-member mixture, ρ_curv.

First-principles source: motif + allotrope geometry + cohesive ladder.
External observations (Sciortino LLCP, Li two-state) live in comparison audits only.

Lean mirror: ``Hqiv.QuantumChemistry.PhaseDiagramMixture``.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from enum import Enum
from functools import lru_cache
from typing import Any

from hqiv_lab._scripts import ensure_scripts_on_path

ensure_scripts_on_path()

import hqiv_lean_physics_primitives as lean
import hqiv_chemistry_coupled_readout as ccr
import hqiv_phase_geometry_density as pgd
import hqiv_thermodynamic_phase_from_tp as tptp
from hqiv_lab.coordination import IntermolecularMotif, MonomerGeometry, infer_monomer_geometry
from hqiv_lab.spec import MoleculeSpec, resolve_spec

K_B_EV_PER_K = tptp.K_B_EV_PER_K
STP_PRESSURE_PA = tptp.STP_PRESSURE_PA
ALPHA = lean.ALPHA
GAMMA = lean.GAMMA


class LiquidSubphase(str, Enum):
    """LDL/HDL-style subphase inside a liquid branch."""

    LOW_DENSITY = "low_density"
    HIGH_DENSITY = "high_density"
    MIXTURE = "mixture"
    INDETERMINATE = "indeterminate"


@dataclass(frozen=True)
class PhaseEndMember:
    """One branch on a phase diagram (geometry witness)."""

    label: str
    rho_curv: float
    coordination_fraction: float


@dataclass(frozen=True)
class MixtureComponent:
    """One species in a multi-component box."""

    name: str
    mole_fraction: float


@dataclass(frozen=True)
class PhaseDiagramPoint:
    """Full readout at one (T, P) state point."""

    temperature_k: float
    pressure_pa: float
    derived_phase: str
    liquid_subphase: LiquidSubphase | None
    f_low_density: float | None
    rho_curv: float
    coordination_fraction: float
    contact_persistence: float
    periodic_weight: float
    T_melt_K: float
    T_boil_K: float
    xi: float
    notes: str
    f_low_density_one_way: float | None = None
    branch_coupling_level: str = "feed_forward"
    branch_coupling_target: float | None = None


def supports_two_liquid_branch(motif: IntermolecularMotif) -> bool:
    """Lean ``supportsTwoLiquidBranch``."""
    return motif in (
        IntermolecularMotif.TETRAHEDRAL_HBOND,
        IntermolecularMotif.PYRAMIDAL_HBOND,
        IntermolecularMotif.POLYOL_HBOND,
    )


def metastable_liquid_kinetic_floor_k(t_melt_k: float) -> float:
    """Lean ``T_melt · γ·α`` — below this, supercooled liquid kinetically freezes to solid."""
    return t_melt_k * GAMMA * ALPHA


def metastable_liquid_allowed(
    temperature_k: float,
    pressure_pa: float,
    t_melt_k: float,
    material: tptp.MaterialThermodynamicScales,
) -> bool:
    """Python mirror of ``_metastable_liquid_allowed`` in thermodynamic phase script."""
    return tptp._metastable_liquid_allowed(temperature_k, pressure_pa, t_melt_k, material)


def tetrahedral_melt_density_ratio(n_inter: int = 4) -> float:
    """Python mirror of Lean ``tetrahedralMeltDensityRatio``."""
    n = max(n_inter, 1)
    overlap = max(0.5, 1.0 - GAMMA * lean.STRONG_CHANNEL_FRACTION / n)
    return overlap * lean.PHASE_LIFT_3 / (1.0 + ALPHA)


def end_members_for_molecule(
    molecule: str,
    *,
    mono: MonomerGeometry | None = None,
) -> tuple[PhaseEndMember, PhaseEndMember]:
    """
    Low- and high-density liquid end members from motif geometry (not MD).

    Low: coordination-heavy tetrahedral melt ratio.
    High: melt-comparison lattice release (ρ = 1).
    """
    if mono is None:
        mono = infer_monomer_geometry(resolve_spec(molecule))
    rho_low = min(1.0, max(0.0, tetrahedral_melt_density_ratio(mono.intermolecular_contacts)))
    low = PhaseEndMember(
        label=f"{molecule}_LDL",
        rho_curv=rho_low,
        coordination_fraction=1.0,
    )
    high = PhaseEndMember(
        label=f"{molecule}_HDL",
        rho_curv=pgd.melt_comparison_curvature_density_fraction(),
        coordination_fraction=pgd.melt_comparison_curvature_density_fraction(),
    )
    return low, high


def liquid_mixture_curvature_fraction(f: float, rho_low: float, rho_high: float) -> float:
    """Lean ``liquidMixtureCurvatureFraction``."""
    f_cl = min(1.0, max(0.0, f))
    return min(1.0, max(0.0, f_cl * rho_low + (1.0 - f_cl) * rho_high))


def _cohesive_scales_ev(material: tptp.MaterialThermodynamicScales) -> tuple[float, float]:
    """LDL-like (coordination-heavy) vs HDL-like (full melt release) cohesive scales [eV]."""
    e_ldl = tptp.intermolecular_cohesive_ev(material)
    e_hdl = tptp.melt_cohesive_ev(material)
    return e_ldl, e_hdl


def _resolve_molecule_name(material: tptp.MaterialThermodynamicScales, molecule: str | None) -> str:
    if molecule is not None:
        key = molecule.strip().upper()
        return "H2O" if key in ("H2O", "WATER") else molecule
    name = material.name.upper()
    if "H2O" in name or name == "WATER":
        return "H2O"
    if name.startswith("MIXTURE("):
        return name.split("(")[1].split(":")[0].strip()
    return material.name.split("_")[0]


def outside_curvature_mixture_dress(
    rho_curv_mix: float,
    xi: float,
    molecule: str,
) -> tuple[float, float, float]:
    """
    Homogeneous + outside dress at mixture ρ.

    Returns ``(B_hom, G_eff(θ) at ρ, liquidCohesiveOutsideFeedback slot)``.

    Lean: ``homogeneousCurvatureBudgetAtXi``, ``scaleOutsideCouplingForMediumDensity``,
    ``liquidCohesiveOutsideFeedback``.
    """
    import hqiv_chemistry_tuft_dynamics as ctd
    import hqiv_curvature_bond_state as cbs
    import hqiv_homogeneous_curvature_feedback as hcf

    spec = resolve_spec(molecule)
    mono = infer_monomer_geometry(spec)
    theta = ctd.dynamic_centre_angle_rad(mono.z_heavy, mono.n_bonds_at_heavy)
    rho = min(1.0, max(0.0, rho_curv_mix))
    b_hom = hcf.homogeneous_curvature_budget_at_xi(xi, rho)
    geff_theta = cbs.outside_contact_coupling(theta)
    geff_rho = cbs.scale_outside_coupling_for_medium_density(geff_theta, rho)
    homogeneous_fb = GAMMA * ALPHA * (b_hom - 1.0)
    outside_fb = GAMMA * ALPHA * max(geff_rho - 1.0, 0.0) * abs(b_hom - 1.0)
    return b_hom, geff_rho, homogeneous_fb + outside_fb


def cohesive_delta_ev_bare(
    temperature_k: float,
    pressure_pa: float,
    material: tptp.MaterialThermodynamicScales,
) -> float:
    """Undressed LDL/HDL Boltzmann gap (legacy seed)."""
    e_ldl, e_hdl = _cohesive_scales_ev(material)
    k_t = max(K_B_EV_PER_K * max(temperature_k, 1e-30), 1e-30)
    p_ratio = max(pressure_pa, 0.0) / STP_PRESSURE_PA
    return e_ldl - e_hdl + GAMMA * k_t * (p_ratio - 1.0) * ALPHA


HOH_ANGLE_TETRAHEDRAL_DEG = 109.47122063449069  # cos θ = −1/3, VSEPRFromBalance
# Comparison quarantine — gas-phase H₂O H–O–H (not PDG; molecular spectroscopy / NIST CCCBDB).
HOH_ANGLE_GAS_REFERENCE_DEG = 104.478  # NIST CCCBDB median; Hoy & Bunker 1979 equilibrium
HOH_ANGLE_GAS_REFERENCE_UNC_DEG = 0.01  # practical comparison band (±0.01°)
HOH_ANGLE_GAS_REFERENCE_RANGE_DEG = (104.45, 104.51)  # literature span (see WATER_HOH_ANGLE_OBSERVATIONS)

# External observations — grade HQIV readouts only; never derivation inputs.
WATER_HOH_ANGLE_OBSERVATIONS: tuple[dict[str, Any], ...] = (
    {
        "source": "Hoy & Bunker, J. Mol. Spectrosc. 1979",
        "doi": "10.1016/0022-2852(79)90019-5",
        "bibkey": "hoy1979waterRotBend",
        "label": "equilibrium structure θe (rotovibrational fit)",
        "theta_deg": 104.4776,
        "sigma_deg": 0.0019,
        "phase": "gas",
        "structure": "equilibrium",
        "role": "comparison_only",
    },
    {
        "source": "NIST CCCBDB (H2O, CAS 7732-18-5)",
        "url": "https://cccbdb.nist.gov/expgeom2.asp?casno=7732185&charge=0",
        "bibkey": "nistCCCBDBwaterH2O",
        "label": "ground-state effective angle (aggregated)",
        "theta_deg": 104.478,
        "sigma_deg": 0.01,
        "phase": "gas",
        "structure": "ground_vibrational",
        "role": "comparison_only",
        "primary_comparison": True,
        "note": "Arena median comparison target; cites Hoy & Bunker 1979 among others",
    },
    {
        "source": "Cook et al., J. Mol. Struct. 1974",
        "doi": "10.1016/0022-2860(74)90261-6",
        "bibkey": "cook1974waterMicrowave",
        "label": "average ground vibrational structure 〈θ〉",
        "theta_deg": 104.50,
        "sigma_deg": 0.05,
        "phase": "gas",
        "structure": "average",
        "role": "comparison_only",
    },
    {
        "source": "Benedict et al., J. Chem. Phys. 1956",
        "doi": "10.1063/1.1742588",
        "bibkey": "benedict1956waterRotation",
        "label": "early microwave rotation spectrum (effective θ)",
        "theta_deg": 104.5,
        "sigma_deg": 0.1,
        "phase": "gas",
        "structure": "effective",
        "role": "comparison_only",
    },
)


def hoh_angle_tetrahedral_deg() -> float:
    """LDL end member: ``centreAngleRadFromDomains 4`` (VSEPR spine)."""
    import hqiv_chemistry_tuft_dynamics as ctd

    return math.degrees(ctd.centre_angle_rad_from_domains(4))


def hoh_angle_dynamic_gas_deg() -> float:
    """Current HQIV gas-phase derivation: ``dynamicCentreAngleRad 8 2``."""
    import hqiv_chemistry_tuft_dynamics as ctd

    return math.degrees(ctd.dynamic_centre_angle_rad(8, 2))


def hoh_angle_mixture_deg(f_ldl: float) -> float:
    """
    Local H–O–H angle from LDL/HDL mixture fraction.

    LDL → θ_tet (109.47° network reference); HDL → θ_dyn (gas-phase dress today).
    Refinement R-θ replaces θ_dyn with torque-tree θ* when proved.
    """
    f = min(1.0, max(0.0, f_ldl))
    theta_ldl = hoh_angle_tetrahedral_deg()
    theta_hdl = hoh_angle_dynamic_gas_deg()
    return f * theta_ldl + (1.0 - f) * theta_hdl


def hoh_angle_witness_row(f_ldl: float) -> dict[str, float | bool]:
    """Audit row: tetrahedral vs dynamic vs mixture vs comparison ref."""
    theta_mix = hoh_angle_mixture_deg(f_ldl)
    theta_dyn = hoh_angle_dynamic_gas_deg()
    lo, hi = HOH_ANGLE_GAS_REFERENCE_RANGE_DEG
    return {
        "f_low_density": f_ldl,
        "theta_tetrahedral_deg": hoh_angle_tetrahedral_deg(),
        "theta_dynamic_gas_deg": theta_dyn,
        "theta_mixture_deg": theta_mix,
        "theta_gas_reference_deg": HOH_ANGLE_GAS_REFERENCE_DEG,
        "theta_gas_reference_unc_deg": HOH_ANGLE_GAS_REFERENCE_UNC_DEG,
        "theta_gas_reference_range_deg": list(HOH_ANGLE_GAS_REFERENCE_RANGE_DEG),
        "theta_dyn_within_comparison_band": lo <= theta_dyn <= hi,
        "theta_tet_minus_ref_deg": hoh_angle_tetrahedral_deg() - HOH_ANGLE_GAS_REFERENCE_DEG,
        "theta_dyn_minus_ref_deg": theta_dyn - HOH_ANGLE_GAS_REFERENCE_DEG,
        "theta_mix_minus_ref_deg": theta_mix - HOH_ANGLE_GAS_REFERENCE_DEG,
    }


FARADAY_J_PER_EV_MOL = 96485.33212


def mixture_latent_barrier_factor(f: float) -> float:
    """Lean ``mixtureLatentBarrierFactor`` — smears first-order cost in mixed LDL/HDL."""
    f_cl = min(1.0, max(0.0, f))
    return f_cl * (1.0 - f_cl)


def ldl_hdl_conversion_barrier_ev_per_contact(
    molecule: str,
    material: tptp.MaterialThermodynamicScales,
) -> float:
    """
    Partial latent barrier between liquid branches (not full solid→liquid ``L_f``).

    Scales HQIV ``latentHeatFusionSlot`` by end-member ρ contrast / ``n_inter``.
    """
    import hqiv_phase_material_response as pmr

    mol = _resolve_molecule_name(material, molecule)
    low, high = end_members_for_molecule(mol)
    branch_fraction = max(high.rho_curv - low.rho_curv, 0.0)
    allotrope = "Ih" if mol.upper() == "H2O" else None
    l_j_mol = pmr.latent_heat_fusion_j_per_mol(mol, allotrope=allotrope)
    l_ev_mol = l_j_mol / FARADAY_J_PER_EV_MOL
    inter = max(material.intermolecular_contacts, 1)
    return l_ev_mol * branch_fraction / inter


@lru_cache(maxsize=32)
def _ldl_hdl_conversion_barrier_cached(
    molecule: str,
    intermolecular_contacts: int,
    contact_xi: float,
) -> float:
    """Cache the latent branch barrier for repeated free-energy grid scans."""
    material = tptp.material_scales_bulk_h2o() if molecule.upper() == "H2O" else tptp.material_scales_from_network_name(molecule)
    # Preserve the caller's branch-contact count when mixtures average material scales.
    material = tptp.MaterialThermodynamicScales(
        name=material.name,
        characteristic_binding_ev=material.characteristic_binding_ev,
        contact_points=material.contact_points,
        molecular_weight_amu=material.molecular_weight_amu,
        intermolecular_contacts=max(intermolecular_contacts, 1),
        contact_xi=contact_xi,
        bulk_condensed=material.bulk_condensed,
        medium_density_fraction=material.medium_density_fraction,
        refractive_index_solid=material.refractive_index_solid,
        intermolecular_motif=material.intermolecular_motif,
        z_heavy=material.z_heavy,
    )
    return ldl_hdl_conversion_barrier_ev_per_contact(molecule, material)


def liquid_branch_barrier_potential_ev(
    f: float,
    molecule: str,
    material: tptp.MaterialThermodynamicScales,
) -> float:
    """Lean ``liquidBranchBarrierPotential`` — (1−2f)·L_branch on cohesive Δμ."""
    l_branch = ldl_hdl_conversion_barrier_ev_per_contact(molecule, material)
    f_cl = min(1.0, max(0.0, f))
    return (1.0 - 2.0 * f_cl) * l_branch


def cohesive_delta_ev_dressed(
    temperature_k: float,
    pressure_pa: float,
    material: tptp.MaterialThermodynamicScales,
    rho_curv_mix: float,
    *,
    molecule: str | None = None,
    f_ldl: float | None = None,
) -> float:
    """
    LDL/HDL cohesive gap with outside curvature + mixture latent-barrier feedback.

    ``ΔE = (E_ldl − E_hdl) + γ·α·(B_hom−1) + (1−2f)·L_branch + pressure tilt``.
    """
    e_ldl, e_hdl = _cohesive_scales_ev(material)
    mol = _resolve_molecule_name(material, molecule)
    b_hom, _geff_rho, curvature_fb = outside_curvature_mixture_dress(
        rho_curv_mix, material.contact_xi, mol
    )
    k_t = max(K_B_EV_PER_K * max(temperature_k, 1e-30), 1e-30)
    p_ratio = max(pressure_pa, 0.0) / STP_PRESSURE_PA
    pressure_tilt = GAMMA * k_t * (p_ratio - 1.0) * ALPHA * b_hom
    barrier = (
        liquid_branch_barrier_potential_ev(f_ldl, mol, material)
        if f_ldl is not None
        else 0.0
    )
    return (e_ldl - e_hdl) + curvature_fb + barrier + pressure_tilt


def two_state_mixing_entropy_shape(f: float) -> float:
    """Dimensionless ``f log f + (1-f) log(1-f)`` with endpoint limits."""
    f_cl = min(1.0, max(0.0, f))
    if f_cl <= 0.0 or f_cl >= 1.0:
        return 0.0
    return f_cl * math.log(f_cl) + (1.0 - f_cl) * math.log(1.0 - f_cl)


def liquid_branch_free_energy_ev(
    f: float,
    temperature_k: float,
    pressure_pa: float,
    material: tptp.MaterialThermodynamicScales,
    *,
    molecule: str | None = None,
    local_coordination_excess: float = 0.0,
    l_branch_ev: float | None = None,
) -> float:
    """
    HQIV two-branch free energy for LDL/HDL fraction ``f``.

    ``F = f·ΔE + L_branch·f(1−f) + kT·[f log f + (1−f)log(1−f)]`` plus the
    local-defect tilt ``−δB·f``.  Comparisons (Kim/Sciortino/Li) do not enter.
    """
    mol = _resolve_molecule_name(material, molecule)
    low, high = end_members_for_molecule(mol)
    f_cl = min(1.0, max(0.0, f))
    rho_mix = liquid_mixture_curvature_fraction(f_cl, low.rho_curv, high.rho_curv)
    # Delta excludes the explicit (1−2f)L derivative because F carries L·f(1−f).
    delta = cohesive_delta_ev_dressed(
        temperature_k,
        pressure_pa,
        material,
        rho_mix,
        molecule=mol,
        f_ldl=None,
    )
    defect_tilt = GAMMA * lean.STRONG_CHANNEL_FRACTION * max(local_coordination_excess, 0.0)
    l_branch = (
        l_branch_ev
        if l_branch_ev is not None
        else ldl_hdl_conversion_barrier_ev_per_contact(mol, material)
    )
    k_t = max(K_B_EV_PER_K * max(temperature_k, 1e-30), 1e-30)
    return (
        f_cl * (delta - defect_tilt)
        + l_branch * mixture_latent_barrier_factor(f_cl)
        + k_t * two_state_mixing_entropy_shape(f_cl)
    )


def low_density_free_energy_minimum(
    temperature_k: float,
    pressure_pa: float,
    material: tptp.MaterialThermodynamicScales,
    *,
    molecule: str | None = None,
    local_coordination_excess: float = 0.0,
    grid_points: int = 400,
) -> dict[str, float]:
    """Deterministic minimizer for the Lean ``stationaryLowDensityFraction`` slot."""
    mol = _resolve_molecule_name(material, molecule)
    n = max(grid_points, 40)
    l_branch = _ldl_hdl_conversion_barrier_cached(
        mol,
        max(material.intermolecular_contacts, 1),
        float(material.contact_xi),
    )

    def energy(f: float) -> float:
        return liquid_branch_free_energy_ev(
            f,
            temperature_k,
            pressure_pa,
            material,
            molecule=mol,
            local_coordination_excess=local_coordination_excess,
            l_branch_ev=l_branch,
        )

    best_f = 0.0
    best_e = energy(0.0)
    for i in range(1, n + 1):
        f = i / n
        e = energy(f)
        if e < best_e:
            best_f = f
            best_e = e

    # Local ternary refinement around the best grid cell.
    lo = max(0.0, best_f - 1.0 / n)
    hi = min(1.0, best_f + 1.0 / n)
    for _ in range(32):
        m1 = lo + (hi - lo) / 3.0
        m2 = hi - (hi - lo) / 3.0
        if energy(m1) <= energy(m2):
            hi = m2
        else:
            lo = m1
    f_min = 0.5 * (lo + hi)
    e_min = energy(f_min)
    curvature = liquid_branch_free_energy_curvature_ev(
        f_min,
        temperature_k,
        pressure_pa,
        material,
        molecule=mol,
        local_coordination_excess=local_coordination_excess,
        l_branch_ev=l_branch,
    )
    return {
        "f_low_density": f_min,
        "free_energy_ev": e_min,
        "free_energy_curvature_ev": curvature,
        "latent_branch_barrier_ev": l_branch,
    }


def liquid_branch_free_energy_curvature_ev(
    f: float,
    temperature_k: float,
    pressure_pa: float,
    material: tptp.MaterialThermodynamicScales,
    *,
    molecule: str | None = None,
    local_coordination_excess: float = 0.0,
    eps: float = 1e-3,
    l_branch_ev: float | None = None,
) -> float:
    """Finite-difference ``∂²F/∂f²`` at fixed ``(T,P)`` for susceptibility proxies."""
    mol = _resolve_molecule_name(material, molecule)
    h = max(eps, 1e-5)
    f0 = min(1.0 - h, max(h, f))

    def energy(x: float) -> float:
        return liquid_branch_free_energy_ev(
            x,
            temperature_k,
            pressure_pa,
            material,
            molecule=mol,
            local_coordination_excess=local_coordination_excess,
            l_branch_ev=l_branch_ev,
        )

    return (energy(f0 + h) - 2.0 * energy(f0) + energy(f0 - h)) / (h * h)


def widom_second_order_window_center_k(t_melt_k: float) -> float:
    """Lean ``widomSecondOrderWindowCenter``: ``T_melt·(1−γ²)``."""
    return t_melt_k * (1.0 - GAMMA * GAMMA)


def widom_second_order_window_width_k(t_melt_k: float) -> float:
    """Lean ``widomSecondOrderWindowWidth``: ``T_melt·α·γ²``."""
    return t_melt_k * ALPHA * GAMMA * GAMMA


def widom_second_order_window_weight(temperature_k: float, t_melt_k: float) -> float:
    """
    Derived supercooled anomaly gate.

    This is not fitted to Kim: center/width are ``γ²`` and ``α·γ²`` melt-scale slots.
    """
    center = widom_second_order_window_center_k(t_melt_k)
    width = max(widom_second_order_window_width_k(t_melt_k), 1e-30)
    x = (temperature_k - center) / width
    return math.exp(-(x * x))


def _boltzmann_f_ldl(delta_ev: float, k_t: float) -> float:
    if delta_ev >= 50.0:
        return 0.0
    if delta_ev <= -50.0:
        return 1.0
    return 1.0 / (1.0 + math.exp(delta_ev / k_t))


def low_density_liquid_fraction(
    temperature_k: float,
    pressure_pa: float,
    material: tptp.MaterialThermodynamicScales,
    *,
    molecule: str | None = None,
    local_coordination_excess: float = 0.0,
    max_iter: int = 12,
) -> float:
    """
    HQIV-derived mixture fraction toward the low-density end member.

    Derived as the minimizer of the two-branch HQIV free energy.
    """
    _ = max_iter  # retained for backward-compatible callers during the transition.
    return low_density_free_energy_minimum(
        temperature_k,
        pressure_pa,
        material,
        molecule=molecule,
        local_coordination_excess=local_coordination_excess,
    )["f_low_density"]


def classify_liquid_subphase(f_low: float) -> LiquidSubphase:
    if f_low >= 0.95:
        return LiquidSubphase.LOW_DENSITY
    if f_low <= 0.05:
        return LiquidSubphase.HIGH_DENSITY
    return LiquidSubphase.MIXTURE


def material_scales_for_spec(
    spec: MoleculeSpec,
    *,
    bulk: bool = False,
    temperature_k: float = 273.15,
) -> tptp.MaterialThermodynamicScales:
    if bulk and spec.name.upper() in ("H2O", "WATER"):
        return tptp.material_scales_bulk_h2o()
    mat = tptp.material_scales_from_network_name(spec.name)
    if bulk and supports_two_liquid_branch(infer_monomer_geometry(spec).motif):
        enriched = pgd.material_scales_with_phase_geometry(
            spec.name, bulk=True, temperature_k=temperature_k
        )
        return enriched
    return mat


def effective_mixture_material(
    components: tuple[MixtureComponent, ...],
    *,
    temperature_k: float = 273.15,
) -> tptp.MaterialThermodynamicScales:
    """Mole-fraction-weighted material scales; phase class follows dominant species."""
    if not components:
        raise ValueError("mixture requires at least one component")
    total = sum(c.mole_fraction for c in components)
    if total <= 0.0:
        raise ValueError("mixture mole fractions must sum positive")
    norm = [(c.name, c.mole_fraction / total) for c in components]
    mats: list[tuple[float, tptp.MaterialThermodynamicScales]] = []
    for name, frac in norm:
        spec = resolve_spec(name)
        mats.append((frac, material_scales_for_spec(spec, bulk=True, temperature_k=temperature_k)))
    dominant_name = max(norm, key=lambda x: x[1])[0]
    dominant = material_scales_for_spec(
        resolve_spec(dominant_name), bulk=True, temperature_k=temperature_k
    )
    be = sum(f * m.characteristic_binding_ev for f, m in mats)
    cp = max(1, round(sum(f * m.contact_points for f, m in mats)))
    inter = max(1, round(sum(f * m.intermolecular_contacts for f, m in mats)))
    mw = sum(f * m.molecular_weight_amu for f, m in mats)
    xi = sum(f * m.contact_xi for f, m in mats)
    rho_frac = sum(
        f * (m.medium_density_fraction if m.medium_density_fraction is not None else 0.0)
        for f, m in mats
    )
    label = "+".join(f"{c.name}:{c.mole_fraction:.3g}" for c in components)
    return tptp.MaterialThermodynamicScales(
        name=f"mixture({label})",
        characteristic_binding_ev=be,
        contact_points=cp,
        molecular_weight_amu=mw,
        intermolecular_contacts=inter,
        contact_xi=xi,
        bulk_condensed=dominant.bulk_condensed,
        medium_density_fraction=min(1.0, max(0.0, rho_frac)) if rho_frac > 0 else None,
        refractive_index_solid=dominant.refractive_index_solid,
        intermolecular_motif=dominant.intermolecular_motif,
        z_heavy=dominant.z_heavy,
    )


def _rho_curv_for_phase(
    *,
    phase: tptp.DerivedPhase,
    material: tptp.MaterialThermodynamicScales,
    molecule: str,
    temperature_k: float,
    pressure_pa: float,
    mono: MonomerGeometry | None = None,
) -> tuple[float, float | None, LiquidSubphase | None]:
    """Map derived phase to ρ_curv and optional LDL/HDL mixture tags."""
    low, high = end_members_for_molecule(molecule, mono=mono)
    if phase == tptp.DerivedPhase.METASTABLE_LIQUID:
        f_low = low_density_liquid_fraction(temperature_k, pressure_pa, material)
        rho = liquid_mixture_curvature_fraction(f_low, low.rho_curv, high.rho_curv)
        return rho, f_low, classify_liquid_subphase(f_low)
    if phase == tptp.DerivedPhase.LIQUID:
        return high.rho_curv, 0.0, LiquidSubphase.HIGH_DENSITY
    if phase == tptp.DerivedPhase.SOLID:
        rho = material.medium_density_fraction
        if rho is None:
            rho = low.rho_curv
        return min(1.0, max(0.0, rho)), None, None
    return 0.0, None, None


def mixture_curvature_fraction(
    components: tuple[MixtureComponent, ...],
    *,
    temperature_k: float,
    pressure_pa: float,
) -> float:
    """Per-component LDL/HDL fractions, mole-fraction weighted."""
    total = sum(c.mole_fraction for c in components)
    acc = 0.0
    for comp in components:
        x = comp.mole_fraction / max(total, 1e-30)
        spec = resolve_spec(comp.name)
        mono = infer_monomer_geometry(spec)
        low, high = end_members_for_molecule(spec.name, mono=mono)
        mat = material_scales_for_spec(spec, bulk=True, temperature_k=temperature_k)
        t_melt, _ = tptp.characteristic_temperatures_K(mat)
        if (
            temperature_k < t_melt
            and metastable_liquid_allowed(temperature_k, pressure_pa, t_melt, mat)
            and supports_two_liquid_branch(mono.motif)
        ):
            f_low = low_density_liquid_fraction(temperature_k, pressure_pa, mat)
        else:
            f_low = 0.0
        acc += x * liquid_mixture_curvature_fraction(f_low, low.rho_curv, high.rho_curv)
    return min(1.0, max(0.0, acc))


def phase_diagram_point(
    molecule_or_mixture: str | tuple[MixtureComponent, ...],
    *,
    temperature_k: float,
    pressure_pa: float = STP_PRESSURE_PA,
    bulk: bool = True,
) -> PhaseDiagramPoint:
    """
    Generalized (T, P) readout for a pure species or mole-fraction mixture.

    ``molecule_or_mixture`` — formula/name string, or tuple of ``MixtureComponent``.
    """
    if isinstance(molecule_or_mixture, tuple):
        components = molecule_or_mixture
        material = effective_mixture_material(components, temperature_k=temperature_k)
        dominant = max(components, key=lambda c: c.mole_fraction).name
        mono = infer_monomer_geometry(resolve_spec(dominant))
        env = tptp.ThermodynamicEnvironment(temperature_k, pressure_pa)
        state = tptp.derive_phase(env, material)
        t_melt, t_boil = tptp.characteristic_temperatures_K(material)
        branch_molecule = dominant
        if state.phase in (tptp.DerivedPhase.LIQUID, tptp.DerivedPhase.METASTABLE_LIQUID):
            rho = mixture_curvature_fraction(
                components, temperature_k=temperature_k, pressure_pa=pressure_pa
            )
            if state.phase == tptp.DerivedPhase.METASTABLE_LIQUID:
                f_low = low_density_liquid_fraction(temperature_k, pressure_pa, material)
                subphase = classify_liquid_subphase(f_low)
            else:
                f_low = 0.0
                subphase = LiquidSubphase.HIGH_DENSITY
        else:
            rho, f_low, subphase = _rho_curv_for_phase(
                phase=state.phase,
                material=material,
                molecule=dominant,
                temperature_k=temperature_k,
                pressure_pa=pressure_pa,
                mono=mono,
            )
    else:
        spec = resolve_spec(molecule_or_mixture)
        mono = infer_monomer_geometry(spec)
        material = material_scales_for_spec(spec, bulk=bulk, temperature_k=temperature_k)
        env = tptp.ThermodynamicEnvironment(temperature_k, pressure_pa)
        state = tptp.derive_phase(env, material)
        t_melt, t_boil = tptp.characteristic_temperatures_K(material)
        rho, f_low, subphase = _rho_curv_for_phase(
            phase=state.phase,
            material=material,
            molecule=spec.name,
            temperature_k=temperature_k,
            pressure_pa=pressure_pa,
            mono=mono,
        )
        branch_molecule = spec.name

    f_low_one_way = f_low
    branch_target = None
    branch_lam = 0.0
    if f_low is not None and subphase == LiquidSubphase.MIXTURE:
        branch_target = min(1.0, max(0.0, state.coordination_fraction))
        branch_lam = lean.GAMMA * lean.ALPHA
        f_low = ccr.branch_fraction_coupled_step(f_low, branch_target, branch_lam)
        low, high = end_members_for_molecule(branch_molecule, mono=mono)
        rho = liquid_mixture_curvature_fraction(f_low, low.rho_curv, high.rho_curv)
        subphase = classify_liquid_subphase(f_low)

    return PhaseDiagramPoint(
        temperature_k=temperature_k,
        pressure_pa=pressure_pa,
        derived_phase=state.phase.value,
        liquid_subphase=subphase,
        f_low_density=f_low,
        rho_curv=rho,
        coordination_fraction=state.coordination_fraction,
        contact_persistence=state.contact_persistence,
        periodic_weight=state.periodic_weight,
        T_melt_K=t_melt,
        T_boil_K=t_boil,
        xi=state.xi,
        notes=state.notes,
        f_low_density_one_way=f_low_one_way,
        branch_coupling_level=ccr.coupling_level_from_weight(branch_lam),
        branch_coupling_target=branch_target,
    )


def phase_diagram_grid(
    molecule_or_mixture: str | tuple[MixtureComponent, ...],
    *,
    temperatures_k: tuple[float, ...],
    pressures_pa: tuple[float, ...],
    bulk: bool = True,
) -> list[dict[str, Any]]:
    """Cartesian (T, P) grid for phase-map export."""
    rows: list[dict[str, Any]] = []
    for t_k in temperatures_k:
        for p_pa in pressures_pa:
            pt = phase_diagram_point(molecule_or_mixture, temperature_k=t_k, pressure_pa=p_pa, bulk=bulk)
            rows.append(
                {
                    "temperature_K": pt.temperature_k,
                    "pressure_Pa": pt.pressure_pa,
                    "pressure_atm": pt.pressure_pa / STP_PRESSURE_PA,
                    "derived_phase": pt.derived_phase,
                    "liquid_subphase": pt.liquid_subphase.value if pt.liquid_subphase else None,
                    "f_low_density": pt.f_low_density,
                    "f_low_density_one_way": pt.f_low_density_one_way,
                    "branch_coupling_level": pt.branch_coupling_level,
                    "branch_coupling_target": pt.branch_coupling_target,
                    "rho_curv": pt.rho_curv,
                    "coordination_fraction": pt.coordination_fraction,
                    "T_melt_K": pt.T_melt_K,
                    "notes": pt.notes,
                }
            )
    return rows


# Comparison quarantine — external observations, never derivation inputs.
WATER_LLPT_OBSERVATIONS: tuple[dict[str, Any], ...] = (
    {
        "source": "Sciortino et al., Nat. Phys. 2025",
        "doi": "10.1038/s41567-024-02761-0",
        "label": "LLCP (MB-pol)",
        "T_K": 198.0,
        "P_atm": 1250.0,
        "role": "comparison_only",
    },
    {
        "source": "Li et al., Nat. Phys. 2026",
        "doi": "10.1038/s41567-026-03301-8",
        "label": "two-state A⇌B (TIP4P/Ice MD)",
        "T_regime_K": "deeply supercooled",
        "role": "comparison_only",
    },
    {
        "source": "Kim et al., Science 2020",
        "doi": "10.1126/science.abb9385",
        "bibkey": "kim2020waterLLPT",
        "label": "bulk LLPT experimental claim",
        "role": "comparison_only",
    },
    {
        "source": "Kim et al., Science 2017",
        "doi": "10.1126/science.aap8269",
        "bibkey": "kim2017waterWidom",
        "label": "compressibility maximum ~229 K at 1 atm",
        "T_K": 229.0,
        "P_atm": 1.0,
        "role": "comparison_only",
    },
)


def widom_line_compressibility_proxy(
    temperature_k: float,
    pressure_pa: float,
    material: tptp.MaterialThermodynamicScales,
    *,
    delta_t_k: float = 1.0,
) -> float:
    """
    κ anomaly proxy from free-energy susceptibility.

    The two-state mixture is derived by minimizing ``F(f;T,P)``.  The anomaly proxy
    uses the curvature at that minimum, ``χ_f ∝ kT / ∂²F/∂f²``, plus the observed
    local thermal response ``|∂f/∂T|``.  Kim et al. grade the peak location only.
    """
    k_t = max(K_B_EV_PER_K * max(temperature_k, 1e-30), 1e-30)
    dt = max(delta_t_k, 0.5)
    mol = _resolve_molecule_name(material, None)
    f_lo = low_density_liquid_fraction(temperature_k - dt, pressure_pa, material, molecule=mol)
    minimum = low_density_free_energy_minimum(temperature_k, pressure_pa, material, molecule=mol)
    f_mid = minimum["f_low_density"]
    f_hi = low_density_liquid_fraction(temperature_k + dt, pressure_pa, material, molecule=mol)
    df_dT = abs(f_hi - f_lo) / (2.0 * dt)
    low, high = end_members_for_molecule(mol)
    rho_mix = liquid_mixture_curvature_fraction(f_mid, low.rho_curv, high.rho_curv)
    b_hom, _geff_rho, curvature_fb = outside_curvature_mixture_dress(
        rho_mix, material.contact_xi, mol
    )
    e_ldl, e_hdl = _cohesive_scales_ev(material)
    l_branch = ldl_hdl_conversion_barrier_ev_per_contact(mol, material)
    mix_factor = mixture_latent_barrier_factor(f_mid)
    free_curvature = abs(minimum["free_energy_curvature_ev"])
    first_order = df_dT * (abs(e_ldl - e_hdl) + abs(curvature_fb)) / k_t * max(b_hom, 1e-30)
    susceptibility = k_t / max(free_curvature, 1e-12)
    second_order = mix_factor * l_branch * susceptibility / max(k_t, 1e-30)
    t_melt, _ = tptp.characteristic_temperatures_K(material)
    window = widom_second_order_window_weight(temperature_k, t_melt)
    return first_order + window * second_order


def widom_proxy_peak_at_pressure(
    material: tptp.MaterialThermodynamicScales,
    pressure_pa: float = STP_PRESSURE_PA,
    *,
    t_min: float = 150.0,
    t_max: float = 280.0,
    t_step: float = 2.0,
) -> dict[str, float]:
    """Scan T at fixed P; return peak compressibility proxy (Widom-line witness)."""
    best_t = t_min
    best_v = 0.0
    t = t_min
    while t <= t_max + 1e-9:
        v = widom_line_compressibility_proxy(t, pressure_pa, material)
        if v > best_v:
            best_v = v
            best_t = t
        t += t_step
    return {
        "temperature_K": best_t,
        "pressure_Pa": pressure_pa,
        "compressibility_proxy": best_v,
    }

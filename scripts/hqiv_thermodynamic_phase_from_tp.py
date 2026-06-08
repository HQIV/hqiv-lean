#!/usr/bin/env python3
"""
Derive matter phase and network coordination from **temperature and pressure** inputs.

Lean spine: `Hqiv.Physics.ThermodynamicLawsFromLadder` (T(m)=1/(m+1)),
`Hqiv.Physics.NuclearOutsideTemperatureDynamics` (T(ξ)=T_Pl/ξ),
`hqiv_lean_physics_primitives.xi_from_T_MeV`.

Phase is an **output**, not a user enum:
  • gas / molecular_cluster — dilute or single-molecule limit
  • liquid — partial inter-molecular coordination
  • solid — full coordination + optional periodic images

Material scales (binding eV, contact count) set T_melt / T_boil / P_solidify
without global fitted potentials.

Consumers: `hqiv_curvature_contact_network`, protein folding, bulk materials.

Run:
  python3 scripts/hqiv_thermodynamic_phase_from_tp.py
"""

from __future__ import annotations

import math
from dataclasses import asdict, dataclass
from enum import Enum
from typing import Any

import hqiv_bbn_abundances as bbn
import hqiv_lean_physics_primitives as lean

K_B_MEV_PER_K = 8.617333262e-11  # CODATA k_B in MeV/K
K_B_EV_PER_K = K_B_MEV_PER_K * 1e6
STP_TEMPERATURE_K = 298.15
STP_PRESSURE_PA = 101_325.0
T_PL_MEV = bbn.T_PL_MEV
ALPHA = lean.ALPHA
GAMMA = lean.GAMMA
XI_LOCKIN = lean.XI_LOCKIN
# Intermolecular cohesive fraction: α² (ladder imprint, distinct from binding κ(ξ)).
KAPPA_MELT = ALPHA * ALPHA


class DerivedPhase(str, Enum):
    """Phase readout from (T, P) + material scales — never supplied as input."""

    GAS = "gas"
    MOLECULAR_CLUSTER = "molecular_cluster"
    LIQUID = "liquid"
    SOLID = "solid"
    SUPERCRITICAL = "supercritical"


@dataclass(frozen=True)
class MaterialThermodynamicScales:
    """
    Per-material characteristic scales from HQIV binding/contact bookkeeping.

    `characteristic_binding_ev` — GMTKN / witness atomization reference (not used for melt).
    `contact_xi` — Compton-triplet mean ξ for dynamic κ(ξ) cohesive scale.
    `contact_points` — intermolecular contact count for melt/boil divisors.
    `bulk_condensed` — ice-like tetrahedral network (4 H-bonds); uses shell-opening melt scale.
    `medium_density_fraction` — geometric ρ_curv ∈ [0,1] from unit-cell / liquid reference.
    `refractive_index_solid` — solid n from θ-derived CM; dresses κ₆ via optical ρ.
    `intermolecular_motif` — VSEPR network motif for melt ladder divisor.
    `z_heavy` — heavy-atom Z for linear-chain halogen melt dress.
    """

    name: str
    characteristic_binding_ev: float
    contact_points: int
    molecular_weight_amu: float = 16.0
    intermolecular_contacts: int = 0
    contact_xi: float = XI_LOCKIN
    bulk_condensed: bool = False
    medium_density_fraction: float | None = None
    refractive_index_solid: float | None = None
    intermolecular_motif: str | None = None
    z_heavy: int = 8


@dataclass(frozen=True)
class ThermodynamicEnvironment:
    """Laboratory or simulation box conditions."""

    temperature_K: float
    pressure_Pa: float

    @classmethod
    def stp(cls) -> ThermodynamicEnvironment:
        return cls(STP_TEMPERATURE_K, STP_PRESSURE_PA)

    @classmethod
    def protein_cytosol(cls) -> ThermodynamicEnvironment:
        """Rough cytosolic-like conditions for folding studies."""
        return cls(310.15, STP_PRESSURE_PA)

    def T_MeV(self) -> float:
        return max(self.temperature_K * K_B_MEV_PER_K, 1e-30)

    def xi(self) -> float:
        return lean.xi_from_T_MeV(self.T_MeV())


@dataclass(frozen=True)
class DerivedThermodynamicState:
    """Full phase derivation witness."""

    environment: ThermodynamicEnvironment
    material: MaterialThermodynamicScales
    phase: DerivedPhase
    xi: float
    shell_m: float
    ladder_T: float
    omega_k: float
    B_curv: float
    T_melt_K: float
    T_boil_K: float
    P_solidify_Pa: float
    coordination_fraction: float
    contact_persistence: float
    periodic_weight: float
    notes: str


def material_scales_from_contact_network(
    name: str,
    *,
    contacts: int,
    intermolecular_contacts: int,
    binding_ev: float | None = None,
    contact_xi: float | None = None,
) -> MaterialThermodynamicScales:
    """
    Material scales for (T,P) phase — **intermolecular** contacts set melt/boil, not covalent count.

    Covalent/H–H graph size must not inflate ``contact_points`` (CH₄ was wrongly solid at STP).
    """
    _ = contacts
    base = material_scales_from_network_name(name, binding_ev=binding_ev)
    inter = (
        intermolecular_contacts
        if intermolecular_contacts > 0
        else base.intermolecular_contacts
    )
    xi = contact_xi if contact_xi is not None else base.contact_xi
    rho = (
        base.medium_density_fraction
        if base.medium_density_fraction is not None
        else lean.intermolecular_density_fraction(inter)
    )
    return MaterialThermodynamicScales(
        name=base.name,
        characteristic_binding_ev=base.characteristic_binding_ev,
        contact_points=inter,
        molecular_weight_amu=base.molecular_weight_amu,
        intermolecular_contacts=inter,
        contact_xi=xi,
        bulk_condensed=base.bulk_condensed,
        medium_density_fraction=rho,
    )


def resolved_medium_density_fraction(material: MaterialThermodynamicScales) -> float:
    """Geometric ρ_curv, optionally dressed by solid n for κ₆ (``phase_curvature_density_fraction``)."""
    rho_geom = _geometric_medium_density_fraction(material)
    if material.refractive_index_solid is not None and material.refractive_index_solid > 1.0:
        import hqiv_phase_geometry_density as pgd

        return pgd.phase_curvature_density_fraction(rho_geom, material.refractive_index_solid)
    return rho_geom


def _geometric_medium_density_fraction(material: MaterialThermodynamicScales) -> float:
    """Mass-geometry ρ_curv before optical n dress."""
    if material.medium_density_fraction is not None:
        return min(1.0, max(0.0, material.medium_density_fraction))
    if not material.bulk_condensed:
        return 0.0
    return lean.intermolecular_density_fraction(intermolecular_contact_count(material))


def material_scales_bulk_h2o() -> MaterialThermodynamicScales:
    """
    Bulk ice / liquid water (not GMTKN55 gas-phase cluster).

    ρ from ice Ih unit-cell geometry (``hqiv_phase_geometry_density``), not a
    blanket ρ=1. Tetrahedral coordination (4 contacts) + shell-opening melt lift.
    """
    import hqiv_phase_geometry_density as pgd

    return pgd.material_scales_with_phase_geometry("H2O", allotrope="Ih", bulk=True)


def material_scales_from_network_name(
    name: str,
    *,
    binding_ev: float | None = None,
    contact_points: int = 4,
) -> MaterialThermodynamicScales:
    """Default cohesive scales for GMTKN55 / protein fragments."""
    defaults: dict[str, tuple[float, int, int]] = {
        "H2": (4.478, 1, 1),
        "LiH": (2.515, 2, 1),
        "HF": (5.87, 2, 1),
        "H2O": (9.51, 5, 1),
        "CH4": (17.0, 7, 4),
        "NH3": (10.07, 6, 3),
        "protein": (0.5, 12, 1),
    }
    if name.startswith("protein"):
        n = 12
        for part in name.split("_"):
            if part.endswith("mer") and part[:-3].isdigit():
                n = int(part[:-3])
                break
        return MaterialThermodynamicScales(
            name=name,
            characteristic_binding_ev=binding_ev or 0.5,
            contact_points=max(2 * n, 2),
            molecular_weight_amu=float(n) * 110.0,
            intermolecular_contacts=1,
            contact_xi=XI_LOCKIN,
        )
    be, cp, inter = defaults.get(name, (binding_ev or 5.0, contact_points, 0))
    if binding_ev is not None:
        be = binding_ev
    if inter <= 0:
        inter = max(1, cp // 2)
    triplet = (1, 1, 1) if name == "H2" else (4, 3, 1)
    return MaterialThermodynamicScales(
        name=name,
        characteristic_binding_ev=be,
        contact_points=inter,
        molecular_weight_amu=16.0,
        intermolecular_contacts=inter,
        contact_xi=lean.xi_from_compton_triplet(triplet),
    )


def intermolecular_contact_count(material: MaterialThermodynamicScales) -> int:
    if material.intermolecular_contacts > 0:
        return material.intermolecular_contacts
    return max(1, material.contact_points)


def intermolecular_cohesive_ev(material: MaterialThermodynamicScales) -> float:
    """
    HQIV intermolecular cohesive scale (no fixed κ_bind, no atomization injection).

    Dilute / assay:
      e_cohesive = κ(ξ) · α² / (n_inter · (1+α)²)

    Bulk condensed (ice network):
      e_cohesive = κ(ξ) · α² · (4/8) · (4/3) / (1+α)²
      (tetrahedral channel fraction × shell-opening phase lift before melt)
    """
    kappa_xi = lean.dynamic_binding_curvature_coupling_at_xi(material.contact_xi)
    shell_div = (1.0 + ALPHA) ** 2
    if material.bulk_condensed:
        return (
            kappa_xi
            * KAPPA_MELT
            * lean.STRONG_CHANNEL_FRACTION
            * lean.PHASE_LIFT_3
            / shell_div
        )
    inter = intermolecular_contact_count(material)
    return kappa_xi * KAPPA_MELT / (float(inter) * shell_div)


def _resolve_motif(material: MaterialThermodynamicScales):
    from hqiv_lab.coordination import IntermolecularMotif

    if material.intermolecular_motif is None:
        return IntermolecularMotif.GENERIC
    try:
        return IntermolecularMotif(material.intermolecular_motif)
    except ValueError:
        return IntermolecularMotif.GENERIC


def melt_motif_relative_scale_for_material(material: MaterialThermodynamicScales) -> float:
    """Motif melt ladder scale relative to tetrahedral ice."""
    from hqiv_lab.coordination import melt_motif_relative_scale

    return melt_motif_relative_scale(
        _resolve_motif(material),
        intermolecular_contact_count(material),
        z_heavy=material.z_heavy,
    )


def melt_cohesive_ev(material: MaterialThermodynamicScales) -> float:
    """Energy scale for solid→liquid (one shell release on the cohesive ladder)."""
    if material.bulk_condensed:
        import hqiv_homogeneous_curvature_feedback as hcf

        kappa_xi = lean.dynamic_binding_curvature_coupling_at_xi(material.contact_xi)
        e_tetra = (
            kappa_xi
            * KAPPA_MELT
            * lean.PHASE_LIFT_3
            / ((1.0 + ALPHA) ** 3)
        )
        rho_kappa = resolved_medium_density_fraction(material)
        fb = hcf.binding_curvature_feedback_second_order_homogeneous(
            material.contact_xi,
            rho_kappa,
            coordination_excess=0.0,
        )
        motif_scale = melt_motif_relative_scale_for_material(material)
        return e_tetra * motif_scale * fb
    return intermolecular_cohesive_ev(material) / (1.0 + ALPHA)


def characteristic_temperatures_K(material: MaterialThermodynamicScales) -> tuple[float, float]:
    """
    Melting / boiling from dynamic κ(ξ) cohesive scale (α² imprint, not atomization eV).

    Dilute: T_melt from e_cohesive / (1+α); T_boil from full e_cohesive.
    Bulk: T_melt from phase-lift melt channel; T_boil one (1+α) rung above melt.
    """
    e_melt = melt_cohesive_ev(material)
    if material.bulk_condensed:
        e_boil = e_melt * (1.0 + ALPHA)
    else:
        e_boil = intermolecular_cohesive_ev(material)
    t_melt = max(e_melt / K_B_EV_PER_K, 1.0)
    t_boil = max(e_boil / K_B_EV_PER_K, t_melt + 1.0)
    return t_melt, t_boil


def solid_liquid_transition_temperature_K(
    material: MaterialThermodynamicScales,
    *,
    pressure_Pa: float = STP_PRESSURE_PA,
) -> float:
    """
    Solid→liquid transition at ``pressure_Pa`` (default 1 atm ≈ STP).

    HQIV: T_sl = melt_cohesive / k_B with optional linear pressure tilt
    ``(1 + γ·(P/P_stp − 1))`` on the melt scale (small at 1 atm).
    """
    t_melt, _ = characteristic_temperatures_K(material)
    if pressure_Pa <= 0.0:
        return t_melt
    ratio = pressure_Pa / STP_PRESSURE_PA
    return t_melt * (1.0 + GAMMA * (ratio - 1.0))


def vapor_pressure_Pa(temperature_K: float, t_boil_K: float) -> float:
    """HQIV vapor-pressure ladder: P_vap ∝ (T/T_boil)^γ at sub-boiling T."""
    if t_boil_K <= 0.0:
        return 0.0
    ratio = max(temperature_K / t_boil_K, 1e-6)
    return STP_PRESSURE_PA * (ratio**GAMMA)


def solidification_pressure_Pa(material: MaterialThermodynamicScales) -> float:
    """
    Pressure scale from Compton IR stress at lock-in contact.

    P_solidify ~ (B_curv at ξ_lock) · (binding_ev / contact) / (a0³) in SI order;
    use STP as reference pressure anchor for dimensionless ratio.
    """
    _ = material
    b_curv = lean.curvature_budget_at_xi(XI_LOCKIN)
    # Dimensionless: STP × (γ · B_curv) sets the HQIV pressure ladder unit.
    return STP_PRESSURE_PA * max(b_curv * GAMMA, 0.1)


def derive_phase(
    env: ThermodynamicEnvironment,
    material: MaterialThermodynamicScales,
) -> DerivedThermodynamicState:
    """
    Classify phase and coordination from (T, P) and material binding scales.
    """
    t_melt, t_boil = characteristic_temperatures_K(material)
    p_solid = solidification_pressure_Pa(material)
    xi = env.xi()
    m_shell = max(T_PL_MEV / max(env.T_MeV(), 1e-30) - 1.0, 0.0)
    ladder_t = 1.0 / (m_shell + 1.0) if m_shell >= 0 else 1.0
    omega_k = lean.omega_k_xi(xi)
    b_curv = lean.curvature_budget_at_xi(xi)

    t = env.temperature_K
    p = env.pressure_Pa
    p_vap = vapor_pressure_Pa(t, t_boil)

    sc_t = t_boil * (1.0 + 1.0 / ALPHA)
    sc_p = p_solid * (1.0 + GAMMA)
    if material.name.startswith("protein") or material.molecular_weight_amu >= 5000.0:
        phase = DerivedPhase.LIQUID
        coord = ALPHA * ladder_t + (1.0 - ALPHA) * 0.5
        persist = min(0.85, 0.5 + 0.35 * ladder_t)
        periodic = 0.0
        notes = "Biopolymer / folding box: coordination from ξ(T) ladder, not small-molecule melt"
    elif t > t_boil or p < p_vap:
        phase = DerivedPhase.GAS if t > t_boil else DerivedPhase.MOLECULAR_CLUSTER
        coord = 0.05 if phase == DerivedPhase.GAS else 1.0
        persist = 0.1 if phase == DerivedPhase.GAS else 1.0
        periodic = 0.0
        notes = (
            "Dilute / above T_boil: gas-phase or molecular-cluster chemistry limit"
            if phase == DerivedPhase.GAS
            else "P < P_vap(T): single-molecule cluster (GMTKN55, dilute assays)"
        )
    elif t > sc_t and p > sc_p:
        phase = DerivedPhase.SUPERCRITICAL
        coord = 0.4
        persist = 0.5
        periodic = 0.0
        notes = "T ≫ T_boil and P ≫ P_solidify; bulk supercritical fluid"
    elif t < t_melt and p >= p_solid:
        phase = DerivedPhase.SOLID
        coord = min(0.95, 0.7 + 0.25 * (p / max(p_solid, 1.0)))
        persist = 1.0
        periodic = min(1.0, p / max(p_solid, 1.0))
        notes = "T < T_melt and P ≥ P_solidify; full coordination + periodic weight"
    elif t_melt <= t <= t_boil and p >= p_vap:
        inter = intermolecular_contact_count(material)
        dilute_assay = (
            not material.bulk_condensed
            and inter <= 3
            and material.molecular_weight_amu < 120.0
        )
        if dilute_assay:
            phase = DerivedPhase.MOLECULAR_CLUSTER
            coord = 1.0
            persist = 1.0
            periodic = 0.0
            notes = "Small-molecule dilute assay (GMTKN55): cluster limit, not bulk liquid"
        else:
            phase = DerivedPhase.LIQUID
            span = max(t_boil - t_melt, 1e-6)
            coord = 0.35 + 0.55 * (1.0 - (t - t_melt) / span)
            persist = 0.6 + 0.3 * (p / max(p_solid, 1.0))
            persist = min(persist, 1.0)
            periodic = 0.0
            notes = "T_melt ≤ T ≤ T_boil and P ≥ P_vap; condensed liquid coordination"
    else:
        phase = DerivedPhase.MOLECULAR_CLUSTER
        coord = 1.0
        persist = 1.0
        periodic = 0.0
        notes = "Sub-boiling, below vapor pressure: intramolecular cluster"

    return DerivedThermodynamicState(
        environment=env,
        material=material,
        phase=phase,
        xi=xi,
        shell_m=m_shell,
        ladder_T=ladder_t,
        omega_k=omega_k,
        B_curv=b_curv,
        T_melt_K=t_melt,
        T_boil_K=t_boil,
        P_solidify_Pa=p_solid,
        coordination_fraction=coord,
        contact_persistence=persist,
        periodic_weight=periodic,
        notes=notes,
    )


def phase_report(state: DerivedThermodynamicState) -> dict[str, Any]:
    return {
        "temperature_K": state.environment.temperature_K,
        "pressure_Pa": state.environment.pressure_Pa,
        "T_MeV": state.environment.T_MeV(),
        "material": asdict(state.material),
        "derived_phase": state.phase.value,
        "xi": state.xi,
        "shell_m": state.shell_m,
        "ladder_T": state.ladder_T,
        "omega_k": state.omega_k,
        "B_curv": state.B_curv,
        "T_melt_K": state.T_melt_K,
        "T_boil_K": state.T_boil_K,
        "P_solidify_Pa": state.P_solidify_Pa,
        "P_vapor_Pa": vapor_pressure_Pa(
            state.environment.temperature_K, state.T_boil_K
        ),
        "coordination_fraction": state.coordination_fraction,
        "contact_persistence": state.contact_persistence,
        "periodic_weight": state.periodic_weight,
        "notes": state.notes,
    }


def main() -> None:
    envs = [
        ("STP", ThermodynamicEnvironment.stp()),
        ("cytosol", ThermodynamicEnvironment.protein_cytosol()),
        ("CH4_boil", ThermodynamicEnvironment(111.63, STP_PRESSURE_PA)),
        ("ice", ThermodynamicEnvironment(273.15, STP_PRESSURE_PA)),
    ]
    materials = ["CH4", "H2O", "protein"]
    print("HQIV phase from (T, P)")
    print("=" * 72)
    for mname in materials:
        mat = material_scales_from_network_name(mname)
        print(f"\n{mname}: T_melt={characteristic_temperatures_K(mat)[0]:.1f} K")
        for label, env in envs:
            st = derive_phase(env, mat)
            print(
                f"  {label:12s} T={env.temperature_K:7.1f} K  P={env.pressure_Pa/1e5:5.2f} bar  "
                f"→ {st.phase.value:18s}  coord={st.coordination_fraction:.3f}"
            )

    bulk = material_scales_bulk_h2o()
    t_sl = solid_liquid_transition_temperature_K(bulk)
    print("\n" + "=" * 72)
    print(f"H2O_bulk solid→liquid @ 1 atm: T_sl ≈ {t_sl:.2f} K  (NIST ice melt ≈ 273.15 K)")
    for t_probe in (272.0, 273.15, 274.0):
        env = ThermodynamicEnvironment(t_probe, STP_PRESSURE_PA)
        st = derive_phase(env, bulk)
        print(f"  T={t_probe:6.2f} K → {st.phase.value}")


if __name__ == "__main__":
    main()

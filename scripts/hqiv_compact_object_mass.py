#!/usr/bin/env python3
"""
Compact-object mass readouts from HQIV curvature slots (no fitted potentials).

Faithful stack (Lean / existing scripts):
  • ``ε = GM/(Rc²)`` — outside gravity witness (`NuclearOutsideTemperatureDynamics`)
  • ``G_eff(1+ε)^α`` modulator with ``α = 3/5``, monogamy fold ``γ = 2/5``
  • Lapse ``N = 1 + Φ`` with ``Φ = −ε`` on a static surface (``HQVM_lapse`` sector)
  • Nuclear binding: inside trapped ratio + outside caustics (`NuclearCurvatureBinding`)
  • Critical tipping scale ``ε_crit = c_rindler_shared = γ/2`` (`GlobalDetuning`)
  • Charmed matter: charmed-baryon mass ladder (`HepDecayReadout` / `QuarkMetaResonance`)

Primary prediction: a uniform sphere at nuclear density reaches the neutron-star
mass ceiling when the surface gravitational slot hits ``γ/2`` (lapse ``N = 1 − γ/2``).

Run:
  python3 scripts/hqiv_compact_object_mass.py
  python3 scripts/hqiv_compact_object_mass.py --json
  python3 scripts/hqiv_compact_object_mass.py --paper-dynamics-outline
  python3 scripts/hqiv_compact_object_mass.py --mhd-equivalence-audit
  python3 scripts/hqiv_compact_object_mass.py --eta-calibration-audit
  python3 scripts/hqiv_compact_object_mass.py --magnetic-field-gap-audit
  python3 scripts/hqiv_compact_object_mass.py --surface-multipole-audit
  python3 scripts/hqiv_pulsar_witness_benchmark.py --json
  papers/compact_object_witness/regenerate_data.sh  # all JSON bundles
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Literal

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(_ROOT / "scripts"))

from cubic_phase_relax_probe import M_TOP_GEV  # noqa: E402

import hqiv_excited_states as hes
import hqiv_hep_decay_readout as hep
import hqiv_lean_physics_primitives as lean
import hqiv_nuclear_curvature_binding as ncur
import hqiv_nuclear_outside_temperature_dynamics as notd

# SI constants (witness comparison only — masses enter through HQIV nucleon slot)
G_NEWTON = 6.674e-11
C_LIGHT = 299792458.0
M_SUN_KG = 1.98847e30

MEV_TO_J = 1.602176634e-13
MEV_TO_KG = MEV_TO_J / C_LIGHT**2

PROTON_MEV = 938.27208816
NEUTRON_MEV = 939.5654133
ALPHA = lean.ALPHA
GAMMA = lean.GAMMA
C_RINDLER_SHARED = lean.C_RINDLER_SHARED  # γ/2 = 1/5
ALPHA_GAMMA = ALPHA * GAMMA  # 0.24
REFERENCE_M = hes.REFERENCE_M

# Nuclear density from HQIV neutron mass (no external table): ρ = m_n / (4/3 π r_n³)
# r_n ≈ 1.1 fm (contact scale from nuclear chart, not a fit knob here).
R_NUCLEON_M = 1.1e-15
M_NUCLEON_KG = NEUTRON_MEV * 1.602176634e-13 / C_LIGHT**2
RHO_NUCLEAR_KG_M3 = M_NUCLEON_KG / (4.0 / 3.0 * math.pi * R_NUCLEON_M**3)


MatterKind = Literal["nuclear", "charmed", "top"]

# Flavor tipping scales on the gravitational ε slot (interior ε(r) = ε_s (3−(r/R)²)/2).
EPS_CHARM_TIP = ALPHA_GAMMA  # open-charm overpressure rung (α·γ = 0.24)
EPS_TOP_TIP = ALPHA  # color-composed closure (α = 0.6)
EPS_HORIZON = 0.5  # Schwarzschild surface ε = GM/(Rc²)


@dataclass(frozen=True)
class CompactObjectRow:
    label: str
    matter: MatterKind
    mass_msun: float
    radius_km: float
    epsilon_surface: float
    lapse_surface: float
    compactness_rs_over_r: float
    geff_modulator: float
    env_modulator_bonded: float
    per_nucleon_binding_mev: float
    trapped_inside_ratio_shell: int
    notes: str


def gravitational_phi_epsilon(mass_kg: float, radius_m: float) -> float:
    """Dimensionless ``ε = GM/(Rc²)``."""
    if mass_kg <= 0.0 or radius_m <= 0.0:
        return 0.0
    return G_NEWTON * mass_kg / (radius_m * C_LIGHT**2)


def schwarzschild_radius_m(mass_kg: float) -> float:
    return 2.0 * G_NEWTON * mass_kg / C_LIGHT**2


def radius_uniform_density(mass_kg: float, rho_kg_m3: float) -> float:
    return (3.0 * mass_kg / (4.0 * math.pi * rho_kg_m3)) ** (1.0 / 3.0)


def mass_from_epsilon_crit(epsilon_crit: float, rho_kg_m3: float) -> float:
    """
    Uniform sphere: ``ε = GM/(Rc²)`` with ``R = (3M/(4πρ))^{1/3}`` ⇒
    ``M = (ε c² (3/(4πρ))^{1/3} / G)^{3/2}``.
    """
    if epsilon_crit <= 0.0 or rho_kg_m3 <= 0.0:
        return 0.0
    pref = (3.0 / (4.0 * math.pi * rho_kg_m3)) ** (1.0 / 3.0)
    m32 = epsilon_crit * C_LIGHT**2 * pref / G_NEWTON
    return m32 ** (3.0 / 2.0)


def epsilon_for_mass_msun(mass_msun: float, rho_kg_m3: float) -> tuple[float, float]:
    mass_kg = mass_msun * M_SUN_KG
    r_m = radius_uniform_density(mass_kg, rho_kg_m3)
    return gravitational_phi_epsilon(mass_kg, r_m), r_m


def matter_density(matter: MatterKind) -> float:
    if matter == "nuclear":
        return RHO_NUCLEAR_KG_M3
    if matter == "charmed":
        m_pi, m_k = 139.57, 493.677
        m_charm_baryon = hep.charmed_baryon_mass_mev(PROTON_MEV, m_k, m_pi, 1)
        return RHO_NUCLEAR_KG_M3 * (m_charm_baryon / NEUTRON_MEV)
    # Top-sector scale: lock-in GeV anchor per cell (QuarkMetaResonance / open-flavour cascade).
    return RHO_NUCLEAR_KG_M3 * (M_TOP_GEV * 1000.0 / NEUTRON_MEV)


def rho_top_kg_m3() -> float:
    return matter_density("top")


def epsilon_interior(epsilon_surface: float, r_m: float, radius_m: float) -> float:
    """Interior gravitational slot for a uniform sphere."""
    if radius_m <= 0.0:
        return epsilon_surface
    t = min(abs(r_m) / radius_m, 1.0)
    return epsilon_surface * (3.0 - t * t) / 2.0


def compactness_rs_over_r(mass_kg: float, radius_m: float) -> float:
    if radius_m <= 0.0:
        return math.inf
    return schwarzschild_radius_m(mass_kg) / radius_m


def rindler_denominator(tangent_speed_m_s: float) -> float:
    """Lean-aligned angular Rindler denominator ``D_R = 1 + (γ/2)(c/v)²``."""
    v = max(abs(tangent_speed_m_s), 1.0)
    return 1.0 + (GAMMA / 2.0) * (C_LIGHT / v) ** 2


def breakup_omega_rad_s(mass_kg: float, radius_m: float) -> float:
    """Keplerian angular velocity at the equatorial surface."""
    return math.sqrt(G_NEWTON * mass_kg / max(radius_m**3, 1.0))


def epsilon_spin_co_rotation(
    omega_rad_s: float,
    radius_m: float,
    *,
    colatitude_rad: float = 0.0,
    projection: float = 1.0,
    radial_power: float = 2.0,
    observer_radius_m: float | None = None,
    use_rindler_denominator: bool = True,
) -> float:
    """
    Co-spinning mass-horizon Doppler ε (flyby / wide-binary slot).

    Mirrors ``co_spin_lapse_fraction`` at ``r = observer_radius`` and
    ``mass_horizon_doppler_lapse`` with optional Rindler suppression.
    """
    if abs(omega_rad_s) <= 0.0 or radius_m <= 0.0:
        return 0.0
    r_obs = observer_radius_m if observer_radius_m is not None else radius_m
    r_obs = max(r_obs, radius_m)
    sin_colat = math.sin(max(0.0, min(math.pi / 2.0, colatitude_rad)))
    sin2 = sin_colat * sin_colat
    v_tangent = abs(omega_rad_s) * radius_m * sin_colat
    eps = 2.0 * (v_tangent / C_LIGHT) * max(0.0, min(1.0, abs(projection)))
    eps *= (radius_m / r_obs) ** radial_power
    eps *= sin2
    if use_rindler_denominator:
        eps /= rindler_denominator(v_tangent)
    return eps


def outside_geff_modulator_from_epsilon(epsilon_total: float) -> float:
    """``NuclearOutsideTemperatureDynamics.outsideGravityGeffModulator``."""
    return notd.outside_gravity_geff_modulator(max(0.0, epsilon_total))


def flyby_phi_readout_at_radius(radius_m: float, lapse_radius_m: float) -> float:
    """Geometric ``φ/φ_ref`` slot at the surface (no spin; ``phi_readout``)."""
    r_lapse = max(lapse_radius_m, 1.0)
    return 1.0 / (1.0 + radius_m / r_lapse)


def flyby_geff_ratio_at_surface(radius_m: float, lapse_radius_m: float) -> float:
    """Orbital ``G_eff/G₀ = (φ/φ_ref)^α`` at the body surface (φ_ref = 1)."""
    phi = flyby_phi_readout_at_radius(radius_m, lapse_radius_m)
    return phi ** ALPHA


@dataclass(frozen=True)
class SpinGeffRow:
    label: str
    mass_msun: float
    radius_km: float
    omega_rad_s: float
    omega_over_breakup: float
    v_surface_over_c: float
    epsilon_gravity: float
    epsilon_spin_raw: float
    epsilon_spin_rindler: float
    epsilon_total_rindler: float
    outside_geff_mod_gravity_only: float
    outside_geff_mod_with_spin: float
    geff_mod_delta: float
    flyby_geff_phi_ratio: float
    compactness_rs_over_r: float
    notes: str


def spin_geff_analysis() -> dict[str, object]:
    """
    Spin effects on compact-object readouts.

    **Two G_eff slots in HQIV (do not conflate):**

    1. **Outside nuclear / binding** — ``1 + γ((1+ε)^α − 1)`` with ε stacking gravity
       and co-spin Doppler (`NuclearOutsideTemperatureDynamics`, flyby horizon ε).
    2. **Orbital φ channel** — ``(φ/φ_ref)^α`` from geometric lapse ``1/(1+r/R)``;
       spin does **not** enter φ directly; it feeds ε → ``φ_eff = φ_loc + 6aε`` → inertia
       screen that **screens** G_eff on Newton sources (`hqiv_orbital_flyby_omaxwell`).
    """
    rows: list[SpinGeffRow] = []

    specs: list[tuple[str, float, float, float, str]] = [
        ("1.4 M☉ NS slow (Ω=10 Hz)", 1.4, 13.0, 2.0 * math.pi * 10.0, "typical pulsar"),
        ("1.4 M☉ NS ms (Ω=640 Hz)", 1.4, 12.0, 2.0 * math.pi * 640.0, "J1748−2446 class"),
        ("1.98 M☉ NS max uniform", 1.98, 14.6, 2.0 * math.pi * 50.0, "at TOV cap"),
        ("1.98 M☉ at breakup Ω", 1.98, 14.6, None, "Ω_break = √(GM/R³)"),
        ("2.0 M☉ heavy pulsar", 2.0, 14.7, 2.0 * math.pi * 300.0, "upper mass pulsar"),
        ("3.16 M☉ charmed tail", 3.16, 14.6, 2.0 * math.pi * 100.0, "post-charm core mass"),
    ]

    for label, m_msun, r_km, omega, note in specs:
        mass_kg = m_msun * M_SUN_KG
        radius_m = r_km * 1000.0
        omega_break = breakup_omega_rad_s(mass_kg, radius_m)
        omega_use = omega_break if omega is None else omega
        eps_g = gravitational_phi_epsilon(mass_kg, radius_m)
        eps_spin_raw = epsilon_spin_co_rotation(
            omega_use,
            radius_m,
            colatitude_rad=math.pi / 2.0,
            use_rindler_denominator=False,
        )
        eps_spin = epsilon_spin_co_rotation(
            omega_use, radius_m, colatitude_rad=math.pi / 2.0
        )
        eps_tot = eps_g + eps_spin
        geff_g = outside_geff_modulator_from_epsilon(eps_g)
        geff_tot = outside_geff_modulator_from_epsilon(eps_tot)
        rows.append(
            SpinGeffRow(
                label=label,
                mass_msun=m_msun,
                radius_km=r_km,
                omega_rad_s=omega_use,
                omega_over_breakup=omega_use / omega_break,
                v_surface_over_c=abs(omega_use) * radius_m / C_LIGHT,
                epsilon_gravity=eps_g,
                epsilon_spin_raw=eps_spin_raw,
                epsilon_spin_rindler=eps_spin,
                epsilon_total_rindler=eps_tot,
                outside_geff_mod_gravity_only=geff_g,
                outside_geff_mod_with_spin=geff_tot,
                geff_mod_delta=geff_tot - geff_g,
                flyby_geff_phi_ratio=flyby_geff_ratio_at_surface(radius_m, radius_m),
                compactness_rs_over_r=compactness_rs_over_r(mass_kg, radius_m),
                notes=note,
            )
        )

    # Tipping with spin: when does ε_tot cross thresholds?
    thresholds = {
        "charm_tip": EPS_CHARM_TIP,
        "uniform_ns_max": C_RINDLER_SHARED,
        "horizon": EPS_HORIZON,
        "top_center_factor": EPS_TOP_TIP / 1.5,
    }
    spin_at_horizon = {}
    for name, m_msun, r_km in [
        ("1.4_Msun", 1.4, 13.0),
        ("1.98_Msun", 1.98, 14.6),
        ("3.16_Msun_tail", 3.16, 14.6),
    ]:
        mass_kg = m_msun * M_SUN_KG
        radius_m = r_km * 1000.0
        eps_g = gravitational_phi_epsilon(mass_kg, radius_m)
        omega_for_horizon = None
        for om in [10.0, 50.0, 100.0, 300.0, 640.0, 1000.0, 2000.0, 5000.0, 10000.0]:
            om *= 2.0 * math.pi
            eps_tot = eps_g + epsilon_spin_co_rotation(
                om, radius_m, colatitude_rad=math.pi / 2.0
            )
            if eps_tot >= EPS_HORIZON:
                omega_for_horizon = om
                break
        spin_at_horizon[name] = {
            "epsilon_gravity": eps_g,
            "omega_horizon_rad_s": omega_for_horizon,
            "omega_horizon_hz": (
                omega_for_horizon / (2.0 * math.pi) if omega_for_horizon else None
            ),
            "omega_breakup_hz": breakup_omega_rad_s(mass_kg, radius_m) / (2.0 * math.pi),
        }

    return {
        "interpretation": (
            "Spin adds ε_spin ≈ 2(v_tan/c)sin²θ/Rindler on the same outside slot as "
            "ε_grav = GM/(Rc²). That raises (1+ε)^α in the nuclear G_eff modulator. "
            "Separately, flyby G_eff uses (φ/φ_ref)^α with geometric φ (not spin); spin "
            "feeds φ_eff via 6aε and screens orbital G_eff through the inertia factor."
        ),
        "lean_modules": [
            "Hqiv.Geometry.HQVMetric",
            "Hqiv.Physics.NuclearOutsideTemperatureDynamics",
            "Hqiv.Physics.OrbitalFlybyScaffold",
            "scripts/hqiv_orbital_flyby_omaxwell.py (co_spin_lapse_fraction)",
            "scripts/hqiv_wide_binary.py (spin_lapse_epsilon)",
        ],
        "epsilon_spin_formula": "2(v_tan/c)|v̂·t̂|(R/r)^2 sin²θ / D_R",
        "outside_geff_formula": "1 + γ((1+ε_total)^α − 1)",
        "flyby_geff_formula": "(φ/φ_ref)^α with φ = 1/(1+r/R_lapse)",
        "thresholds": thresholds,
        "spin_horizon_crossing": spin_at_horizon,
        "rows": [asdict(r) for r in rows],
    }


def zone_outer_radii(epsilon_surface: float, radius_m: float) -> tuple[float, float]:
    """
    Outer radii of top and charmed zones: [0, r_top)=top, [r_top, r_charm)=charm, [r_charm, R]=nuclear.
    """
    epsilon_center = 1.5 * epsilon_surface
    r_top = 0.0
    r_charm = 0.0
    if epsilon_center >= EPS_TOP_TIP:
        if epsilon_surface >= EPS_TOP_TIP:
            r_top = radius_m
        else:
            r_top = radius_m * math.sqrt(max(0.0, 3.0 - 2.0 * EPS_TOP_TIP / epsilon_surface))
    if epsilon_center >= EPS_CHARM_TIP:
        if epsilon_surface >= EPS_CHARM_TIP:
            r_charm = radius_m
        else:
            r_charm = radius_m * math.sqrt(max(0.0, 3.0 - 2.0 * EPS_CHARM_TIP / epsilon_surface))
        r_charm = max(r_charm, r_top)
    return r_top, r_charm


def layered_mass_kg(
    radius_m: float,
    r_top: float,
    r_charm: float,
    *,
    rho_n: float = RHO_NUCLEAR_KG_M3,
    rho_c: float | None = None,
    rho_t: float | None = None,
) -> float:
    rho_c = rho_c if rho_c is not None else matter_density("charmed")
    rho_t = rho_t if rho_t is not None else rho_top_kg_m3()
    mass = 0.0
    if r_top > 0.0:
        mass += (4.0 * math.pi / 3.0) * r_top**3 * rho_t
    if r_charm > r_top:
        mass += (4.0 * math.pi / 3.0) * (r_charm**3 - r_top**3) * rho_c
    if radius_m > r_charm:
        mass += (4.0 * math.pi / 3.0) * (radius_m**3 - r_charm**3) * rho_n
    return mass


def mass_uniform_nuclear_at_epsilon(epsilon_surface: float) -> tuple[float, float]:
    mass_kg = mass_from_epsilon_crit(epsilon_surface, RHO_NUCLEAR_KG_M3)
    radius_m = radius_uniform_density(mass_kg, RHO_NUCLEAR_KG_M3)
    return mass_kg, radius_m


def horizon_mass_at_radius(radius_m: float) -> float:
    """Mass for ε_s = 1/2 (Schwarzschild surface) at fixed R."""
    return EPS_HORIZON * radius_m * C_LIGHT**2 / G_NEWTON


@dataclass(frozen=True)
class GradientCollapseStage:
    stage: str
    mass_msun: float
    radius_km: float
    epsilon_surface: float
    epsilon_center: float
    r_top_over_R: float
    r_charm_over_R: float
    compactness_rs_over_r: float
    notes: str


def gradient_collapse_hypothesis() -> dict[str, object]:
    """
    Radial gradient hypothesis: crust stays nuclear while the core tips charmed, extending
    the mass tail; a charm→top cascade raises compactness toward an event horizon.

    Stages are computed at fixed outer radius after the uniform NS max (no hydrodynamic
    relaxation — a deliberate comparison-layer witness).
    """
    rho_c = matter_density("charmed")
    rho_t = rho_top_kg_m3()

    m_uniform, r_uniform = mass_uniform_nuclear_at_epsilon(C_RINDLER_SHARED)
    eps_s0 = C_RINDLER_SHARED
    eps_center0 = 1.5 * eps_s0
    r_top, r_charm = zone_outer_radii(eps_s0, r_uniform)
    m_charm_tail = layered_mass_kg(r_uniform, r_top, r_charm, rho_c=rho_c, rho_t=rho_t)
    m_horizon_fixed_r = horizon_mass_at_radius(r_uniform)

    # Top tipping at fixed R: ε_s must reach EPS_TOP_TIP / 1.5
    eps_top_at_fixed_r = EPS_TOP_TIP / 1.5
    m_top_threshold = eps_top_at_fixed_r * r_uniform * C_LIGHT**2 / G_NEWTON
    m_top_sphere = layered_mass_kg(r_uniform, r_uniform, 0.0, rho_c=rho_c, rho_t=rho_t)

    stages = [
        GradientCollapseStage(
            stage="uniform_nuclear_max",
            mass_msun=m_uniform / M_SUN_KG,
            radius_km=r_uniform / 1000.0,
            epsilon_surface=eps_s0,
            epsilon_center=eps_center0,
            r_top_over_R=r_top / r_uniform,
            r_charm_over_R=r_charm / r_uniform,
            compactness_rs_over_r=compactness_rs_over_r(m_uniform, r_uniform),
            notes="Surface ε = γ/2; core ε = 0.30 already above α·γ charm tipping",
        ),
        GradientCollapseStage(
            stage="charmed_core_tail",
            mass_msun=m_charm_tail / M_SUN_KG,
            radius_km=r_uniform / 1000.0,
            epsilon_surface=gravitational_phi_epsilon(m_charm_tail, r_uniform),
            epsilon_center=epsilon_interior(
                gravitational_phi_epsilon(m_charm_tail, r_uniform), 0.0, r_uniform
            ),
            r_top_over_R=r_top / r_uniform,
            r_charm_over_R=r_charm / r_uniform,
            compactness_rs_over_r=compactness_rs_over_r(m_charm_tail, r_uniform),
            notes=f"Inner {r_charm/r_uniform:.0%} volume → charmed (ρ×{rho_c/RHO_NUCLEAR_KG_M3:.2f})",
        ),
        GradientCollapseStage(
            stage="top_seed_threshold",
            mass_msun=m_top_threshold / M_SUN_KG,
            radius_km=r_uniform / 1000.0,
            epsilon_surface=eps_top_at_fixed_r,
            epsilon_center=EPS_TOP_TIP,
            r_top_over_R=0.0,
            r_charm_over_R=r_charm / r_uniform,
            compactness_rs_over_r=compactness_rs_over_r(m_top_threshold, r_uniform),
            notes="Center ε hits α; top core can nucleate before horizon",
        ),
        GradientCollapseStage(
            stage="horizon_at_fixed_radius",
            mass_msun=m_horizon_fixed_r / M_SUN_KG,
            radius_km=r_uniform / 1000.0,
            epsilon_surface=EPS_HORIZON,
            epsilon_center=1.5 * EPS_HORIZON,
            r_top_over_R=0.0,
            r_charm_over_R=0.0,
            compactness_rs_over_r=1.0,
            notes="ε_s = 1/2 Schwarzschild surface at same R",
        ),
        GradientCollapseStage(
            stage="full_top_sphere_runaway",
            mass_msun=m_top_sphere / M_SUN_KG,
            radius_km=r_uniform / 1000.0,
            epsilon_surface=gravitational_phi_epsilon(m_top_sphere, r_uniform),
            epsilon_center=epsilon_interior(
                gravitational_phi_epsilon(m_top_sphere, r_uniform), 0.0, r_uniform
            ),
            r_top_over_R=1.0,
            r_charm_over_R=0.0,
            compactness_rs_over_r=compactness_rs_over_r(m_top_sphere, r_uniform),
            notes=f"Charm→top cascade completion (ρ×{rho_t/RHO_NUCLEAR_KG_M3:.0f}); collapse driver",
        ),
    ]

    return {
        "hypothesis": (
            "Radial ε gradient tips charmed matter in the core before the uniform NS ceiling; "
            "a charm→top cascade at ε_0 = α raises ρ by ~80× and drives Rs/R → 1."
        ),
        "tipping_thresholds": {
            "epsilon_charm_tip": EPS_CHARM_TIP,
            "epsilon_top_tip_center": EPS_TOP_TIP,
            "epsilon_horizon_surface": EPS_HORIZON,
            "epsilon_uniform_ns_max_surface": C_RINDLER_SHARED,
        },
        "matter_density_kg_m3": {
            "nuclear": RHO_NUCLEAR_KG_M3,
            "charmed": rho_c,
            "top": rho_t,
            "charmed_over_nuclear": rho_c / RHO_NUCLEAR_KG_M3,
            "top_over_nuclear": rho_t / RHO_NUCLEAR_KG_M3,
            "top_over_charmed": rho_t / rho_c,
        },
        "mass_tail_msun": {
            "uniform_nuclear_max": m_uniform / M_SUN_KG,
            "charmed_core_at_same_R": m_charm_tail / M_SUN_KG,
            "delta_charm_tail": (m_charm_tail - m_uniform) / M_SUN_KG,
            "top_seed_at_same_R": m_top_threshold / M_SUN_KG,
            "horizon_at_same_R": m_horizon_fixed_r / M_SUN_KG,
            "full_top_sphere_at_same_R": m_top_sphere / M_SUN_KG,
        },
        "cascade_gap_msun": {
            "charm_tail_to_top_seed": (m_top_threshold - m_charm_tail) / M_SUN_KG,
            "charm_tail_to_horizon": (m_horizon_fixed_r - m_charm_tail) / M_SUN_KG,
            "top_seed_to_horizon": (m_horizon_fixed_r - m_top_threshold) / M_SUN_KG,
        },
        "stages": [asdict(s) for s in stages],
        "open_flavour_cascade_weight": hep.heavy_quarkonium_cascade_weight(),
        "charm_to_bottom_ratio": hep.bottom_strange_spectator_coherence_weight(),
    }


def flattening_fraction(omega_rad_s: float, omega_break_rad_s: float) -> float:
    """
    Centrifugal flattening slot: ``f = (γ/2)(Ω/Ω_break)²`` capped at breakup.

    Same ``γ/2 = c_rindler_shared`` lattice constant as the NS mass ceiling and
    ``liquidLocalFieldDivisorH2O = 1 − γ/2``.
    """
    if omega_break_rad_s <= 0.0:
        return 0.0
    ratio = min(1.0, abs(omega_rad_s) / omega_break_rad_s)
    return (GAMMA / 2.0) * ratio * ratio


def oblate_radii_m(
    spherical_radius_m: float,
    mass_kg: float,
    omega_rad_s: float,
) -> tuple[float, float, float, float]:
    """
    Volume-preserving oblate spheroid from spherical reference radius.

    ``R_eq = R_sph (1+f)``, ``R_pol = R_sph / (1+f)²`` with ``f = (γ/2)(Ω/Ω_break)²``.
    """
    omega_break = breakup_omega_rad_s(mass_kg, spherical_radius_m)
    f_flat = flattening_fraction(omega_rad_s, omega_break)
    k = 1.0 + f_flat
    r_equatorial = spherical_radius_m * k
    r_polar = spherical_radius_m / (k * k)
    return r_equatorial, r_polar, f_flat, omega_break


def ellipsoid_surface_radius_m(
    r_equatorial_m: float,
    r_polar_m: float,
    colatitude_rad: float,
) -> float:
    """Distance from center to oblate surface at colatitude θ (from spin pole)."""
    sin_t = math.sin(colatitude_rad)
    cos_t = math.cos(colatitude_rad)
    return math.sqrt((r_equatorial_m * sin_t) ** 2 + (r_polar_m * cos_t) ** 2)


def epsilon_surface_at_latitude(
    mass_kg: float,
    r_equatorial_m: float,
    r_polar_m: float,
    omega_rad_s: float,
    colatitude_rad: float,
) -> tuple[float, float, float, float]:
    """
    Surface ε slots at latitude θ: (ε_grav, ε_spin, ε_total, r_surface).
    """
    r_surf = ellipsoid_surface_radius_m(r_equatorial_m, r_polar_m, colatitude_rad)
    eps_grav = gravitational_phi_epsilon(mass_kg, r_surf)
    eps_spin = epsilon_spin_co_rotation(
        omega_rad_s,
        r_polar_m,
        colatitude_rad=colatitude_rad,
        observer_radius_m=r_surf,
    )
    return eps_grav, eps_spin, eps_grav + eps_spin, r_surf


def matter_phase_flags(epsilon_surface: float) -> dict[str, bool]:
    eps_center = 1.5 * epsilon_surface
    return {
        "charm_tipped": eps_center >= EPS_CHARM_TIP,
        "top_tipped": eps_center >= EPS_TOP_TIP,
        "horizon_surface": epsilon_surface >= EPS_HORIZON,
    }


@dataclass(frozen=True)
class LatitudeGradientRow:
    label: str
    colatitude_deg: float
    epsilon_gravity: float
    epsilon_spin: float
    epsilon_total: float
    epsilon_center: float
    outside_geff_mod: float
    charm_tipped: bool
    top_tipped: bool
    horizon_surface: bool
    r_charm_over_Rpol: float
    r_top_over_Rpol: float
    notes: str


@dataclass(frozen=True)
class SpinOblateScenario:
    label: str
    mass_msun: float
    omega_hz: float
    omega_over_breakup: float
    flattening_f: float
    radius_equatorial_km: float
    radius_polar_km: float
    radius_spherical_km: float
    mass_charmed_tail_msun: float
    delta_tail_vs_no_spin_msun: float
    compactness_equator: float
    compactness_polar: float
    latitude_rows: tuple[LatitudeGradientRow, ...]


def charmed_tail_mass_oblate(
    mass_kg: float,
    omega_rad_s: float,
    *,
    spherical_radius_m: float | None = None,
    use_equatorial_tipping: bool = True,
) -> tuple[float, float, float, float, float]:
    """
  Layered charmed-tail mass on oblate geometry.

    Tipping uses equatorial ε if ``use_equatorial_tipping``; integration uses polar
    depth coordinate ``R_pol`` (spin flattens polar radius).
    """
    rho_c = matter_density("charmed")
    rho_t = rho_top_kg_m3()
    if spherical_radius_m is None:
        spherical_radius_m = radius_uniform_density(mass_kg, RHO_NUCLEAR_KG_M3)
    r_eq, r_pol, f_flat, _ = oblate_radii_m(spherical_radius_m, mass_kg, omega_rad_s)

    if use_equatorial_tipping:
        eps_s, _, _, _ = epsilon_surface_at_latitude(
            mass_kg, r_eq, r_pol, omega_rad_s, math.pi / 2.0
        )
    else:
        eps_s = gravitational_phi_epsilon(mass_kg, r_pol)

    r_top, r_charm = zone_outer_radii(eps_s, r_pol)
    m_tail = layered_mass_kg(r_pol, r_top, r_charm, rho_c=rho_c, rho_t=rho_t)
    return m_tail, r_eq, r_pol, f_flat, eps_s


def latitude_scan_for_scenario(
    label: str,
    mass_msun: float,
    omega_hz: float,
) -> SpinOblateScenario:
    mass_kg = mass_msun * M_SUN_KG
    omega = omega_hz * 2.0 * math.pi
    r_sph = radius_uniform_density(mass_kg, RHO_NUCLEAR_KG_M3)
    r_eq, r_pol, f_flat, om_break = oblate_radii_m(r_sph, mass_kg, omega)
    m_tail, _, _, _, eps_eq = charmed_tail_mass_oblate(mass_kg, omega, spherical_radius_m=r_sph)
    m_tail_no_spin, _, _, _, _ = charmed_tail_mass_oblate(mass_kg, 0.0, spherical_radius_m=r_sph)

    lat_rows: list[LatitudeGradientRow] = []
    for colat_deg in (0.0, 45.0, 90.0):
        colat = math.radians(colat_deg)
        eps_g, eps_s, eps_t, _ = epsilon_surface_at_latitude(
            mass_kg, r_eq, r_pol, omega, colat
        )
        flags = matter_phase_flags(eps_t)
        r_top, r_charm = zone_outer_radii(eps_t, r_pol)
        lat_rows.append(
            LatitudeGradientRow(
                label=label,
                colatitude_deg=colat_deg,
                epsilon_gravity=eps_g,
                epsilon_spin=eps_s,
                epsilon_total=eps_t,
                epsilon_center=1.5 * eps_t,
                outside_geff_mod=outside_geff_modulator_from_epsilon(eps_t),
                charm_tipped=flags["charm_tipped"],
                top_tipped=flags["top_tipped"],
                horizon_surface=flags["horizon_surface"],
                r_charm_over_Rpol=r_charm / r_pol if r_pol > 0 else 0.0,
                r_top_over_Rpol=r_top / r_pol if r_pol > 0 else 0.0,
                notes="pole" if colat_deg == 0 else ("equator" if colat_deg == 90 else "mid"),
            )
        )

    return SpinOblateScenario(
        label=label,
        mass_msun=mass_msun,
        omega_hz=omega_hz,
        omega_over_breakup=omega / om_break if om_break > 0 else 0.0,
        flattening_f=f_flat,
        radius_equatorial_km=r_eq / 1000.0,
        radius_polar_km=r_pol / 1000.0,
        radius_spherical_km=r_sph / 1000.0,
        mass_charmed_tail_msun=m_tail / M_SUN_KG,
        delta_tail_vs_no_spin_msun=(m_tail - m_tail_no_spin) / M_SUN_KG,
        compactness_equator=compactness_rs_over_r(mass_kg, r_eq),
        compactness_polar=compactness_rs_over_r(mass_kg, r_pol),
        latitude_rows=tuple(lat_rows),
    )


def spin_oblate_gradient_hypothesis() -> dict[str, object]:
    """
    Spin + oblate flattening folded into the radial gradient witness.

    * Flattening ``f = (γ/2)(Ω/Ω_break)²`` shrinks ``R_pol`` and grows ``R_eq``.
    * ``ε_spin(θ)`` vanishes at the pole, peaks at the equator.
    * Charmed/top tipping thresholds are evaluated per latitude; equatorial spin
      can cross horizon ε before the pole sees charm tipping.
    """
    m_uniform, r_uniform = mass_uniform_nuclear_at_epsilon(C_RINDLER_SHARED)
    om_break_uniform = breakup_omega_rad_s(m_uniform, r_uniform)

    scenario_specs: list[tuple[str, float, float | None]] = [
        ("1.98 M☉ uniform max, no spin", 1.98, 0.0),
        ("1.98 M☉ at half breakup", 1.98, om_break_uniform * 0.5 / (2 * math.pi)),
        ("1.98 M☉ at breakup", 1.98, om_break_uniform / (2 * math.pi)),
        ("3.16 M☉ charmed tail, no spin", 3.16, 0.0),
        ("3.16 M☉ charmed tail, half breakup", 3.16, None),
        ("1.4 M☉ ms pulsar (640 Hz)", 1.4, 640.0),
    ]

    scenarios: list[SpinOblateScenario] = []
    for label, m_msun, hz in scenario_specs:
        if hz is None:
            mass_kg = m_msun * M_SUN_KG
            r_sph = radius_uniform_density(mass_kg, RHO_NUCLEAR_KG_M3)
            hz = breakup_omega_rad_s(mass_kg, r_sph) * 0.5 / (2 * math.pi)
        scenarios.append(latitude_scan_for_scenario(label, m_msun, hz))

    # First latitude to hit each threshold (scan omega for 1.98 Msun equator)
    mass_kg = 1.98 * M_SUN_KG
    r_sph = radius_uniform_density(mass_kg, RHO_NUCLEAR_KG_M3)
    om_break = breakup_omega_rad_s(mass_kg, r_sph)
    tipping_omega: dict[str, float | None] = {}
    for name, threshold in [
        ("charm_tip_equator", EPS_CHARM_TIP),
        ("top_tip_center_equator", EPS_TOP_TIP),
        ("horizon_surface_equator", EPS_HORIZON),
    ]:
        found = None
        for frac in [x * 0.05 for x in range(0, 21)]:
            om = om_break * frac
            r_eq, r_pol, _, _ = oblate_radii_m(r_sph, mass_kg, om)
            _, _, eps_t, _ = epsilon_surface_at_latitude(
                mass_kg, r_eq, r_pol, om, math.pi / 2.0
            )
            eps_c = 1.5 * eps_t
            if name.startswith("charm") and eps_c >= threshold:
                found = om / (2 * math.pi)
                break
            if name.startswith("top") and eps_c >= threshold:
                found = om / (2 * math.pi)
                break
            if name.startswith("horizon") and eps_t >= threshold:
                found = om / (2 * math.pi)
                break
        tipping_omega[name] = found

    return {
        "hypothesis": (
            "Oblate flattening f=(γ/2)(Ω/Ω_break)² couples breakup spin to R_pol shrink; "
            "ε_spin(θ) tips charmed/top slots at the equator first; cascade horizon "
            "can open before polar charm tipping."
        ),
        "flattening_formula": "f = (γ/2)(Ω/Ω_break)², R_eq = R_sph(1+f), R_pol = R_sph/(1+f)²",
        "equatorial_tipping_omega_hz_1p98Msun": tipping_omega,
        "scenarios": [
            {
                **asdict(s),
                "latitude_rows": [asdict(r) for r in s.latitude_rows],
            }
            for s in scenarios
        ],
    }


# Longitudinal O-Maxwell + lapse-drag torsion (flyby / fluid closure slots)
KAPPA_L_DEFAULT = GAMMA  # monogamy tangent overlap γ = 2/5
RHO_CRUST_KG_M3 = 1.0e14  # witness crust density scale (not a fit knob)
H_CRUST_M = 1.0e3  # integrated crust thickness (mass budget)
H_CRUST_TORQUE_M = 10.0  # active shear layer for HQIV–Alfvén coupling (~skin depth)
B_SURFACE_T_DEFAULT = 1.0e8  # 10^{12} G
ETA_DYNAMO_DEFAULT = GAMMA  # lattice-aligned dynamo / induction efficiency (γ = 2/5)
NS_SURFACE_T_K = 1.0e5  # photosphere-scale witness for η(ξ, ε) induction slot
BETA_KINETIC_CAP = 0.9999  # witness cap below horizon tangent slot
M_ELECTRON_EV = 510998.9499969  # eV
PAIR_THRESHOLD_VACUUM_EV = 2.0 * M_ELECTRON_EV
K_B_EV_PER_K = 8.617333262e-5
WIEN_PEAK_FACTOR = 2.821439  # x ≈ 2.82 for Planck peak energy / kT
B_CR_TESLA = 4.414e13  # Schwinger / critical field scale
MAX_MAGNETOSPHERIC_UPSCATTERS = 12
MU_0_SI = 4.0 * math.pi * 1.0e-7  # N/A²
R_CRUST_CALIBRATION_M = 1.0e3  # ~1 km crust diffusion scale for η calibration witness
SECONDS_PER_YEAR = 365.25 * 86400.0


def relativistic_doppler_temperature_boost(beta: float) -> float:
    """Relativistic Doppler factor √(1+β)/(1−β) for an incoming photon bath."""
    b = min(max(beta, 0.0), BETA_KINETIC_CAP)
    if b <= 0.0:
        return 1.0
    return math.sqrt((1.0 + b) / (1.0 - b))


def surface_co_spin_v_over_c(
    omega_rad_s: float,
    radius_m: float,
    colatitude_rad: float,
) -> float:
    """Equatorial co-spin speed ``v = Ω R sinθ`` as ``v/c``."""
    sin_t = math.sin(colatitude_rad)
    v = abs(omega_rad_s) * radius_m * sin_t
    return min(BETA_KINETIC_CAP, v / C_LIGHT)


def combined_kinetic_v_over_c(
    omega_rad_s: float,
    radius_m: float,
    colatitude_rad: float,
    *,
    cmb_doppler_v_m_s: float = notd.CMB_DIPOLE_V_M_S,
) -> float:
    """
    Additive kinetic slot (lab convention): co-spin plus CMB peculiar motion.

    Matches ``LabOutsideEnvironment.combined_phi_epsilon`` booking of dipole ``v/c``
    on the outside channel, extended with crust co-rotation.
    """
    v_spin = surface_co_spin_v_over_c(omega_rad_s, radius_m, colatitude_rad)
    v_cmb = notd.cmb_proper_motion_v_over_c(cmb_doppler_v_m_s)
    return min(BETA_KINETIC_CAP, v_spin + v_cmb)


def compact_object_effective_outside_temperature_K(
    surface_temperature_K: float,
    omega_rad_s: float,
    radius_m: float,
    colatitude_rad: float,
    *,
    cmb_temperature_K: float = notd.CMB_TEMPERATURE_K,
    cmb_doppler_v_m_s: float = notd.CMB_DIPOLE_V_M_S,
) -> dict[str, float]:
    """
    Spin- and CMB-aware outside temperature for the ``T(ξ)`` ladder.

    * Photosphere channel — ``T_surf × (1 + 2 β_spin)`` (same ``2v/c`` witness as
      ``mass_horizon_doppler_lapse`` / ``epsilon_spin_co_rotation``).
    * CMB channel — monopole ``T_CMB`` Doppler-boosted by ``β_spin + v_CMB/c``.
    * ``T_out`` — max of the two (whichever bath dominates the crust readout).
    """
    beta_spin = surface_co_spin_v_over_c(omega_rad_s, radius_m, colatitude_rad)
    beta_combined = combined_kinetic_v_over_c(
        omega_rad_s, radius_m, colatitude_rad, cmb_doppler_v_m_s=cmb_doppler_v_m_s
    )
    boost_cmb = relativistic_doppler_temperature_boost(beta_combined)
    t_surface_eff = surface_temperature_K * (1.0 + 2.0 * beta_spin)
    t_cmb_eff = cmb_temperature_K * boost_cmb
    t_out = max(t_surface_eff, t_cmb_eff)
    return {
        "surface_temperature_K": surface_temperature_K,
        "surface_temperature_effective_K": t_surface_eff,
        "cmb_temperature_effective_K": t_cmb_eff,
        "outside_temperature_effective_K": t_out,
        "beta_spin_over_c": beta_spin,
        "beta_combined_over_c": beta_combined,
        "cmb_doppler_boost": boost_cmb,
    }


def compact_object_combined_phi_epsilon(
    phi_gravity: float,
    omega_rad_s: float,
    radius_m: float,
    colatitude_rad: float,
    *,
    cmb_doppler_v_m_s: float = notd.CMB_DIPOLE_V_M_S,
    use_rindler_spin: bool = True,
) -> dict[str, float]:
    """
    Outside ``G_eff`` stack: gravity + co-spin ε + CMB dipole ``v/c``.

    Spin uses ``epsilon_spin_co_rotation`` (Rindler-suppressed Doppler slot).
    """
    eps_spin = epsilon_spin_co_rotation(
        omega_rad_s,
        radius_m,
        colatitude_rad=colatitude_rad,
        use_rindler_denominator=use_rindler_spin,
    )
    eps_cmb = notd.cmb_proper_motion_v_over_c(cmb_doppler_v_m_s)
    phi_combined = max(0.0, phi_gravity) + eps_spin + eps_cmb
    return {
        "phi_gravity": max(0.0, phi_gravity),
        "epsilon_spin": eps_spin,
        "epsilon_cmb_dipole": eps_cmb,
        "phi_combined": phi_combined,
    }


def thermal_photon_peak_energy_ev(temperature_K: float) -> float:
    """Planck-peak photon energy ``≈ 2.82 kT``."""
    return WIEN_PEAK_FACTOR * K_B_EV_PER_K * max(temperature_K, 0.0)


def infall_photon_energy_boost_factor(phi_gravity: float, beta_spin: float) -> float:
    """Blueshift slot for infalling bath photons: gravity well + co-spin ``2v/c``."""
    return 1.0 + max(0.0, phi_gravity) + 2.0 * max(0.0, beta_spin)


def pair_production_threshold_ev(B_tesla: float) -> float:
    """
    Pair threshold in a magnetized bath (softens as ``B → B_cr``).

    Vacuum limit ``2 m_e c²``; witness uses ``2 m_e c² √(1 − (B/B_cr)²)``.
    """
    b = min(abs(B_tesla), 0.999 * B_CR_TESLA)
    ratio = b / B_CR_TESLA
    return PAIR_THRESHOLD_VACUUM_EV * math.sqrt(max(1e-12, 1.0 - ratio * ratio))


def magnetospheric_upscatter_to_threshold(
    e_infall_ev: float,
    e_threshold_ev: float,
    beta_spin: float,
    phi_gravity: float = 0.0,
    *,
    max_scatters: int = MAX_MAGNETOSPHERIC_UPSCATTERS,
) -> tuple[float, int, bool]:
    """
    Repeated magnetospheric upscatter (Compton / curvature chain witness).

    Per-step gain ``infall_boost × (1 + 2β_spin)`` re-applies the infall + co-spin
    blueshift on each magnetospheric leg (photon bath keeps infalling toward ``c``).
    """
    kinetic_gain = 1.0 + 2.0 * max(0.0, beta_spin)
    infall_boost = infall_photon_energy_boost_factor(phi_gravity, beta_spin)
    gain = infall_boost * kinetic_gain
    if e_infall_ev <= 0.0 or e_threshold_ev <= 0.0 or gain <= 1.0:
        return e_infall_ev, 0, e_infall_ev >= e_threshold_ev
    e = e_infall_ev
    n = 0
    while e < e_threshold_ev and n < max_scatters:
        e *= gain
        n += 1
    return e, n, e >= e_threshold_ev


def pair_production_witness(
    t_out_K: float,
    phi_gravity: float,
    beta_spin: float,
    B_tesla: float,
) -> dict[str, float | bool | int]:
    """
    Pair-production margin for infalling / bathed photons at the crust.

    Direct thermal+infall energy is usually sub-MeV; fast spin opens a **cascade
    channel** in the magnetosphere so upscattered photons can cross ``2 m_e c²``
    (or a lowered threshold in strong ``B``).
    """
    e_thermal = thermal_photon_peak_energy_ev(t_out_K)
    infall_boost = infall_photon_energy_boost_factor(phi_gravity, beta_spin)
    e_infall = e_thermal * infall_boost
    e_thr = pair_production_threshold_ev(B_tesla)
    direct_margin = e_infall / max(e_thr, 1.0e-30)
    e_cascade, n_scatter, cascade_hit = magnetospheric_upscatter_to_threshold(
        e_infall, e_thr, beta_spin, phi_gravity
    )
    effective_margin = e_cascade / max(e_thr, 1.0e-30)
    active = cascade_hit or direct_margin >= 1.0
    excess = max(0.0, effective_margin - 1.0)
    rate = min(1.0, excess) if active else 0.0
    return {
        "thermal_photon_energy_ev": e_thermal,
        "infall_boost_factor": infall_boost,
        "infall_photon_energy_ev": e_infall,
        "pair_threshold_ev": e_thr,
        "pair_production_margin_direct": direct_margin,
        "pair_cascade_scatters": n_scatter,
        "pair_cascade_energy_ev": e_cascade,
        "pair_production_margin_effective": effective_margin,
        "pair_production_active": active,
        "pair_rate_proxy": rate,
    }


def pair_induction_b_field_t(
    pair_rate_proxy: float,
    eta_induction: float,
    B_surface_t: float,
    a_lt_si: float,
    a_grav_si: float,
) -> float:
    """Pair cascade feeds the induction / current channel → schematic ``B_pair``."""
    if pair_rate_proxy <= 0.0:
        return 0.0
    shear_frac = min(1.0, abs(a_lt_si) / max(a_grav_si, 1.0e-30))
    return eta_induction * min(1.0, pair_rate_proxy) * B_surface_t * shear_frac * GAMMA


def coupling_log_phi(phi_readout: float) -> float:
    """Algebra-first O-Maxwell log slot ``log(φ+1)``."""
    return math.log(max(phi_readout, 0.0) + 1.0)


def co_rotation_specific_h(
    omega_rad_s: float,
    r_surface_m: float,
    colatitude_rad: float,
) -> float:
    """Specific angular momentum |h| = ω R² sin²θ for co-rotating surface material."""
    sin_t = math.sin(colatitude_rad)
    return abs(omega_rad_s) * r_surface_m * r_surface_m * sin_t * sin_t


def polar_fiber_release_at_latitude(
    omega_rad_s: float,
    r_equatorial_m: float,
    r_surface_m: float,
    colatitude_rad: float,
) -> float:
    """
    Polar-fiber release ``ρ_pol = 1 − (h_z/h_ref)²`` on a co-rotating shell.

    Low |L_z| (pole) releases the tangent lapse channel; equatorial lock suppresses it
  (`hqiv_orbital_flyby_omaxwell.polar_fiber_release_fraction`).
    """
    if abs(omega_rad_s) <= 0.0:
        return 0.0
    h_ref = abs(omega_rad_s) * r_equatorial_m * r_equatorial_m
    if h_ref <= 0.0:
        return 0.0
    h_z = co_rotation_specific_h(omega_rad_s, r_surface_m, colatitude_rad)
    frac = min(1.0, h_z / h_ref)
    return max(0.0, 1.0 - frac * frac)


def lapse_drag_vector_fraction(
    colatitude_rad: float,
    rho_pol: float,
) -> float:
    """
    Lense–Thirring fraction ``λ = γ sin²θ ρ_pol`` (`derived_horizon_vector_fraction`).
    """
    sin_t = math.sin(colatitude_rad)
    return max(0.0, min(1.0, GAMMA * sin_t * sin_t * max(0.0, rho_pol)))


def axial_phi_gradient_si(
    mass_kg: float,
    r_surface_m: float,
    colatitude_rad: float,
    eps_pole: float,
    eps_equator: float,
    r_polar_m: float,
) -> float:
    """
    Axial ``|s·∇φ|`` for longitudinal O-Maxwell stress along the spin axis.

    * Newtonian slot: ``|∂_z (GM/r)| = GM|cosθ|/r²``.
    * Spin/oblate slot: lapse differential ``|Δε| c² / R_pol`` from equator–pole tipping.
    """
    cos_t = abs(math.cos(colatitude_rad))
    grad_newton = G_NEWTON * mass_kg * cos_t / max(r_surface_m * r_surface_m, 1.0)
    grad_spin = abs(eps_equator - eps_pole) * C_LIGHT * C_LIGHT / max(r_polar_m, 1.0)
    return grad_newton + grad_spin


def longitudinal_em_axial_accel_si(
    phi_readout: float,
    grad_axial_phi: float,
    *,
    kappa_l: float = KAPPA_L_DEFAULT,
) -> float:
    """
    Longitudinal stress acceleration ``κ_L Λ (s·∇φ)`` (`HQIVFluidClosureScaffold` /
    conductor O-Maxwell slot; flyby ``kappa_l`` channel).
    """
    lam = coupling_log_phi(phi_readout)
    return kappa_l * lam * grad_axial_phi


def lapse_drag_metric_accel_si(
    a_grav: float,
    epsilon_spin: float,
    epsilon_total: float,
    vector_fraction: float,
) -> tuple[float, float, float]:
    """
    Horizon metric stress split into isotropic trace vs L-T tangent.

    L-T tangent uses spin lapse ε_spin only (co-spin Doppler slot); isotropic trace
    uses total ε. Weak-field proxy: ``a = a_grav × ε × γ``.
    """
    a_lt = a_grav * epsilon_spin * GAMMA * vector_fraction
    a_iso = a_grav * epsilon_total * GAMMA * (1.0 - vector_fraction)
    a_drag = a_lt + a_iso
    return a_drag, a_lt, a_iso


@dataclass(frozen=True)
class FieldTorsionRow:
    label: str
    colatitude_deg: float
    epsilon_total: float
    rho_pol: float
    lapse_vector_fraction: float
    phi_readout: float
    grad_axial_phi_si: float
    a_grav_si: float
    a_longitudinal_si: float
    a_lapse_drag_si: float
    a_lense_thirring_si: float
    a_isotropic_drag_si: float
    psi_shear_deg: float
    psi_long_deg: float
    torsion_coupling_chi: float
    delta_b_over_b: float
    notes: str


@dataclass(frozen=True)
class FieldTorsionScenario:
    label: str
    mass_msun: float
    omega_hz: float
    omega_over_breakup: float
    peak_psi_shear_deg: float
    peak_psi_long_deg: float
    peak_torsion_colatitude_deg: float
    peak_torsion_coupling_chi: float
    equator_psi_shear_deg: float
    pole_psi_shear_deg: float
    latitude_rows: tuple[FieldTorsionRow, ...]


def field_torsion_at_latitude(
    mass_kg: float,
    r_equatorial_m: float,
    r_polar_m: float,
    omega_rad_s: float,
    colatitude_rad: float,
    *,
    label: str = "",
    eps_equator: float | None = None,
    eps_pole: float | None = None,
    B_surface_t: float = B_SURFACE_T_DEFAULT,
    rho_crust_kg_m3: float = RHO_CRUST_KG_M3,
) -> FieldTorsionRow:
    ch = torsion_channels_at_latitude(
        mass_kg,
        r_equatorial_m,
        r_polar_m,
        omega_rad_s,
        colatitude_rad,
        B_surface_t=B_surface_t,
        rho_crust_kg_m3=rho_crust_kg_m3,
        eps_equator=eps_equator,
        eps_pole=eps_pole,
    )
    _, eps_s, eps_t, _ = epsilon_surface_at_latitude(
        mass_kg, r_equatorial_m, r_polar_m, omega_rad_s, colatitude_rad
    )
    a_drag, _, a_iso = lapse_drag_metric_accel_si(
        ch.a_grav_si, eps_s, eps_t, ch.lapse_vector_fraction
    )

    col_deg = ch.colatitude_deg
    notes = "pole" if col_deg < 1.0 else ("equator" if col_deg > 89.0 else "mid")
    return FieldTorsionRow(
        label=label,
        colatitude_deg=col_deg,
        epsilon_total=ch.epsilon_total,
        rho_pol=ch.rho_pol,
        lapse_vector_fraction=ch.lapse_vector_fraction,
        phi_readout=ch.phi_readout,
        grad_axial_phi_si=ch.grad_axial_phi_si,
        a_grav_si=ch.a_grav_si,
        a_longitudinal_si=ch.a_long_linear_si,
        a_lapse_drag_si=a_drag,
        a_lense_thirring_si=ch.a_lense_thirring_si,
        a_isotropic_drag_si=a_iso,
        psi_shear_deg=math.degrees(ch.psi_shear_rad),
        psi_long_deg=math.degrees(ch.psi_long_rad),
        torsion_coupling_chi=ch.chi_shear,
        delta_b_over_b=ch.delta_b_over_b,
        notes=notes,
    )


def latitude_torsion_scan(
    mass_msun: float,
    omega_hz: float,
    label: str,
) -> FieldTorsionScenario:
    mass_kg = mass_msun * M_SUN_KG
    r_sph = radius_uniform_density(mass_kg, RHO_NUCLEAR_KG_M3)
    omega_rad_s = 2.0 * math.pi * omega_hz
    om_break = breakup_omega_rad_s(mass_kg, r_sph)
    r_eq, r_pol, _, _ = oblate_radii_m(r_sph, mass_kg, omega_rad_s)

    _, _, eps_equator, _ = epsilon_surface_at_latitude(
        mass_kg, r_eq, r_pol, omega_rad_s, math.pi / 2.0
    )
    _, _, eps_pole, _ = epsilon_surface_at_latitude(
        mass_kg, r_eq, r_pol, omega_rad_s, 0.0
    )

    rows: list[FieldTorsionRow] = []
    peak_shear = -1.0
    peak_long = 0.0
    peak_colat = 0.0
    peak_chi = 0.0
    pole_shear = 0.0
    equator_shear = 0.0

    for col_deg in range(0, 91, 5):
        col_rad = math.radians(col_deg)
        row = field_torsion_at_latitude(
            mass_kg,
            r_eq,
            r_pol,
            omega_rad_s,
            col_rad,
            label=label,
            eps_equator=eps_equator,
            eps_pole=eps_pole,
        )
        rows.append(row)
        if row.psi_shear_deg > peak_shear:
            peak_shear = row.psi_shear_deg
            peak_colat = row.colatitude_deg
            peak_chi = row.torsion_coupling_chi
            peak_long = row.psi_long_deg
        if col_deg == 0:
            pole_shear = row.psi_shear_deg
        if col_deg == 90:
            equator_shear = row.psi_shear_deg

    return FieldTorsionScenario(
        label=label,
        mass_msun=mass_msun,
        omega_hz=omega_hz,
        omega_over_breakup=omega_rad_s / om_break if om_break > 0 else 0.0,
        peak_psi_shear_deg=peak_shear,
        peak_psi_long_deg=peak_long,
        peak_torsion_colatitude_deg=peak_colat,
        peak_torsion_coupling_chi=peak_chi,
        equator_psi_shear_deg=equator_shear,
        pole_psi_shear_deg=pole_shear,
        latitude_rows=tuple(rows),
    )


def legendre_p(l: int, mu: float) -> float:
    """Legendre polynomial ``P_l(mu)`` for ``mu = cos θ`` (colatitude θ from spin pole)."""
    if l == 0:
        return 1.0
    if l == 1:
        return mu
    if l == 2:
        return 0.5 * (3.0 * mu * mu - 1.0)
    if l == 3:
        return 0.5 * (5.0 * mu * mu * mu - 3.0 * mu)
    raise ValueError(f"legendre_p supports l<=3, got l={l}")


def zonal_multipole_coefficients(
    mu_values: list[float],
    f_values: list[float],
    sin_theta_weights: list[float],
    *,
    max_l: int = 3,
) -> dict[int, float]:
    """
    Axisymmetric (m=0) projection ``c_l = ∫ f(θ) P_l(cosθ) sinθ dθ / ∫ P_l² sinθ dθ``.
    """
    coeffs: dict[int, float] = {}
    for l in range(max_l + 1):
        pl = [legendre_p(l, mu) for mu in mu_values]
        norm = sum(p * p * w for p, w in zip(pl, sin_theta_weights))
        if norm <= 0.0:
            coeffs[l] = 0.0
            continue
        coeffs[l] = sum(f * p * w for f, p, w in zip(f_values, pl, sin_theta_weights)) / norm
    return coeffs


def multipole_fractions(coeffs: dict[int, float]) -> dict[str, float]:
    """Relative |c_l|/|c_0| for l=1,2,3."""
    c0 = abs(coeffs.get(0, 0.0))
    ref = max(c0, 1.0e-30)
    return {
        "l1_over_l0": abs(coeffs.get(1, 0.0)) / ref,
        "l2_over_l0": abs(coeffs.get(2, 0.0)) / ref,
        "l3_over_l0": abs(coeffs.get(3, 0.0)) / ref,
    }


def coriolis_surface_accel_si(
    omega_rad_s: float,
    radius_m: float,
    colatitude_rad: float,
) -> float:
    """Co-spin Coriolis scale ``|2Ω×v| ~ 2 Ω² R sinθ`` (crust co-rotation witness)."""
    sin_t = math.sin(colatitude_rad)
    return 2.0 * abs(omega_rad_s) * abs(omega_rad_s) * radius_m * sin_t


def crust_coriolis_shear_gate(colatitude_rad: float) -> float:
    """Mid-latitude Coriolis–shear gate ``sin²θ |cosθ|`` (peaks near 45° colatitude)."""
    sin_t = math.sin(colatitude_rad)
    cos_t = math.cos(colatitude_rad)
    return sin_t * sin_t * abs(cos_t)


def emission_centroid_cos_colatitude(
    mu_values: list[float],
    f_values: list[float],
    sin_theta_weights: list[float],
) -> float:
    """Brightness-weighted ``⟨cos θ⟩`` along the spin axis (NICER offset proxy)."""
    denom = sum(f * w for f, w in zip(f_values, sin_theta_weights))
    if denom <= 0.0:
        return 0.0
    return sum(mu * f * w for mu, f, w in zip(mu_values, f_values, sin_theta_weights)) / denom


def tau_mis_m1_gate(slip: SlipTorqueBalanceRow) -> dict[str, float]:
    """
    Azimuthal m=1 amplitude and phase from crust misalignment torque balance.

    ``τ_mis`` tilts the magnetic axis relative to the spin axis; witness uses
    ``ψ_shear`` and ``δB/B`` as obliquity proxies (not catalog ``τ_ratio``, which
    is misaligning-dominated at observed B).
    """
    psi_rad = math.radians(min(max(slip.psi_shear_deg, 0.0), 89.9))
    mis_amp = min(
        1.0,
        slip.delta_b_over_b * (1.0 + GAMMA)
        + GAMMA * math.sin(psi_rad)
        + ALPHA * min(slip.chi_shear_peak, 1.0),
    )
    phi_mis_rad = psi_rad * (1.0 + ALPHA_GAMMA)
    alpha_tilt_deg = slip.alpha_equilibrium_aligning_enhanced_deg
    return {
        "m1_amplitude": mis_amp,
        "phi_mis_rad": phi_mis_rad,
        "psi_shear_deg": slip.psi_shear_deg,
        "delta_b_over_b": slip.delta_b_over_b,
        "tau_misalign_n_m": slip.tau_misalign_n_m,
        "torque_ratio_b_eff": slip.torque_ratio_b_eff,
        "torque_ratio_aligning_enhanced": slip.torque_ratio_aligning_enhanced,
        "alpha_equilibrium_b_eff_deg": slip.alpha_equilibrium_b_eff_deg,
        "alpha_equilibrium_aligning_enhanced_deg": slip.alpha_equilibrium_aligning_enhanced_deg,
        "alpha_tilt_deg": alpha_tilt_deg,
        "B_align_t": slip.B_align_t,
        "aligning_enhancement_factor": slip.aligning_enhancement_factor,
    }


def emission_at_colatitude_phi(
    emit_zonal: float,
    mu: float,
    sin_theta: float,
    m1_amplitude: float,
    phi_mis_rad: float,
    phi_rad: float,
) -> float:
    """Zonal emission × (1 + m₁ sinθ cos(φ − φ_mis)) — tilted-dipole azimuthal modulation."""
    az = sin_theta * math.cos(phi_rad - phi_mis_rad)
    return max(0.0, emit_zonal * (1.0 + m1_amplitude * az))


def emission_at_colatitude_phi_tilted(
    pole_ch: float,
    cor_g: float,
    eq_ch: float,
    cor_a_term: float,
    sin_theta: float,
    m1_amplitude: float,
    phi_mis_rad: float,
    alpha_tilt_rad: float,
    phi_rad: float,
) -> float:
    """
    Tilted dipole: pole and Coriolis/shear belts carry m=1 with α_B phase offset.

    Pole channel keeps weak azimuthal modulation; mid-latitude shear uses full m₁
  with ``φ_mis + α_B`` so two bright regions need not be antipodal (NICER J0740).
    """
    m1_pole = m1_amplitude * ALPHA
    m1_shear = m1_amplitude
    pole_emit = pole_ch * (1.0 + m1_pole * sin_theta * math.cos(phi_rad - phi_mis_rad))
    shear_emit = cor_g * eq_ch * (
        1.0 + m1_shear * sin_theta * math.cos(phi_rad - phi_mis_rad + alpha_tilt_rad)
    )
    return max(0.0, pole_emit + shear_emit + cor_a_term)


def synthesize_two_spot_from_surface_map(
    ring_rows: list[dict[str, float]],
    m1_amplitude: float,
    phi_mis_rad: float,
    alpha_tilt_rad: float,
    *,
    n_phi: int = 72,
    peak_exclusion_rad: float = 0.35,
) -> dict[str, float]:
    """Two brightest peaks on the full (θ, φ) emission map (tilted m=1 channels)."""
    phis = [2.0 * math.pi * i / n_phi for i in range(n_phi)]
    grid: list[list[float]] = []
    for row in ring_rows:
        sin_t = row["sin_theta"]
        ring = [
            emission_at_colatitude_phi_tilted(
                row["pole_ch"],
                row["cor_g"],
                row["eq_ch"],
                row["cor_a_term"],
                sin_t,
                m1_amplitude,
                phi_mis_rad,
                alpha_tilt_rad,
                phi,
            )
            for phi in phis
        ]
        grid.append(ring)

    if not grid or m1_amplitude <= 0.0:
        return {
            "phi_spot1_rad": phi_mis_rad,
            "phi_spot2_rad": phi_mis_rad + math.pi,
            "theta_spot1_rad": 0.0,
            "theta_spot2_rad": 0.0,
            "longitude_separation_deg": 180.0,
            "azimuthal_offset_from_antipode_deg": 0.0,
        }

    n_theta = len(grid)
    flat_max = max(
        ((i, j, grid[i][j]) for i in range(n_theta) for j in range(n_phi)),
        key=lambda t: t[2],
    )
    i1, j1, v1 = flat_max
    theta1 = ring_rows[i1]["col_rad"]
    phi1 = phis[j1]

    def _ang_sep(i: int, j: int) -> float:
        th1, th2 = ring_rows[i1]["col_rad"], ring_rows[i]["col_rad"]
        dth = th1 - th2
        dphi = phis[j1] - phis[j]
        if dphi > math.pi:
            dphi -= 2.0 * math.pi
        if dphi < -math.pi:
            dphi += 2.0 * math.pi
        return math.sqrt(dth * dth + dphi * dphi)

    candidates = [
        (i, j, grid[i][j])
        for i in range(n_theta)
        for j in range(n_phi)
        if _ang_sep(i, j) >= peak_exclusion_rad
    ]
    if not candidates:
        i2, j2 = (i1 + n_theta // 2) % n_theta, (j1 + n_phi // 2) % n_phi
        v2 = grid[i2][j2]
    else:
        i2, j2, v2 = max(candidates, key=lambda t: t[2])

    theta2 = ring_rows[i2]["col_rad"]
    phi2 = phis[j2]
    dphi = abs(phi2 - phi1)
    if dphi > math.pi:
        dphi = 2.0 * math.pi - dphi
    antipode_phi = (phi1 + math.pi) % (2.0 * math.pi)
    offset_from_antipode = abs(phi2 - antipode_phi)
    if offset_from_antipode > math.pi:
        offset_from_antipode = 2.0 * math.pi - offset_from_antipode

    return {
        "phi_spot1_rad": phi1,
        "phi_spot2_rad": phi2,
        "theta_spot1_rad": theta1,
        "theta_spot2_rad": theta2,
        "colatitude_spot1_deg": math.degrees(theta1),
        "colatitude_spot2_deg": math.degrees(theta2),
        "longitude_separation_deg": math.degrees(dphi),
        "azimuthal_offset_from_antipode_deg": math.degrees(offset_from_antipode),
        "peak_emit_at_spot1": v1,
        "peak_emit_at_spot2": v2,
        "alpha_tilt_rad": alpha_tilt_rad,
    }


def synthesize_two_spot_longitudes(
    emit_at_peak_colat: float,
    mu_peak: float,
    sin_theta_peak: float,
    m1_amplitude: float,
    phi_mis_rad: float,
    *,
    n_phi: int = 360,
) -> dict[str, float]:
    """Two longitude peaks from m=1 cos(φ) at the shear-belt colatitude."""
    if emit_at_peak_colat <= 0.0 or m1_amplitude <= 0.0:
        return {
            "phi_spot1_rad": phi_mis_rad,
            "phi_spot2_rad": phi_mis_rad + math.pi,
            "longitude_separation_deg": 180.0,
            "azimuthal_offset_from_antipode_deg": 0.0,
        }
    phis = [2.0 * math.pi * i / n_phi for i in range(n_phi)]
    vals = [
        emission_at_colatitude_phi(
            emit_at_peak_colat, mu_peak, sin_theta_peak, m1_amplitude, phi_mis_rad, phi
        )
        for phi in phis
    ]
    idx1 = max(range(n_phi), key=lambda i: vals[i])
    phi1 = phis[idx1]
    half = n_phi // 2
    idx2 = max(range(n_phi), key=lambda i: vals[(i + half) % n_phi])
    phi2 = phis[idx2]
    sep = abs(phi2 - phi1)
    if sep > math.pi:
        sep = 2.0 * math.pi - sep
    sep_deg = math.degrees(sep)
    antipode_phi = (phi1 + math.pi) % (2.0 * math.pi)
    offset_from_antipode = abs(phi2 - antipode_phi)
    if offset_from_antipode > math.pi:
        offset_from_antipode = 2.0 * math.pi - offset_from_antipode
    return {
        "phi_spot1_rad": phi1,
        "phi_spot2_rad": phi2,
        "longitude_separation_deg": sep_deg,
        "azimuthal_offset_from_antipode_deg": math.degrees(offset_from_antipode),
        "peak_emit_at_spot1": vals[idx1],
        "peak_emit_at_spot2": vals[idx2],
    }


def m1_azimuthal_fraction(
    mu_values: list[float],
    emit_zonal_values: list[float],
    sin_theta_weights: list[float],
    m1_amplitude: float,
    phi_mis_rad: float,
    *,
    n_phi: int = 36,
    alpha_tilt_rad: float = 0.0,
    ring_channel_rows: list[dict[str, float]] | None = None,
) -> float:
    """RMS azimuthal variation / mean from tilted m=1 modulation (witness fraction)."""
    phis = [2.0 * math.pi * i / n_phi for i in range(n_phi)]
    mean_total = 0.0
    var_total = 0.0
    count = 0.0
    if ring_channel_rows is not None:
        for row, w in zip(ring_channel_rows, sin_theta_weights):
            if w <= 0.0:
                continue
            sin_t = row["sin_theta"]
            ring = [
                emission_at_colatitude_phi_tilted(
                    row["pole_ch"],
                    row["cor_g"],
                    row["eq_ch"],
                    row["cor_a_term"],
                    sin_t,
                    m1_amplitude,
                    phi_mis_rad,
                    alpha_tilt_rad,
                    phi,
                )
                for phi in phis
            ]
            ring_mean = sum(ring) / len(ring)
            ring_var = sum((v - ring_mean) ** 2 for v in ring) / len(ring)
            mean_total += ring_mean * w
            var_total += ring_var * w
            count += w
    else:
        for mu, ez, w in zip(mu_values, emit_zonal_values, sin_theta_weights):
            if w <= 0.0:
                continue
            sin_t = math.sqrt(max(0.0, 1.0 - mu * mu))
            ring = [
                emission_at_colatitude_phi(ez, mu, sin_t, m1_amplitude, phi_mis_rad, phi)
                for phi in phis
            ]
            ring_mean = sum(ring) / len(ring)
            ring_var = sum((v - ring_mean) ** 2 for v in ring) / len(ring)
            mean_total += ring_mean * w
            var_total += ring_var * w
            count += w
    if count <= 0.0:
        return 0.0
    mean = mean_total / count
    rms = math.sqrt(var_total / count)
    return rms / max(mean, 1.0e-30)


def surface_multipole_decomposition(
    mass_msun: float,
    omega_hz: float,
    *,
    label: str = "",
    B_surface_t: float = B_SURFACE_T_DEFAULT,
    rho_crust_kg_m3: float = RHO_CRUST_KG_M3,
    include_m1_from_tau_mis: bool = True,
) -> dict[str, object]:
    """
    Zonal l=1–3 decomposition of crust surface channels vs colatitude.

    Pole channel: ``ρ_pol × |ẑ·∇φ|/a_grav`` (stable alignment).
    Equator channel: ``χ × ψ_long × λ`` (induction / shear).
    Coriolis gate: ``sin²θ|cosθ|`` at mid-latitudes.
    Combined emission proxy feeds NICER-style centroid + quadrupole/octupole fractions.
    """
    scan = latitude_torsion_scan(mass_msun, omega_hz, label or f"{mass_msun:.2f} M☉")
    mass_kg = mass_msun * M_SUN_KG
    r_sph = radius_uniform_density(mass_kg, RHO_NUCLEAR_KG_M3)
    omega_rad_s = 2.0 * math.pi * omega_hz

    mu_vals: list[float] = []
    weights: list[float] = []
    pole_align: list[float] = []
    equator_ind: list[float] = []
    coriolis_g: list[float] = []
    b_proxy: list[float] = []
    psi_shear: list[float] = []
    emission: list[float] = []
    ring_channel_rows: list[dict[str, float]] = []

    for row in scan.latitude_rows:
        col_rad = math.radians(row.colatitude_deg)
        sin_t = math.sin(col_rad)
        mu = math.cos(col_rad)
        mu_vals.append(mu)
        weights.append(max(sin_t, 0.0))

        pole_ch = row.rho_pol * row.grad_axial_phi_si / max(row.a_grav_si, 1.0e-30)
        eq_ch = row.torsion_coupling_chi * math.radians(row.psi_long_deg) * row.lapse_vector_fraction
        cor_g = crust_coriolis_shear_gate(col_rad)
        r_eq, r_pol, _, _ = oblate_radii_m(
            radius_uniform_density(mass_kg, RHO_NUCLEAR_KG_M3),
            mass_kg,
            omega_rad_s,
        )
        r_surf = ellipsoid_surface_radius_m(r_eq, r_pol, col_rad)
        cor_a = coriolis_surface_accel_si(omega_rad_s, r_surf, col_rad)
        cor_a_term = GAMMA * cor_a / max(row.a_grav_si, 1.0e-30)

        b_loc = B_surface_t * (
            1.0
            + GAMMA * row.rho_pol
            + ALPHA * row.torsion_coupling_chi
            + row.delta_b_over_b
        )
        emit = pole_ch + cor_g * eq_ch + cor_a_term

        pole_align.append(pole_ch)
        equator_ind.append(eq_ch)
        coriolis_g.append(cor_g)
        b_proxy.append(b_loc)
        psi_shear.append(row.psi_shear_deg)
        emission.append(max(emit, 0.0))
        ring_channel_rows.append(
            {
                "col_rad": col_rad,
                "sin_theta": sin_t,
                "pole_ch": pole_ch,
                "eq_ch": eq_ch,
                "cor_g": cor_g,
                "cor_a_term": cor_a_term,
            }
        )

    channels: dict[str, object] = {}
    for name, vals in [
        ("pole_alignment", pole_align),
        ("equator_induction", equator_ind),
        ("coriolis_shear_gate", coriolis_g),
        ("B_surface_proxy", b_proxy),
        ("psi_shear_deg", psi_shear),
        ("emission_proxy", emission),
    ]:
        coeffs = zonal_multipole_coefficients(mu_vals, vals, weights, max_l=3)
        channels[name] = {
            "coefficients": coeffs,
            "fractions": multipole_fractions(coeffs),
        }

    emit_coeffs = zonal_multipole_coefficients(mu_vals, emission, weights, max_l=3)
    centroid_mu = emission_centroid_cos_colatitude(mu_vals, emission, weights)
    pole_offset = 1.0 - centroid_mu
    equator_offset = centroid_mu

    m1_block: dict[str, object] = {}
    if include_m1_from_tau_mis:
        slip = slip_torque_balance_for_star(
            mass_msun,
            omega_hz,
            label or f"{mass_msun:.2f} M☉ m1",
            B_surface_t=B_surface_t,
            rho_crust_kg_m3=rho_crust_kg_m3,
        )
        m1_gate = tau_mis_m1_gate(slip)
        m1_amp = float(m1_gate["m1_amplitude"])
        phi_mis = float(m1_gate["phi_mis_rad"])
        alpha_tilt_rad = math.radians(float(m1_gate["alpha_tilt_deg"]))
        m1_frac = m1_azimuthal_fraction(
            mu_vals,
            emission,
            weights,
            m1_amp,
            phi_mis,
            alpha_tilt_rad=alpha_tilt_rad,
            ring_channel_rows=ring_channel_rows,
        )
        two_spots = synthesize_two_spot_from_surface_map(
            ring_channel_rows,
            m1_amp,
            phi_mis,
            alpha_tilt_rad,
        )
        m1_block = {
            "tau_mis_m1_gate": m1_gate,
            "m1_azimuthal_fraction": m1_frac,
            "two_spot_longitudes": two_spots,
            "spot_colatitude_deg": two_spots.get("colatitude_spot1_deg", scan.peak_torsion_colatitude_deg),
        }

    return {
        "label": scan.label,
        "mass_msun": mass_msun,
        "omega_hz": omega_hz,
        "omega_over_breakup": scan.omega_over_breakup,
        "B_surface_t": B_surface_t,
        "peak_torsion_colatitude_deg": scan.peak_torsion_colatitude_deg,
        "emission_centroid_cos_colatitude": centroid_mu,
        "emission_offset_from_pole_over_R": pole_offset,
        "emission_offset_from_equator_over_R": equator_offset,
        "emission_multipole_coefficients": emit_coeffs,
        "emission_multipole_fractions": multipole_fractions(emit_coeffs),
        "channels": channels,
        "latitude_rows": [asdict(r) for r in scan.latitude_rows],
        **m1_block,
    }


def surface_zonal_multipole_decomposition(
    mass_msun: float,
    omega_hz: float,
    *,
    label: str = "",
    B_surface_t: float = B_SURFACE_T_DEFAULT,
    rho_crust_kg_m3: float = RHO_CRUST_KG_M3,
) -> dict[str, object]:
    """Backward-compatible alias (m=1 from τ_mis enabled by default)."""
    return surface_multipole_decomposition(
        mass_msun,
        omega_hz,
        label=label,
        B_surface_t=B_surface_t,
        rho_crust_kg_m3=rho_crust_kg_m3,
        include_m1_from_tau_mis=True,
    )


# Published NICER pulse-profile geometry overlays (comparison layer, not fits).
NICER_PPM_LITERATURE: dict[str, dict[str, object]] = {
    "J0030+0451": {
        "name": "PSR J0030+0451",
        "mass_msun": 1.37,
        "period_s": 4.865e-3,
        "radius_km_miller_median": 13.02,
        "radius_km_riley_median": 13.0,
        "spot_colatitude_deg_miller_median": math.degrees(0.531),  # θc1 rad Miller 2019 table
        "spot_colatitude_deg_riley_stpst": (15.0, 60.0),  # small spot + crescent, same hemisphere
        "hotspot_offset_km_range": (3.0, 15.0),
        "spot_count_miller": 3,
        "spot_count_riley_favored": 2,
        "references_bib": ["miller2019_j0030", "riley2021_j0740"],
    },
    "J0740+6620": {
        "name": "PSR J0740+6620",
        "mass_msun": 2.08,
        "period_s": 0.002885736411412693,
        "radius_km_riley_median": 12.39,
        "spot_angular_radius_deg_typical": 10.0,
        "azimuthal_offset_from_antipode_deg_min_prob": 25.0,
        "azimuthal_offset_from_antipode_probability": 0.84,
        "references_bib": ["riley2021_j0740", "miller2019_j0030"],
    },
}

NICER_J0030_MASS_MSUN = float(NICER_PPM_LITERATURE["J0030+0451"]["mass_msun"])
NICER_J0030_PERIOD_S = float(NICER_PPM_LITERATURE["J0030+0451"]["period_s"])
NICER_J0030_FREQ_HZ = 1.0 / NICER_J0030_PERIOD_S
NICER_J0030_B_GAUSS = 4.0e8
NICER_J0030_HOTSPOT_OFFSET_KM = tuple(NICER_PPM_LITERATURE["J0030+0451"]["hotspot_offset_km_range"])


def nicer_ppm_comparison_witness(pulsar_key: str) -> dict[str, object]:
    """Quantitative NICER overlay with m=1 τ_mis azimuthal spots."""
    lit = NICER_PPM_LITERATURE[pulsar_key]
    mass_msun = float(lit["mass_msun"])
    period_s = float(lit["period_s"])
    freq_hz = 1.0 / period_s
    if pulsar_key == "J0030+0451":
        b_t = NICER_J0030_B_GAUSS * 1.0e-4
    else:
        mass_kg = mass_msun * M_SUN_KG
        r_sph = radius_uniform_density(mass_kg, RHO_NUCLEAR_KG_M3)
        # catalog dipole if available; J0740 has weak Ṗ
        b_t = 1.9e4  # ~1.9e8 G from ATNF catalog witness
    decomp = surface_multipole_decomposition(
        mass_msun,
        freq_hz,
        label=f"{lit['name']} (NICER overlay)",
        B_surface_t=b_t,
        include_m1_from_tau_mis=True,
    )
    mass_kg = mass_msun * M_SUN_KG
    r_km = radius_uniform_density(mass_kg, RHO_NUCLEAR_KG_M3) / 1000.0
    emit_frac = decomp["emission_multipole_fractions"]
    centroid_km_from_pole = decomp["emission_offset_from_pole_over_R"] * r_km

    comparisons: dict[str, object] = {
        "centroid_offset_km_hqiv": centroid_km_from_pole,
        "spot_colatitude_deg_hqiv": decomp.get("spot_colatitude_deg"),
        "emission_l2_over_l0": emit_frac["l2_over_l0"],
        "emission_l3_over_l0": emit_frac["l3_over_l0"],
    }
    if "m1_azimuthal_fraction" in decomp:
        comparisons["m1_azimuthal_fraction"] = decomp["m1_azimuthal_fraction"]
        two = decomp.get("two_spot_longitudes", {})
        comparisons["longitude_separation_deg"] = two.get("longitude_separation_deg")
        comparisons["azimuthal_offset_from_antipode_deg"] = two.get(
            "azimuthal_offset_from_antipode_deg"
        )

    if pulsar_key == "J0030+0451":
        miller_col = float(lit["spot_colatitude_deg_miller_median"])
        comparisons["spot_colatitude_deg_miller_median"] = miller_col
        comparisons["spot_colatitude_delta_deg"] = abs(
            float(decomp.get("spot_colatitude_deg", 0.0)) - miller_col
        )
        offset_range = lit["hotspot_offset_km_range"]
        comparisons["centroid_in_literature_offset_km_range"] = (
            float(offset_range[0]) <= centroid_km_from_pole <= float(offset_range[1])
        )
    if pulsar_key == "J0740+6620":
        comparisons["azimuthal_offset_literature_min_deg"] = lit[
            "azimuthal_offset_from_antipode_deg_min_prob"
        ]
        comparisons["hqiv_exceeds_antipodal_offset_threshold"] = (
            float(comparisons.get("azimuthal_offset_from_antipode_deg", 0.0))
            >= float(lit["azimuthal_offset_from_antipode_deg_min_prob"])
        )
        comparisons["radius_km_riley_median"] = lit["radius_km_riley_median"]
        comparisons["radius_km_hqiv_uniform"] = r_km

    verdict_parts: list[str] = []
    if pulsar_key == "J0030+0451" and comparisons.get("centroid_in_literature_offset_km_range"):
        verdict_parts.append("centroid_offset_consistent")
    if emit_frac["l2_over_l0"] > 0.05:
        verdict_parts.append("quadrupole_present")
    if decomp.get("m1_azimuthal_fraction", 0.0) > 0.01:
        verdict_parts.append("m1_from_tau_mis")
    if pulsar_key == "J0740+6620" and comparisons.get("hqiv_exceeds_antipodal_offset_threshold"):
        verdict_parts.append("non_antipodal_like_nicer")

    return {
        "pulsar": lit["name"],
        "pulsar_key": pulsar_key,
        "nicer_literature": lit,
        "hqiv_decomposition": decomp,
        "quantitative_comparison": comparisons,
        "hqiv_centroid_offset_km_from_pole": centroid_km_from_pole,
        "hqiv_emission_l2_over_l0": emit_frac["l2_over_l0"],
        "hqiv_emission_l3_over_l0": emit_frac["l3_over_l0"],
        "verdict": verdict_parts or ["witness_computed"],
    }


def nicer_j0030_surface_multipole_witness() -> dict[str, object]:
    """HQIV zonal + m=1 multipoles vs NICER J0030+0451."""
    return nicer_ppm_comparison_witness("J0030+0451")


def nicer_j0740_surface_multipole_witness() -> dict[str, object]:
    """HQIV zonal + m=1 multipoles vs NICER J0740+6620."""
    return nicer_ppm_comparison_witness("J0740+6620")


def high_spin_mass_tail_multipole_grid() -> list[dict[str, object]]:
    """Scan high-mass / high-spin tail: equatorial induction vs Coriolis belt."""
    specs: list[tuple[str, float, float | None, float]] = [
        ("1.98 M☉ half breakup", 1.98, 0.5, B_SURFACE_T_DEFAULT),
        ("1.98 M☉ breakup", 1.98, 1.0, B_SURFACE_T_DEFAULT),
        ("2.08 M☉ J0740 mass @ catalog f", 2.08, None, 1.9e4),
        ("2.08 M☉ @ half breakup", 2.08, 0.5, B_SURFACE_T_DEFAULT),
        ("2.35 M☉ heavy tail", 2.35, 0.75, B_SURFACE_T_DEFAULT),
        ("2.35 M☉ @ breakup", 2.35, 1.0, B_SURFACE_T_DEFAULT),
    ]
    rows: list[dict[str, object]] = []
    for label, m_msun, om_frac, b_t in specs:
        mass_kg = m_msun * M_SUN_KG
        r_sph = radius_uniform_density(mass_kg, RHO_NUCLEAR_KG_M3)
        om_break_hz = breakup_omega_rad_s(mass_kg, r_sph) / (2.0 * math.pi)
        if om_frac is None:
            hz = 346.53  # J0740 catalog
        else:
            hz = om_break_hz * om_frac
        decomp = surface_multipole_decomposition(
            m_msun,
            hz,
            label=label,
            B_surface_t=b_t,
        )
        ef = decomp["emission_multipole_fractions"]
        rows.append(
            {
                "label": label,
                "mass_msun": m_msun,
                "omega_hz": hz,
                "omega_over_breakup": decomp["omega_over_breakup"],
                "emission_l2_over_l0": ef["l2_over_l0"],
                "emission_l3_over_l0": ef["l3_over_l0"],
                "centroid_cos_colatitude": decomp["emission_centroid_cos_colatitude"],
                "centroid_offset_from_pole_over_R": decomp["emission_offset_from_pole_over_R"],
                "peak_torsion_colatitude_deg": decomp["peak_torsion_colatitude_deg"],
                "m1_azimuthal_fraction": decomp.get("m1_azimuthal_fraction"),
                "longitude_separation_deg": (
                    decomp.get("two_spot_longitudes", {}).get("longitude_separation_deg")
                ),
            }
        )
    return rows


def solar_analogue_multipole_notes() -> dict[str, object]:
    """
    Solar–NS parallel for 2nd/3rd-degree surface dynamics (witness notes, not a simulation).

    Sun: differential rotation and active latitudes (~15–35°) concentrate shear and
    induction away from poles; helioseismology and surface magnetism carry strong
    quadrupole / octupole bands in cycle evolution. HQIV uses the same sin²θ / ρ_pol
    split on a rotating oblate body.
    """
    return {
        "solar_parallels": [
            "Differential rotation: equator faster → mid-latitude shear belts (active regions).",
            "HQIV: ε_spin and χ peak toward equator; ρ_pol releases poles.",
            "Coriolis: mid-latitude drift organizes flows — crust_coriolis_shear_gate peaks ~45°.",
            "Solar cycle: dipole + quadrupole/octupole G-band evolution (2nd/3rd degree).",
            "Coronal heating paper: longitudinal stress along ẑ·∇φ (same axial slot as NS crust).",
        ],
        "hqiv_latitude_division": {
            "poles": "ρ_pol → 1, axial ∇φ, stable μ_n alignment witness",
            "mid_latitudes": "Coriolis × shear, ψ_shear peak, l=2/l=3 emission",
            "equator": "ε_spin max, induction η, Alfvén launch",
        },
        "lean_refs": [
            "Hqiv.Physics.OrbitalTrajectoryJ2Scaffold (colatitudeSinSq)",
            "Hqiv.Physics.HQIVCollectiveModes (quadrupole torque)",
            "Hqiv.Physics.HorizonBlackbodyLadder (E/B mode fractions)",
        ],
    }


def surface_multipole_dynamics_hypothesis() -> dict[str, object]:
    """Zonal l=2/l=3 + m=1 τ_mis overlay vs NICER J0030/J0740 and high-spin tail."""
    scenarios = [
        ("PSR J0030+0451 NICER", NICER_J0030_MASS_MSUN, NICER_J0030_FREQ_HZ, NICER_J0030_B_GAUSS * 1.0e-4),
        ("PSR J0740+6620 NICER", float(NICER_PPM_LITERATURE["J0740+6620"]["mass_msun"]), 1.0 / float(NICER_PPM_LITERATURE["J0740+6620"]["period_s"]), 1.9e4),
        ("1.4 M☉ ms (640 Hz)", 1.4, 640.0, B_SURFACE_T_DEFAULT),
        ("1.98 M☉ breakup", 1.98, None, B_SURFACE_T_DEFAULT),
    ]
    rows: list[dict[str, object]] = []
    for label, m_msun, hz, b_t in scenarios:
        if hz is None:
            mass_kg = m_msun * M_SUN_KG
            r_sph = radius_uniform_density(mass_kg, RHO_NUCLEAR_KG_M3)
            hz = breakup_omega_rad_s(mass_kg, r_sph) / (2.0 * math.pi)
        row = surface_multipole_decomposition(
            m_msun,
            hz,
            label=label,
            B_surface_t=b_t,
            include_m1_from_tau_mis=True,
        )
        ef = row["emission_multipole_fractions"]
        two = row.get("two_spot_longitudes", {})
        rows.append(
            {
                "label": label,
                "mass_msun": m_msun,
                "omega_hz": hz,
                "omega_over_breakup": row["omega_over_breakup"],
                "peak_torsion_colatitude_deg": row["peak_torsion_colatitude_deg"],
                "emission_l1_over_l0": ef["l1_over_l0"],
                "emission_l2_over_l0": ef["l2_over_l0"],
                "emission_l3_over_l0": ef["l3_over_l0"],
                "B_proxy_l2_over_l0": row["channels"]["B_surface_proxy"]["fractions"]["l2_over_l0"],
                "B_proxy_l3_over_l0": row["channels"]["B_surface_proxy"]["fractions"]["l3_over_l0"],
                "centroid_cos_colatitude": row["emission_centroid_cos_colatitude"],
                "centroid_offset_from_pole_over_R": row["emission_offset_from_pole_over_R"],
                "m1_azimuthal_fraction": row.get("m1_azimuthal_fraction"),
                "longitude_separation_deg": two.get("longitude_separation_deg"),
                "azimuthal_offset_from_antipode_deg": two.get("azimuthal_offset_from_antipode_deg"),
            }
        )

    return {
        "hypothesis": (
            "Pole-aligned crust (ρ_pol, axial ∇φ) sources zonal dipole offset; "
            "mid-latitude Coriolis shear and equatorial induction feed l=2/l=3; "
            "τ_mis m=1 tilts the dipole to two longitude-offset spots "
            "(NICER J0030/J0740 pulse-profile geometry)."
        ),
        "formulas": {
            "zonal_projection": "c_l = ∫ f(θ) P_l(cosθ) sinθ dθ / ∫ P_l² sinθ dθ",
            "pole_channel": "ρ_pol |ẑ·∇φ| / a_grav",
            "equator_channel": "χ ψ_long λ",
            "coriolis_gate": "sin²θ |cosθ|",
            "coriolis_accel": "2 Ω² R sinθ",
            "emission_proxy": "pole_ch + coriolis_gate × equator_ch + γ a_Coriolis/a_grav",
            "centroid_offset": "1 − ⟨cosθ⟩_emission",
            "m1_from_tau_mis": "E(θ,φ) = E_zonal(θ) × (1 + m₁ sinθ cos(φ − φ_mis))",
            "m1_amplitude": "min(1, δB/B(1+γ) + γ sinψ + α χ_peak)",
        },
        "solar_analogue": solar_analogue_multipole_notes(),
        "nicer_j0030": nicer_j0030_surface_multipole_witness(),
        "nicer_j0740": nicer_j0740_surface_multipole_witness(),
        "high_spin_mass_tail": high_spin_mass_tail_multipole_grid(),
        "scenario_summary": rows,
        "full_scenarios": [
            surface_multipole_decomposition(
                NICER_J0030_MASS_MSUN,
                NICER_J0030_FREQ_HZ,
                label="J0030 full",
                B_surface_t=NICER_J0030_B_GAUSS * 1.0e-4,
            ),
            surface_multipole_decomposition(
                float(NICER_PPM_LITERATURE["J0740+6620"]["mass_msun"]),
                1.0 / float(NICER_PPM_LITERATURE["J0740+6620"]["period_s"]),
                label="J0740 full",
                B_surface_t=1.9e4,
            ),
        ],
    }


def mass_spin_torsion_grid() -> list[dict[str, float]]:
    """Peak field torsion vs mass and Ω/Ω_break (uniform nuclear sphere reference)."""
    grid: list[dict[str, float]] = []
    for m_msun in (1.4, 1.98, 3.16):
        mass_kg = m_msun * M_SUN_KG
        r_sph = radius_uniform_density(mass_kg, RHO_NUCLEAR_KG_M3)
        om_break = breakup_omega_rad_s(mass_kg, r_sph)
        for frac in (0.0, 0.25, 0.5, 0.75, 1.0):
            omega_rad_s = om_break * frac
            hz = omega_rad_s / (2.0 * math.pi)
            sc = latitude_torsion_scan(
                m_msun,
                hz,
                f"{m_msun:.2f} M☉ Ω/Ω_break={frac:.2f}",
            )
            grid.append(
                {
                    "mass_msun": m_msun,
                    "omega_over_breakup": frac,
                    "omega_hz": hz,
                    "peak_psi_shear_deg": sc.peak_psi_shear_deg,
                    "peak_torsion_colatitude_deg": sc.peak_torsion_colatitude_deg,
                    "peak_torsion_coupling_chi": sc.peak_torsion_coupling_chi,
                    "equator_psi_shear_deg": sc.equator_psi_shear_deg,
                }
            )
    return grid


def longitudinal_em_lapse_torsion_hypothesis() -> dict[str, object]:
    """
    Longitudinal EM + lapse-drag field torsion relative to the spin axis.

    **Longitudinal channel** (O-Maxwell / fluid closure):
      ``a_∥ = κ_L Λ (ẑ·∇φ)`` with ``κ_L = γ``, ``Λ = log(φ+1)``, and axial φ gradient
      from Newtonian ``GM|cosθ|/r²`` plus equator–pole lapse differential ``|Δε|c²/R_pol``.

    **Lapse-drag channel** (flyby repartition):
      ``a_drag = a_grav × ε × γ`` split into isotropic trace vs L-T tangent with
      ``λ = γ sin²θ ρ_pol`` (`derived_horizon_vector_fraction`).

    **Field torsion angle** (relative to spin axis):
      ``ψ_shear = atan2(a_LT, a_∥^lin)`` — Alfvén launch + ``τ_mis``.
      ``ψ_long = atan2(a_LT, a_∥^nl)`` — nonlinear ``φ_eff`` current drive.
    """
    scenario_specs: list[tuple[str, float, float | None]] = [
        ("1.4 M☉ slow pulsar (10 Hz)", 1.4, 10.0),
        ("1.4 M☉ ms pulsar (640 Hz)", 1.4, 640.0),
        ("1.98 M☉ uniform max, no spin", 1.98, 0.0),
        ("1.98 M☉ at half breakup", 1.98, None),
        ("1.98 M☉ at breakup", 1.98, None),
        ("3.16 M☉ charmed tail, half breakup", 3.16, None),
    ]

    scenarios: list[FieldTorsionScenario] = []
    for label, m_msun, hz in scenario_specs:
        if hz is None:
            mass_kg = m_msun * M_SUN_KG
            r_sph = radius_uniform_density(mass_kg, RHO_NUCLEAR_KG_M3)
            om_break = breakup_omega_rad_s(mass_kg, r_sph)
            if "half" in label:
                hz = om_break * 0.5 / (2.0 * math.pi)
            else:
                hz = om_break / (2.0 * math.pi)
        scenarios.append(latitude_torsion_scan(m_msun, hz, label))

    return {
        "hypothesis": (
            "Longitudinal O-Maxwell stress along the spin axis couples to lapse-drag "
            "Lense–Thirring tangent stress; field torsion ψ = atan2(a_LT, a_∥) peaks at "
            "mid-latitudes where sin²θ and polar-fiber release ρ_pol are both nonzero."
        ),
        "formulas": {
            "psi_shear": "atan2(a_LT, a_parallel_linear)",
            "psi_long": "atan2(a_LT, a_parallel_nonlinear_phi_eff)",
            "longitudinal_accel_linear": "a_∥ = κ_L log(φ+1) |ẑ·∇φ|, κ_L = γ",
            "longitudinal_accel_nonlinear": "a_∥^nl = κ_L log(6 a_grav ε + 1) |ẑ·∇φ|",
            "axial_phi_gradient": "GM|cosθ|/r² + |Δε|c²/R_pol",
            "lapse_drag": "a_LT = a_grav ε_spin γ λ, λ = γ sin²θ ρ_pol",
            "chi_shear": "a_LT a_∥^lin / a_grav²",
            "delta_b_over_b": "min(1, ψ_shear Ω R sinθ / v_A)",
            "polar_fiber_release": "ρ_pol = 1 − (h/h_ref)², h = ω R² sin²θ",
        },
        "lean_refs": [
            "Hqiv.Physics.HQIVFluidClosureScaffold (hqivLongitudinalStressTensor3)",
            "Hqiv.Physics.OrbitalFlybyScaffold (polar_fiber_phi_boost)",
            "scripts/hqiv_orbital_flyby_omaxwell.py (derived_horizon_vector_fraction)",
            "papers/longitudinal_em_force/longitudinal_em_force_hqiv.tex",
        ],
        "mass_spin_torsion_grid": mass_spin_torsion_grid(),
        "scenarios": [
            {
                **asdict(s),
                "latitude_rows": [asdict(r) for r in s.latitude_rows],
            }
            for s in scenarios
        ],
    }


# --- Alfvén slip-angle torque balance (ψ as misaligning shear driver) ----------


@dataclass(frozen=True)
class TorsionChannelsAtPoint:
    """Split slip angles: shear (Alfvén / τ_mis) vs longitudinal (φ_eff current drive)."""

    colatitude_deg: float
    epsilon_total: float
    rho_pol: float
    lapse_vector_fraction: float
    phi_readout: float
    grad_axial_phi_si: float
    a_grav_si: float
    a_long_linear_si: float
    a_long_nonlinear_si: float
    a_lense_thirring_si: float
    psi_shear_rad: float
    psi_long_rad: float
    chi_shear: float
    delta_b_over_b: float


def torsion_channels_at_latitude(
    mass_kg: float,
    r_equatorial_m: float,
    r_polar_m: float,
    omega_rad_s: float,
    colatitude_rad: float,
    *,
    B_surface_t: float = B_SURFACE_T_DEFAULT,
    rho_crust_kg_m3: float = RHO_CRUST_KG_M3,
    eps_equator: float | None = None,
    eps_pole: float | None = None,
) -> TorsionChannelsAtPoint:
    """
    Split HQIV torsion channels at one surface latitude.

    * ``ψ_shear = atan2(a_LT, a_∥^lin)`` — linear longitudinal; Alfvén launch + ``τ_mis``.
    * ``ψ_long = atan2(a_LT, a_∥^nl)`` — nonlinear ``φ_eff = 6 a_grav ε``; induction / currents.
    """
    r_surf = ellipsoid_surface_radius_m(r_equatorial_m, r_polar_m, colatitude_rad)
    eps_g, eps_s, eps_t, _ = epsilon_surface_at_latitude(
        mass_kg, r_equatorial_m, r_polar_m, omega_rad_s, colatitude_rad
    )
    if eps_equator is None:
        _, _, eps_equator, _ = epsilon_surface_at_latitude(
            mass_kg, r_equatorial_m, r_polar_m, omega_rad_s, math.pi / 2.0
        )
    if eps_pole is None:
        _, _, eps_pole, _ = epsilon_surface_at_latitude(
            mass_kg, r_equatorial_m, r_polar_m, omega_rad_s, 0.0
        )

    a_grav = G_NEWTON * mass_kg / max(r_surf * r_surf, 1.0)
    rho_pol = polar_fiber_release_at_latitude(
        omega_rad_s, r_equatorial_m, r_surf, colatitude_rad
    )
    vec_frac = lapse_drag_vector_fraction(colatitude_rad, rho_pol)
    phi_readout = flyby_phi_readout_at_radius(r_surf, r_surf)
    grad_ax = axial_phi_gradient_si(
        mass_kg, r_surf, colatitude_rad, eps_pole, eps_equator, r_polar_m
    )
    a_long_lin = longitudinal_em_axial_accel_si(phi_readout, grad_ax)
    a_long_nl = longitudinal_em_axial_accel_nonlinear(a_grav, eps_t, grad_ax)
    _, a_lt, _ = lapse_drag_metric_accel_si(a_grav, eps_s, eps_t, vec_frac)

    psi_shear = math.atan2(a_lt, max(a_long_lin, 1.0e-30))
    psi_long = math.atan2(a_lt, max(a_long_nl, 1.0e-30))
    chi_shear = (a_lt * a_long_lin) / max(a_grav * a_grav, 1.0e-30)

    v_a = alfven_speed_si(B_surface_t, rho_crust_kg_m3)
    delta_b = wave_amplitude_proxy(psi_shear, omega_rad_s, r_surf, colatitude_rad, v_a)

    return TorsionChannelsAtPoint(
        colatitude_deg=math.degrees(colatitude_rad),
        epsilon_total=eps_t,
        rho_pol=rho_pol,
        lapse_vector_fraction=vec_frac,
        phi_readout=phi_readout,
        grad_axial_phi_si=grad_ax,
        a_grav_si=a_grav,
        a_long_linear_si=a_long_lin,
        a_long_nonlinear_si=a_long_nl,
        a_lense_thirring_si=a_lt,
        psi_shear_rad=psi_shear,
        psi_long_rad=psi_long,
        chi_shear=chi_shear,
        delta_b_over_b=delta_b,
    )


def magnetospheric_b_eff_t(B_surface_t: float, delta_b_over_b: float) -> float:
    """``B_eff = B_surf × min(1, δB/B)`` for aligning torque in saturated rotators."""
    return B_surface_t * min(1.0, max(0.0, delta_b_over_b))


def steady_induction_field_t(
    a_lt_si: float,
    a_parallel_si: float,
    psi_long_rad: float,
    radius_m: float,
    B_surface_t: float,
    a_grav_si: float,
    *,
    eta: float = ETA_DYNAMO_DEFAULT,
) -> tuple[float, float]:
    """
    Schematic steady-state induction closure (stress → field).

    * LT shear branch: ``B_LT = η (a_LT / a_grav) B_surf``.
    * Longitudinal branch: ``B_long = η (a_∥ ψ_long / R) (R/c) B_surf / a_grav`` so
      ``∂B/∂t ~ η a_LT/R`` and ``B ~ η a_∥ ψ / R`` share the same lattice ``η``.
    """
    r = max(radius_m, 1.0)
    a_g = max(a_grav_si, 1.0e-30)
    b_lt = eta * (abs(a_lt_si) / a_g) * B_surface_t
    b_long = eta * (abs(a_parallel_si) * abs(psi_long_rad) / r) * (r / C_LIGHT) * (
        B_surface_t / a_g
    )
    return b_lt, b_long


def induction_growth_rate_t_per_s(
    a_lt_si: float,
    radius_m: float,
    *,
    eta: float = ETA_DYNAMO_DEFAULT,
) -> float:
    """``∂B/∂t ~ η a_LT / R`` (schematic induction source)."""
    return eta * abs(a_lt_si) / max(radius_m, 1.0)


def phi_eff_horizon_boost_accel_si(a_grav: float, epsilon_total: float) -> float:
    """Flyby repartitioned horizon boost ``φ_drag = 6 a_loc ε`` (metric channel)."""
    return 6.0 * a_grav * max(0.0, epsilon_total)


def coupling_log_from_accel(phi_accel_si: float) -> float:
    return math.log(max(phi_accel_si, 0.0) + 1.0)


def longitudinal_em_axial_accel_nonlinear(
    a_grav: float,
    epsilon_total: float,
    grad_axial_phi: float,
    *,
    kappa_l: float = KAPPA_L_DEFAULT,
) -> float:
    """Longitudinal channel with ``Λ = log(φ_eff+1)``, ``φ_eff = 6 a_grav ε``."""
    phi_eff = phi_eff_horizon_boost_accel_si(a_grav, epsilon_total)
    return kappa_l * coupling_log_from_accel(phi_eff) * grad_axial_phi


def alfven_speed_si(B_tesla: float, rho_kg_m3: float) -> float:
    return B_tesla / math.sqrt(4.0 * math.pi * max(rho_kg_m3, 1.0))


def light_cylinder_radius_m(omega_rad_s: float) -> float:
    if abs(omega_rad_s) <= 0.0:
        return float("inf")
    return C_LIGHT / abs(omega_rad_s)


def light_cylinder_magnetosphere_occupancy(
    omega_rad_s: float,
    radius_m: float,
) -> tuple[float, float]:
    """
    Trapped magnetosphere volume fraction ``(R/R_LC)³`` inside the light cylinder.

    As ``Ω → Ω_break``, ``R_LC → R`` and occupancy → 1 — pairs cascade in a
    closed volume before escaping.
    """
    r_lc = light_cylinder_radius_m(omega_rad_s)
    if not math.isfinite(r_lc) or r_lc <= 0.0:
        return 0.0, r_lc
    ratio = min(1.0, radius_m / r_lc)
    return ratio ** 3, r_lc


def magnetosphere_scatter_capture_fraction(
    n_scatters: int,
    omega_over_breakup: float,
    *,
    max_scatters: int = MAX_MAGNETOSPHERIC_UPSCATTERS,
) -> float:
    """Fraction of cascade depth realized before photon escape; ramps with spin."""
    scatter_frac = n_scatters / max(max_scatters, 1)
    spin_ramp = min(1.0, max(0.0, omega_over_breakup) ** 2)
    return min(1.0, scatter_frac * (0.25 + 0.75 * spin_ramp))


def continuous_pair_rate_proxy(
    margin_effective: float,
    n_scatters: int,
    omega_rad_s: float,
    radius_m: float,
    omega_break_rad_s: float,
) -> dict[str, float]:
    """
    Smooth pair turn-on: light-cylinder occupancy × scatter capture × margin excess.

    Below threshold, partial rate ``∝ margin³ × occupancy`` (incomplete cascades).
    """
    occupancy, r_lc = light_cylinder_magnetosphere_occupancy(omega_rad_s, radius_m)
    om_frac = abs(omega_rad_s) / max(omega_break_rad_s, 1.0e-30)
    capture = magnetosphere_scatter_capture_fraction(n_scatters, om_frac)
    gate = occupancy * capture
    margin = max(0.0, margin_effective)
    if margin >= 1.0:
        excess = min(1.0, margin - 1.0)
        rate = min(1.0, gate * (0.35 + 0.65 * excess))
    else:
        rate = min(1.0, gate * margin * margin * margin)
    strength = min(1.0, rate * om_frac)
    return {
        "light_cylinder_radius_m": r_lc,
        "light_cylinder_occupancy": occupancy,
        "pair_scatter_capture_fraction": capture,
        "pair_rate_continuous": rate,
        "cosmic_brake_strength": strength,
    }


def pair_production_spin_brake_torque_n_m(
    pair_rate_proxy: float,
    omega_rad_s: float,
    radius_m: float,
    *,
    eta_pair: float = GAMMA,
    cosmic_brake_strength: float = 1.0,
    light_cylinder_occupancy: float = 1.0,
) -> float:
    """
    Cosmic brake: ``τ_brake = P_pair / Ω`` with continuous light-cylinder gating.

    ``P_pair ~ η × rate² × 2 m_e c² × c × A × occupancy``.
    """
    if pair_rate_proxy <= 0.0 or abs(omega_rad_s) <= 0.0:
        return 0.0
    e_pair_j = PAIR_THRESHOLD_VACUUM_EV * 1.602176634e-19
    area = 4.0 * math.pi * radius_m * radius_m
    gate = max(0.0, min(1.0, cosmic_brake_strength)) * max(0.0, min(1.0, light_cylinder_occupancy))
    power = eta_pair * pair_rate_proxy * pair_rate_proxy * e_pair_j * C_LIGHT * area * gate
    return power / abs(omega_rad_s)


def charm_ledger_open_fraction(epsilon_center: float, epsilon_surface: float) -> float:
    """Open-charm ledger fraction from interior vs ``ε_crit = α·γ`` tipping."""
    if epsilon_center >= EPS_CHARM_TIP:
        return 1.0
    half_tip = EPS_CHARM_TIP * 0.5
    if epsilon_center <= half_tip:
        return 0.0
    return min(1.0, (epsilon_center - half_tip) / (EPS_CHARM_TIP - half_tip))


def charm_decay_b_field_t(
    epsilon_center: float,
    epsilon_surface: float,
    omega_over_breakup: float,
    eta_induction: float,
    B_surface_t: float,
) -> float:
    """
    Charmed-core weak decay sources B through multi-ledger induction.

    Couples open-charm tipping (``ε_center > α·γ``) to the induction channel with
    ``α·γ`` ledger weight and spin gate ``(Ω/Ω_break)²``.
    """
    charm_frac = charm_ledger_open_fraction(epsilon_center, epsilon_surface)
    if charm_frac <= 0.0:
        return 0.0
    ledger_coupling = ALPHA_GAMMA  # α·γ open-charm rung
    spin_gate = min(1.0, max(0.0, omega_over_breakup) ** 2)
    weak_branch = GAMMA  # weak ledger participates at γ
    return (
        eta_induction
        * charm_frac
        * spin_gate
        * B_surface_t
        * ledger_coupling
        * weak_branch
    )


def charm_shell_mass_kg(
    radius_m: float,
    r_top: float,
    r_charm: float,
    *,
    rho_c: float | None = None,
) -> float:
    rho_c = rho_c if rho_c is not None else matter_density("charmed")
    if r_charm <= r_top:
        return 0.0
    return (4.0 * math.pi / 3.0) * (r_charm**3 - r_top**3) * rho_c


def matter_layer_snapshot(
    mass_kg: float,
    radius_m: float,
    omega_rad_s: float,
    *,
    B_surface_t: float = B_SURFACE_T_DEFAULT,
) -> dict[str, float]:
    """Layered-matter + charm-B state at fixed radius (comparison witness)."""
    rho_c = matter_density("charmed")
    eps_s = gravitational_phi_epsilon(mass_kg, radius_m)
    eps_c = epsilon_interior(eps_s, 0.0, radius_m)
    r_top, r_charm = zone_outer_radii(eps_s, radius_m)
    m_layered = layered_mass_kg(radius_m, r_top, r_charm, rho_c=rho_c)
    m_charm = charm_shell_mass_kg(radius_m, r_top, r_charm, rho_c=rho_c)
    om_break = breakup_omega_rad_s(mass_kg, radius_m)
    om_over = omega_rad_s / om_break if om_break > 0.0 else 0.0
    charm_frac = charm_ledger_open_fraction(eps_c, eps_s)
    env = induction_environment_witness(
        eps_s,
        NS_SURFACE_T_K,
        omega_rad_s=omega_rad_s,
        radius_m=radius_m,
        colatitude_rad=math.pi / 2.0,
        B_tesla=B_surface_t,
    )
    eta = float(env["eta_induction"])
    b_charm = charm_decay_b_field_t(eps_c, eps_s, om_over, eta, B_surface_t)
    return {
        "mass_kg": mass_kg,
        "radius_m": radius_m,
        "epsilon_surface": eps_s,
        "epsilon_center": eps_c,
        "r_top_m": r_top,
        "r_charm_m": r_charm,
        "r_top_over_R": r_top / radius_m,
        "r_charm_over_R": r_charm / radius_m,
        "layered_mass_kg": m_layered,
        "charm_shell_mass_kg": m_charm,
        "charm_ledger_open_fraction": charm_frac,
        "omega_rad_s": omega_rad_s,
        "omega_over_breakup": om_over,
        "eta_induction": eta,
        "B_charm_t": b_charm,
    }


def spin_kinetic_energy_delta_j(
    mass_kg: float,
    radius_m: float,
    omega_from_rad_s: float,
    omega_to_rad_s: float,
) -> float:
    moment = moment_of_inertia_uniform_sphere(mass_kg, radius_m)
    return 0.5 * moment * (omega_from_rad_s**2 - omega_to_rad_s**2)


def charm_phase_conversion_mass_kg(
    r_charm_before_m: float,
    r_charm_after_m: float,
    *,
    rho_n: float = RHO_NUCLEAR_KG_M3,
    rho_c: float | None = None,
) -> float:
    """Mass change when a charmed-shell annulus reverts to nuclear density."""
    rho_c = rho_c if rho_c is not None else matter_density("charmed")
    delta_r3 = r_charm_before_m**3 - r_charm_after_m**3
    if delta_r3 <= 0.0:
        return 0.0
    return (4.0 * math.pi / 3.0) * delta_r3 * (rho_n - rho_c)


def _import_hep_decay_chain():
    import hqiv_hep_decay_chain as hdc

    return hdc


def compact_object_charm_decay_environment(
    B_surface_t: float,
    surface_temperature_K: float,
    *,
    phi_epsilon: float = 0.0,
) -> object:
    """
    NS magnetosphere environment for ``hqiv_hep_decay_chain`` width dressing.

    Uses surface B as collider reference so ``(B/B_ref)²`` is O(1) at the crust.
    """
    hdc = _import_hep_decay_chain()
    return hdc.ExperimentEnvironment(
        magnetic_field_tesla=max(B_surface_t, 0.0),
        collider_reference_tesla=max(abs(B_surface_t), 1.0),
        lab_temperature_K=max(surface_temperature_K, 1.0),
        gravity_tier="full",
    )


def charmed_baryon_hep_decay_readout(
    *,
    B_surface_t: float = B_SURFACE_T_DEFAULT,
    surface_temperature_K: float = NS_SURFACE_T_K,
    phi_epsilon: float = 0.0,
    species_id: str = "lambda_c",
) -> dict[str, float | str | int]:
    """
    Charmed-baryon width / Q from ``hqiv_hep_decay_chain`` at compact-object conditions.

    Returns laboratory and NS widths so callers can scale boundary pulses and mass-loss
    budgets without injecting external PDG tables.
    """
    hdc = _import_hep_decay_chain()
    env_ns = compact_object_charm_decay_environment(
        B_surface_t,
        surface_temperature_K,
        phi_epsilon=phi_epsilon,
    )
    env_lab = hdc.ExperimentEnvironment(
        magnetic_field_tesla=0.0,
        collider_reference_tesla=4.0,
        lab_temperature_K=293.15,
        gravity_tier="full",
    )
    parent = hdc.build_particle(species_id)
    edges_ns = hdc.edges_from_particle(parent, env=env_ns)
    edges_lab = hdc.edges_from_particle(parent, env=env_lab)
    width_ns = sum(e.width_per_s for e in edges_ns)
    width_lab = sum(e.width_per_s for e in edges_lab)
    dominant = max(edges_ns, key=lambda e: e.width_per_s) if edges_ns else None
    q_mev = float(dominant.q_mev) if dominant is not None else 0.0
    q_j = q_mev * MEV_TO_J
    m_baryon_kg = parent.mass_mev * MEV_TO_KG
    outside_support = notd.lab_outside_support_lifetime_factor(
        max(surface_temperature_K, 1.0),
        phi_gravity_epsilon=phi_epsilon,
    )
    width_eff = width_ns / max(outside_support, 1.0e-30)
    ledger_coupling = (
        hep.open_charm_production_weight() / hep.charmed_baryon_three_body_contact()
    )
    half_life_ns_s = math.inf if width_eff <= 0.0 else math.log(2.0) / width_eff
    half_life_lab_s = math.inf if width_lab <= 0.0 else math.log(2.0) / width_lab
    return {
        "species_id": species_id,
        "mass_mev": parent.mass_mev,
        "mass_kg": m_baryon_kg,
        "width_per_s_ns": width_ns,
        "width_per_s_lab": width_lab,
        "width_per_s_effective": width_eff,
        "width_ns_over_lab": width_ns / max(width_lab, 1.0e-30),
        "dominant_q_mev": q_mev,
        "dominant_q_j": q_j,
        "half_life_ns_s": half_life_ns_s,
        "half_life_lab_s": half_life_lab_s,
        "open_charm_weight": hep.open_charm_production_weight(),
        "charmed_baryon_three_body_contact": hep.charmed_baryon_three_body_contact(),
        "ledger_coupling": ledger_coupling,
        "outside_support_factor": outside_support,
        "weak_width_factor_ns": env_ns.weak_width_factor(),
        "open_channel_count": len(edges_ns),
        "lean_module": "Hqiv.Physics.HepDecayReadout",
        "python_module": "hqiv_hep_decay_chain",
    }


def charm_weak_energy_from_phase_conversion_j(
    phase_mass_kg: float,
    hep_readout: dict[str, float | str | int],
) -> float:
    """
    Radiative energy from charmed-baryon weak decay during charm→nuclear conversion.

    ``E = |Δm_phase| / m_Λc · Q · (γ/4) / charmedBaryonThreeBodyContact``.
    """
    mass_abs = abs(phase_mass_kg)
    if mass_abs <= 0.0:
        return 0.0
    m_baryon = float(hep_readout["mass_kg"])
    if m_baryon <= 0.0:
        return 0.0
    q_j = float(hep_readout["dominant_q_j"])
    ledger = float(hep_readout["ledger_coupling"])
    return (mass_abs / m_baryon) * q_j * ledger


def charm_retreat_transition_b_field_t(
    delta_r_charm_m: float,
    radius_m: float,
    eta_induction: float,
    B_surface_t: float,
    omega_rad_s: float,
    omega_break_rad_s: float,
    *,
    charm_mass_released_kg: float = 0.0,
    structural_mass_kg: float = 0.0,
    hep_readout: dict[str, float | str | int] | None = None,
) -> float:
    """
    Induction pulse from a retreating charm/nuclear phase boundary.

    When ``hep_readout`` is supplied, amplitude scales with HQIV weak width and
    dominant Q from ``hqiv_hep_decay_chain`` (Λ_c ladder).
    """
    if delta_r_charm_m <= 0.0:
        return 0.0
    radial_gate = min(1.0, delta_r_charm_m / max(radius_m, 1.0))
    spin_gate = min(1.0, abs(omega_rad_s) / max(omega_break_rad_s, 1.0e-30))
    ref_mass = max(structural_mass_kg, 1.0e-30)
    mass_gate = min(1.0, charm_mass_released_kg / (0.01 * ref_mass))
    ledger = ALPHA_GAMMA * GAMMA
    width_scale = 1.0
    q_scale = 1.0
    if hep_readout is not None:
        width_scale = float(hep_readout.get("width_ns_over_lab", 1.0))
        q_ref = 574.0 * MEV_TO_J
        q_scale = float(hep_readout.get("dominant_q_j", q_ref)) / max(q_ref, 1.0e-30)
        ledger *= float(hep_readout.get("ledger_coupling", 1.0))
    return (
        eta_induction
        * ledger
        * B_surface_t
        * radial_gate
        * spin_gate
        * (1.0 + mass_gate)
        * width_scale
        * q_scale
    )


def _spindown_charm_verdict(
    delta_r_over_r: float,
    b_retreat_ratio: float,
    b_charm_fractional_change: float,
) -> str:
    if delta_r_over_r < 1.0e-6:
        return "charm_geometry_unchanged_spin_energy_too_small"
    if b_retreat_ratio > 0.1:
        return "retreat_boundary_B_pulse_meaningful"
    if abs(b_charm_fractional_change) > 0.05:
        return "B_charm_tracks_retreat"
    return "retreat_geometry_visible_B_channels_minor"


def quantify_spindown_charm_retreat_feedback(
    mass_msun: float = 1.98,
    *,
    omega_start_fraction: float | None = None,
    omega_end_fraction: float = 0.5,
    B_surface_t: float = B_SURFACE_T_DEFAULT,
    radius_m: float | None = None,
) -> dict[str, object]:
    """
    Radiative / spin-down mass loss → lower ε → charm retreat → B response.

    Mass budget couples ``hqiv_hep_decay_chain`` Λ_c width and Q into:
      • charm-weak radiative mass loss from phase conversion
      • boundary ``B_transition`` amplitude (width/Q scaling)

    Spin kinetic energy ``ΔE = ½I(Ω₁²−Ω₂²)`` still books dipole-driven spindown mass.
    """
    rho_c = matter_density("charmed")
    mass_kg = mass_msun * M_SUN_KG
    r_sph = (
        radius_m
        if radius_m is not None
        else radius_uniform_density(mass_kg, RHO_NUCLEAR_KG_M3)
    )
    om_break = breakup_omega_rad_s(mass_kg, r_sph)
    om_start_frac = omega_start_fraction if omega_start_fraction is not None else 1.0
    omega1 = om_break * om_start_frac
    omega2 = om_break * omega_end_fraction

    eps_before_s = gravitational_phi_epsilon(mass_kg, r_sph)
    env_before = induction_environment_witness(
        eps_before_s,
        NS_SURFACE_T_K,
        omega_rad_s=omega1,
        radius_m=r_sph,
        colatitude_rad=math.pi / 2.0,
        B_tesla=B_surface_t,
    )
    t_out = float(env_before["outside_temperature_effective_K"])
    hep_readout = charmed_baryon_hep_decay_readout(
        B_surface_t=B_surface_t,
        surface_temperature_K=t_out,
        phi_epsilon=eps_before_s,
    )

    e_spin_j = spin_kinetic_energy_delta_j(mass_kg, r_sph, omega1, omega2)
    delta_m_spin_kg = e_spin_j / C_LIGHT**2

    before = matter_layer_snapshot(mass_kg, r_sph, omega1, B_surface_t=B_surface_t)

    # Provisional retreat geometry from spin-only mass loss (for phase mass estimate).
    mass_after_spin_only = mass_kg - delta_m_spin_kg
    after_spin_only = matter_layer_snapshot(
        mass_after_spin_only, r_sph, omega2, B_surface_t=B_surface_t
    )
    delta_r_charm_spin = before["r_charm_m"] - after_spin_only["r_charm_m"]
    delta_m_phase_spin = charm_phase_conversion_mass_kg(
        before["r_charm_m"],
        after_spin_only["r_charm_m"],
        rho_c=rho_c,
    )
    e_charm_weak_j = charm_weak_energy_from_phase_conversion_j(
        delta_m_phase_spin, hep_readout
    )
    delta_m_hep_kg = e_charm_weak_j / C_LIGHT**2
    delta_m_total_kg = delta_m_spin_kg + delta_m_hep_kg

    mass_after_struct = mass_kg - delta_m_total_kg
    after = matter_layer_snapshot(
        mass_after_struct, r_sph, omega2, B_surface_t=B_surface_t
    )

    delta_r_charm = before["r_charm_m"] - after["r_charm_m"]
    delta_charm_mass = before["charm_shell_mass_kg"] - after["charm_shell_mass_kg"]
    delta_m_phase = charm_phase_conversion_mass_kg(
        before["r_charm_m"], after["r_charm_m"], rho_c=rho_c
    )
    delta_layered = before["layered_mass_kg"] - after["layered_mass_kg"]

    b_transition_schematic = charm_retreat_transition_b_field_t(
        delta_r_charm,
        r_sph,
        before["eta_induction"],
        B_surface_t,
        omega2,
        om_break,
        charm_mass_released_kg=delta_charm_mass,
        structural_mass_kg=mass_kg,
    )
    b_transition = charm_retreat_transition_b_field_t(
        delta_r_charm,
        r_sph,
        before["eta_induction"],
        B_surface_t,
        omega2,
        om_break,
        charm_mass_released_kg=delta_charm_mass,
        structural_mass_kg=mass_kg,
        hep_readout=hep_readout,
    )
    b_charm_before = before["B_charm_t"]
    b_charm_after = after["B_charm_t"]
    delta_b_charm = b_charm_after - b_charm_before

    row_break = slip_torque_balance_for_star(
        mass_msun,
        omega1 / (2.0 * math.pi),
        "breakup spindown witness",
        B_surface_t=B_surface_t,
    )
    p_dipole_w = row_break.tau_align_b_eff_n_m * omega1
    i_spin = moment_of_inertia_uniform_sphere(mass_kg, r_sph)
    spin_energy_frac = e_spin_j / max(0.5 * i_spin * omega1**2, 1.0e-30)
    t_spindown_s = e_spin_j / max(p_dipole_w, 1.0e-30)
    p_charm_weak_w = e_charm_weak_j / max(t_spindown_s, 1.0e-30)

    charm_center_below_tip_after = after["epsilon_center"] < EPS_CHARM_TIP
    charm_shell_closed = after["charm_ledger_open_fraction"] < 0.01

    b_retreat_ratio = b_transition / max(b_charm_before, 1.0e-30)
    b_charm_frac_change = delta_b_charm / max(b_charm_before, 1.0e-30)

    return {
        "label": f"{mass_msun:.2f} M☉ spindown charm-retreat feedback",
        "mass_msun_initial": mass_msun,
        "radius_km": r_sph / 1000.0,
        "omega_hz_initial": omega1 / (2.0 * math.pi),
        "omega_hz_final": omega2 / (2.0 * math.pi),
        "omega_start_fraction": om_start_frac,
        "omega_end_fraction": omega_end_fraction,
        "bookkeeping": (
            "fixed_radius: Δm_spin from ½IΔΩ² + Δm_hep from Λ_c weak Q on phase conversion"
        ),
        "hep_decay_readout": hep_readout,
        "spin_kinetic_energy_released_j": e_spin_j,
        "spin_kinetic_energy_released_msun": e_spin_j / (M_SUN_KG * C_LIGHT**2),
        "charm_weak_energy_released_j": e_charm_weak_j,
        "charm_weak_energy_released_msun": e_charm_weak_j / (M_SUN_KG * C_LIGHT**2),
        "delta_mass_from_spin_kg": delta_m_spin_kg,
        "delta_mass_from_spin_msun": delta_m_spin_kg / M_SUN_KG,
        "delta_mass_from_charm_weak_kg": delta_m_hep_kg,
        "delta_mass_from_charm_weak_msun": delta_m_hep_kg / M_SUN_KG,
        "delta_mass_total_kg": delta_m_total_kg,
        "delta_mass_total_msun": delta_m_total_kg / M_SUN_KG,
        "before": before,
        "after": after,
        "delta_epsilon_surface": after["epsilon_surface"] - before["epsilon_surface"],
        "delta_epsilon_center": after["epsilon_center"] - before["epsilon_center"],
        "delta_r_charm_m": delta_r_charm,
        "delta_r_charm_over_R": delta_r_charm / r_sph,
        "delta_r_charm_spin_only_m": delta_r_charm_spin,
        "delta_charm_shell_mass_kg": delta_charm_mass,
        "delta_charm_shell_mass_msun": delta_charm_mass / M_SUN_KG,
        "charm_to_nuclear_phase_mass_kg": delta_m_phase,
        "charm_to_nuclear_phase_msun": delta_m_phase / M_SUN_KG,
        "delta_layered_mass_kg": delta_layered,
        "delta_layered_mass_msun": delta_layered / M_SUN_KG,
        "B_surface_t": B_surface_t,
        "B_charm_before_t": b_charm_before,
        "B_charm_after_t": b_charm_after,
        "delta_B_charm_t": delta_b_charm,
        "B_charm_fractional_change": b_charm_frac_change,
        "B_transition_from_retreat_t": b_transition,
        "B_transition_schematic_t": b_transition_schematic,
        "B_retreat_over_B_charm_before": b_retreat_ratio,
        "charm_center_below_tip_after": charm_center_below_tip_after,
        "charm_ledger_nearly_closed_after": charm_shell_closed,
        "dipole_radiation_power_at_breakup_w": p_dipole_w,
        "charm_weak_power_during_spindown_w": p_charm_weak_w,
        "charm_weak_over_dipole_power": p_charm_weak_w / max(p_dipole_w, 1.0e-30),
        "characteristic_spindown_time_s": t_spindown_s,
        "characteristic_spindown_time_kyr": t_spindown_s / (365.25 * 24.0 * 3600.0 * 1000.0),
        "spin_energy_fraction_lost": spin_energy_frac,
        "feedback_verdict": _spindown_charm_verdict(
            delta_r_charm / r_sph,
            b_retreat_ratio,
            b_charm_frac_change,
        ),
    }


def spindown_charm_dynamics_for_star(
    mass_msun: float,
    omega_hz: float,
    *,
    name: str = "",
    B_surface_t: float | None = None,
    b_field_gauss: float | None = None,
    period_s: float | None = None,
    period_dot_s_per_s: float | None = None,
    integration_time_s: float | None = None,
) -> dict[str, object]:
    """
    Per-star spindown + charm-retreat dynamics for catalog overlay.

    Integrates dipole power over ``integration_time`` (default: catalog characteristic
    age when available, else full spin drain time).
    """
    if b_field_gauss is not None:
        b_t = b_field_gauss * 1.0e-4
    elif B_surface_t is not None:
        b_t = B_surface_t
    else:
        b_t = B_SURFACE_T_DEFAULT

    mass_kg = mass_msun * M_SUN_KG
    r_sph = radius_uniform_density(mass_kg, RHO_NUCLEAR_KG_M3)
    omega_rad = 2.0 * math.pi * omega_hz
    om_break = breakup_omega_rad_s(mass_kg, r_sph)
    omega_over_breakup = omega_rad / om_break if om_break > 0.0 else 0.0

    slip = slip_torque_balance_for_star(
        mass_msun,
        omega_hz,
        name or f"{mass_msun:.2f} M☉",
        B_surface_t=b_t,
    )
    p_dipole_w = slip.tau_align_b_eff_n_m * omega_rad
    i_spin = moment_of_inertia_uniform_sphere(mass_kg, r_sph)
    e_spin_full_j = 0.5 * i_spin * omega_rad**2
    t_spin_drain_s = e_spin_full_j / max(p_dipole_w, 1.0e-30)

    char_age_s: float | None = None
    if (
        period_s is not None
        and period_dot_s_per_s is not None
        and period_s > 0.0
        and period_dot_s_per_s > 0.0
    ):
        char_age_s = period_s / (2.0 * period_dot_s_per_s)

    if integration_time_s is not None:
        t_int = integration_time_s
    elif char_age_s is not None:
        t_int = min(char_age_s, t_spin_drain_s)
    else:
        t_int = t_spin_drain_s

    e_spin_step_j = min(p_dipole_w * t_int, e_spin_full_j)
    omega_end = math.sqrt(max(omega_rad**2 - 2.0 * e_spin_step_j / i_spin, 0.0))

    retreat = quantify_spindown_charm_retreat_feedback(
        mass_msun,
        omega_start_fraction=omega_over_breakup,
        omega_end_fraction=max(omega_end / om_break, 1.0e-9),
        B_surface_t=b_t,
        radius_m=r_sph,
    )

    scale = e_spin_step_j / max(float(retreat["spin_kinetic_energy_released_j"]), 1.0e-30)
    delta_m_spin_msun = float(retreat["delta_mass_from_spin_msun"]) * scale
    delta_m_hep_msun = float(retreat["delta_mass_from_charm_weak_msun"]) * scale
    delta_m_total_msun = delta_m_spin_msun + delta_m_hep_msun

    return {
        "name": name,
        "mass_msun": mass_msun,
        "omega_hz": omega_hz,
        "omega_over_breakup": omega_over_breakup,
        "b_field_gauss": b_field_gauss if b_field_gauss is not None else b_t * 1.0e4,
        "period_s": period_s,
        "period_dot_s_per_s": period_dot_s_per_s,
        "characteristic_age_yr": (
            char_age_s / (365.25 * 24.0 * 3600.0) if char_age_s is not None else None
        ),
        "integration_time_s": t_int,
        "integration_time_over_spin_drain": t_int / max(t_spin_drain_s, 1.0e-30),
        "spin_drain_time_yr": t_spin_drain_s / (365.25 * 24.0 * 3600.0),
        "dipole_power_w": p_dipole_w,
        "charm_weak_power_w": float(retreat["charm_weak_power_during_spindown_w"]) * scale,
        "charm_weak_over_dipole": (
            float(retreat["charm_weak_over_dipole_power"])
        ),
        "delta_mass_spin_msun": delta_m_spin_msun,
        "delta_mass_charm_weak_msun": delta_m_hep_msun,
        "delta_mass_total_msun": delta_m_total_msun,
        "delta_r_charm_over_R": float(retreat["delta_r_charm_over_R"]) * scale,
        "B_transition_t": float(retreat["B_transition_from_retreat_t"]) * scale,
        "hep_width_per_s_effective": float(
            retreat["hep_decay_readout"]["width_per_s_effective"]
        ),
        "hep_dominant_q_mev": float(retreat["hep_decay_readout"]["dominant_q_mev"]),
        "psi_shear_deg": slip.psi_shear_deg,
        "torque_ratio_b_eff": slip.torque_ratio_b_eff,
        "alpha_equilibrium_b_eff_deg": slip.alpha_equilibrium_b_eff_deg,
    }


def compare_spindown_charm_to_pulsar_dataset(
    catalog_path: Path | None = None,
    *,
    max_rows: int = 5000,
    millisecond_only: bool = False,
    mass_measured_only: bool = False,
    include_all_rows: bool = False,
) -> dict[str, object]:
    """Compare HQIV spindown/charm dynamics to ``data/pulsar_catalog.json``."""
    cat_path = catalog_path or (_ROOT / "data" / "pulsar_catalog.json")
    payload = json.loads(cat_path.read_text())
    rows_in = payload.get("rows", [])[:max_rows]

    dynamics: list[dict[str, object]] = []
    for entry in rows_in:
        period = entry.get("period_s")
        pdot = entry.get("period_dot_s_per_s")
        if not isinstance(period, float) or not isinstance(pdot, float):
            continue
        if period <= 0.0 or pdot <= 0.0:
            continue
        is_ms = bool(entry.get("is_millisecond"))
        in_mass = str(entry.get("mass_source", "")) != "canonical_1.4Msun_default"
        if millisecond_only and not is_ms:
            continue
        if mass_measured_only and not in_mass:
            continue
        freq = float(entry.get("freq_hz") or (1.0 / period))
        row = spindown_charm_dynamics_for_star(
            float(entry["mass_msun"]),
            freq,
            name=str(entry.get("name", "")),
            b_field_gauss=float(entry.get("b_field_gauss") or 0.0),
            period_s=period,
            period_dot_s_per_s=pdot,
        )
        dynamics.append(row)

    def _mean(vals: list[float]) -> float:
        return sum(vals) / len(vals) if vals else 0.0

    ratios_age = [
        r["integration_time_over_spin_drain"]
        for r in dynamics
        if r.get("characteristic_age_yr") is not None
    ]
    charm_over_dipole = [float(r["charm_weak_over_dipole"]) for r in dynamics]
    delta_m_total = [float(r["delta_mass_total_msun"]) for r in dynamics]

    showcase = sorted(
        [r for r in dynamics if r.get("characteristic_age_yr") is not None],
        key=lambda r: float(r["delta_mass_total_msun"]),
        reverse=True,
    )[:12]

    return {
        "catalog_path": str(cat_path),
        "row_count": len(dynamics),
        "millisecond_only": millisecond_only,
        "mass_measured_only": mass_measured_only,
        "mean_integration_over_spin_drain": _mean(ratios_age),
        "mean_charm_weak_over_dipole": _mean(charm_over_dipole),
        "mean_delta_mass_total_msun": _mean(delta_m_total),
        "max_delta_mass_total_msun": max(delta_m_total) if delta_m_total else 0.0,
        "showcase_highest_mass_loss": showcase,
        **({"rows": dynamics} if include_all_rows else {}),
    }


def quantify_breakup_b_channels(
    mass_msun: float = 1.98,
    *,
    B_surface_t: float = B_SURFACE_T_DEFAULT,
) -> dict[str, object]:
    """Report ``B_pair``, ``B_charm``, and ratios for the canonical breakup witness."""
    mass_kg = mass_msun * M_SUN_KG
    r_sph = radius_uniform_density(mass_kg, RHO_NUCLEAR_KG_M3)
    om_break = breakup_omega_rad_s(mass_kg, r_sph)
    omega_hz = om_break / (2.0 * math.pi)
    row = slip_torque_balance_for_star(
        mass_msun,
        omega_hz,
        f"{mass_msun:.2f} M☉ at breakup (B channel audit)",
        B_surface_t=B_surface_t,
    )
    b_eff = row.B_eff_t
    b_pair = row.B_pair_t
    b_charm = row.B_charm_t
    ratio_pair = b_pair / max(b_eff, 1.0e-30)
    ratio_charm = b_charm / max(b_eff, 1.0e-30)
    torque_align_b_eff = row.tau_align_b_eff_n_m
    torque_align_total = row.tau_align_closed_loop_n_m
    delta_torque_pair = (
        (row.tau_align_closed_loop_n_m / max(row.tau_align_b_eff_n_m, 1.0e-30) - 1.0)
        if b_eff > 0
        else 0.0
    )
    return {
        "label": row.label,
        "mass_msun": mass_msun,
        "omega_hz": omega_hz,
        "omega_over_breakup": row.omega_over_breakup,
        "B_surface_t": B_surface_t,
        "B_eff_t": b_eff,
        "B_pair_t": b_pair,
        "B_charm_t": b_charm,
        "B_induction_lt_t": row.B_induction_lt_t,
        "B_induction_long_t": row.B_induction_long_t,
        "B_total_eff_t": row.B_total_eff_t,
        "B_pair_over_B_eff": ratio_pair,
        "B_charm_over_B_eff": ratio_charm,
        "B_pair_fraction_of_B_total": b_pair / max(row.B_total_eff_t, 1.0e-30),
        "pair_production_margin_effective": row.pair_production_margin_effective,
        "pair_rate_continuous": row.pair_rate_continuous,
        "light_cylinder_occupancy": row.light_cylinder_occupancy,
        "cosmic_brake_strength": row.cosmic_brake_strength,
        "tau_pair_brake_n_m": row.tau_pair_brake_n_m,
        "tau_align_b_eff_n_m": torque_align_b_eff,
        "tau_align_closed_loop_n_m": torque_align_total,
        "aligning_torque_lift_from_B_channels": delta_torque_pair,
        "pair_meaningful_for_aligning_torque": ratio_pair > 0.01 or ratio_charm > 0.01,
        "B_pair_verdict": "minor_correction" if ratio_pair < 0.01 else "meaningful_contributor",
        "B_charm_verdict": "minor_correction" if ratio_charm < 0.01 else "meaningful_contributor",
        "verdict": (
            "charm_meaningful_pair_minor"
            if ratio_charm >= 0.01 and ratio_pair < 0.01
            else (
                "meaningful_contributor"
                if ratio_pair >= 0.01 or ratio_charm >= 0.01
                else "minor_correction"
            )
        ),
    }


def alfven_bunching_factor(
    omega_rad_s: float,
    radius_m: float,
    B_tesla: float,
    rho_kg_m3: float,
) -> float:
    """
    Differential-rotation bunching ``min(1, (ΩR/v_A)²)`` capped at unity.

    Uses crust Alfvén speed and light-cylinder radius as upper shear scale.
    """
    v_a = alfven_speed_si(B_tesla, rho_kg_m3)
    if v_a <= 0.0:
        return 0.0
    r_lc = light_cylinder_radius_m(omega_rad_s)
    shear_surface = abs(omega_rad_s) * radius_m / v_a
    shear_lc = abs(omega_rad_s) * r_lc / v_a
    shear = max(shear_surface, shear_lc)
    return min(1.0, shear * shear)


def dipole_torque_scale_si(B_tesla: float, radius_m: float, omega_rad_s: float) -> float:
    """``|τ|`` at ``α = 1``: ``(2/3) μ² Ω³ / c³`` for oblique rotator spin-down."""
    mu = B_tesla * radius_m ** 3
    omega = abs(omega_rad_s)
    return (2.0 / 3.0) * mu * mu * omega * omega * omega / (C_LIGHT ** 3)


def moment_of_inertia_uniform_sphere(mass_kg: float, radius_m: float) -> float:
    return 0.4 * mass_kg * radius_m * radius_m


def compact_object_shear_coupling(
    a_lt_si: float,
    a_parallel_si: float,
    a_grav_si: float,
) -> float:
    """Lean ``compactObjectShearCoupling``: ``a_LT a_∥ / a_grav²``."""
    a_g = max(a_grav_si, 1.0e-30)
    return a_lt_si * a_parallel_si / (a_g * a_g)


def compact_object_crust_shell_thin_factor(h_shell_m: float, radius_m: float) -> float:
    """Lean ``compactObjectCrustShellThinFactor``: ``(h/R)²``."""
    r = max(radius_m, 1.0)
    return (h_shell_m / r) ** 2


def compact_object_lt_stress_magnitude_si(
    grad_axial_phi: float,
    lt_fraction: float,
    phi_readout: float,
    rho_kg_m3: float,
    *,
    kappa_l: float = KAPPA_L_DEFAULT,
) -> float:
    """Lean ``compactObjectLtStressMagnitude`` (scalar stress driver on crust shell)."""
    lam = coupling_log_phi(phi_readout)
    return kappa_l * rho_kg_m3 * lam * grad_axial_phi * lt_fraction


def crust_misalign_torque_from_stress_div_si(
    radius_m: float,
    a_grav_si: float,
    shear_coupling: float,
    colatitude_rad: float,
    *,
    h_crust_m: float = H_CRUST_TORQUE_M,
    rho_crust_kg_m3: float = RHO_CRUST_KG_M3,
    rho_nuclear_kg_m3: float = RHO_NUCLEAR_KG_M3,
) -> float:
    """
    Thin-shell discharge of ``hqivLongitudinalStressForce3`` on the crust.

    Lean: ``crustMisalignTorqueFromStressDivergence``.
    """
    sin_t = math.sin(colatitude_rad)
    mass_shell = 4.0 * math.pi * radius_m * radius_m * h_crust_m * rho_crust_kg_m3
    geo = sin_t * sin_t * compact_object_crust_shell_thin_factor(h_crust_m, radius_m)
    density_frac = rho_crust_kg_m3 / max(rho_nuclear_kg_m3, 1.0)
    screen = 1.0 - C_RINDLER_SHARED
    return (
        mass_shell
        * radius_m
        * a_grav_si
        * abs(shear_coupling)
        * geo
        * density_frac
        * screen
    )


def crust_misalign_torque_from_accelerations_si(
    radius_m: float,
    a_grav_si: float,
    a_lt_si: float,
    a_parallel_si: float,
    colatitude_rad: float,
    *,
    h_crust_m: float = H_CRUST_TORQUE_M,
    rho_crust_kg_m3: float = RHO_CRUST_KG_M3,
    rho_nuclear_kg_m3: float = RHO_NUCLEAR_KG_M3,
) -> float:
    """Lean ``crustMisalignTorqueFromAccelerations``."""
    chi = compact_object_shear_coupling(a_lt_si, a_parallel_si, a_grav_si)
    return crust_misalign_torque_from_stress_div_si(
        radius_m,
        a_grav_si,
        chi,
        colatitude_rad,
        h_crust_m=h_crust_m,
        rho_crust_kg_m3=rho_crust_kg_m3,
        rho_nuclear_kg_m3=rho_nuclear_kg_m3,
    )


def induction_resistivity_eta_from_environment(
    phi_epsilon: float,
    surface_temperature_K: float = NS_SURFACE_T_K,
    *,
    omega_rad_s: float = 0.0,
    radius_m: float = 0.0,
    colatitude_rad: float = math.pi / 2.0,
    cmb_doppler_v_m_s: float = notd.CMB_DIPOLE_V_M_S,
) -> float:
    """
    Lean ``inductionResistivityEta``: ``γ × release(ξ) × G_eff(ε)``.

    ``ξ`` from spin/CMB-boosted outside temperature; ``ε`` stacks gravity, co-spin,
    and CMB dipole on the same channel as the lab outside environment.
    """
    t_out = compact_object_effective_outside_temperature_K(
        surface_temperature_K,
        omega_rad_s,
        radius_m,
        colatitude_rad,
        cmb_doppler_v_m_s=cmb_doppler_v_m_s,
    )["outside_temperature_effective_K"]
    xi = notd.xi_from_temperature_K(max(t_out, 1.0))
    release = notd.outside_curvature_release_factor(xi)
    phi = compact_object_combined_phi_epsilon(
        phi_epsilon,
        omega_rad_s,
        radius_m,
        colatitude_rad,
        cmb_doppler_v_m_s=cmb_doppler_v_m_s,
    )["phi_combined"]
    geff = notd.outside_gravity_geff_modulator(phi)
    return GAMMA * release * geff


def induction_environment_witness(
    phi_epsilon: float,
    surface_temperature_K: float = NS_SURFACE_T_K,
    *,
    omega_rad_s: float = 0.0,
    radius_m: float = 0.0,
    colatitude_rad: float = math.pi / 2.0,
    cmb_doppler_v_m_s: float = notd.CMB_DIPOLE_V_M_S,
    B_tesla: float = B_SURFACE_T_DEFAULT,
) -> dict[str, float | bool | int]:
    """Full outside-environment readout for η induction and pair-production audits."""
    temp = compact_object_effective_outside_temperature_K(
        surface_temperature_K,
        omega_rad_s,
        radius_m,
        colatitude_rad,
        cmb_doppler_v_m_s=cmb_doppler_v_m_s,
    )
    phi = compact_object_combined_phi_epsilon(
        phi_epsilon,
        omega_rad_s,
        radius_m,
        colatitude_rad,
        cmb_doppler_v_m_s=cmb_doppler_v_m_s,
    )
    pair = pair_production_witness(
        temp["outside_temperature_effective_K"],
        phi["phi_gravity"],
        temp["beta_spin_over_c"],
        B_tesla,
    )
    xi = notd.xi_from_temperature_K(max(temp["outside_temperature_effective_K"], 1.0))
    release = notd.outside_curvature_release_factor(xi)
    geff = notd.outside_gravity_geff_modulator(phi["phi_combined"])
    eta = GAMMA * release * geff
    return {
        **temp,
        **phi,
        **pair,
        "xi_from_outside_temperature": xi,
        "outside_release_factor": release,
        "outside_geff_modulator": geff,
        "eta_induction": eta,
    }


def steady_induction_fields_si(
    a_lt_si: float,
    a_parallel_si: float,
    psi_long_rad: float,
    radius_m: float,
    B_surface_t: float,
    a_grav_si: float,
    *,
    eta: float | None = None,
    phi_epsilon: float = 0.0,
    surface_temperature_K: float = NS_SURFACE_T_K,
    omega_rad_s: float = 0.0,
    colatitude_rad: float = math.pi / 2.0,
) -> tuple[float, float, float]:
    """
    Steady induction closure with environment ``η(ξ, ε)``.

    Returns ``(B_LT, B_long, dB/dt)``; Lean ``steadyInductionFieldLt`` /
    ``steadyInductionFieldLong`` / ``inductionGrowthRateFromLt``.
    """
    eta_eff = eta if eta is not None else induction_resistivity_eta_from_environment(
        phi_epsilon,
        surface_temperature_K,
        omega_rad_s=omega_rad_s,
        radius_m=radius_m,
        colatitude_rad=colatitude_rad,
    )
    a_g = max(a_grav_si, 1.0e-30)
    r = max(radius_m, 1.0)
    b_lt = eta_eff * (abs(a_lt_si) / a_g) * B_surface_t
    b_long = (
        eta_eff * abs(a_parallel_si) * abs(psi_long_rad) * B_surface_t
        / (a_g * C_LIGHT)
    )
    d_b_growth = eta_eff * abs(a_lt_si) / r
    return b_lt, b_long, d_b_growth


def crust_shear_torque_si(
    mass_kg: float,
    radius_m: float,
    chi: float,
    a_grav_si: float,
    colatitude_rad: float,
    *,
    rho_crust_kg_m3: float = RHO_CRUST_KG_M3,
    h_crust_m: float = H_CRUST_TORQUE_M,
    rho_nuclear_kg_m3: float = RHO_NUCLEAR_KG_M3,
) -> float:
    """
    Misaligning torque from variational crust stress divergence.

    ``χ`` is the shear coupling ``a_LT a_∥ / a_grav²``; discharge matches
    ``crustMisalignTorqueFromStressDivergence`` in Lean.
    """
    return crust_misalign_torque_from_stress_div_si(
        radius_m,
        a_grav_si,
        chi,
        colatitude_rad,
        h_crust_m=h_crust_m,
        rho_crust_kg_m3=rho_crust_kg_m3,
        rho_nuclear_kg_m3=rho_nuclear_kg_m3,
    )


def crust_shear_torque_legacy_screened_si(
    mass_kg: float,
    radius_m: float,
    chi: float,
    a_grav_si: float,
    colatitude_rad: float,
    *,
    rho_crust_kg_m3: float = RHO_CRUST_KG_M3,
    h_crust_m: float = H_CRUST_TORQUE_M,
    rho_nuclear_kg_m3: float = RHO_NUCLEAR_KG_M3,
) -> float:
    """Legacy alias — identical to variational ``crust_shear_torque_si``."""
    return crust_shear_torque_si(
        mass_kg,
        radius_m,
        chi,
        a_grav_si,
        colatitude_rad,
        rho_crust_kg_m3=rho_crust_kg_m3,
        h_crust_m=h_crust_m,
        rho_nuclear_kg_m3=rho_nuclear_kg_m3,
    )


def wave_amplitude_proxy(
    psi_rad: float,
    omega_rad_s: float,
    radius_m: float,
    colatitude_rad: float,
    v_alfven_si: float,
) -> float:
    """``δB/B ~ min(1, ψ × Ω R sinθ / v_A)`` — shear-launched wave saturation."""
    if v_alfven_si <= 0.0:
        return 0.0
    sin_t = math.sin(colatitude_rad)
    shear_drive = abs(psi_rad) * abs(omega_rad_s) * radius_m * sin_t / v_alfven_si
    return min(1.0, shear_drive)


@dataclass(frozen=True)
class SlipTorqueBalanceRow:
    label: str
    mass_msun: float
    omega_hz: float
    omega_over_breakup: float
    peak_colatitude_deg: float
    psi_shear_deg: float
    psi_long_deg: float
    chi_shear_peak: float
    a_lt_peak_si: float
    a_long_linear_si: float
    a_long_nonlinear_si: float
    alfven_speed_km_s: float
    bunching_factor: float
    delta_b_over_b: float
    B_surface_t: float
    B_eff_t: float
    B_induction_lt_t: float
    B_induction_long_t: float
    B_total_eff_t: float
    dB_growth_t_per_s: float
    eta_induction: float
    outside_temperature_effective_K: float
    beta_spin_over_c: float
    cmb_doppler_boost: float
    phi_combined_epsilon: float
    pair_production_margin_effective: float
    pair_cascade_scatters: int
    pair_production_active: bool
    pair_rate_continuous: float
    light_cylinder_occupancy: float
    light_cylinder_radius_m: float
    cosmic_brake_strength: float
    B_pair_t: float
    B_pair_over_B_eff: float
    B_charm_t: float
    B_charm_over_B_eff: float
    tau_pair_brake_n_m: float
    cosmic_brake_active: bool
    tau_misalign_n_m: float
    tau_misalign_variational_n_m: float
    tau_align_surface_b_n_m: float
    tau_align_b_eff_n_m: float
    tau_align_closed_loop_n_m: float
    torque_ratio_surface_b: float
    torque_ratio_b_eff: float
    torque_ratio_closed_loop: float
    alpha_equilibrium_surface_deg: float
    alpha_equilibrium_b_eff_deg: float
    alpha_equilibrium_closed_loop_deg: float
    closes_with_b_eff: bool
    closes_closed_loop: bool
    B_align_t: float
    charm_ledger_open_fraction: float
    aligning_enhancement_factor: float
    tau_jxb_align_n_m: float
    tau_align_enhanced_n_m: float
    torque_ratio_aligning_enhanced: float
    alpha_equilibrium_aligning_enhanced_deg: float
    closes_with_aligning_enhanced: bool
    notes: str


def aligning_b_for_torque_t(
    B_eff_t: float,
    b_lt_t: float,
    b_long_t: float,
    b_charm_t: float,
    b_pair_t: float,
) -> float:
    """Lattice-weighted RMS B for closed induction aligning torque."""
    return math.sqrt(
        B_eff_t * B_eff_t
        + (GAMMA * b_lt_t) ** 2
        + (ALPHA * b_long_t) ** 2
        + (GAMMA * b_charm_t) ** 2
        + (ALPHA_GAMMA * b_pair_t) ** 2
    )


def aligning_torque_enhancement_factor(
    omega_over_breakup: float,
    charm_ledger_open_fraction: float,
) -> float:
    """
    Charm-ledger / spin closure boosts aligning torque when interior ledger is open
    but spin remains below breakup (millisecond band).
    """
    om = min(1.0, max(0.0, omega_over_breakup))
    om_gate = max(om, GAMMA)
    charm_boost = GAMMA * max(0.0, charm_ledger_open_fraction) / om_gate
    spin_boost = GAMMA * om * om
    ledger_closure_boost = ALPHA_GAMMA * max(0.0, charm_ledger_open_fraction) / om_gate
    return 1.0 + charm_boost + spin_boost + ledger_closure_boost


def crust_jxb_aligning_torque_n_m(
    radius_m: float,
    B_tesla: float,
    omega_rad_s: float,
    a_long_si: float,
    a_lt_si: float,
    a_grav_si: float,
    charm_ledger_open_fraction: float,
) -> float:
    """
    Minimal internal J×B aligning torque from longitudinal crust current closure.
    Scales as dipole torque × γ × (a_∥/a_grav) × charm ledger openness.
    """
    a_g = max(a_grav_si, 1.0e-30)
    tau_dipole = dipole_torque_scale_si(B_tesla, radius_m, omega_rad_s)
    stress_current = GAMMA * abs(a_long_si) / a_g * max(0.0, charm_ledger_open_fraction)
    lt_coupling = ALPHA * abs(a_lt_si) / a_g
    return tau_dipole * min(1.0, stress_current + lt_coupling)


def _alpha_eq_deg_from_torque_ratio(ratio: float) -> float:
    if ratio >= 1.0:
        return 90.0
    return math.degrees(math.asin(max(0.0, min(1.0, ratio))))


def slip_torque_balance_for_star(
    mass_msun: float,
    omega_hz: float,
    label: str,
    *,
    B_surface_t: float = B_SURFACE_T_DEFAULT,
    rho_crust_kg_m3: float = RHO_CRUST_KG_M3,
    eta_dynamo: float = ETA_DYNAMO_DEFAULT,
) -> SlipTorqueBalanceRow:
    mass_kg = mass_msun * M_SUN_KG
    r_sph = radius_uniform_density(mass_kg, RHO_NUCLEAR_KG_M3)
    omega_rad_s = 2.0 * math.pi * omega_hz
    om_break = breakup_omega_rad_s(mass_kg, r_sph)
    r_eq, r_pol, _, _ = oblate_radii_m(r_sph, mass_kg, omega_rad_s)

    _, _, eps_equator, _ = epsilon_surface_at_latitude(
        mass_kg, r_eq, r_pol, omega_rad_s, math.pi / 2.0
    )
    _, _, eps_pole, _ = epsilon_surface_at_latitude(
        mass_kg, r_eq, r_pol, omega_rad_s, 0.0
    )

    peak_ch: TorsionChannelsAtPoint | None = None
    peak_shear_deg = -1.0
    peak_col_deg = 0.0

    for col_deg in range(0, 91, 5):
        col_rad = math.radians(col_deg)
        ch = torsion_channels_at_latitude(
            mass_kg,
            r_eq,
            r_pol,
            omega_rad_s,
            col_rad,
            B_surface_t=B_surface_t,
            rho_crust_kg_m3=rho_crust_kg_m3,
            eps_equator=eps_equator,
            eps_pole=eps_pole,
        )
        shear_deg = math.degrees(ch.psi_shear_rad)
        if shear_deg > peak_shear_deg:
            peak_shear_deg = shear_deg
            peak_col_deg = col_deg
            peak_ch = ch

    if peak_ch is None:
        raise RuntimeError("slip torque scan produced no rows")

    col_peak_rad = math.radians(peak_col_deg)
    chi_peak = peak_ch.chi_shear
    a_lt_peak = peak_ch.a_lense_thirring_si
    a_grav_peak = peak_ch.a_grav_si
    a_long_lin = peak_ch.a_long_linear_si
    a_long_nl = peak_ch.a_long_nonlinear_si
    psi_long_deg = math.degrees(peak_ch.psi_long_rad)
    delta_b = peak_ch.delta_b_over_b

    v_a = alfven_speed_si(B_surface_t, rho_crust_kg_m3)
    bunch = alfven_bunching_factor(omega_rad_s, r_eq, B_surface_t, rho_crust_kg_m3)

    B_eff = magnetospheric_b_eff_t(B_surface_t, delta_b)
    eps_peak = peak_ch.epsilon_total
    env = induction_environment_witness(
        eps_peak,
        NS_SURFACE_T_K,
        omega_rad_s=omega_rad_s,
        radius_m=r_eq,
        colatitude_rad=col_peak_rad,
        B_tesla=B_eff,
    )
    eta_env = env["eta_induction"]
    eta_use = eta_env if eta_dynamo == ETA_DYNAMO_DEFAULT else eta_dynamo
    om_over_break = omega_rad_s / om_break if om_break > 0 else 0.0
    cont = continuous_pair_rate_proxy(
        float(env["pair_production_margin_effective"]),
        int(env["pair_cascade_scatters"]),
        omega_rad_s,
        r_eq,
        om_break,
    )
    pair_rate = cont["pair_rate_continuous"]
    lc_occupancy = cont["light_cylinder_occupancy"]
    brake_strength = cont["cosmic_brake_strength"]
    b_pair = pair_induction_b_field_t(
        pair_rate, eta_use, B_surface_t, a_lt_peak, a_grav_peak
    )
    eps_surf = gravitational_phi_epsilon(mass_kg, r_sph)
    eps_center = epsilon_interior(eps_surf, 0.0, r_sph)
    b_charm = charm_decay_b_field_t(
        eps_center, eps_peak, om_over_break, eta_use, B_surface_t
    )
    tau_pair_brake = pair_production_spin_brake_torque_n_m(
        pair_rate,
        omega_rad_s,
        r_eq,
        cosmic_brake_strength=brake_strength,
        light_cylinder_occupancy=lc_occupancy,
    )
    b_lt, b_long, dB_growth = steady_induction_fields_si(
        a_lt_peak,
        a_long_nl,
        peak_ch.psi_long_rad,
        r_eq,
        B_surface_t,
        a_grav_peak,
        eta=eta_use,
        phi_epsilon=eps_peak,
        omega_rad_s=omega_rad_s,
        colatitude_rad=col_peak_rad,
    )
    B_total = math.sqrt(
        B_eff * B_eff + b_lt * b_lt + b_long * b_long + b_pair * b_pair + b_charm * b_charm
    )

    tau_mis_var = crust_misalign_torque_from_accelerations_si(
        r_eq,
        a_grav_peak,
        a_lt_peak,
        a_long_lin,
        col_peak_rad,
        rho_crust_kg_m3=rho_crust_kg_m3,
    )
    tau_mis = crust_shear_torque_si(
        mass_kg,
        r_eq,
        chi_peak,
        a_grav_peak,
        col_peak_rad,
        rho_crust_kg_m3=rho_crust_kg_m3,
    )

    tau_surface = dipole_torque_scale_si(B_surface_t, r_eq, omega_rad_s) * bunch
    tau_b_eff = dipole_torque_scale_si(B_eff, r_eq, omega_rad_s) * bunch
    tau_closed = dipole_torque_scale_si(B_total, r_eq, omega_rad_s) * bunch
    cosmic_brake = brake_strength > 0.15
    b_pair_over_b_eff = b_pair / max(B_eff, 1.0e-30)
    b_charm_over_b_eff = b_charm / max(B_eff, 1.0e-30)

    charm_frac = charm_ledger_open_fraction(eps_center, eps_peak)
    B_align = aligning_b_for_torque_t(B_eff, b_lt, b_long, b_charm, b_pair)
    align_enhance = aligning_torque_enhancement_factor(om_over_break, charm_frac)
    tau_jxb = crust_jxb_aligning_torque_n_m(
        r_eq,
        B_align,
        omega_rad_s,
        a_long_lin,
        a_lt_peak,
        a_grav_peak,
        charm_frac,
    )
    tau_align_enhanced = (
        dipole_torque_scale_si(B_align, r_eq, omega_rad_s) * bunch * align_enhance + tau_jxb
    )

    ratio_surface = tau_mis / max(tau_surface, 1.0e-30)
    ratio_b_eff = tau_mis / max(tau_b_eff, 1.0e-30)
    ratio_closed = tau_mis / max(tau_closed, 1.0e-30)
    ratio_align_enhanced = tau_mis / max(tau_align_enhanced, 1.0e-30)

    return SlipTorqueBalanceRow(
        label=label,
        mass_msun=mass_msun,
        omega_hz=omega_hz,
        omega_over_breakup=om_over_break,
        peak_colatitude_deg=peak_col_deg,
        psi_shear_deg=peak_shear_deg,
        psi_long_deg=psi_long_deg,
        chi_shear_peak=chi_peak,
        a_lt_peak_si=a_lt_peak,
        a_long_linear_si=a_long_lin,
        a_long_nonlinear_si=a_long_nl,
        alfven_speed_km_s=v_a / 1000.0,
        bunching_factor=bunch,
        delta_b_over_b=delta_b,
        B_surface_t=B_surface_t,
        B_eff_t=B_eff,
        B_induction_lt_t=b_lt,
        B_induction_long_t=b_long,
        B_total_eff_t=B_total,
        dB_growth_t_per_s=dB_growth,
        eta_induction=eta_use,
        outside_temperature_effective_K=env["outside_temperature_effective_K"],
        beta_spin_over_c=env["beta_spin_over_c"],
        cmb_doppler_boost=env["cmb_doppler_boost"],
        phi_combined_epsilon=env["phi_combined"],
        pair_production_margin_effective=float(env["pair_production_margin_effective"]),
        pair_cascade_scatters=int(env["pair_cascade_scatters"]),
        pair_production_active=bool(env["pair_production_active"]),
        pair_rate_continuous=pair_rate,
        light_cylinder_occupancy=lc_occupancy,
        light_cylinder_radius_m=cont["light_cylinder_radius_m"],
        cosmic_brake_strength=brake_strength,
        B_pair_t=b_pair,
        B_pair_over_B_eff=b_pair_over_b_eff,
        B_charm_t=b_charm,
        B_charm_over_B_eff=b_charm_over_b_eff,
        tau_pair_brake_n_m=tau_pair_brake,
        cosmic_brake_active=cosmic_brake,
        tau_misalign_n_m=tau_mis,
        tau_misalign_variational_n_m=tau_mis_var,
        tau_align_surface_b_n_m=tau_surface,
        tau_align_b_eff_n_m=tau_b_eff,
        tau_align_closed_loop_n_m=tau_closed,
        torque_ratio_surface_b=ratio_surface,
        torque_ratio_b_eff=ratio_b_eff,
        torque_ratio_closed_loop=ratio_closed,
        alpha_equilibrium_surface_deg=_alpha_eq_deg_from_torque_ratio(ratio_surface),
        alpha_equilibrium_b_eff_deg=_alpha_eq_deg_from_torque_ratio(ratio_b_eff),
        alpha_equilibrium_closed_loop_deg=_alpha_eq_deg_from_torque_ratio(ratio_closed),
        closes_with_b_eff=ratio_b_eff < 1.0,
        closes_closed_loop=ratio_closed < 1.0,
        B_align_t=B_align,
        charm_ledger_open_fraction=charm_frac,
        aligning_enhancement_factor=align_enhance,
        tau_jxb_align_n_m=tau_jxb,
        tau_align_enhanced_n_m=tau_align_enhanced,
        torque_ratio_aligning_enhanced=ratio_align_enhanced,
        alpha_equilibrium_aligning_enhanced_deg=_alpha_eq_deg_from_torque_ratio(
            ratio_align_enhanced
        ),
        closes_with_aligning_enhanced=ratio_align_enhanced < 1.0,
        notes=f"peak shear band θ≈{peak_col_deg:.0f}°",
    )


def alfven_slip_torque_balance_hypothesis() -> dict[str, object]:
    """
    Dynamic equilibrium with split channels, magnetospheric ``B_eff``, and induction.

    **Misaligning:** ``τ_mis`` from ``χ_shear`` (linear channel) at peak ``ψ_shear``.

    **Aligning (B readouts + enhanced closure):**
      * Surface ``B_surf`` (fixed witness default).
      * ``B_eff = B_surf min(1, δB/B)`` — saturated fast rotators.
      * ``B_total = √(B_eff² + B_LT² + B_long² + B_pair² + B_charm²)``.
      * ``B_align`` — lattice-weighted RMS of closed induction channels.
      * ``τ_align_enhanced`` — ``B_align`` dipole torque × bunch × ledger/spin boost
        plus minimal crust J×B term from ``a_∥`` closure.

    **Equilibrium:** ``α_eq = arcsin(τ_mis / τ_align)`` for each torque choice.
    """
    specs: list[tuple[str, float, float | None]] = [
        ("1.4 M☉ slow (10 Hz)", 1.4, 10.0),
        ("1.4 M☉ ms (640 Hz)", 1.4, 640.0),
        ("1.98 M☉ at breakup", 1.98, None),
        ("3.16 M☉ charmed tail, half breakup", 3.16, None),
    ]
    rows: list[SlipTorqueBalanceRow] = []
    for label, m_msun, hz in specs:
        if hz is None:
            mass_kg = m_msun * M_SUN_KG
            r_sph = radius_uniform_density(mass_kg, RHO_NUCLEAR_KG_M3)
            om_break = breakup_omega_rad_s(mass_kg, r_sph)
            hz = (
                om_break * 0.5 / (2.0 * math.pi)
                if "half" in label
                else om_break / (2.0 * math.pi)
            )
        rows.append(slip_torque_balance_for_star(m_msun, hz, label))

    return {
        "hypothesis": (
            "ψ_shear (linear) drives Alfvén launch and τ_mis; ψ_long (φ_eff) drives "
            "induction. B_eff = B_surf min(1,δB/B) strengthens aligning torque when "
            "waves saturate; closed loop adds B_LT and B_long from η."
        ),
        "formulas": {
            "tau_misalign": (
                "τ_mis = crustMisalignTorqueFromStressDivergence "
                "(thin-shell ∫ r×(∇·σ) discharge; χ = a_LT a_∥/a_grav²)"
            ),
            "eta_induction": "η = γ × release(ξ(T_out)) × G_eff(ε_g + ε_spin + v_CMB/c)",
            "T_out_effective": (
                "max(T_surf(1+2β_spin), T_CMB × √(1+β_combined)/(1−β_combined)); "
                "β_combined = v_spin/c + v_CMB/c"
            ),
            "pair_production": (
                "cascade upscatter (1+2β)^n to 2m_e c²; pairs → B_pair + τ_brake"
            ),
            "B_charm": "charmed-core weak ledger × (Ω/Ω_break)² → B_charm",
            "spindown_charm_retreat": (
                "ΔE_spin → Δm; Λ_c weak Q on phase conversion adds Δm_hep; "
                "B_transition scales with hep width/Q"
            ),
            "cosmic_brake": "τ_brake ∝ rate² × (R/R_LC)³ × scatter capture × Ω/Ω_break",
            "tau_align": "τ_align = (2/3)μ²Ω³sin(α)/c³ × bunch",
            "B_eff": "B_eff = B_surf min(1, δB/B)",
            "B_induction_lt": "B_LT = η (a_LT/a_grav) B_surf",
            "B_induction_long": "B_long = η (a_∥^nl ψ_long / R) (R/c) B_surf / a_grav",
            "dB_dt": "∂B/∂t ~ η a_LT / R",
            "B_total_eff": "√(B_eff² + B_LT² + B_long² + B_pair² + B_charm²)",
            "B_align": (
                "√(B_eff² + (γ B_LT)² + (α B_long)² + (γ B_charm)² + (α·γ B_pair)²)"
            ),
            "aligning_enhancement": (
                "1 + γ charm_frac/max(Ω/Ω_break,γ) + γ (Ω/Ω_break)² "
                "+ α·γ charm_frac/max(Ω/Ω_break,γ)"
            ),
            "tau_jxb_align": (
                "τ_J×B ~ dipole(B_align) × γ (a_∥/a_grav) charm_frac "
                "+ α (a_LT/a_grav)"
            ),
            "tau_align_enhanced": "dipole(B_align)×bunch×enhance + τ_J×B",
            "alpha_equilibrium": "α_eq = arcsin(τ_mis / τ_align)",
        },
        "breakup_b_channel_audit": quantify_breakup_b_channels(1.98),
        "spindown_charm_retreat_feedback": quantify_spindown_charm_retreat_feedback(1.98),
        "witness_defaults": {
            "B_surface_t": B_SURFACE_T_DEFAULT,
            "rho_crust_kg_m3": RHO_CRUST_KG_M3,
            "h_crust_integrated_m": H_CRUST_M,
            "h_crust_torque_layer_m": H_CRUST_TORQUE_M,
            "eta_dynamo": ETA_DYNAMO_DEFAULT,
            "ns_surface_temperature_K": NS_SURFACE_T_K,
        },
        "lean_refs": [
            "Hqiv.Physics.CompactObjectRotatingCrustScaffold",
            "Hqiv.Physics.CompactObjectMhdEquivalenceScaffold",
            "Hqiv.Physics.HQIVFluidClosureScaffold.hqivLongitudinalStressTensor3",
            "Hqiv.Physics.NuclearOutsideTemperatureDynamics",
        ],
        "rows": [asdict(r) for r in rows],
    }


def lapse_from_epsilon(epsilon: float) -> float:
    return 1.0 - epsilon


def curvature_slots_at_epsilon(epsilon: float) -> dict[str, float]:
    geff = notd.outside_gravity_geff_modulator(epsilon)
    env_bonded = notd.outside_environment_modulator(
        notd.XI_LOCKIN, bonded=True, phi_gravity_epsilon=epsilon
    )
    env_free = notd.outside_environment_modulator(
        notd.XI_LOCKIN, bonded=False, phi_gravity_epsilon=epsilon
    )
    return {
        "epsilon_gravity": epsilon,
        "lapse_surface": lapse_from_epsilon(epsilon),
        "geff_modulator": geff,
        "outside_env_modulator_bonded": env_bonded,
        "outside_env_modulator_free": env_free,
        "liquid_local_field_divisor": 1.0 - C_RINDLER_SHARED,
    }


def per_nucleon_binding_at_epsilon(epsilon: float, *, A: int = 56) -> float:
    anchor = notd.outside_environment_modulator(
        notd.XI_LOCKIN, bonded=True, phi_gravity_epsilon=0.0
    )
    mod = notd.outside_environment_modulator(
        notd.XI_LOCKIN, bonded=True, phi_gravity_epsilon=epsilon
    )
    base = ncur.per_nucleon_binding_mev(REFERENCE_M, A)
    return base * mod / anchor


def build_row(
    label: str,
    matter: MatterKind,
    mass_msun: float,
    *,
    notes: str,
) -> CompactObjectRow:
    rho = matter_density(matter)
    mass_kg = mass_msun * M_SUN_KG
    r_m = radius_uniform_density(mass_kg, rho)
    eps = gravitational_phi_epsilon(mass_kg, r_m)
    rs = schwarzschild_radius_m(mass_kg)
    shell = ncur.nucleus_curvature_shell(56)
    return CompactObjectRow(
        label=label,
        matter=matter,
        mass_msun=mass_msun,
        radius_km=r_m / 1000.0,
        epsilon_surface=eps,
        lapse_surface=lapse_from_epsilon(eps),
        compactness_rs_over_r=rs / r_m,
        geff_modulator=notd.outside_gravity_geff_modulator(eps),
        env_modulator_bonded=notd.outside_environment_modulator(
            notd.XI_LOCKIN, bonded=True, phi_gravity_epsilon=eps
        ),
        per_nucleon_binding_mev=per_nucleon_binding_at_epsilon(eps),
        trapped_inside_ratio_shell=shell,
        notes=notes,
    )


def critical_mass_table(matter: MatterKind) -> list[dict[str, object]]:
    rho = matter_density(matter)
    rows: list[dict[str, object]] = []
    crit_specs = [
        (C_RINDLER_SHARED, "neutron_star_max (ε_crit = c_rindler_shared = γ/2)"),
        (ALPHA_GAMMA, "overpressure branch (ε_crit = α·γ)"),
        (0.5, "Schwarzschild surface (ε = 1/2, BH horizon)"),
        (ALPHA, "lapse N = 1−α (ε = α)"),
        (1.0 - ALPHA, "lapse N = α (ε = 1−α)"),
    ]
    for eps_crit, note in crit_specs:
        m_kg = mass_from_epsilon_crit(eps_crit, rho)
        m_msun = m_kg / M_SUN_KG
        r_m = radius_uniform_density(m_kg, rho)
        slots = curvature_slots_at_epsilon(eps_crit)
        rows.append(
            {
                "matter": matter,
                "epsilon_crit": eps_crit,
                "mass_msun": m_msun,
                "radius_km": r_m / 1000.0,
                "compactness_rs_over_r": schwarzschild_radius_m(m_kg) / r_m,
                "per_nucleon_binding_mev": per_nucleon_binding_at_epsilon(eps_crit),
                "note": note,
                **slots,
            }
        )
    return rows


def epsilon_scan(matter: MatterKind, epsilons: list[float]) -> list[dict[str, float]]:
    out: list[dict[str, float]] = []
    rho = matter_density(matter)
    for eps in epsilons:
        m_kg = mass_from_epsilon_crit(eps, rho)
        slots = curvature_slots_at_epsilon(eps)
        out.append(
            {
                "matter": matter,
                "mass_msun": m_kg / M_SUN_KG,
                "radius_km": radius_uniform_density(m_kg, rho) / 1000.0,
                "per_nucleon_binding_mev": per_nucleon_binding_at_epsilon(eps),
                **slots,
            }
        )
    return out


def trapped_mass_ladder(m_max: int = 20) -> list[dict[str, float]]:
    rows: list[dict[str, float]] = []
    for m in range(REFERENCE_M, m_max + 1):
        ratio = hes.meta_horizon_trapped_inside_ratio(m, REFERENCE_M)
        rows.append(
            {
                "shell_m": m,
                "inside_ratio": ratio,
                "trapped_mass_gev": PROTON_MEV * ratio / 1000.0,
                "lapse_corrected_gev": PROTON_MEV * ratio / 1000.0 / max(1.0 - C_RINDLER_SHARED, 1e-9),
            }
        )
    return rows


# Literature reference scales for dynamics gap witness (comparison layer, not fits).
MAGNETAR_B_GAUSS_TYPICAL = (1.0e14, 1.0e15)
PROTO_NS_DYNAMO_B_GAUSS_TYPICAL = (1.0e12, 1.0e13)
OHMIC_DECAY_TIME_YR_LITERATURE = (1.0e4, 1.0e6)
CRUST_CONDUCTIVITY_S_M_LITERATURE = (1.0e7, 1.0e8, 1.0e9)


def coefficient_calibration_witness() -> dict[str, object]:
    """
    Numeric comparison of HQIV ``η(ξ, ε)`` and induction growth vs crust σ(T) band.

    HQIV ``η`` is a dimensionless induction efficiency (not MHD magnetic diffusivity).
    The witness maps literature ``σ`` to ``η_MHD = 1/(μ₀ σ)`` and ``τ_ohm ~ L²/η_MHD``,
    then compares to HQIV ``∂B/∂t ~ η a_LT/R`` at representative NS crust points.
    """
    mass_kg = 1.4 * M_SUN_KG
    r_sph = radius_uniform_density(mass_kg, RHO_NUCLEAR_KG_M3)
    omega_ms = 2.0 * math.pi * 640.0
    r_eq, r_pol, _, _ = oblate_radii_m(r_sph, mass_kg, omega_ms)
    eps_surf = gravitational_phi_epsilon(mass_kg, r_sph)
    col_rad = math.radians(55.0)
    ch = torsion_channels_at_latitude(
        mass_kg,
        r_eq,
        r_pol,
        omega_ms,
        col_rad,
        B_surface_t=B_SURFACE_T_DEFAULT,
        rho_crust_kg_m3=RHO_CRUST_KG_M3,
    )
    a_lt = ch.a_lense_thirring_si
    a_grav = ch.a_grav_si

    temperature_cases: list[tuple[str, float, str]] = [
        ("ns_surface", NS_SURFACE_T_K, "witness default photosphere"),
        ("cooling_1e6K", 1.0e6, "cooling NS outer crust"),
        ("hot_pns_1e8K", 1.0e8, "proto-NS hot crust layer"),
        ("hot_pns_1e9K", 1.0e9, "vigorous PNS convection band"),
    ]
    epsilon_cases = [0.15, 0.2, EPS_CHARM_TIP]

    calibration_rows: list[dict[str, object]] = []
    length_scales_m = {
        "crust_skin_1km": R_CRUST_CALIBRATION_M,
        "stellar_radius": r_eq,
    }
    for t_label, t_k, t_note in temperature_cases:
        xi = notd.xi_from_temperature_K(max(t_k, 1.0))
        release = notd.outside_curvature_release_factor(xi)
        for eps in epsilon_cases:
            eta_static = induction_resistivity_eta_from_environment(eps, t_k)
            eta_spin = induction_resistivity_eta_from_environment(
                eps,
                t_k,
                omega_rad_s=omega_ms,
                radius_m=r_eq,
                colatitude_rad=col_rad,
            )
            d_b_static = induction_growth_rate_t_per_s(a_lt, r_eq, eta=eta_static)
            d_b_spin = induction_growth_rate_t_per_s(a_lt, r_eq, eta=eta_spin)
            for sigma in CRUST_CONDUCTIVITY_S_M_LITERATURE:
                eta_mhd_m2_s = 1.0 / (MU_0_SI * sigma)
                tau_by_length: dict[str, float] = {}
                for length_label, length_m in length_scales_m.items():
                    tau_ohm_yr = MU_0_SI * sigma * (length_m ** 2) / SECONDS_PER_YEAR
                    tau_by_length[length_label] = tau_ohm_yr
                tau_ohm_stellar_yr = tau_by_length["stellar_radius"]
                tau_growth_static_yr = (
                    B_SURFACE_T_DEFAULT / max(d_b_static, 1.0e-30) / SECONDS_PER_YEAR
                )
                tau_growth_spin_yr = (
                    B_SURFACE_T_DEFAULT / max(d_b_spin, 1.0e-30) / SECONDS_PER_YEAR
                )
                calibration_rows.append(
                    {
                        "temperature_label": t_label,
                        "temperature_K": t_k,
                        "temperature_note": t_note,
                        "xi_from_temperature": xi,
                        "outside_release_factor": release,
                        "phi_epsilon": eps,
                        "sigma_S_m": sigma,
                        "eta_hqiv_static": eta_static,
                        "eta_hqiv_spin_boosted": eta_spin,
                        "eta_mhd_m2_s_from_sigma": eta_mhd_m2_s,
                        "tau_ohm_yr_mu0_sigma_L2": tau_by_length,
                        "tau_ohm_yr_stellar_radius": tau_ohm_stellar_yr,
                        "dB_growth_static_t_per_s": d_b_static,
                        "dB_growth_spin_t_per_s": d_b_spin,
                        "schematic_tau_growth_static_yr": tau_growth_static_yr,
                        "schematic_tau_growth_spin_yr": tau_growth_spin_yr,
                        "tau_ohm_stellar_in_literature_band": (
                            OHMIC_DECAY_TIME_YR_LITERATURE[0]
                            <= tau_ohm_stellar_yr
                            <= OHMIC_DECAY_TIME_YR_LITERATURE[1]
                        ),
                    }
                )

    representative = {
        "mass_msun": 1.4,
        "omega_hz": 640.0,
        "colatitude_deg": 55.0,
        "B_surface_t": B_SURFACE_T_DEFAULT,
        "a_lt_si": a_lt,
        "a_grav_si": a_grav,
        "radius_equatorial_m": r_eq,
        "phi_surface": eps_surf,
    }

    tau_ohm_stellar_at_sigma = {
        f"sigma_{int(sigma)}": MU_0_SI * sigma * (r_eq ** 2) / SECONDS_PER_YEAR
        for sigma in CRUST_CONDUCTIVITY_S_M_LITERATURE
    }
    eta_ns_surface = induction_resistivity_eta_from_environment(
        eps_surf, NS_SURFACE_T_K, omega_rad_s=omega_ms, radius_m=r_eq, colatitude_rad=col_rad
    )

    return {
        "witness_role": (
            "coefficient_discharge_for_mhd_equivalence_paper: same equation slots, "
            "calibrate HQIV η(ξ,ε) against literature crust σ(T,B,ρ) band"
        ),
        "hqiv_eta_definition": "η = γ × release(ξ(T_out)) × G_eff(ε_combined)",
        "trad_mhd_mapping": {
            "sigma_S_m_literature": CRUST_CONDUCTIVITY_S_M_LITERATURE,
            "eta_mhd_m2_s": "1/(μ₀ σ)",
            "tau_ohm_sketch_yr": "μ₀ σ L² converted to years",
            "length_scales_m": length_scales_m,
            "ohmic_decay_literature_yr": OHMIC_DECAY_TIME_YR_LITERATURE,
        },
        "hqiv_growth_sketch": {
            "dB_dt": "η × a_LT / R",
            "tau_growth_sketch_yr": "B_surf / (dB/dt) if unsaturated",
            "note": (
                "HQIV η is dimensionless induction efficiency, not η_MHD; "
                "growth sketch ignores saturation and Hall back-reaction"
            ),
        },
        "representative_ms_pulsar_point": representative,
        "eta_ns_surface_spin_boosted": eta_ns_surface,
        "tau_ohm_yr_at_sigma_stellar_radius": tau_ohm_stellar_at_sigma,
        "calibration_grid": calibration_rows,
        "discharge_verdict": (
            f"Literature τ_ohm ≈ {OHMIC_DECAY_TIME_YR_LITERATURE[0]:.0e}–"
            f"{OHMIC_DECAY_TIME_YR_LITERATURE[1]:.0e} yr matches μ₀ σ R² for "
            f"σ ∈ [{CRUST_CONDUCTIVITY_S_M_LITERATURE[0]:.0e}, "
            f"{CRUST_CONDUCTIVITY_S_M_LITERATURE[-1]:.0e}] S/m at R ≈ {r_eq:.0f} m "
            f"(stellar-radius scale; crust-skin 1 km gives faster decay). "
            f"HQIV η at NS surface (spin-boosted) = {eta_ns_surface:.4f} — same "
            "inductive PDE slot; numeric calibration is coefficient identification, "
            "not a missing physics class."
        ),
        "lean_refs": [
            "Hqiv.Physics.CompactObjectRotatingCrustScaffold.inductionResistivityEta",
            "Hqiv.Physics.CompactObjectMhdEquivalenceScaffold.TraditionalResistiveEtaIdentification",
            "Hqiv.Physics.CoronalLongitudinalStress.ohmicAxialField",
        ],
    }


def tradsci_mhd_equivalence_bridge() -> dict[str, object]:
    """
    Map traditional MHD / Hall-MHD equations to HQIV Lean + Python slots.

    HQIV is composite MHD (O-Maxwell + modified fluid), not a separate phenomenology.
    Numerical gaps are coefficient calibration and vector PDE discharge — not missing physics class.
    """
    return {
        "thesis": (
            "Traditional MHD = Maxwell + fluid + conductivity; HQIV names the same stack "
            "via S_O + HQIVFluidClosureScaffold with lattice coefficients α, γ, ε, ξ."
        ),
        "paper_refs": {
            "mhd_equivalence_map": "papers/compact_object_witness/MHD_EQUIVALENCE_MAP.md",
            "omaxwell_fluid_chart": "papers/omaxwell_fluid_chart/HQIV_OMaxwell_fluid_chart.tex",
            "fluid_roadmap": "AGENTS/FLUID_OMAXWELL_ROADMAP.md",
            "lagrangian_audit": "papers/compact_object_witness/LAGRANGIAN_FAITHFULNESS_AUDIT.md",
        },
        "layer_0_action": [
            {
                "trad": "Maxwell + sources in curved spacetime",
                "hqiv": "S_O(J,A,φ) + L_O_phi_coupling",
                "lean": "Hqiv.Physics.Action",
                "status": "proved_naming",
            },
            {
                "trad": "Inhomogeneous Maxwell ∇×F = J",
                "hqiv": "EL_O_general → F_divergence_sum − 4πJ",
                "lean": "Hqiv.Physics.Action.ModifiedMaxwell",
                "status": "proved_naming",
            },
        ],
        "layer_1_resistive_mhd": [
            {
                "trad": "∂B/∂t = ∇×(v×B) − ∇×(η∇×B)",
                "hqiv": "inductionGrowthRateFromLt; steadyInductionFieldLt",
                "lean": "Hqiv.Physics.CompactObjectRotatingCrustScaffold",
                "python": "steady_induction_fields_si, induction_growth_rate_t_per_s",
                "status": "same_structure_scalar_discharge",
            },
            {
                "trad": "E = J/σ (ohmic) + v×B corrections",
                "hqiv": "ohmicAxialField J σ; coronalEffectiveAxialField",
                "lean": "Hqiv.Physics.CoronalLongitudinalStress",
                "status": "proved_classical_limit",
            },
            {
                "trad": "η resistivity / σ(T,ρ,B) conductivity",
                "hqiv": "inductionResistivityEta(ξ,ε) = γ release(ξ) G_eff(ε)",
                "lean": "CompactObjectRotatingCrustScaffold.inductionResistivityEta",
                "python": "induction_resistivity_eta_from_environment",
                "status": "proved_nonneg; xi_from_T_epsilon_from_gravity",
            },
            {
                "trad": "Frozen-in flux (ideal MHD)",
                "hqiv": "frozenFirstIndexJet; rapidityNormalized_frozenFirstIndexJet",
                "lean": "Hqiv.Physics.CovariantSolution",
                "status": "chart_transport",
            },
        ],
        "layer_2_momentum_stress": [
            {
                "trad": "ρ(∂v/∂t + v·∇v) = −∇p + J×B/c + ∇·τ",
                "hqiv": "ρ f(a,φ) Dv/Dt = RHS; f = hqivFluidInertiaFactor",
                "lean": "Hqiv.Physics.HQIVFluidClosureScaffold",
                "python": "pyhqiv.fluid",
                "status": "defined_modified_momentum",
            },
            {
                "trad": "τ = τ_mol + τ_eddy (turbulent viscosity)",
                "hqiv": "nuTotal = ν_mol + hqivEddyViscosity",
                "lean": "PlasmaFluidClosureAssumptions.nuTotal_eq_nuMol_add_hqivEddy",
                "status": "f3_bookkeeping",
            },
            {
                "trad": "PNS convective buoyancy / α effect",
                "hqiv": "hqivVacuumMomentumSource3; hot ξ → η, ν_eddy; J_O_plasma coherence",
                "lean": "OMaxwellFluidChartHypothesis",
                "status": "f2_hypothesis_same_driver_slots",
            },
            {
                "trad": "Crust longitudinal stress → torque",
                "hqiv": "hqivLongitudinalStressForce3 → crustMisalignTorqueFromStressDivergence",
                "lean": "CompactObjectRotatingCrustScaffold",
                "python": "crust_misalign_torque_from_stress_div_si",
                "status": "tensor_slot_thin_shell_discharge",
            },
        ],
        "layer_3_hall_crust": [
            {
                "trad": "Hall drift ∂B/∂t ∝ σ/(ne) ∇×((∇×B)×B)",
                "hqiv": "rapidityNormalizedJet on frozen EM jet (Hall-scale transport)",
                "lean": "CovariantSolution.rapidityNormalized_frozenFirstIndexJet",
                "status": "milestone_vector_hall_discharge",
            },
            {
                "trad": "Crust elasticity + plastic flow",
                "hqiv": "thin-shell (h/R)² screen; variational σ_ij extension",
                "lean": "crustMisalignTorqueFromStressDivergence",
                "status": "milestone_elasticity_variational",
            },
            {
                "trad": "Ohmic decay τ_ohm ~ 10⁴–10⁶ yr",
                "hqiv": "J/σ leg; σ from ξ ladder (same equation, calibrate σ)",
                "python": "magnetic_field_dynamics_gap_witness.crust_diffusion_sketch",
                "status": "coefficient_calibration",
            },
            {
                "trad": "Multipole evolution (Hall vs ohmic)",
                "hqiv": "surface_multipole_decomposition + future ∂_t c_l",
                "python": "surface_multipole_dynamics_hypothesis",
                "status": "geometry_witness_time_derivative_open",
            },
        ],
        "layer_4_dynamo": [
            {
                "trad": "αΩ proto-NS dynamo → 10¹²–10¹³ G seed",
                "hqiv": "High ξ PNS: η, ν_eddy, g_vac, plasma J on same induction PDE",
                "status": "same_pde_boundary_condition_slot",
            },
            {
                "trad": "Magnetar 10¹⁴–10¹⁵ G",
                "hqiv": "Pair cascade at B > B_cr; not separate Maxwell sector",
                "python": "pair_production_margin_effective, B_CR_TESLA",
                "status": "saturation_and_seed_calibration",
            },
        ],
        "coefficient_identification": {
            "trad_eta_resistivity": "η_MHD in induction equation",
            "hqiv_eta": "inductionResistivityEta(ξ,ε) = γ × release(ξ) × G_eff(ε)",
            "trad_sigma": "σ(T,B) in J = σ(E + v×B)",
            "hqiv_sigma_bridge": "ξ from T_out (spin/CMB); ohmicAxialField J/σ",
            "trad_alpha_dynamo": "turbulent α from convection",
            "hqiv_alpha_bridge": "ν_eddy(Θ,|δ̇θ′|,ℓ_coh,C) + g_vac from ∇(φ∇δ̇θ′)",
            "lattice_constants": {"alpha": ALPHA, "gamma": GAMMA, "c_rindler_shared": C_RINDLER_SHARED},
        },
        "same_dynamics_verdict": (
            "TradSci and HQIV share Maxwell + resistive induction + MHD momentum + "
            "Hall/ohmic crust evolution. HQIV fixes geometry (ε layers, colatitude belts, "
            "τ_mis) and coefficient algebra (α, γ); trad codes fix σ(T,B) and α by tuning. "
            "Paper should display equations side-by-side, not compete with naïve dipole bags."
        ),
        "implementation_milestones": [
            "Vector ∇× induction on oblate crust chart",
            "σ(ξ,ε,B) witness ↔ literature τ_ohm",
            "Hall τ_H witness ↔ rapidityNormalizedJet",
            "∂_t multipoles coupled to dB_growth and diffusion",
            "PNS high-ξ initial condition on same PDE stack",
        ],
        "coefficient_calibration_witness": coefficient_calibration_witness(),
    }


def paper_dynamics_section_bundle() -> dict[str, object]:
    """
    Paper-ready bundle: MHD reduction + geometry differentiators + predictions.

    Supports PAPER_DYNAMICS_SECTION.md — not a new magnetic theory; same physics,
    ε-layer / spin-axis organization, testable multipole predictions.
    """
    bridge = tradsci_mhd_equivalence_bridge()
    gap = magnetic_field_dynamics_gap_witness()
    multipole = surface_multipole_dynamics_hypothesis()
    j0030 = nicer_j0030_surface_multipole_witness()
    j0740 = nicer_j0740_surface_multipole_witness()

    geometric_advantages = [
        {
            "title": "ε-tipping composition layers",
            "mechanism": "r_top, r_charm move with ε; charm retreat on spindown",
            "witness": "gradient_collapse_hypothesis, spindown_charm_retreat_feedback",
            "cli": "--spindown-charm-audit",
        },
        {
            "title": "Spin-axis latitude organization",
            "mechanism": "ρ_pol, ε_spin(θ), axial ∇φ, Coriolis gate sin²θ|cosθ|",
            "witness": "latitude_torsion_scan, surface_multipole_decomposition",
            "cli": "--surface-multipole-audit",
        },
        {
            "title": "Mid-latitude shear belt → l=2/l=3",
            "mechanism": "ψ_shear, χ peak ~45–70° colatitude",
            "witness": "surface_multipole_dynamics_hypothesis.scenario_summary",
        },
        {
            "title": "Enhanced aligning torque closure",
            "mechanism": "B_align lattice RMS + charm-ledger boost + crust J×B",
            "witness": "aligning_b_for_torque_t, tau_align_enhanced",
            "cli": "slip_torque_balance_for_star (aligning_enhanced fields)",
        },
        {
            "title": "Unified obliquity τ_mis",
            "mechanism": "Longitudinal stress divergence vs τ_align",
            "witness": "slip_torque_balance_for_star, alfven_slip_torque_balance_hypothesis",
        },
        {
            "title": "m=1 azimuthal spots from τ_mis",
            "mechanism": "Tilted dipole; two longitude-offset hotspots",
            "witness": "tau_mis_m1_gate, nicer_ppm_comparison_witness",
        },
        {
            "title": "Spin-dependent multipole transition",
            "mechanism": "Coriolis×shear at moderate Ω vs equatorial induction at breakup",
            "witness": "high_spin_mass_tail_multipole_grid",
            "cli": "--surface-multipole-audit",
        },
        {
            "title": "Environment-aware η(ξ,ε)",
            "mechanism": "T_out with co-spin + CMB Doppler → ξ → η",
            "witness": "induction_resistivity_eta_from_environment",
        },
    ]

    traditional_edges = [
        {
            "area": "σ(T,B), Hall, plastic yield, τ_ohm calibration",
            "hqiv_status": "coefficient_calibration_witness vs literature σ band",
            "paper_frame": "discharging coefficients (η witness + τ_ohm sketch)",
        },
        {
            "area": "Time-dependent 3D/2D Hall-MHD 10³–10⁶ yr",
            "hqiv_status": "static multipole projections; ∂_t c_l schematic",
            "paper_frame": "same PDEs; integration milestone",
        },
        {
            "area": "Hall term benchmark",
            "hqiv_status": "rapidityNormalizedJet map sketched",
            "paper_frame": "explicit Hall discharge next",
        },
        {
            "area": "Proto-NS αΩ seed for magnetar B",
            "hqiv_status": "B₀ boundary; evolution + pair saturation in witness",
            "paper_frame": "birth B external; HQIV for geometry evolution",
        },
    ]

    differentiating_predictions = [
        {
            "prediction": "Mass/spin dependence of l₂/l₃, centroid, m₁",
            "evidence_summary": (
                f"J0030 l2/l0={j0030['hqiv_emission_l2_over_l0']:.2f}, "
                f"J0740 antipodal offset "
                f"{j0740['quantitative_comparison'].get('azimuthal_offset_from_antipode_deg')}°"
            ),
            "data": "surface_multipole_dynamics_hypothesis, high_spin_mass_tail",
            "cli": "--surface-multipole-audit",
        },
        {
            "prediction": "Field obliquity α_eq vs catalog B and spin regime",
            "evidence_summary": (
                "Catalog B → α_eq≈90° (misaligning-dominated); canonical 10¹² G ms → "
                "~71°; breakup → ~11°; Crab catalog B → ~24°. Surface NICER geometry "
                "uses separate multipole layer (m=1 tilt from enhanced α_eq)."
            ),
            "data": "pulsar_witness_comparison.json, alfven_slip_torque_balance_hypothesis",
            "cli": "hqiv_pulsar_witness_benchmark.py --json",
        },
        {
            "prediction": "Obliquity correlates with m₁ and τ_mis/τ_align",
            "evidence_summary": "slip_torque_balance rows vs pulsar catalog overlay",
            "data": "pulsar_witness_comparison.json",
            "cli": "--spindown-charm-pulsar-audit",
        },
        {
            "prediction": "Charm retreat + pair/B_charm in high-mass high-spin tail",
            "evidence_summary": gap["breakup_channel_audit"]["verdict"],
            "data": "spindown_charm_retreat_feedback",
            "cli": "--spindown-charm-audit, --breakup-b-audit",
        },
        {
            "prediction": "η(ξ,ε) vs crust σ and τ_ohm literature band",
            "evidence_summary": (
                "coefficient_calibration_witness: μ₀σR² at stellar radius matches "
                "10⁴–10⁶ yr order for σ∈[10⁷,10⁹] S/m"
            ),
            "data": "coefficient_calibration_witness",
            "cli": "--eta-calibration-audit",
        },
    ]

    cal = coefficient_calibration_witness()
    coefficient_discharge_plan = {
        "goal": "Side-by-side η_HQIV(ξ,ε) and σ(T,B) literature on benchmark stars",
        "benchmarks_msun": [1.4, 1.98],
        "literature_sigma_S_m": CRUST_CONDUCTIVITY_S_M_LITERATURE,
        "literature_tau_ohm_yr": OHMIC_DECAY_TIME_YR_LITERATURE,
        "hqiv_eta_formula": bridge["coefficient_identification"]["hqiv_eta"],
        "status": "numeric_table_in_coefficient_calibration_witness",
        "eta_ns_surface_spin_boosted": cal["eta_ns_surface_spin_boosted"],
        "tau_ohm_yr_stellar_radius": cal["tau_ohm_yr_at_sigma_stellar_radius"],
        "discharge_verdict": cal["discharge_verdict"],
    }

    return {
        "framing_statement": (
            "First-principles organization of the same Hall-MHD / resistive-MHD physics "
            "around ε-tipping layers and the spin axis—not a new magnetic theory."
        ),
        "paper_outline_markdown": "papers/compact_object_witness/PAPER_DYNAMICS_SECTION.md",
        "mhd_equivalence_bridge": bridge,
        "magnetic_field_gap": {
            "log10_gap_vs_magnetar": gap["log10_gap_surface_B_vs_magnetar"],
            "incremental_channels": gap["incremental_channel_fractions_at_breakup"],
            "witness_role": gap["witness_role"],
        },
        "geometric_advantages": geometric_advantages,
        "traditional_edges": traditional_edges,
        "differentiating_predictions": differentiating_predictions,
        "coefficient_discharge_plan": coefficient_discharge_plan,
        "nicer_overlay_summary": {
            "J0030+0451": {
                "verdict": j0030["verdict"],
                "centroid_km": j0030["hqiv_centroid_offset_km_from_pole"],
                "l2_over_l0": j0030["hqiv_emission_l2_over_l0"],
            },
            "J0740+6620": {
                "verdict": j0740["verdict"],
                "azimuthal_offset_deg": j0740["quantitative_comparison"].get(
                    "azimuthal_offset_from_antipode_deg"
                ),
                "l2_over_l0": j0740["hqiv_emission_l2_over_l0"],
            },
        },
        "high_spin_tail_sample": multipole.get("high_spin_mass_tail", [])[:4],
        "recommended_section_order": [
            "Framing: same MHD, geometry-first",
            "Equation equivalence table (prove reduction)",
            "ε-layers and spin-axis geometry",
            "Obliquity and multipoles (NICER)",
            "Spin/mass multipole transition",
            "Coefficient discharge vs σ, Hall, τ_ohm",
            "Testable predictions",
            "Limitations: proto-NS seed B, time-dependent Hall-MHD",
        ],
        "lean_discharged_theorem": (
            "Hqiv.Physics.CompactObjectMhdEquivalenceScaffold.compactObjectMhdEquivalenceDischarged_holds"
        ),
        "lean_paper_tex": (
            "papers/compact_object_witness/hqiv_compact_object_crust_mhd_equivalence.tex"
        ),
    }


def magnetic_field_dynamics_gap_witness(
    mass_msun: float = 1.98,
    *,
    B_surface_t: float = B_SURFACE_T_DEFAULT,
) -> dict[str, object]:
    """
    Quantify HQIV B-channel strength vs magnetar / proto-NS dynamo scales.

    Documents where the witness is an **evolution** layer on a seeded dipole
    rather than a **generation** mechanism for 10^{14}–10^{15} G fields.
    """
    breakup = quantify_breakup_b_channels(mass_msun, B_surface_t=B_surface_t)
    mass_kg = mass_msun * M_SUN_KG
    r_m = radius_uniform_density(mass_kg, RHO_NUCLEAR_KG_M3)
    om_break = breakup_omega_rad_s(mass_kg, r_m)
    hz = om_break / (2.0 * math.pi)
    slip = slip_torque_balance_for_star(
        mass_msun,
        hz,
        f"{mass_msun:.2f} M☉ breakup (dynamics gap)",
        B_surface_t=B_surface_t,
    )

    b_surf_g = B_surface_t * 1.0e4
    log_gaps_magnetar = {
        f"log10_gap_vs_{int(lo)}G": math.log10(lo / max(b_surf_g, 1.0))
        for lo in MAGNETAR_B_GAUSS_TYPICAL
    }

    b_total = float(breakup["B_total_eff_t"])
    channel_fractions = {
        "B_eff_fraction_of_total": float(breakup["B_eff_t"]) / max(b_total, 1.0e-30),
        "B_LT_fraction_of_total": float(breakup["B_induction_lt_t"]) / max(b_total, 1.0e-30),
        "B_long_fraction_of_total": float(breakup["B_induction_long_t"]) / max(b_total, 1.0e-30),
        "B_pair_fraction_of_total": float(breakup["B_pair_fraction_of_B_total"]),
        "B_charm_fraction_of_total": float(breakup["B_charm_t"]) / max(b_total, 1.0e-30),
    }

    # Schematic growth rate (η a_LT/R) — unphysical for seeding without back-reaction.
    d_b_growth = slip.dB_growth_t_per_s
    schematic_growth_yr = (
        B_surface_t / max(d_b_growth, 1.0e-30) / (365.25 * 86400.0)
        if d_b_growth > 0.0
        else float("inf")
    )

    # Crust ohmic diffusion: use literature range (layered σ(T), Hall coupling not in sketch).
    tau_ohm_yr_literature_mid = math.sqrt(
        OHMIC_DECAY_TIME_YR_LITERATURE[0] * OHMIC_DECAY_TIME_YR_LITERATURE[1]
    )

    return {
        "witness_role": (
            "evolution_and_complexification_on_seeded_B0; "
            "not_proto_neutron_star_dynamo_generation"
        ),
        "reference_scales_gauss": {
            "B_surface_witness_default": b_surf_g,
            "magnetar_typical_range": MAGNETAR_B_GAUSS_TYPICAL,
            "proto_ns_dynamo_typical_range": PROTO_NS_DYNAMO_B_GAUSS_TYPICAL,
            "schwinger_critical": B_CR_TESLA * 1.0e4,
        },
        "log10_gap_surface_B_vs_magnetar": log_gaps_magnetar,
        "breakup_channel_audit": breakup,
        "incremental_channel_fractions_at_breakup": channel_fractions,
        "induction_schematic": {
            "eta_induction": slip.eta_induction,
            "dB_growth_t_per_s": d_b_growth,
            "schematic_time_to_B_surface_yr_if_unsaturated": schematic_growth_yr,
            "steady_B_LT_t": slip.B_induction_lt_t,
            "steady_B_LT_over_B_surface": slip.B_induction_lt_t / max(B_surface_t, 1.0e-30),
            "note": (
                "∂B/∂t ~ η a_LT/R ignores resistivity saturation and Hall back-reaction; "
                "steady closure B_LT = η(a_LT/a_grav)B_surf is O(10^{-3}) of B_surf at breakup."
            ),
        },
        "crust_diffusion_sketch": {
            "conductivity_S_m_literature_range": CRUST_CONDUCTIVITY_S_M_LITERATURE,
            "ohmic_decay_time_yr_literature_range": OHMIC_DECAY_TIME_YR_LITERATURE,
            "ohmic_decay_time_yr_literature_mid": tau_ohm_yr_literature_mid,
            "hall_mhd_evolution_yr": "10^3–10^6 (literature; not yet in HQIV witness)",
        },
        "verdict_table": {
            "generating_strong_initial_B": {
                "traditional": "strong",
                "hqiv": "weak",
                "status": "trad_sci_leads",
            },
            "explaining_non_dipolar_offset_geometry": {
                "traditional": "good_parameter_heavy",
                "hqiv": "competitive_cleaner",
                "status": "hqiv_competitive",
            },
            "mass_spin_dependence": {
                "traditional": "often_post_hoc",
                "hqiv": "natural_quantitative",
                "status": "hqiv_advantage",
            },
            "unifying_obliquity_multipoles_activity": {
                "traditional": "fragmented",
                "hqiv": "unified",
                "status": "hqiv_advantage",
            },
            "microphysical_rigor": {
                "traditional": "high",
                "hqiv": "schematic",
                "status": "trad_sci_leads",
            },
            "first_principles_geometry": {
                "traditional": "moderate",
                "hqiv": "strong",
                "status": "hqiv_advantage",
            },
            "time_evolution_10^3_to_10^6_yr": {
                "traditional": "hall_mhd_mature",
                "hqiv": "not_yet_coupled",
                "status": "trad_sci_leads",
            },
        },
        "paper_scope_recommendation": [
            "Treat B_surface as boundary data from spindown / NICER / catalog (or proto-NS dynamo seed).",
            "HQIV predicts geometry evolution: ψ_shear, multipoles, τ_mis m=1, obliquity balance.",
            "Do not claim magnetar 10^{14} G generation without a new turbulent-dynamo slot.",
            "Position vs Hall-MHD codes: complementary geometry-first layer, not replacement.",
        ],
        "dynamics_milestones_before_final_paper": [
            "Couple ∂B/∂t to crust stress current with σ(ρ,T,B) and Hall drift timescale witness.",
            "Feed B_total back into τ_mis and induction η (closed stress → current → B loop).",
            "Track multipole l=2/l=3 evolution over ohmic/Hall times (compare to NICER offsets).",
            "Optional: proto-NS convection αΩ dynamo as explicit birth boundary, separate from crust induction.",
        ],
    }


def compact_object_witness() -> dict[str, object]:
    rho_n = matter_density("nuclear")
    rho_c = matter_density("charmed")

    benchmark_rows = [
        build_row("canonical 1.4 M☉ NS", "nuclear", 1.4, notes="GW170817-style mass"),
        build_row("heavy NS 2.0 M☉", "nuclear", 2.0, notes="upper observed pulsar masses"),
        build_row("charmed 1.0 M☉", "charmed", 1.0, notes="hypothetical charmed-nuclear sphere"),
    ]

    return {
        "lean_modules": [
            "Hqiv.Physics.NuclearOutsideTemperatureDynamics",
            "Hqiv.Physics.NuclearCurvatureBinding",
            "Hqiv.Physics.MetaHorizonTrappedPlanckMass",
            "Hqiv.Geometry.HQVMetric",
            "Hqiv.Physics.GlobalDetuning",
            "Hqiv.Physics.HepDecayReadout",
            "Hqiv.Physics.CompactObjectRotatingCrustScaffold",
            "Hqiv.Physics.CompactObjectMhdEquivalenceScaffold",
            "Hqiv.Physics.CoronalLongitudinalStress",
            "Hqiv.Physics.HQIVFluidClosureScaffold",
        ],
        "lattice_constants": {
            "alpha": ALPHA,
            "gamma": GAMMA,
            "c_rindler_shared": C_RINDLER_SHARED,
            "alpha_times_gamma": ALPHA_GAMMA,
            "reference_m": REFERENCE_M,
            "liquid_local_field_divisor": 1.0 - C_RINDLER_SHARED,
        },
        "matter_density_kg_m3": {
            "nuclear": rho_n,
            "charmed": rho_c,
            "charmed_over_nuclear": rho_c / rho_n,
        },
        "primary_prediction": {
            "object": "neutron_star_max_mass",
            "epsilon_crit": C_RINDLER_SHARED,
            "mass_msun": mass_from_epsilon_crit(C_RINDLER_SHARED, rho_n) / M_SUN_KG,
            "lapse_at_crit": 1.0 - C_RINDLER_SHARED,
            "interpretation": (
                "Uniform nuclear-density sphere: surface ε hits c_rindler_shared = γ/2; "
                "outside G_eff and bonded binding slots saturate before Schwarzschild."
            ),
        },
        "critical_mass_table_nuclear": critical_mass_table("nuclear"),
        "critical_mass_table_charmed": critical_mass_table("charmed"),
        "epsilon_scan_nuclear": epsilon_scan(
            "nuclear",
            [6e-7, 1e-4, 0.01, 0.1, 0.155, 0.2, 0.24, 0.3, 0.5],
        ),
        "benchmark_objects": [asdict(r) for r in benchmark_rows],
        "trapped_mass_ladder": trapped_mass_ladder(),
        "charmed_baryon_masses_mev": {
            f"n_charm_{n}": hep.charmed_baryon_mass_mev(
                PROTON_MEV, 493.677, 139.57, n
            )
            for n in (1, 2, 3)
        },
        "gradient_collapse_hypothesis": gradient_collapse_hypothesis(),
        "spindown_charm_retreat_feedback": quantify_spindown_charm_retreat_feedback(1.98),
        "spindown_charm_pulsar_comparison_ms": compare_spindown_charm_to_pulsar_dataset(
            millisecond_only=True,
        ),
        "spindown_charm_pulsar_comparison_mass_measured": compare_spindown_charm_to_pulsar_dataset(
            mass_measured_only=True,
        ),
        "surface_multipole_dynamics_hypothesis": surface_multipole_dynamics_hypothesis(),
        "magnetic_field_dynamics_gap": magnetic_field_dynamics_gap_witness(),
        "tradsci_mhd_equivalence_bridge": tradsci_mhd_equivalence_bridge(),
        "coefficient_calibration_witness": coefficient_calibration_witness(),
        "paper_dynamics_section_bundle": paper_dynamics_section_bundle(),
        "spin_geff_analysis": spin_geff_analysis(),
        "spin_oblate_gradient_hypothesis": spin_oblate_gradient_hypothesis(),
        "longitudinal_em_lapse_torsion_hypothesis": longitudinal_em_lapse_torsion_hypothesis(),
        "alfven_slip_torque_balance_hypothesis": alfven_slip_torque_balance_hypothesis(),
    }


def print_report(data: dict[str, object]) -> None:
    pred = data["primary_prediction"]
    print("HQIV compact-object mass (curvature slots)")
    print(f"  α={ALPHA}, γ={GAMMA}, c_rindler_shared=γ/2={C_RINDLER_SHARED}")
    print(f"  ρ_nuclear={data['matter_density_kg_m3']['nuclear']:.3e} kg/m³")
    print()
    print("Primary NS max-mass prediction:")
    print(f"  ε_crit = γ/2 = {pred['epsilon_crit']}")
    print(f"  M_max ≈ {pred['mass_msun']:.2f} M☉  (lapse N = {pred['lapse_at_crit']})")
    print()
    print("Critical mass table (nuclear matter):")
    for row in data["critical_mass_table_nuclear"]:
        print(
            f"  ε={row['epsilon_crit']:.3f}: "
            f"M={row['mass_msun']:.2f} M☉, R={row['radius_km']:.1f} km, "
            f"Rs/R={row['compactness_rs_over_r']:.3f} — {row['note']}"
        )
    print()
    print("Charmed matter (ρ_charm / ρ_nuc = "
          f"{data['matter_density_kg_m3']['charmed_over_nuclear']:.2f}):")
    for row in data["critical_mass_table_charmed"]:
        if row["epsilon_crit"] in (C_RINDLER_SHARED, 0.5):
            print(
                f"  ε={row['epsilon_crit']:.3f}: M={row['mass_msun']:.2f} M☉, "
                f"R={row['radius_km']:.1f} km"
            )
    print()
    print("Benchmarks:")
    for row in data["benchmark_objects"]:
        print(
            f"  {row['label']}: M={row['mass_msun']} M☉, R={row['radius_km']:.1f} km, "
            f"ε={row['epsilon_surface']:.3f}, N={row['lapse_surface']:.3f}, "
            f"B/A={row['per_nucleon_binding_mev']:.2f} MeV"
        )
    grad = data["gradient_collapse_hypothesis"]
    tail = grad["mass_tail_msun"]
    print()
    print("Gradient tail + cascade hypothesis (fixed outer R at NS max):")
    print(f"  uniform max     {tail['uniform_nuclear_max']:.2f} M☉")
    print(f"  + charmed core  {tail['charmed_core_at_same_R']:.2f} M☉  (+{tail['delta_charm_tail']:.2f})")
    print(f"  top seed (ε₀=α) {tail['top_seed_at_same_R']:.2f} M☉")
    print(f"  horizon (ε=½)   {tail['horizon_at_same_R']:.2f} M☉")
    print(f"  full top sphere {tail['full_top_sphere_at_same_R']:.0f} M☉ (runaway)")
    gaps = grad["cascade_gap_msun"]
    print(
        f"  gaps: charm→top seed {gaps['charm_tail_to_top_seed']:.2f} M☉, "
        f"charm→horizon {gaps['charm_tail_to_horizon']:.2f} M☉"
    )
    spin = data["spin_geff_analysis"]
    print()
    print("Spin → outside G_eff (nuclear ε slot; equatorial co-rotation):")
    for row in spin["rows"]:
        print(
            f"  {row['label']}: ε_g={row['epsilon_gravity']:.3f} "
            f"+ε_spin={row['epsilon_spin_rindler']:.3f} → "
            f"G_eff mod {row['outside_geff_mod_gravity_only']:.4f} → "
            f"{row['outside_geff_mod_with_spin']:.4f} "
            f"(Δ={row['geff_mod_delta']:+.4f}), Ω/Ω_break={row['omega_over_breakup']:.3f}"
        )
    print(f"  Flyby φ-channel G_eff at surface (no spin): ≈ {spin['rows'][0]['flyby_geff_phi_ratio']:.3f}")
    oblate = data["spin_oblate_gradient_hypothesis"]
    print()
    print("Spin + oblate gradient (latitude tipping + flattening):")
    for tipping, hz in oblate["equatorial_tipping_omega_hz_1p98Msun"].items():
        hz_s = f"{hz:.0f} Hz" if hz is not None else "not reached"
        print(f"  1.98 M☉ equator {tipping}: {hz_s}")
    for sc in oblate["scenarios"]:
        print(
            f"  {sc['label']}: Ω/Ω_break={sc['omega_over_breakup']:.2f}, "
            f"R_eq={sc['radius_equatorial_km']:.1f}km R_pol={sc['radius_polar_km']:.1f}km, "
            f"tail={sc['mass_charmed_tail_msun']:.2f} M☉ (Δ={sc['delta_tail_vs_no_spin_msun']:+.2f})"
        )
        for lat in sc["latitude_rows"]:
            if lat["colatitude_deg"] in (0.0, 90.0):
                print(
                    f"    θ={lat['colatitude_deg']:3.0f}°: ε={lat['epsilon_total']:.3f} "
                    f"charm={lat['charm_tipped']} top={lat['top_tipped']} "
                    f"horizon={lat['horizon_surface']} "
                    f"r_charm/R_pol={lat['r_charm_over_Rpol']:.2f}"
                )
    torsion = data["longitudinal_em_lapse_torsion_hypothesis"]
    print()
    print("Longitudinal EM + lapse-drag torsion (ψ_shear vs ψ_long):")
    for sc in torsion["scenarios"]:
        print(
            f"  {sc['label']}: ψ_shear={sc['peak_psi_shear_deg']:.2f}° "
            f"ψ_long={sc['peak_psi_long_deg']:.3f}° @θ={sc['peak_torsion_colatitude_deg']:.0f}°, "
            f"χ={sc['peak_torsion_coupling_chi']:.2e}"
        )
    grid = torsion["mass_spin_torsion_grid"]
    print("  Mass–spin grid (peak ψ_shear):")
    for row in grid:
        if row["omega_over_breakup"] in (0.0, 0.5, 1.0):
            print(
                f"    M={row['mass_msun']:.2f} M☉ Ω/Ω_break={row['omega_over_breakup']:.2f}: "
                f"ψ_shear={row['peak_psi_shear_deg']:.2f}° "
                f"θ_peak={row['peak_torsion_colatitude_deg']:.0f}°"
            )
    slip = data["alfven_slip_torque_balance_hypothesis"]
    print()
    print("Alfvén slip torque balance (τ_mis vs B_surf / B_eff / closed loop):")
    for row in slip["rows"]:
        print(
            f"  {row['label']}: ψ_shear={row['psi_shear_deg']:.2f}° "
            f"ψ_long={row['psi_long_deg']:.3f}°, δB/B={row['delta_b_over_b']:.2f}, "
            f"B_eff={row['B_eff_t']:.2e} T, B_total={row['B_total_eff_t']:.2e} T"
        )
        print(
            f"    τ_ratio: surf={row['torque_ratio_surface_b']:.3f} "
            f"b_eff={row['torque_ratio_b_eff']:.3f} "
            f"closed={row['torque_ratio_closed_loop']:.3f} "
            f"enhanced={row['torque_ratio_aligning_enhanced']:.3f} → "
            f"α_eq: {row['alpha_equilibrium_surface_deg']:.1f}° / "
            f"{row['alpha_equilibrium_b_eff_deg']:.1f}° / "
            f"{row['alpha_equilibrium_closed_loop_deg']:.1f}° / "
            f"{row['alpha_equilibrium_aligning_enhanced_deg']:.1f}°"
        )


def main() -> None:
    parser = argparse.ArgumentParser(description="HQIV compact-object mass from curvature slots")
    parser.add_argument("--json", action="store_true", help="write data/compact_object_witnesses.json")
    parser.add_argument(
        "--breakup-b-audit",
        action="store_true",
        help="print 1.98 M☉ breakup B_pair / B_charm quantification",
    )
    parser.add_argument(
        "--spindown-charm-audit",
        action="store_true",
        help="quantify spin-down mass loss → charm retreat → B feedback at 1.98 M☉",
    )
    parser.add_argument(
        "--spindown-charm-pulsar-audit",
        action="store_true",
        help="compare spindown/charm dynamics to pulsar catalog (ms + mass-measured)",
    )
    parser.add_argument(
        "--paper-dynamics-outline",
        action="store_true",
        help="paper section bundle: MHD reduction + geometry predictions",
    )
    parser.add_argument(
        "--mhd-equivalence-audit",
        action="store_true",
        help="traditional MHD / Hall-MHD equation map to HQIV Lean slots",
    )
    parser.add_argument(
        "--magnetic-field-gap-audit",
        action="store_true",
        help="B-channel gap vs magnetar / proto-NS dynamo + dynamics target verdict",
    )
    parser.add_argument(
        "--eta-calibration-audit",
        action="store_true",
        help="HQIV η(ξ,ε) vs literature crust σ and τ_ohm sketch",
    )
    parser.add_argument(
        "--surface-multipole-audit",
        action="store_true",
        help="zonal l=2/l=3 + m=1 τ_mis overlay vs NICER J0030/J0740",
    )
    args = parser.parse_args()
    if args.paper_dynamics_outline:
        bundle = paper_dynamics_section_bundle()
        print("\n=== Paper dynamics section bundle ===")
        print(f"  Framing: {bundle['framing_statement']}")
        print(f"  Outline: {bundle['paper_outline_markdown']}")
        print("\n  Geometric advantages (HQIV differentiators):")
        for item in bundle["geometric_advantages"]:
            print(f"    • {item['title']}: {item['mechanism']}")
        print("\n  Traditional edges (honest):")
        for item in bundle["traditional_edges"]:
            print(f"    • {item['area']}: {item['paper_frame']}")
        print("\n  Differentiating predictions:")
        for item in bundle["differentiating_predictions"]:
            print(f"    • {item['prediction']}")
            print(f"      evidence: {item['evidence_summary']}")
        nicer = bundle["nicer_overlay_summary"]
        print("\n  NICER summary:")
        for key, val in nicer.items():
            print(f"    {key}: {val}")
        print("\n  Recommended section order:")
        for i, step in enumerate(bundle["recommended_section_order"], 1):
            print(f"    {i}. {step}")
        return
    if args.mhd_equivalence_audit:
        bridge = tradsci_mhd_equivalence_bridge()
        print("\n=== Traditional MHD ↔ HQIV equation correspondence ===")
        print(f"  Thesis: {bridge['thesis']}")
        print(f"  Verdict: {bridge['same_dynamics_verdict']}")
        for layer_key in (
            "layer_0_action",
            "layer_1_resistive_mhd",
            "layer_2_momentum_stress",
            "layer_3_hall_crust",
            "layer_4_dynamo",
        ):
            rows = bridge[layer_key]
            print(f"\n  {layer_key}:")
            for row in rows:
                trad = row["trad"][:70] + ("…" if len(row["trad"]) > 70 else "")
                print(f"    trad: {trad}")
                print(f"      hqiv: {row['hqiv']}")
                print(f"      status: {row['status']}")
        ident = bridge["coefficient_identification"]
        print("\n  Coefficient identification:")
        print(f"    trad η ↔ {ident['hqiv_eta']}")
        print(f"    trad σ ↔ {ident['hqiv_sigma_bridge']}")
        print(f"    trad α ↔ {ident['hqiv_alpha_bridge']}")
        print("\n  Milestones:")
        for line in bridge["implementation_milestones"]:
            print(f"    • {line}")
        print(f"\n  Full map: {bridge['paper_refs']['mhd_equivalence_map']}")
        cal = bridge.get("coefficient_calibration_witness", {})
        if cal:
            print("\n  η calibration discharge:")
            print(f"    {cal.get('discharge_verdict', '')}")
            print(f"    η(NS surface, spin-boosted) = {cal.get('eta_ns_surface_spin_boosted', 0):.4f}")
            for key, val in cal.get("tau_ohm_yr_at_sigma_stellar_radius", {}).items():
                print(f"    τ_ohm stellar ({key}) = {val:.2e} yr")
        return
    if args.eta_calibration_audit:
        cal = coefficient_calibration_witness()
        print("\n=== HQIV η(ξ,ε) vs crust σ calibration ===")
        print(f"  HQIV η: {cal['hqiv_eta_definition']}")
        print(f"  Verdict: {cal['discharge_verdict']}")
        rep = cal["representative_ms_pulsar_point"]
        print(
            f"  Representative: {rep['mass_msun']} M☉ @ {rep['omega_hz']:.0f} Hz, "
            f"θ={rep['colatitude_deg']:.0f}°, B={rep['B_surface_t']:.2e} T"
        )
        print(f"  η(NS surface, spin-boosted) = {cal['eta_ns_surface_spin_boosted']:.4f}")
        print("  τ_ohm sketch (μ₀ σ R², stellar radius):")
        for key, val in cal["tau_ohm_yr_at_sigma_stellar_radius"].items():
            print(f"    {key}: {val:.2e} yr")
        print("\n  Sample grid rows (static η, mid-ε):")
        mid_eps = EPS_CHARM_TIP
        for row in cal["calibration_grid"]:
            if row["phi_epsilon"] == mid_eps and row["temperature_label"] == "ns_surface":
                print(
                    f"    σ={row['sigma_S_m']:.0e} S/m: "
                    f"η_HQIV={row['eta_hqiv_static']:.4f}, "
                    f"τ_ohm(stellar)={row['tau_ohm_yr_stellar_radius']:.2e} yr, "
                    f"dB/dt={row['dB_growth_static_t_per_s']:.2e} T/s"
                )
        return
    if args.surface_multipole_audit:
        hyp = surface_multipole_dynamics_hypothesis()
        print("\n=== Surface multipoles (zonal l=2/l=3 + m=1 τ_mis) + NICER overlay ===")
        print(f"  Hypothesis: {hyp['hypothesis']}")
        for row in hyp["scenario_summary"]:
            m1 = row.get("m1_azimuthal_fraction")
            m1_str = f"{m1:.3f}" if m1 is not None else "—"
            az = row.get("azimuthal_offset_from_antipode_deg")
            az_str = f"{az:.1f}°" if az is not None else "—"
            print(
                f"  {row['label']}: Ω/Ω_break={row['omega_over_breakup']:.3f}, "
                f"emit l2/l0={row['emission_l2_over_l0']:.3f}, "
                f"l3/l0={row['emission_l3_over_l0']:.3f}, "
                f"centroid cosθ={row['centroid_cos_colatitude']:.3f}, "
                f"m₁ frac={m1_str}, az offset={az_str}, "
                f"ψ peak @ {row['peak_torsion_colatitude_deg']:.0f}°"
            )

        def _print_nicer_overlay(tag: str, witness: dict[str, object]) -> None:
            qc = witness["quantitative_comparison"]
            print(f"\n  NICER {tag} verdict: {witness['verdict']}")
            print(f"    HQIV centroid offset from pole: {witness['hqiv_centroid_offset_km_from_pole']:.2f} km")
            print(
                f"    emission l2/l0={witness['hqiv_emission_l2_over_l0']:.3f}, "
                f"l3/l0={witness['hqiv_emission_l3_over_l0']:.3f}"
            )
            if "m1_azimuthal_fraction" in qc:
                print(f"    m₁ azimuthal fraction: {qc['m1_azimuthal_fraction']:.3f}")
                print(
                    f"    two-spot longitude sep: {qc.get('longitude_separation_deg', 0.0):.1f}°, "
                    f"offset from antipode: {qc.get('azimuthal_offset_from_antipode_deg', 0.0):.1f}°"
                )
            if tag == "J0030+0451":
                lit = witness["nicer_literature"]
                print(f"    Miller colatitude median: {lit['spot_colatitude_deg_miller_median']:.1f}°")
                print(f"    HQIV spot colatitude: {qc.get('spot_colatitude_deg_hqiv', 0.0):.1f}°")
                print(f"    literature offset range (km): {lit['hotspot_offset_km_range']}")
                print(f"    centroid in literature range: {qc.get('centroid_in_literature_offset_km_range')}")
            if tag == "J0740+6620":
                lit = witness["nicer_literature"]
                print(
                    f"    Riley antipodal offset >{lit['azimuthal_offset_from_antipode_deg_min_prob']:.0f}° "
                    f"at {lit['azimuthal_offset_from_antipode_probability']:.0%} prob"
                )
                print(f"    HQIV exceeds threshold: {qc.get('hqiv_exceeds_antipodal_offset_threshold')}")
                print(f"    radius Riley median: {lit['radius_km_riley_median']:.2f} km, HQIV uniform: {qc['radius_km_hqiv_uniform']:.2f} km")

        _print_nicer_overlay("J0030+0451", hyp["nicer_j0030"])
        _print_nicer_overlay("J0740+6620", hyp["nicer_j0740"])

        print("\n  High-spin / high-mass tail (equatorial induction vs Coriolis belt):")
        for row in hyp["high_spin_mass_tail"]:
            print(
                f"    {row['label']}: Ω/Ω_break={row['omega_over_breakup']:.3f}, "
                f"l2/l0={row['emission_l2_over_l0']:.3f}, l3/l0={row['emission_l3_over_l0']:.3f}, "
                f"centroid offset/R={row['centroid_offset_from_pole_over_R']:.3f}, "
                f"m₁={row.get('m1_azimuthal_fraction', 0.0):.3f}, "
                f"ψ peak @ {row['peak_torsion_colatitude_deg']:.0f}°"
            )

        solar = hyp["solar_analogue"]
        print("\n  Solar analogue (HQIV latitude division):")
        for key, val in solar["hqiv_latitude_division"].items():
            print(f"    {key}: {val}")
        return
    if args.spindown_charm_pulsar_audit:
        ms = compare_spindown_charm_to_pulsar_dataset(millisecond_only=True)
        measured = compare_spindown_charm_to_pulsar_dataset(mass_measured_only=True)
        print("\n=== Spindown/charm dynamics vs pulsar catalog ===")
        print(f"  Millisecond pulsars ({ms['row_count']}):")
        print(f"    mean τ_char/τ_spin_drain = {ms['mean_integration_over_spin_drain']:.4g}")
        print(f"    mean charm_weak/dipole power = {ms['mean_charm_weak_over_dipole']:.4g}")
        print(f"    mean Δm_total = {ms['mean_delta_mass_total_msun']:.4g} M☉")
        print(f"  Mass-measured overlay ({measured['row_count']}):")
        print(f"    mean Δm_total = {measured['mean_delta_mass_total_msun']:.4g} M☉")
        print(f"    max Δm_total = {measured['max_delta_mass_total_msun']:.4g} M☉")
        for row in measured.get("showcase_highest_mass_loss", [])[:6]:
            print(
                f"    {row['name']}: M={row['mass_msun']:.2f} M☉, "
                f"τ_char={row['characteristic_age_yr']:.2e} yr, "
                f"Δm={row['delta_mass_total_msun']:.4g} M☉, "
                f"Δr_charm/R={row['delta_r_charm_over_R']:.4g}"
            )
        return
    if args.spindown_charm_audit:
        report = quantify_spindown_charm_retreat_feedback(1.98)
        print("\n=== 1.98 M☉ spindown → charm retreat → B feedback ===")
        skip_nested = {"before", "after"}
        for key, val in report.items():
            if key in skip_nested:
                continue
            if isinstance(val, float):
                print(f"  {key}: {val:.6g}")
            else:
                print(f"  {key}: {val}")
        print("  before:")
        for key, val in report["before"].items():
            print(f"    {key}: {val:.6g}" if isinstance(val, float) else f"    {key}: {val}")
        print("  after:")
        for key, val in report["after"].items():
            print(f"    {key}: {val:.6g}" if isinstance(val, float) else f"    {key}: {val}")
        return
    if args.magnetic_field_gap_audit:
        gap = magnetic_field_dynamics_gap_witness()
        print("\n=== Magnetic field dynamics gap (HQIV vs trad. Hall-MHD / dynamo) ===")
        print(f"  Role: {gap['witness_role']}")
        refs = gap["reference_scales_gauss"]
        print(f"  Witness B_surface: {refs['B_surface_witness_default']:.3e} G")
        print(f"  Magnetar range: {refs['magnetar_typical_range'][0]:.0e}–{refs['magnetar_typical_range'][1]:.0e} G")
        for key, val in gap["log10_gap_surface_B_vs_magnetar"].items():
            print(f"    {key}: {val:.2f} dex")
        fr = gap["incremental_channel_fractions_at_breakup"]
        print("\n  Breakup incremental channel fractions of B_total:")
        for key, val in fr.items():
            print(f"    {key}: {val:.6g}")
        ind = gap["induction_schematic"]
        print(f"\n  Steady B_LT / B_surf: {ind['steady_B_LT_over_B_surface']:.6g}")
        print(f"  Note: {ind['note']}")
        crust = gap["crust_diffusion_sketch"]
        print(
            f"\n  Ohmic decay (literature): {crust['ohmic_decay_time_yr_literature_range'][0]:.0e}–"
            f"{crust['ohmic_decay_time_yr_literature_range'][1]:.0e} yr "
            f"(mid {crust['ohmic_decay_time_yr_literature_mid']:.0e} yr)"
        )
        print("\n  Paper scope:")
        for line in gap["paper_scope_recommendation"]:
            print(f"    • {line}")
        print("\n  Dynamics milestones:")
        for line in gap["dynamics_milestones_before_final_paper"]:
            print(f"    • {line}")
        return
    if args.breakup_b_audit:
        report = quantify_breakup_b_channels(1.98)
        print("\n=== 1.98 M☉ breakup B-channel audit ===")
        for key, val in report.items():
            if isinstance(val, float):
                print(f"  {key}: {val:.6g}")
            else:
                print(f"  {key}: {val}")
        return
    data = compact_object_witness()
    print_report(data)
    if args.json:
        out = _ROOT / "data" / "compact_object_witnesses.json"
        out.write_text(json.dumps(data, indent=2) + "\n")
        print(f"\nWrote {out}")


if __name__ == "__main__":
    main()

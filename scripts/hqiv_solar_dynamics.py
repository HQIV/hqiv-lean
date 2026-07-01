#!/usr/bin/env python3
"""
HQIV solar dynamics readout — flux tubes, cycle oscillator, sunspot pins.

Lean mirrors:
  • Hqiv.Physics.SolarDynamics
  • Hqiv.Physics.CoronalLongitudinalStress
  • Hqiv.Physics.CoronalHeatingComparisonWitness
  • Hqiv.Physics.FluxTubeStressDivergenceBridge
  • Hqiv.Physics.WeakFanoHopfBridge

Composes existing Sun rotation / O-Maxwell helpers (no PDG mass injection):
  • hqiv_orbital_flyby_omaxwell (SUN, phi_of_shell, OMEGA_SUN)
  • hqiv_compact_object_mass (longitudinal stress, latitude torsion)
  • hqiv_weak_fano_hopf_bridge (Hopf / phase-lift shapes)

Run:
  PYTHONPATH=scripts python3 scripts/hqiv_solar_dynamics.py
  PYTHONPATH=scripts python3 scripts/hqiv_solar_dynamics.py --json data/solar_dynamics_readout.json
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import asdict, dataclass
from datetime import date, datetime, timezone
from pathlib import Path
from typing import Any

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(_ROOT / "scripts"))

import hqiv_compact_object_mass as com
import hqiv_lean_physics_primitives as lean
import hqiv_nuclear_outside_temperature_dynamics as notd
import hqiv_orbital_flyby_omaxwell as orb
import hqiv_weak_fano_hopf_bridge as wfh
import hqiv_whim_filament as whim

ALPHA = lean.ALPHA
GAMMA = lean.GAMMA
REFERENCE_M = lean.REFERENCE_M
M_SUN_KG = com.M_SUN_KG
G_NEWTON = com.G_NEWTON
C_LIGHT = com.C_LIGHT

# Default solar-atmosphere shell anchors (explicit inputs — not derived in Lean).
DEFAULT_M_PHOTO = 0
DEFAULT_M_CORONA = 8
DEFAULT_HOPF_WINDING = 1
DEFAULT_DISCHARGE_THRESHOLD = float(orb.phi_of_shell(REFERENCE_M))  # lock-in φ anchor

# WHIM / galactic outside-curvature defaults (hqiv_whim_filament / notd).
DEFAULT_M_ISM = whim.M_ISM_DEFAULT
DEFAULT_M_WHIM = whim.M_WHIM_DEFAULT

# Jupiter orbital period — dominant planetary magnetic beat carrier (~11.86 yr).
JUPITER_ORBITAL_PERIOD_YEARS = 11.862
SATURN_ORBITAL_PERIOD_YEARS = 29.457

# Dimensionless dipole-coupling witnesses (relative weights, not fitted B-fields).
PLANETARY_DIPOLE_WITNESSES = {
    "jupiter": 3.0,
    "saturn": 1.2,
}

LEAN_MODULES = [
    "Hqiv.Physics.SolarDynamics",
    "Hqiv.Physics.CoronalLongitudinalStress",
    "Hqiv.Physics.CoronalHeatingComparisonWitness",
    "Hqiv.Physics.FluxTubeStressDivergenceBridge",
    "Hqiv.Physics.CoronalEstarSIAnchorWitness",
    "Hqiv.Physics.StellarPhiShellProfile",
    "Hqiv.Physics.LongitudinalStressActionDivergenceBridge",
    "Hqiv.Physics.OMaxwellLongitudinalMomentumBridge",
    "Hqiv.Physics.CoronalHeatedPlasmaBackReaction",
    "Hqiv.Physics.PspHcsReconnectionWitness",
    "Hqiv.Physics.WeakFanoHopfBridge",
    "Hqiv.Physics.NuclearOutsideTemperatureDynamics",
    "Hqiv.Geometry.AuxiliaryField",
    "Hqiv.Geometry.OctonionicLightCone",
]


def phi_of_shell(m: int) -> float:
    return orb.phi_of_shell(m)


def phi_jump(m_photo: int, m_corona: int) -> float:
    """Lean `solarPhiJump` / `coronalPhiJump_closed_form`: Δφ = 2(m_cor − m_ph)."""
    if m_corona < m_photo:
        raise ValueError("m_corona must be ≥ m_photo")
    return 2.0 * float(m_corona - m_photo)


def hqiv_axial_field(
    j_parallel: float,
    sigma: float,
    dphi_ds: float,
    *,
    e_star: float = 1.0,
    coupling_log: float | None = None,
    phi_readout: float | None = None,
) -> dict[str, float]:
    """
    Effective axial field E_eff = J/σ + E_* (α/4π) Λ_s ∂_s φ.

    Lean: `solarEffectiveAxialField`, `coronalLongitudinalHQIVField_alpha_3_5`.
    """
    lam = coupling_log if coupling_log is not None else com.coupling_log_phi(phi_readout or 1.0)
    e_hqiv = e_star * (ALPHA / (4.0 * math.pi)) * lam * dphi_ds
    e_ohm = j_parallel / sigma if sigma > 0.0 else 0.0
    e_eff = e_ohm + e_hqiv
    e_hqiv_alpha = e_star * (3.0 / (20.0 * math.pi)) * lam * dphi_ds
    return {
        "E_ohm": e_ohm,
        "E_HQIV": e_hqiv,
        "E_HQIV_alpha_3_5": e_hqiv_alpha,
        "E_eff": e_eff,
        "Lambda_s": lam,
    }


def heating_flux_boundary(
    nq: float,
    v_parallel: float,
    phi_photo: float,
    phi_corona: float,
    *,
    e_star: float = 1.0,
    coupling_log: float = 1.0,
) -> float:
    """Lean `coronalHeatingFluxBoundary` / `hqivBoundaryHeatingFluxDensity` with α = 3/5 inlined."""
    delta_phi = phi_corona - phi_photo
    return nq * v_parallel * e_star * (3.0 / (20.0 * math.pi)) * coupling_log * delta_phi


def alfven_wave_heating_flux_density(rho: float, v_alfven: float, damping_fraction: float) -> float:
    """Lean `alfvenWaveHeatingFluxDensity`: F_A = f_damp · ρ · v_A³."""
    return damping_fraction * rho * v_alfven**3


def nanoflare_heating_flux_density(event_energy: float, event_rate: float, cross_section: float) -> float:
    """Lean `nanoflareHeatingFluxDensity`: F_N = (E_event · rate) / area."""
    if cross_section == 0.0:
        return 0.0
    return event_energy * event_rate / cross_section


def wave_heating_flux_with_length(
    flux_ref: float,
    loop_length: float,
    length_ref: float,
    length_exponent: float,
) -> float:
    """Lean `waveHeatingFluxWithLength`: F(L) = F_ref · (L / L_ref)^α."""
    if length_ref == 0.0:
        return 0.0
    return flux_ref * (loop_length / length_ref) ** length_exponent


def hqiv_to_alfven_flux_ratio(hqiv_flux: float, alfven_flux: float) -> float:
    """Lean `hqivToAlfvenFluxRatio`."""
    if alfven_flux == 0.0:
        return 0.0
    return hqiv_flux / alfven_flux


def hqiv_to_nanoflare_flux_ratio(hqiv_flux: float, nanoflare_flux: float) -> float:
    """Lean `hqivToNanoflareFluxRatio`."""
    if nanoflare_flux == 0.0:
        return 0.0
    return hqiv_flux / nanoflare_flux


def coronal_heating_flux_denominator(
    nq: float,
    v_parallel: float,
    phi_photo: float,
    phi_corona: float,
    *,
    coupling_log: float = 1.0,
) -> float:
    """Lean `coronalHeatingFluxDenominator`: nq v_∥ (3/20π) Λ_s Δφ."""
    return nq * v_parallel * (3.0 / (20.0 * math.pi)) * coupling_log * (phi_corona - phi_photo)


def estar_for_target_heating_flux(
    target_flux: float,
    nq: float,
    v_parallel: float,
    phi_photo: float,
    phi_corona: float,
    *,
    coupling_log: float = 1.0,
) -> float:
    """Lean `estarForTargetHeatingFlux`: E_∗ = (Q/A) / denom when denom ≠ 0."""
    denom = coronal_heating_flux_denominator(
        nq, v_parallel, phi_photo, phi_corona, coupling_log=coupling_log
    )
    if denom == 0.0:
        return 0.0
    return target_flux / denom


def solar_shear_gate(sin_colatitude: float) -> float:
    """Lean `solarShearGate`: sin²θ |cosθ|."""
    return sin_colatitude * sin_colatitude * abs(sin_colatitude)


def solar_active_belt_witness() -> dict[str, float]:
    """
    Heliographic active-belt latitudes from compact-object witness slots (γ = 2/5).

    ``papers/compact_object_witness`` maps crust Coriolis/shear belts to solar
    active regions. Two algebraic candidates (not fitted to sunspot catalogs):

      • monogamy latitude:  90° − arccos(γ)  ≈ 23.6°
      • Rindler-half latitude: arcsin(√(γ/2)) ≈ 26.6°

    Legacy observational placeholder 30° is retained for comparison only.
    """
    monogamy_lat = 90.0 - math.degrees(math.acos(GAMMA))
    rindler_half_lat = math.degrees(math.asin(math.sqrt(GAMMA / 2.0)))
    return {
        "latitude_monogamy_deg": monogamy_lat,
        "latitude_rindler_half_deg": rindler_half_lat,
        "latitude_legacy_obs_deg": 30.0,
        "gamma": GAMMA,
        "formula_monogamy": "90 - arccos(gamma)",
        "formula_rindler_half": "arcsin(sqrt(gamma/2))",
        "compact_object_witness_ref": "papers/compact_object_witness",
    }


def sin_colatitude_from_heliographic_latitude(latitude_deg: float) -> float:
    """Northern active belt: colatitude from equator = 90° − latitude."""
    return math.sin(math.radians(90.0 - latitude_deg))


def planetary_alignment_sin_from_separation(separation_deg: float) -> float:
    """sin²(alignment) witness with alignment = half the J–S ecliptic separation."""
    half_rad = math.radians(separation_deg / 2.0)
    return math.sin(half_rad)


def gnevyshev_ohl_phase_factor(cycle_number: int, same_side: bool, *, at_maximum: bool) -> float:
    """
    Parity-dressed planetary gate: odd cycles favour J+S same side at maximum;
    even cycles favour opposite side at maximum (Gnevyshev–Ohl readout).
    """
    odd = cycle_number % 2 == 1
    want_same = odd if at_maximum else not odd
    return 1.0 + GAMMA if same_side == want_same else 1.0 - GAMMA


def solar_extremum_activity_score(
    *,
    cycle_number: int,
    at_maximum: bool,
    year: int,
    month: int,
    active_belt_latitude_deg: float,
    m_photo: int = DEFAULT_M_PHOTO,
    m_corona: int = DEFAULT_M_CORONA,
    hopf_winding: int = DEFAULT_HOPF_WINDING,
    lon_jupiter_deg: float,
    lon_saturn_deg: float,
    jupiter_year_fraction: float | None = None,
) -> dict[str, float]:
    """
    Target-model activity score at a SILSO extremum date.

    Combines shear gate at the active belt, environment phase, planetary coupling
    with measured J–S alignment, and Gnevyshev–Ohl parity dressing.
    """
    sep = abs((lon_jupiter_deg - lon_saturn_deg + 180.0) % 360.0 - 180.0)
    align_sin = planetary_alignment_sin_from_separation(sep)
    same_side = math.cos(math.radians(lon_jupiter_deg)) * math.cos(
        math.radians(lon_saturn_deg)
    ) + math.sin(math.radians(lon_jupiter_deg)) * math.sin(math.radians(lon_saturn_deg)) > 0.0
    go_factor = gnevyshev_ohl_phase_factor(cycle_number, same_side, at_maximum=at_maximum)
    yf = (
        jupiter_year_fraction
        if jupiter_year_fraction is not None
        else (float((date(year, month, 15).toordinal() - date(2000, 1, 1).toordinal()) / 365.25)
              / JUPITER_ORBITAL_PERIOD_YEARS
              % 1.0)
    )
    sin_colat = sin_colatitude_from_heliographic_latitude(active_belt_latitude_deg)
    shear = solar_shear_gate(sin_colat)
    planetary = solar_planetary_magnetic_coupling(year_fraction=yf, alignment_sin=align_sin)
    env = solar_cycle_environment_phase(
        m_photo,
        m_corona,
        hopf_winding,
        year_fraction=yf,
        alignment_sin=align_sin,
    )
    # Target readout: parity (G–O) × Jupiter beat × shear × alignment aperture.
    align_aperture = 1.0 + GAMMA * align_sin * align_sin
    activity = shear * go_factor * planetary["jupiter_harmonic"] * align_aperture
    return {
        "active_belt_latitude_deg": active_belt_latitude_deg,
        "sin_colatitude": sin_colat,
        "shear_gate": shear,
        "jupiter_saturn_separation_deg": sep,
        "alignment_sin": align_sin,
        "gnevyshev_ohl_same_side": 1.0 if same_side else 0.0,
        "gnevyshev_ohl_phase_factor": go_factor,
        "jupiter_harmonic": planetary["jupiter_harmonic"],
        "planetary_multiplier": planetary["combined_multiplier"],
        "environment_phase": env,
        "activity_score": activity,
    }


def solar_cycle_memory_gate(
    prev_max_sunspot: float | None,
    *,
    reference_amplitude: float = 180.0,
) -> float:
    """
    Prior-cycle amplitude memory on the discharge threshold (readout_model).

    A weak preceding maximum leaves toroidal/poloidal flux deficit; the next
    cycle discharges from a lower effective threshold (rebound witness). Uses
    γ deficit slot: ``1 + γ·max(0, 1 − S_{n−1}/S_ref)``.
    """
    if prev_max_sunspot is None or prev_max_sunspot <= 0.0:
        return 1.0
    deficit = max(0.0, 1.0 - prev_max_sunspot / max(reference_amplitude, 1.0))
    return 1.0 + GAMMA * deficit


def solar_cycle_rise_rate_years(
    min_year: int,
    min_month: int,
    max_year: int,
    max_month: int,
) -> float:
    """Rise time from smoothed minimum month to maximum month."""
    t_min = min_year + (min_month - 0.5) / 12.0
    t_max = max_year + (max_month - 0.5) / 12.0
    return max(t_max - t_min, 0.1)


def solar_cycle_period_years(
    min_year: int,
    min_month: int,
    next_min_year: int,
    next_min_month: int,
) -> float | None:
    if next_min_year <= 0:
        return None
    t0 = min_year + (min_month - 0.5) / 12.0
    t1 = next_min_year + (next_min_month - 0.5) / 12.0
    return max(t1 - t0, 0.1)


def solar_magnetic_change_rate(
    sn_now: float,
    sn_prev: float,
    dt_years: float,
    *,
    reference_amplitude: float = 180.0,
) -> float:
    """Dimensionless |ΔS|/Δt slot driving induction (sunspot proxy for dB/dt)."""
    return abs(sn_now - sn_prev) / max(dt_years, 1.0e-6) / max(reference_amplitude, 1.0)


def solar_induction_current_readout(
    dB_dt_tesla_per_s: float,
    *,
    j_parallel: float = 1.0e3,
    sigma: float = 1.0e7,
    dphi_ds: float | None = None,
    m_corona: int = DEFAULT_M_CORONA,
    e_star: float = 1.0,
) -> dict[str, float]:
    """
    Induced axial current from magnetic cycle change (readout_model).

    Books Faraday drive as an effective axial field increment on the coronal flux
    tube: ``E_ind ~ (R/c) dB/dt`` (order-of-magnitude), then ``J = σ E_eff`` with
    the HQIV longitudinal correction from ``CoronalLongitudinalStress``.

    Lean analogue: ``∂B/∂t ~ η a_LT/R`` (`CompactObjectMhdEquivalenceScaffold`);
    odd-in-current reversal channel (`CoronalLongitudinalStress` §7).
    """
    r_sun = com.radius_uniform_density(M_SUN_KG, com.RHO_NUCLEAR_KG_M3)
    e_ind = (r_sun / C_LIGHT) * dB_dt_tesla_per_s
    grad = dphi_ds if dphi_ds is not None else phi_jump(DEFAULT_M_PHOTO, m_corona)
    fields = hqiv_axial_field(
        j_parallel,
        sigma,
        grad,
        e_star=e_star,
        phi_readout=phi_of_shell(m_corona),
    )
    e_eff = fields["E_eff"] + e_ind
    j_induced = sigma * e_ind
    j_total = j_parallel + j_induced
    return {
        "dB_dt_tesla_per_s": dB_dt_tesla_per_s,
        "E_induced": e_ind,
        "E_eff_baseline": fields["E_eff"],
        "E_eff_with_induction": e_eff,
        "J_parallel_baseline": j_parallel,
        "J_induced": j_induced,
        "J_total": j_total,
        "induced_fraction": abs(j_induced) / max(abs(j_total), 1.0e-30),
    }


def solar_induction_from_sunspot_change(
    sn_now: float,
    sn_prev: float,
    dt_years: float,
    *,
    b_surface_tesla: float = 1.0e-4,
    reference_amplitude: float = 180.0,
    **kwargs: Any,
) -> dict[str, float]:
    """
    Proxy ``dB/dt`` from sunspot-index change, then full induction readout.

    ``dB/dt ~ B_surf · (ΔS/S_ref) / Δt`` — diagnostic only, not a theorem.
    """
    rate = solar_magnetic_change_rate(sn_now, sn_prev, dt_years, reference_amplitude=reference_amplitude)
    d_b_dt = b_surface_tesla * rate
    out = solar_induction_current_readout(d_b_dt, **kwargs)
    out["sunspot_change_rate"] = rate
    return out


def solar_extremum_activity_score_with_memory(
    *,
    prev_max_sunspot: float | None,
    prev_rise_years: float | None,
    **kwargs: Any,
) -> dict[str, float]:
    """
    Activity score dressed by prior-cycle memory and rise-time gate.

    Long rise on cycle n−1 slightly suppresses amplitude witness on cycle n
    (empirical SILSO trend: corr ≈ −0.5 over cycles 12–25).
    """
    base = solar_extremum_activity_score(**kwargs)
    mem = solar_cycle_memory_gate(prev_max_sunspot)
    rise_gate = 1.0
    if prev_rise_years is not None:
        # centre ≈ 4 yr rise; each extra year costs γ/2 in gate
        rise_gate = max(0.5, 1.0 - GAMMA * max(0.0, prev_rise_years - 4.0) / 2.0)
    activity = base["activity_score"] * mem * rise_gate
    return {
        **base,
        "prior_cycle_memory_gate": mem,
        "prior_rise_time_gate": rise_gate,
        "activity_score_with_memory": activity,
    }


def solar_cycle_phase(m_photo: int, m_corona: int, hopf_winding: int) -> float:
    """Lean `solarCyclePhase`."""
    return (
        phi_jump(m_photo, m_corona)
        * wfh.hopf_fibration_shape(hopf_winding)
        * wfh.phase_lift_shape(m_corona)
    )


def solar_rotation_current_gate(m_photo: int, m_corona: int, sin_colatitude: float) -> float:
    """Lean `solarRotationCurrentGate`."""
    return phi_jump(m_photo, m_corona) * solar_shear_gate(sin_colatitude) * wfh.phase_lift_shape(m_corona)


def solar_galactic_curvature_modulator(
    v_c_m_s: float = notd.GALACTIC_VC_M_S,
) -> float:
    """Lean `solarGalacticCurvatureModulator` / `outsideGravityGeffModulator`."""
    eps_gal = notd.galactic_circular_phi_epsilon(v_c_m_s)
    return notd.outside_gravity_geff_modulator(eps_gal)


def solar_whim_boundary_shape(m_ism: int = DEFAULT_M_ISM, m_whim: int = DEFAULT_M_WHIM) -> float:
    """Lean `solarWhimBoundaryShape`: max(0, Δφ) / φ(m_ism)."""
    delta = max(0.0, phi_jump(m_ism, m_whim))
    return delta / max(phi_of_shell(m_ism), 1.0e-30)


def solar_whim_galactic_outside_gate(
    *,
    m_ism: int = DEFAULT_M_ISM,
    m_whim: int = DEFAULT_M_WHIM,
    v_c_m_s: float = notd.GALACTIC_VC_M_S,
) -> dict[str, float]:
    """
    Combined galactic-core outside curvature + WHIM filament boundary gate.

    Books the Milky-Way circular-support ε_gal through G_eff(1+ε)^α and the
    WHIM ISM→WHIM shell jump as a boundary φ readout (hqiv_whim_filament).
    """
    eps_gal = notd.galactic_circular_phi_epsilon(v_c_m_s)
    geff = solar_galactic_curvature_modulator(v_c_m_s)
    whim_shape = solar_whim_boundary_shape(m_ism, m_whim)
    combined = geff * (1.0 + GAMMA * whim_shape)
    return {
        "epsilon_galactic": eps_gal,
        "geff_modulator": geff,
        "whim_delta_phi": whim.whim_shell_delta_phi(m_ism, m_whim),
        "whim_boundary_shape": whim_shape,
        "combined_outside_gate": combined,
    }


def solar_planetary_magnetic_coupling(
    *,
    year_fraction: float = 0.0,
    alignment_sin: float = 0.5,
    dipole_witnesses: dict[str, float] | None = None,
) -> dict[str, float]:
    """
    Lean `solarPlanetaryMagneticCoupling` envelope over Jupiter/Saturn beats.

    Jupiter's ~11.86 yr orbit is the dominant long-period magnetic beat carrier;
    Saturn supplies the secondary harmonic. ``year_fraction`` is heliographic
    phase in Jupiter-orbit units (0–1).
    """
    weights = dipole_witnesses or PLANETARY_DIPOLE_WITNESSES
    jupiter_harmonic = 1.0 + GAMMA * math.cos(2.0 * math.pi * year_fraction)
    saturn_phase = year_fraction * JUPITER_ORBITAL_PERIOD_YEARS / SATURN_ORBITAL_PERIOD_YEARS
    saturn_harmonic = 1.0 + (GAMMA / 2.0) * math.cos(2.0 * math.pi * saturn_phase)
    dipole_gate = weights.get("jupiter", 3.0) * jupiter_harmonic + weights.get("saturn", 1.2) * saturn_harmonic
    coupling = GAMMA * alignment_sin * alignment_sin * math.log1p(max(dipole_gate, 0.0))
    return {
        "jupiter_harmonic": jupiter_harmonic,
        "saturn_harmonic": saturn_harmonic,
        "dipole_gate": dipole_gate,
        "planetary_magnetic_coupling": coupling,
        "combined_multiplier": 1.0 + coupling,
    }


def solar_cycle_environment_phase(
    m_photo: int,
    m_corona: int,
    hopf_winding: int,
    *,
    v_c_m_s: float = notd.GALACTIC_VC_M_S,
    dipole_ratio: float = PLANETARY_DIPOLE_WITNESSES["jupiter"],
    alignment_sin: float = 0.5,
    year_fraction: float = 0.0,
) -> float:
    """Lean `solarCycleEnvironmentPhase` (Python readout)."""
    interior = solar_cycle_phase(m_photo, m_corona, hopf_winding)
    geff = solar_galactic_curvature_modulator(v_c_m_s)
    planetary = solar_planetary_magnetic_coupling(
        year_fraction=year_fraction,
        alignment_sin=alignment_sin,
    )
    dipole_effective = dipole_ratio * planetary["jupiter_harmonic"]
    coupling = GAMMA * max(dipole_effective, 0.0) * alignment_sin * alignment_sin
    return interior * geff * (1.0 + coupling)


def sunspot_pin_stress(
    gate: float,
    threshold: float,
    nq: float,
    v_parallel: float,
    *,
    e_star: float = 1.0,
    coupling_log: float = 1.0,
) -> float:
    """Lean `sunspotPinStress`."""
    if threshold < gate:
        return nq * v_parallel * e_star * (3.0 / (20.0 * math.pi)) * coupling_log * gate
    return 0.0


@dataclass(frozen=True)
class SolarFluxTubeRow:
    label: str
    m_photo: int
    m_corona: int
    phi_photo: float
    phi_corona: float
    delta_phi: float
    j_parallel: float
    sigma: float
    dphi_ds: float
    nq: float
    v_parallel: float
    e_ohm: float
    e_hqiv: float
    e_eff: float
    force_density: float
    heating_flux_boundary: float
    coupling_log: float


def solar_flux_tube_readout(
    *,
    m_photo: int = DEFAULT_M_PHOTO,
    m_corona: int = DEFAULT_M_CORONA,
    j_parallel: float = 1.0e3,
    sigma: float = 1.0e7,
    dphi_ds: float | None = None,
    nq: float = 1.0e20,
    v_parallel: float = 5.0e3,
    e_star: float = 1.0,
    label: str = "photosphere_corona_column",
) -> SolarFluxTubeRow:
    """Flux-tube longitudinal O-Maxwell readout for one shell pair."""
    p_ph = phi_of_shell(m_photo)
    p_cor = phi_of_shell(m_corona)
    dphi = phi_jump(m_photo, m_corona)
    grad = dphi_ds if dphi_ds is not None else dphi
    lam = com.coupling_log_phi(p_cor)
    fields = hqiv_axial_field(j_parallel, sigma, grad, e_star=e_star, coupling_log=lam)
    force = nq * fields["E_eff"]
    flux = heating_flux_boundary(nq, v_parallel, p_ph, p_cor, e_star=e_star, coupling_log=lam)
    return SolarFluxTubeRow(
        label=label,
        m_photo=m_photo,
        m_corona=m_corona,
        phi_photo=p_ph,
        phi_corona=p_cor,
        delta_phi=dphi,
        j_parallel=j_parallel,
        sigma=sigma,
        dphi_ds=grad,
        nq=nq,
        v_parallel=v_parallel,
        e_ohm=fields["E_ohm"],
        e_hqiv=fields["E_HQIV"],
        e_eff=fields["E_eff"],
        force_density=force,
        heating_flux_boundary=flux,
        coupling_log=lam,
    )


@dataclass(frozen=True)
class SolarLatitudeRow:
    colatitude_deg: float
    sin_colatitude: float
    shear_gate: float
    rotation_current_gate: float
    rho_pol: float
    grad_axial_phi_si: float
    a_longitudinal_si: float
    a_grav_si: float
    notes: str


def solar_latitude_scan(
    *,
    m_photo: int = DEFAULT_M_PHOTO,
    m_corona: int = DEFAULT_M_CORONA,
    colatitudes_deg: tuple[float, ...] = (0.0, 15.0, 30.0, 45.0, 60.0, 75.0, 90.0),
) -> list[SolarLatitudeRow]:
    """Latitude belt scan using Sun mass/spin geometry."""
    mass_kg = M_SUN_KG
    r_sph = com.radius_uniform_density(mass_kg, com.RHO_NUCLEAR_KG_M3)
    omega = orb.OMEGA_SUN
    r_eq, r_pol, _, _ = com.oblate_radii_m(r_sph, mass_kg, omega)
    _, _, eps_equator, _ = com.epsilon_surface_at_latitude(
        mass_kg, r_eq, r_pol, omega, math.pi / 2.0
    )
    _, _, eps_pole, _ = com.epsilon_surface_at_latitude(
        mass_kg, r_eq, r_pol, omega, 0.0
    )

    rows: list[SolarLatitudeRow] = []
    for col_deg in colatitudes_deg:
        col_rad = math.radians(col_deg)
        sin_colat = math.sin(col_rad)
        ch = com.torsion_channels_at_latitude(
            mass_kg,
            r_eq,
            r_pol,
            omega,
            col_rad,
            eps_equator=eps_equator,
            eps_pole=eps_pole,
        )
        gate = solar_rotation_current_gate(m_photo, m_corona, sin_colat)
        notes = "pole" if col_deg < 1.0 else ("equator" if col_deg > 89.0 else "active_belt")
        rows.append(
            SolarLatitudeRow(
                colatitude_deg=col_deg,
                sin_colatitude=sin_colat,
                shear_gate=solar_shear_gate(sin_colat),
                rotation_current_gate=gate,
                rho_pol=ch.rho_pol,
                grad_axial_phi_si=ch.grad_axial_phi_si,
                a_longitudinal_si=ch.a_long_linear_si,
                a_grav_si=ch.a_grav_si,
                notes=notes,
            )
        )
    return rows


@dataclass(frozen=True)
class SolarCycleOscillatorRow:
    m_photo: int
    m_corona: int
    hopf_winding: int
    discharge_threshold: float
    cycle_phase: float
    cycle_phase_environment: float
    rotation_period_days: float
    estimated_period_days: float
    estimated_period_years: float
    jupiter_orbital_carrier_years: float
    outside_gate: float
    planetary_multiplier: float
    discharge_active: bool
    claim_status: str


def solar_cycle_oscillator(
    *,
    m_photo: int = DEFAULT_M_PHOTO,
    m_corona: int = DEFAULT_M_CORONA,
    hopf_winding: int = DEFAULT_HOPF_WINDING,
    discharge_threshold: float = DEFAULT_DISCHARGE_THRESHOLD,
    omega_rad_s: float = orb.OMEGA_SUN,
    sin_colatitude: float | None = None,
    active_belt_latitude_deg: float | None = None,
    year_fraction: float = 0.0,
    alignment_sin: float = 0.5,
    m_ism: int = DEFAULT_M_ISM,
    m_whim: int = DEFAULT_M_WHIM,
) -> SolarCycleOscillatorRow:
    """
    Holonomy-discharge cycle readout with galactic WHIM + planetary magnetic dressing.

    Long-period envelope uses Jupiter's orbital year as the planetary magnetic beat
    carrier; galactic outside curvature (ε_gal, WHIM boundary) dresses the threshold.

    Active belt defaults to the Rindler-half latitude ``arcsin(√(γ/2))`` from the
    compact-object witness (≈26.6° heliographic). The monogamy candidate
    ``90° − arccos(γ)`` (≈23.6°) is the alternate witness slot.
    """
    belt = solar_active_belt_witness()
    lat = active_belt_latitude_deg
    if lat is None:
        lat = belt["latitude_rindler_half_deg"]
    if sin_colatitude is None:
        sin_colatitude = sin_colatitude_from_heliographic_latitude(lat)
    phase = solar_cycle_phase(m_photo, m_corona, hopf_winding)
    phase_env = solar_cycle_environment_phase(
        m_photo, m_corona, hopf_winding, year_fraction=year_fraction, alignment_sin=alignment_sin
    )
    outside = solar_whim_galactic_outside_gate(m_ism=m_ism, m_whim=m_whim)
    planetary = solar_planetary_magnetic_coupling(
        year_fraction=year_fraction,
        alignment_sin=alignment_sin,
    )
    shear = solar_shear_gate(sin_colatitude)
    phase_lift = wfh.phase_lift_shape(m_corona)
    threshold_eff = discharge_threshold * outside["combined_outside_gate"]
    rot_period_s = 2.0 * math.pi / max(omega_rad_s, 1.0e-12)
    rot_period_days = rot_period_s / 86_400.0
    denom = max(phase * shear * phase_lift * planetary["combined_multiplier"], 1.0e-30)
    est_period_years = JUPITER_ORBITAL_PERIOD_YEARS * threshold_eff / denom
    est_period_days = est_period_years * 365.25
    return SolarCycleOscillatorRow(
        m_photo=m_photo,
        m_corona=m_corona,
        hopf_winding=hopf_winding,
        discharge_threshold=discharge_threshold,
        cycle_phase=phase,
        cycle_phase_environment=phase_env,
        rotation_period_days=rot_period_days,
        estimated_period_days=est_period_days,
        estimated_period_years=est_period_years,
        jupiter_orbital_carrier_years=JUPITER_ORBITAL_PERIOD_YEARS,
        outside_gate=outside["combined_outside_gate"],
        planetary_multiplier=planetary["combined_multiplier"],
        discharge_active=threshold_eff < phase_env,
        claim_status="readout_model",
    )


@dataclass(frozen=True)
class SunspotPinRow:
    gate: float
    threshold: float
    pin_stress: float
    pin_active: bool
    convection_suppression_proxy: float


def sunspot_pin_readout(
    *,
    gate: float,
    threshold: float,
    nq: float = 1.0e20,
    v_parallel: float = 5.0e3,
    e_star: float = 1.0,
    coupling_log: float = 1.0,
) -> SunspotPinRow:
    """Localized sunspot pin channel (Lean `sunspotPinStress` bookkeeping)."""
    stress = sunspot_pin_stress(gate, threshold, nq, v_parallel, e_star=e_star, coupling_log=coupling_log)
    active = threshold < gate
    suppression = gate / (gate + threshold) if threshold > 0.0 and gate > 0.0 else 0.0
    return SunspotPinRow(
        gate=gate,
        threshold=threshold,
        pin_stress=stress,
        pin_active=active,
        convection_suppression_proxy=suppression if active else 0.0,
    )


@dataclass(frozen=True)
class CoronalHeatingComparisonRow:
    """Lean `CoronalHeatingComparisonWitness` readout row (comparison layer only)."""

    nq: float
    e_star: float
    coupling_log: float
    v_parallel: float
    phi_photo: float
    phi_corona: float
    rho: float
    v_alfven: float
    damping_fraction: float
    event_energy: float
    event_rate: float
    cross_section: float
    loop_length_1: float
    loop_length_2: float
    length_ref: float
    length_exponent: float
    hqiv_flux: float
    alfven_flux: float
    nanoflare_flux: float
    hqiv_to_alfven: float
    hqiv_to_nanoflare: float
    hqiv_flux_loop_1: float
    hqiv_flux_loop_2: float
    wave_flux_loop_1: float
    wave_flux_loop_2: float
    hqiv_length_independent: bool
    wave_length_fluxes_differ: bool
    claim_status: str


def coronal_heating_comparison_readout(
    *,
    m_photo: int = DEFAULT_M_PHOTO,
    m_corona: int = DEFAULT_M_CORONA,
    nq: float = 1.0e20,
    v_parallel: float = 5.0e3,
    e_star: float = 1.0,
    rho: float = 1.0e-12,
    v_alfven: float = 1.0e6,
    damping_fraction: float = 0.1,
    event_energy: float = 1.0e24,
    event_rate: float = 1.0e-3,
    cross_section: float = 1.0e6,
    loop_length_1: float = 1.0e8,
    loop_length_2: float = 2.0e8,
    length_ref: float = 1.0e8,
    length_exponent: float = 1.0,
    wave_flux_ref: float | None = None,
) -> CoronalHeatingComparisonRow:
    """
    HQIV vs Alfvén / nanoflare schematic comparison (Lean discharge via definitional equalities).

    Plasma and wave/nanoflare slots are explicit readout inputs — not derived from HQIV shells.
    """
    p_ph = phi_of_shell(m_photo)
    p_cor = phi_of_shell(m_corona)
    lam = com.coupling_log_phi(p_cor)
    hqiv = heating_flux_boundary(nq, v_parallel, p_ph, p_cor, e_star=e_star, coupling_log=lam)
    alfven = alfven_wave_heating_flux_density(rho, v_alfven, damping_fraction)
    nanoflare = nanoflare_heating_flux_density(event_energy, event_rate, cross_section)
    wave_ref = alfven if wave_flux_ref is None else wave_flux_ref
    hqiv_l1 = hqiv
    hqiv_l2 = hqiv
    wave_l1 = wave_heating_flux_with_length(wave_ref, loop_length_1, length_ref, length_exponent)
    wave_l2 = wave_heating_flux_with_length(wave_ref, loop_length_2, length_ref, length_exponent)
    lengths_distinct = loop_length_1 != loop_length_2
    return CoronalHeatingComparisonRow(
        nq=nq,
        e_star=e_star,
        coupling_log=lam,
        v_parallel=v_parallel,
        phi_photo=p_ph,
        phi_corona=p_cor,
        rho=rho,
        v_alfven=v_alfven,
        damping_fraction=damping_fraction,
        event_energy=event_energy,
        event_rate=event_rate,
        cross_section=cross_section,
        loop_length_1=loop_length_1,
        loop_length_2=loop_length_2,
        length_ref=length_ref,
        length_exponent=length_exponent,
        hqiv_flux=hqiv,
        alfven_flux=alfven,
        nanoflare_flux=nanoflare,
        hqiv_to_alfven=hqiv_to_alfven_flux_ratio(hqiv, alfven),
        hqiv_to_nanoflare=hqiv_to_nanoflare_flux_ratio(hqiv, nanoflare),
        hqiv_flux_loop_1=hqiv_l1,
        hqiv_flux_loop_2=hqiv_l2,
        wave_flux_loop_1=wave_l1,
        wave_flux_loop_2=wave_l2,
        hqiv_length_independent=math.isclose(hqiv_l1, hqiv_l2),
        wave_length_fluxes_differ=lengths_distinct and not math.isclose(wave_l1, wave_l2),
        claim_status="comparison_witness",
    )


def build_readout_payload(
    *,
    m_photo: int = DEFAULT_M_PHOTO,
    m_corona: int = DEFAULT_M_CORONA,
    hopf_winding: int = DEFAULT_HOPF_WINDING,
    discharge_threshold: float = DEFAULT_DISCHARGE_THRESHOLD,
) -> dict[str, Any]:
    flux = solar_flux_tube_readout(m_photo=m_photo, m_corona=m_corona)
    lat_rows = solar_latitude_scan(m_photo=m_photo, m_corona=m_corona)
    cycle = solar_cycle_oscillator(
        m_photo=m_photo,
        m_corona=m_corona,
        hopf_winding=hopf_winding,
        discharge_threshold=discharge_threshold,
    )
    outside = solar_whim_galactic_outside_gate()
    planetary = solar_planetary_magnetic_coupling()
    belt = solar_active_belt_witness()
    peak_gate = max((r.rotation_current_gate for r in lat_rows), default=0.0)
    pin = sunspot_pin_readout(gate=peak_gate, threshold=discharge_threshold * 0.5)
    heating_cmp = coronal_heating_comparison_readout(m_photo=m_photo, m_corona=m_corona)

    return {
        "source": "scripts/hqiv_solar_dynamics.py",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "lean_modules": LEAN_MODULES,
        "constants": {
            "alpha": ALPHA,
            "gamma": GAMMA,
            "referenceM": REFERENCE_M,
            "phi_of_shell_referenceM": phi_of_shell(REFERENCE_M),
            "jupiter_orbital_period_years": JUPITER_ORBITAL_PERIOD_YEARS,
            "active_belt_witness": belt,
        },
        "inputs": {
            "m_photo": m_photo,
            "m_corona": m_corona,
            "m_ism": DEFAULT_M_ISM,
            "m_whim": DEFAULT_M_WHIM,
            "hopf_winding": hopf_winding,
            "discharge_threshold": discharge_threshold,
            "omega_sun_rad_s": orb.OMEGA_SUN,
            "rotation_period_days": orb.SOLAR_ROTATION_PERIOD_DAYS,
            "galactic_v_c_m_s": notd.GALACTIC_VC_M_S,
        },
        "proved_algebra": {
            "description": "Lean-certified identities (zero sorry)",
            "delta_phi_formula": "2 * (m_corona - m_photo)",
            "E_HQIV_formula": "E_star * (alpha/4pi) * Lambda_s * dphi_ds",
            "E_eff_formula": "J/sigma + E_HQIV",
            "heating_flux_boundary": "nq * v_parallel * E_star * (3/20pi) * Lambda_s * delta_phi",
            "alfven_flux_proxy": "f_damp * rho * v_A^3",
            "nanoflare_flux_proxy": "E_event * rate / cross_section",
            "wave_flux_length_scaling": "F_ref * (L / L_ref)^alpha",
            "hqiv_length_independent": "Q/A fixed at footpoints; bulk L does not enter boundary form",
            "galactic_modulator": "outsideGravityGeffModulator(epsilon_gal)",
            "whim_boundary_shape": "max(0, delta_phi) / phi(m_ism)",
            "planetary_coupling": "gamma * dipole_ratio * sin^2(alignment)",
            "environment_phase": "interior_phase * geff * (1 + planetary_coupling)",
        },
        "readout_model": {
            "description": "Python phenomenology — Jupiter beat + galactic WHIM outside curvature",
            "outside_curvature_whim": outside,
            "planetary_magnetic_coupling": planetary,
            "cycle_oscillator": asdict(cycle),
            "sunspot_pin": asdict(pin),
        },
        "flux_tube": asdict(flux),
        "heating_comparison": asdict(heating_cmp),
        "latitude_scan": [asdict(r) for r in lat_rows],
        "caveats": [
            "Photosphere/corona shell indices are explicit inputs, not derived from horizon shells.",
            "Estimated cycle period uses Jupiter orbital carrier + galactic WHIM gate (readout_model).",
            "Planetary magnetic coupling uses dimensionless dipole witnesses, not fitted B-tables.",
            "Galactic ε_gal = (v_c/c)^2 books outside curvature from the Milky-Way disk support.",
            "Alfvén/nanoflare slots in heating_comparison are schematic proxies, not quadrature superposition.",
            "No full MHD dynamo PDE or plasma opacity theory is included.",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="HQIV solar dynamics readout")
    parser.add_argument("--json", type=str, default="", help="Write JSON witness bundle")
    parser.add_argument("--m-photo", type=int, default=DEFAULT_M_PHOTO)
    parser.add_argument("--m-corona", type=int, default=DEFAULT_M_CORONA)
    parser.add_argument("--hopf-winding", type=int, default=DEFAULT_HOPF_WINDING)
    parser.add_argument("--threshold", type=float, default=DEFAULT_DISCHARGE_THRESHOLD)
    args = parser.parse_args()

    payload = build_readout_payload(
        m_photo=args.m_photo,
        m_corona=args.m_corona,
        hopf_winding=args.hopf_winding,
        discharge_threshold=args.threshold,
    )

    if args.json:
        out = Path(args.json)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        print(f"Wrote {out}")
    else:
        print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()

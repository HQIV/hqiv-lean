#!/usr/bin/env python3
"""Z-pinch / filament compression readout: coronal lab → WHIM spine → localized intensity.

Heated return currents (``J_hot`` from coronal back-reaction) and WHIM filament axial
currents generate azimuthal fields and magnetic pinch pressure. Flux conservation
compresses the column so **local** density and heating exceed the bulk by
``(R_bulk / r_pinch)²``.

This is the equation layer for the programme: WHIM filaments pinch along their
spines, steepening boundary ``φ`` and heating at focal lines — a **hypothesis**
slot for seeding collapsed objects and galaxies (not derived here).

Lean: ``Hqiv.Physics.PlasmaZPinchFilament``
"""

from __future__ import annotations

import math
from dataclasses import asdict, dataclass

import hqiv_bbn_abundances as bbn
import hqiv_lean_physics_primitives as lean
import hqiv_nuclear_outside_temperature_dynamics as notd

MU0 = 4.0e-7 * math.pi  # H/m
K_B = 1.380649e-23  # J/K
H_PLANCK_SI = 6.62607015e-34
HBAR_SI = H_PLANCK_SI / (2.0 * math.pi)
C_LIGHT_SI = 299792458.0
G_NEWTON_SI = 6.67430e-11
ZETA_3 = 1.2020569031595942
SECONDS_PER_GYR = 365.25 * 24.0 * 3600.0 * 1.0e9

# HQIV-derived coefficients (Lean: alpha, gamma_HQIV) — not tunable witnesses
COOLING_ALPHA = lean.ALPHA
PINCH_HEATING_FRACTION = lean.GAMMA

CORONAL_FILAMENT_N_M3 = 1.0e20
CORONAL_FILAMENT_T_K = 1.0e6


def planck_temperature_k() -> float:
    """T_Pl from CODATA SI (bridge only; HQIV ladder uses T_Pl_MeV export)."""
    return math.sqrt(HBAR_SI * C_LIGHT_SI**5 / G_NEWTON_SI) / K_B


def planck_time_s() -> float:
    return math.sqrt(HBAR_SI * G_NEWTON_SI / C_LIGHT_SI**5)


def phi_of_shell(m: int) -> float:
    """Lean ``phi_of_shell_closed_form``: φ(m) = 2(m+1)."""
    return 2.0 * float(m + 1)


def wall_clock_age_homogeneous(phi: float, t_coord: float) -> float:
    """Lean ``wallClockAgeHomogeneous``: τ = t + φ t²/2."""
    return t_coord + phi * t_coord**2 / 2.0


def photon_number_density_m3(T_K: float) -> float:
    """Blackbody photon number density at ``T`` (no external tables)."""
    if T_K <= 0.0:
        return 0.0
    return (2.0 * ZETA_3 / math.pi**2) * ((K_B * T_K) / (HBAR_SI * C_LIGHT_SI)) ** 3


@dataclass(frozen=True)
class CosmicFilamentEpoch:
    """CMB / age slot derived from HQIV temperature ladder + lock-in η (no fitted WHIM constants)."""

    T_cmb_K: float
    T_cmb_MeV: float
    m_cmb: float
    xi_cmb: float
    n_gamma_m3: float
    n_baryon_m3: float
    eta: float
    omega_cmb: float
    coordinate_time_nat: float
    age_ratio_wall_over_apparent: float
    age_apparent_s: float
    age_wall_s: float
    note: str


def derived_structural_apparent_age_s(T_cmb_MeV: float) -> float:
    """
    Coordinate age from radiation–shell scaling (structural; compare to UniverseAge.lean paper witnesses).
    """
    t_pl_s = planck_time_s()
    t_ratio = bbn.T_PL_MEV / max(T_cmb_MeV, 1.0e-99)
    return t_pl_s * t_ratio * lean.GAMMA / float(lean.REFERENCE_M + 1)


def derived_coordinate_time_nat(omega_cmb: float) -> float:
    """Natural coordinate time from cumulative Ω readout at the CMB slot."""
    return math.log(max(omega_cmb, 1.0)) / lean.ALPHA


def derived_age_ratio_wall_over_apparent(omega_cmb: float) -> float:
    """Wall-clock / apparent from homogeneous lapse integral (Lean ``ageRatioHomogeneous``)."""
    t_nat = derived_coordinate_time_nat(omega_cmb)
    if t_nat <= 0.0:
        return 1.0
    return wall_clock_age_homogeneous(lean.GAMMA, t_nat) / t_nat


def derive_cosmic_filament_epoch() -> CosmicFilamentEpoch:
    """Build present-epoch slots from ``Now.lean`` / ``BBNEpochEvolution`` ladder exports."""
    T_cmb_MeV = bbn.cmb_temperature_mev()
    T_cmb_K = T_cmb_MeV / notd.K_B_MEV_PER_K
    m_cmb = bbn.shell_index_from_mev(T_cmb_MeV)
    xi_cmb = notd.xi_from_temperature_K(T_cmb_K)
    n_gamma = photon_number_density_m3(T_cmb_K)
    eta = lean.ETA_PAPER
    n_baryon = eta * n_gamma
    omega_cmb = lean.omega_k_xi(xi_cmb)
    t_nat = derived_coordinate_time_nat(omega_cmb)
    age_ratio = derived_age_ratio_wall_over_apparent(omega_cmb)
    age_apparent_s = derived_structural_apparent_age_s(T_cmb_MeV)
    age_wall_s = age_apparent_s * age_ratio
    return CosmicFilamentEpoch(
        T_cmb_K=T_cmb_K,
        T_cmb_MeV=T_cmb_MeV,
        m_cmb=m_cmb,
        xi_cmb=xi_cmb,
        n_gamma_m3=n_gamma,
        n_baryon_m3=n_baryon,
        eta=eta,
        omega_cmb=omega_cmb,
        coordinate_time_nat=t_nat,
        age_ratio_wall_over_apparent=age_ratio,
        age_apparent_s=age_apparent_s,
        age_wall_s=age_wall_s,
        note=(
            "T_CMB from T_CMB_natural·T_Pl (Now.lean); η from lock-in export; "
            "ages from lapse + Ω_cmb structural map (compare 13.8 / 51.2 Gyr paper witnesses)."
        ),
    )


def derived_lambda0_baryon_cmb(
    epoch: CosmicFilamentEpoch,
    *,
    eta: float = PINCH_HEATING_FRACTION,
    alpha: float = COOLING_ALPHA,
    k_b: float = K_B,
) -> float:
    """Λ scale from baryon-slot pinch–radiative balance at the CMB chart: λ₀ = η k_B T^{1+α}/n_b."""
    n_b = epoch.n_baryon_m3
    if n_b <= 0.0:
        return 0.0
    return eta * k_b * epoch.T_cmb_K ** (1.0 + alpha) / n_b


def whim_age_cooling_factor(T_K: float, epoch: CosmicFilamentEpoch) -> float:
    """Universe-age / outside-chart factor: (ξ_CMB/ξ(T))^γ with wall-clock lapse weight."""
    if T_K <= 0.0:
        return 1.0
    xi_T = notd.xi_from_temperature_K(T_K)
    shell_factor = (epoch.xi_cmb / max(xi_T, 1.0e-99)) ** lean.GAMMA
    lapse_factor = epoch.age_ratio_wall_over_apparent ** (lean.GAMMA / (1.0 + lean.ALPHA))
    return shell_factor * lapse_factor


def whim_lambda_cooling(
    T_K: float,
    *,
    epoch: CosmicFilamentEpoch | None = None,
    lambda0: float | None = None,
    alpha: float = COOLING_ALPHA,
    m_ism: int = 0,
    m_whim: int = 1,
) -> float:
    """Λ(T) = λ₀ (T/T_CMB)^{-α} × age factors; λ₀ derived at CMB baryon slot unless overridden."""
    if T_K <= 0.0:
        return 0.0
    ep = epoch if epoch is not None else derive_cosmic_filament_epoch()
    lam0 = lambda0 if lambda0 is not None else derived_lambda0_baryon_cmb(ep)
    boundary = (phi_of_shell(m_whim) / phi_of_shell(m_ism)) ** alpha
    base = lam0 * (T_K / ep.T_cmb_K) ** (-alpha) * whim_age_cooling_factor(T_K, ep) * boundary
    return base


def radiative_cooling_w_m3(
    n_m3: float,
    T_K: float,
    *,
    epoch: CosmicFilamentEpoch | None = None,
    lambda0: float | None = None,
    alpha: float = COOLING_ALPHA,
    m_ism: int = 0,
    m_whim: int = 1,
) -> float:
    """q_cool = n² Λ(T) [W/m³]."""
    return n_m3**2 * whim_lambda_cooling(
        T_K, epoch=epoch, lambda0=lambda0, alpha=alpha, m_ism=m_ism, m_whim=m_whim
    )


def whim_pinch_heating_w_m3(
    n_m3: float,
    T_K: float,
    *,
    eta: float = PINCH_HEATING_FRACTION,
    k_b: float = K_B,
) -> float:
    """q_heat = η p_th [W/m³]."""
    return eta * n_m3 * k_b * T_K


def whim_radiative_equilibrium_residual(
    n_m3: float,
    T_K: float,
    *,
    epoch: CosmicFilamentEpoch | None = None,
    eta: float = PINCH_HEATING_FRACTION,
    lambda0: float | None = None,
    alpha: float = COOLING_ALPHA,
    k_b: float = K_B,
    m_ism: int = 0,
    m_whim: int = 1,
) -> float:
    """q_heat − q_cool; ≈ 0 at pinch–radiative balance."""
    return whim_pinch_heating_w_m3(n_m3, T_K, eta=eta, k_b=k_b) - radiative_cooling_w_m3(
        n_m3,
        T_K,
        epoch=epoch,
        lambda0=lambda0,
        alpha=alpha,
        m_ism=m_ism,
        m_whim=m_whim,
    )


def whim_equilibrium_density_m3(
    T_K: float,
    *,
    epoch: CosmicFilamentEpoch | None = None,
    eta: float = PINCH_HEATING_FRACTION,
    lambda0: float | None = None,
    alpha: float = COOLING_ALPHA,
    k_b: float = K_B,
    m_ism: int = 0,
    m_whim: int = 1,
) -> float:
    """Closed-form n at balance with baryon-normalized λ₀: n = n_b (T/T_CMB)^{1+α} (age factors in Λ)."""
    ep = epoch if epoch is not None else derive_cosmic_filament_epoch()
    lam0 = lambda0 if lambda0 is not None else derived_lambda0_baryon_cmb(ep, eta=eta, alpha=alpha, k_b=k_b)
    if lam0 <= 0.0 or T_K <= 0.0 or ep.n_baryon_m3 <= 0.0:
        return 0.0
    n_b = ep.n_baryon_m3
    age_fac = whim_age_cooling_factor(T_K, ep)
    boundary = (phi_of_shell(m_whim) / phi_of_shell(m_ism)) ** alpha
    T_ratio = T_K / ep.T_cmb_K
    return n_b * T_ratio ** (1.0 + alpha) / max(age_fac * boundary, 1.0e-99)


def filament_baryon_loading(
    compression_ratio: float,
    *,
    m_ism: int = 0,
    m_whim: int = 1,
) -> float:
    """Geometric pinch load: compression × φ(WHIM)/φ(ISM) (no fitted overdensity)."""
    phi_ratio = phi_of_shell(m_whim) / phi_of_shell(m_ism)
    return compression_ratio * phi_ratio


def node_thermal_load_multiplier(n_filaments: int) -> float:
    """
    Junction thermal boost: ``C_node / C_spine = N²`` on the spine radius.

    Lean: ``nodeLocalizedIntensity / pinchCompressionRatio(R, r_spine) = N²``.
    """
    n = float(max(1, n_filaments))
    return n * n


def whim_thermal_load_factor(
    compression_ratio: float,
    epoch: CosmicFilamentEpoch,
    *,
    m_ism: int = 0,
    m_whim: int = 1,
    n_filaments: int = 1,
) -> float:
    """Thermal ladder load: compression × φ × Ω_cmb × N² junction factor."""
    base = filament_baryon_loading(compression_ratio, m_ism=m_ism, m_whim=m_whim)
    omega_factor = (
        epoch.omega_cmb / max(lean.omega_k_xi(lean.XI_LOCKIN), 1.0e-99)
    ) ** (lean.GAMMA / (1.0 + lean.ALPHA))
    return base * omega_factor * node_thermal_load_multiplier(n_filaments)


def whim_temperature_from_baryon_loading(
    baryon_load: float,
    epoch: CosmicFilamentEpoch,
    *,
    alpha: float = COOLING_ALPHA,
    m_ism: int = 0,
    m_whim: int = 1,
) -> float:
    """Analytic T estimate from ``n = n_b · load`` on the CMB-normalized cooling chart."""
    if baryon_load <= 0.0:
        return epoch.T_cmb_K
    boundary = phi_of_shell(m_whim) / phi_of_shell(m_ism)
    load_eff = baryon_load / boundary
    T_base = epoch.T_cmb_K * load_eff ** (1.0 / (1.0 + alpha))
    age_fac = whim_age_cooling_factor(T_base, epoch)
    return T_base * age_fac ** (1.0 / (1.0 + alpha))


def solve_whim_temperature_at_density(
    n_m3: float,
    epoch: CosmicFilamentEpoch,
    *,
    m_ism: int = 0,
    m_whim: int = 1,
    T_lo_K: float | None = None,
    T_hi_K: float | None = None,
    max_iter: int = 96,
) -> float:
    """Solve ``q_heat(n,T) = q_cool(n,T)`` for ``T`` at fixed filament density (bisection on log grid)."""
    if n_m3 <= 0.0:
        return epoch.T_cmb_K
    lo = T_lo_K if T_lo_K is not None else epoch.T_cmb_K
    hi = T_hi_K if T_hi_K is not None else min(planck_temperature_k() / 1.0e6, 1.0e8)
    if hi <= lo:
        hi = lo * 1.0e6

    def residual(T: float) -> float:
        return whim_radiative_equilibrium_residual(
            n_m3, T, epoch=epoch, m_ism=m_ism, m_whim=m_whim
        )

    r_lo = residual(lo)
    r_hi = residual(hi)
    if r_lo == 0.0:
        return lo
    if r_hi == 0.0:
        return hi
    if r_lo * r_hi > 0.0:
        # Monotone fallback: analytic load inversion at CMB chart
        return whim_temperature_from_baryon_loading(
            n_m3 / max(epoch.n_baryon_m3, 1.0e-99),
            epoch,
            m_ism=m_ism,
            m_whim=m_whim,
        )

    for _ in range(max_iter):
        mid = math.sqrt(lo * hi)
        r_mid = residual(mid)
        if abs(r_mid) <= 1.0e-12 * max(abs(residual(lo)), abs(residual(hi)), 1.0e-30):
            return mid
        if r_lo * r_mid <= 0.0:
            hi = mid
            r_hi = r_mid
        else:
            lo = mid
            r_lo = r_mid
    return math.sqrt(lo * hi)


def coupled_whim_filament_nt(
    R_bulk_m: float,
    r_pinch_m: float,
    *,
    epoch: CosmicFilamentEpoch | None = None,
    m_ism: int = 0,
    m_whim: int = 1,
    n_filaments: int = 1,
) -> tuple[float, float, float]:
    """Fully coupled (n, T): thermal load includes N² junction boost; n from radiative closure at T."""
    ep = epoch if epoch is not None else derive_cosmic_filament_epoch()
    compression = pinch_compression_ratio(R_bulk_m, r_pinch_m)
    load_geom = filament_baryon_loading(compression, m_ism=m_ism, m_whim=m_whim)
    thermal_load = whim_thermal_load_factor(
        compression, ep, m_ism=m_ism, m_whim=m_whim, n_filaments=n_filaments
    )
    T = whim_temperature_from_baryon_loading(thermal_load, ep, m_ism=m_ism, m_whim=m_whim)
    n = whim_equilibrium_density_m3(T, epoch=ep, m_ism=m_ism, m_whim=m_whim)
    return n, T, load_geom


@dataclass(frozen=True)
class CoupledWhimFilamentReadout:
    """WHIM filament (n, T) from cosmic epoch + pinch geometry (no WHIM witness constants)."""

    epoch: CosmicFilamentEpoch
    compression_ratio: float
    baryon_load: float
    n_filaments: int
    node_thermal_multiplier: float
    n_m3: float
    T_K: float
    lambda0_derived: float
    cooling_alpha: float
    pinch_heating_fraction: float
    radiative_residual_w_m3: float
    radiative_ok: bool
    cooling_time_s: float
    age_wall_s: float
    note: str


def coupled_whim_filament_readout(
    R_bulk_m: float,
    r_pinch_m: float,
    *,
    epoch: CosmicFilamentEpoch | None = None,
    m_ism: int = 0,
    m_whim: int = 1,
    n_filaments: int = 1,
    residual_tol: float = 1.0e-6,
) -> CoupledWhimFilamentReadout:
    """Coupled WHIM thermodynamic state + radiative residual check."""
    ep = epoch if epoch is not None else derive_cosmic_filament_epoch()
    compression = pinch_compression_ratio(R_bulk_m, r_pinch_m)
    n, T, load = coupled_whim_filament_nt(
        R_bulk_m,
        r_pinch_m,
        epoch=ep,
        m_ism=m_ism,
        m_whim=m_whim,
        n_filaments=n_filaments,
    )
    lam0 = derived_lambda0_baryon_cmb(ep)
    q_heat = whim_pinch_heating_w_m3(n, T)
    q_cool = radiative_cooling_w_m3(n, T, epoch=ep, m_ism=m_ism, m_whim=m_whim)
    residual = q_heat - q_cool
    scale = max(abs(q_heat), abs(q_cool), 1.0e-30)
    tol = max(residual_tol * scale, 1.0e-12)
    t_cool = 1.5 * n * K_B * T / max(q_cool, 1.0e-99)
    node_mult = node_thermal_load_multiplier(n_filaments)
    return CoupledWhimFilamentReadout(
        epoch=ep,
        compression_ratio=compression,
        baryon_load=load,
        n_filaments=n_filaments,
        node_thermal_multiplier=node_mult,
        n_m3=n,
        T_K=T,
        lambda0_derived=lam0,
        cooling_alpha=COOLING_ALPHA,
        pinch_heating_fraction=PINCH_HEATING_FRACTION,
        radiative_residual_w_m3=residual,
        radiative_ok=abs(residual) <= tol,
        cooling_time_s=t_cool,
        age_wall_s=ep.age_wall_s,
        note=(
            "Thermal load: compression×φ×Ω_cmb×N²; n from radiative closure at derived T. "
            "N-way junction uses nodeLocalizedIntensity/spine compression (no extra witnesses)."
        ),
    )


@dataclass(frozen=True)
class CoupledWhimFilamentNodeReadout:
    """Coupled (n,T) at an N-way junction + node pinch / collapse diagnostics."""

    coupled: CoupledWhimFilamentReadout
    node: FilamentNodeReadout
    beta_spine: BetaPinchBalanceReadout
    beta_node_radius: BetaPinchBalanceReadout
    node_localized_intensity: float
    note: str


def coupled_whim_filament_node_readout(
    r_spine_m: float,
    R_filament_m: float,
    n_filaments: int,
    *,
    r_pinch_m: float | None = None,
    epoch: CosmicFilamentEpoch | None = None,
    m_ism: int = 0,
    m_whim: int = 1,
    collapse_threshold: float = 100.0,
) -> CoupledWhimFilamentNodeReadout:
    """N-way junction: coupled thermodynamics + node-local pinch (preferred collapse site)."""
    r_p = r_pinch_m if r_pinch_m is not None else max(r_spine_m * 0.05, 1.0e19)
    coupled = coupled_whim_filament_readout(
        R_filament_m,
        r_p,
        epoch=epoch,
        m_ism=m_ism,
        m_whim=m_whim,
        n_filaments=n_filaments,
    )
    beta_spine = beta_pinch_balance_readout(
        coupled.n_m3, coupled.T_K, r_spine_m, regime="whim_filament_spine"
    )
    J_spine = beta_spine.current_density_a_m2
    node = filament_node_readout(
        J_spine,
        r_spine_m,
        R_filament_m,
        n_filaments,
        m_ism=m_ism,
        m_whim=m_whim,
        collapse_threshold=collapse_threshold,
    )
    r_node = node_pinch_radius(r_spine_m, n_filaments)
    beta_node = beta_pinch_balance_readout(
        coupled.n_m3, coupled.T_K, r_node, regime="whim_filament_node"
    )
    intensity = node_localized_intensity(R_filament_m, r_spine_m, n_filaments)
    return CoupledWhimFilamentNodeReadout(
        coupled=coupled,
        node=node,
        beta_spine=beta_spine,
        beta_node_radius=beta_node,
        node_localized_intensity=intensity,
        note=(
            "Junction N² thermal load drives hotter/denser coupled state; "
            "node pinch uses superposed current at r_node = r_spine/√N."
        ),
    )




@dataclass(frozen=True)
class WhimRadiativeEquilibriumReadout:
    """Pinch-heating vs radiative cooling balance at fixed T (CMB/age-aware Λ)."""

    T_K: float
    n_equilibrium_m3: float
    q_heat_w_m3: float
    q_cool_w_m3: float
    residual_w_m3: float
    equilibrium_ok: bool
    eta: float
    lambda0: float
    alpha: float
    T_cmb_K: float
    age_wall_s: float
    note: str


def whim_radiative_equilibrium_readout(
    T_K: float,
    *,
    epoch: CosmicFilamentEpoch | None = None,
    eta: float = PINCH_HEATING_FRACTION,
    lambda0: float | None = None,
    alpha: float = COOLING_ALPHA,
    residual_tol: float = 1.0e-6,
    k_b: float = K_B,
    m_ism: int = 0,
    m_whim: int = 1,
) -> WhimRadiativeEquilibriumReadout:
    """Equilibrium density at ``T`` on the derived CMB/age cooling chart."""
    ep = epoch if epoch is not None else derive_cosmic_filament_epoch()
    lam0 = lambda0 if lambda0 is not None else derived_lambda0_baryon_cmb(ep, eta=eta, alpha=alpha, k_b=k_b)
    n = whim_equilibrium_density_m3(
        T_K,
        epoch=ep,
        eta=eta,
        lambda0=lam0,
        alpha=alpha,
        k_b=k_b,
        m_ism=m_ism,
        m_whim=m_whim,
    )
    q_heat = whim_pinch_heating_w_m3(n, T_K, eta=eta, k_b=k_b)
    q_cool = radiative_cooling_w_m3(n, T_K, epoch=ep, lambda0=lam0, alpha=alpha, m_ism=m_ism, m_whim=m_whim)
    residual = q_heat - q_cool
    scale = max(abs(q_heat), abs(q_cool), 1.0e-30)
    tol = max(residual_tol * scale, 1.0e-12)
    return WhimRadiativeEquilibriumReadout(
        T_K=T_K,
        n_equilibrium_m3=n,
        q_heat_w_m3=q_heat,
        q_cool_w_m3=q_cool,
        residual_w_m3=residual,
        equilibrium_ok=abs(residual) <= tol,
        eta=eta,
        lambda0=lam0,
        alpha=alpha,
        T_cmb_K=ep.T_cmb_K,
        age_wall_s=ep.age_wall_s,
        note=ep.note,
    )


@dataclass(frozen=True)
class PinchState:
    """Cylindrical Z-pinch bookkeeping at radius ``r``."""

    axial_current_A: float
    radius_m: float
    B_theta_T: float
    p_mag_Pa: float
    bennett_I_A: float | None  # if deltaP supplied


@dataclass(frozen=True)
class LocalizedIntensityState:
    """Bulk vs pinch-local enhancement."""

    R_bulk_m: float
    r_pinch_m: float
    compression_ratio: float
    heating_enhancement: float
    n_loc_over_n_bulk: float


@dataclass(frozen=True)
class CoronalPinchReadout:
    """Coronal flux-tube pinch from hot return current."""

    J_hot_A_m2: float
    tube_radius_m: float
    p_pinch_Pa: float
    compression: LocalizedIntensityState
    q_dot_enhancement: float


@dataclass(frozen=True)
class WhimFilamentPinchReadout:
    """WHIM spine pinch + boundary φ enhancement (galaxy-seeding diagnostic)."""

    J_spine_A_m2: float
    r_spine_m: float
    R_filament_m: float
    r_pinch_m: float
    p_pinch_Pa: float
    compression: LocalizedIntensityState
    phi_whim_shape: float
    phi_pinch_enhancement: float
    collapse_hypothesis: bool
    collapse_threshold: float
    note: str


def pinch_azimuthal_field(axial_current_A: float, radius_m: float) -> float:
    """B_θ = μ₀ I / (2π r)."""
    if radius_m <= 0.0:
        return 0.0
    return MU0 * axial_current_A / (2.0 * math.pi * radius_m)


def magnetic_pinch_pressure(B_theta_T: float) -> float:
    """p_mag = B² / (2μ₀)."""
    return B_theta_T**2 / (2.0 * MU0)


def pinch_azimuthal_pressure(axial_current_A: float, radius_m: float) -> float:
    """μ₀ I² / (8π² r²)."""
    if radius_m <= 0.0:
        return 0.0
    return MU0 * axial_current_A**2 / (8.0 * math.pi**2 * radius_m**2)


def pinch_axial_current(J_A_m2: float, radius_m: float) -> float:
    """I = J π r²."""
    return J_A_m2 * math.pi * radius_m**2


def bennett_equilibrium_current(a_m: float, delta_p_Pa: float) -> float:
    """I = sqrt(8π² a² Δp / μ₀)."""
    if a_m <= 0.0 or delta_p_Pa <= 0.0:
        return 0.0
    return math.sqrt(8.0 * math.pi**2 * a_m**2 * delta_p_Pa / MU0)


def pinch_compression_ratio(R_bulk_m: float, r_pinch_m: float) -> float:
    """(R_bulk / r_pinch)² flux-conservation scaffold."""
    if r_pinch_m <= 0.0:
        return 1.0
    return (R_bulk_m / r_pinch_m) ** 2


def localized_intensity(R_bulk_m: float, r_pinch_m: float) -> LocalizedIntensityState:
    c = pinch_compression_ratio(R_bulk_m, r_pinch_m)
    return LocalizedIntensityState(
        R_bulk_m=R_bulk_m,
        r_pinch_m=r_pinch_m,
        compression_ratio=c,
        heating_enhancement=c,
        n_loc_over_n_bulk=c,
    )


def hot_current_pinch_pressure(J_hot_A_m2: float, radius_m: float) -> float:
    """Pinch pressure from hot return-current density."""
    I = pinch_axial_current(J_hot_A_m2, radius_m)
    return pinch_azimuthal_pressure(I, radius_m)


@dataclass(frozen=True)
class BetaPinchBalanceReadout:
    """β = p_th/p_mag with Bennett-derived current from (n, T, r)."""

    n_m3: float
    T_K: float
    radius_m: float
    p_thermal_pa: float
    axial_current_A: float
    current_density_a_m2: float
    B_theta_T: float
    p_mag_pa: float
    beta: float
    balance_residual_pa: float
    balance_ok: bool
    regime: str
    note: str


def thermal_plasma_pressure(n_m3: float, T_K: float, k_b: float = K_B) -> float:
    """p_th = n k_B T."""
    return n_m3 * k_b * T_K


def bennett_current_from_thermal_pressure(radius_m: float, p_thermal_pa: float, mu0: float = MU0) -> float:
    """I = 2π r √(2 p_th / μ₀) at β = 1."""
    if radius_m <= 0.0 or p_thermal_pa <= 0.0:
        return 0.0
    return 2.0 * math.pi * radius_m * math.sqrt(2.0 * p_thermal_pa / mu0)


def bennett_current_from_nt(radius_m: float, n_m3: float, T_K: float, mu0: float = MU0) -> float:
    return bennett_current_from_thermal_pressure(radius_m, thermal_plasma_pressure(n_m3, T_K), mu0)


def bennett_current_density_from_nt(radius_m: float, n_m3: float, T_K: float, mu0: float = MU0) -> float:
    """J = 2√(2 n k_B T / μ₀) / r."""
    if radius_m <= 0.0:
        return 0.0
    I = bennett_current_from_nt(radius_m, n_m3, T_K, mu0=mu0)
    return I / (math.pi * radius_m**2)


def pinch_plasma_beta(
    n_m3: float,
    T_K: float,
    axial_current_A: float,
    radius_m: float,
    mu0: float = MU0,
) -> float:
    p_th = thermal_plasma_pressure(n_m3, T_K)
    p_mag = pinch_azimuthal_pressure(axial_current_A, radius_m)
    if p_mag <= 0.0:
        return 0.0
    return p_th / p_mag


def bennett_pressure_balance_residual(
    radius_m: float,
    n_m3: float,
    T_K: float,
    *,
    axial_current_A: float | None = None,
    mu0: float = MU0,
) -> float:
    """p_mag − p_th; should be ≈ 0 when I is Bennett-derived."""
    p_th = thermal_plasma_pressure(n_m3, T_K)
    I = axial_current_A if axial_current_A is not None else bennett_current_from_nt(radius_m, n_m3, T_K, mu0)
    p_mag = pinch_azimuthal_pressure(I, radius_m)
    return p_mag - p_th


def beta_pinch_balance_readout(
    n_m3: float,
    T_K: float,
    radius_m: float,
    *,
    regime: str = "generic",
    balance_tol_pa: float = 1.0e-6,
    mu0: float = MU0,
) -> BetaPinchBalanceReadout:
    """Derive Bennett-balanced I from (n, T, r) and report β and force-balance residual."""
    p_th = thermal_plasma_pressure(n_m3, T_K)
    I = bennett_current_from_thermal_pressure(radius_m, p_th, mu0)
    J = I / (math.pi * radius_m**2) if radius_m > 0.0 else 0.0
    B = pinch_azimuthal_field(I, radius_m)
    p_mag = magnetic_pinch_pressure(B)
    beta = pinch_plasma_beta(n_m3, T_K, I, radius_m, mu0=mu0)
    residual = p_mag - p_th
    return BetaPinchBalanceReadout(
        n_m3=n_m3,
        T_K=T_K,
        radius_m=radius_m,
        p_thermal_pa=p_th,
        axial_current_A=I,
        current_density_a_m2=J,
        B_theta_T=B,
        p_mag_pa=p_mag,
        beta=beta,
        balance_residual_pa=residual,
        balance_ok=abs(residual) <= balance_tol_pa * max(p_th, 1.0),
        regime=regime,
        note=(
            "Bennett β=1: I from √(2 p_th/μ₀); residual p_mag−p_th checks cylindrical identity. "
            "J_spine derived from (n,T,r) — not fitted."
        ),
    )


def pinch_state_at_radius(
    axial_current_A: float,
    radius_m: float,
    *,
    delta_p_Pa: float | None = None,
) -> PinchState:
    B = pinch_azimuthal_field(axial_current_A, radius_m)
    p = magnetic_pinch_pressure(B)
    bennett = None
    if delta_p_Pa is not None and delta_p_Pa > 0.0:
        bennett = bennett_equilibrium_current(radius_m, delta_p_Pa)
    return PinchState(
        axial_current_A=axial_current_A,
        radius_m=radius_m,
        B_theta_T=B,
        p_mag_Pa=p,
        bennett_I_A=bennett,
    )


def solar_whim_boundary_shape(m_ism: int = 0, m_whim: int = 1) -> float:
    """Match ``solarWhimBoundaryShape``: max(0, 2(m_whim−m_ism)) / φ(m_ism)."""
    phi_m = 2.0 * (m_ism + 1)  # φ(m) = 2(m+1) HQIV ladder
    return max(0.0, 2.0 * (m_whim - m_ism)) / phi_m


def junction_filament_count(n_filaments: int) -> float:
    return float(max(1, n_filaments))


def node_pinch_radius(r_spine_pinch_m: float, n_filaments: int) -> float:
    """r_node = r_spine / sqrt(N)."""
    return r_spine_pinch_m / math.sqrt(junction_filament_count(n_filaments))


def node_spine_compression(R_bulk_m: float, r_spine_pinch_m: float, n_filaments: int) -> float:
    return pinch_compression_ratio(R_bulk_m, node_pinch_radius(r_spine_pinch_m, n_filaments))


def node_mass_flux_enhancement(n_filaments: int) -> float:
    return junction_filament_count(n_filaments)


def node_localized_intensity(R_bulk_m: float, r_spine_pinch_m: float, n_filaments: int) -> float:
    """C_node = N · (R / r_node)²."""
    return node_mass_flux_enhancement(n_filaments) * node_spine_compression(
        R_bulk_m, r_spine_pinch_m, n_filaments
    )


def node_current_superposition(J_spine_a_m2: float, n_filaments: int) -> float:
    return junction_filament_count(n_filaments) * J_spine_a_m2


def node_pinch_pressure(J_spine_a_m2: float, r_spine_pinch_m: float, n_filaments: int) -> float:
    return hot_current_pinch_pressure(
        node_current_superposition(J_spine_a_m2, n_filaments),
        node_pinch_radius(r_spine_pinch_m, n_filaments),
    )


def whim_node_phi_enhancement(
    m_ism: int,
    m_whim: int,
    R_bulk_m: float,
    r_spine_pinch_m: float,
    n_filaments: int,
) -> float:
    return solar_whim_boundary_shape(m_ism, m_whim) * node_localized_intensity(
        R_bulk_m, r_spine_pinch_m, n_filaments
    )


@dataclass(frozen=True)
class FilamentNodeReadout:
    n_filaments: int
    r_spine_pinch_m: float
    R_bulk_m: float
    r_node_m: float
    node_intensity: float
    mass_flux_enhancement: float
    p_pinch_pa: float
    phi_node_enhancement: float
    collapse_hypothesis: bool
    collapse_threshold: float
    note: str


def filament_node_readout(
    J_spine_a_m2: float,
    r_spine_pinch_m: float,
    R_bulk_m: float,
    n_filaments: int,
    *,
    m_ism: int = 0,
    m_whim: int = 1,
    collapse_threshold: float = 100.0,
) -> FilamentNodeReadout:
    """N-way filament junction — preferred pinch collapse site."""
    r_node = node_pinch_radius(r_spine_pinch_m, n_filaments)
    intensity = node_localized_intensity(R_bulk_m, r_spine_pinch_m, n_filaments)
    p = node_pinch_pressure(J_spine_a_m2, r_spine_pinch_m, n_filaments)
    phi_enh = whim_node_phi_enhancement(m_ism, m_whim, R_bulk_m, r_spine_pinch_m, n_filaments)
    return FilamentNodeReadout(
        n_filaments=n_filaments,
        r_spine_pinch_m=r_spine_pinch_m,
        R_bulk_m=R_bulk_m,
        r_node_m=r_node,
        node_intensity=intensity,
        mass_flux_enhancement=node_mass_flux_enhancement(n_filaments),
        p_pinch_pa=p,
        phi_node_enhancement=phi_enh,
        collapse_hypothesis=intensity >= collapse_threshold,
        collapse_threshold=collapse_threshold,
        note=(
            "N-way junction: mass-flux × geometric pinch tightening (r_node = r_spine/√N). "
            "Preferred BH/galaxy seed site — hypothesis threshold only."
        ),
    )


def coronal_flux_tube_pinch_readout(
    J_hot_A_m2: float,
    tube_radius_m: float,
    *,
    R_loop_m: float | None = None,
    r_pinch_m: float | None = None,
) -> CoronalPinchReadout:
    """Pinch at a coronal flux tube from heated return current."""
    R = R_loop_m if R_loop_m is not None else tube_radius_m
    r_p = r_pinch_m if r_pinch_m is not None else max(tube_radius_m * 0.1, 1.0e3)
    p = hot_current_pinch_pressure(J_hot_A_m2, tube_radius_m)
    comp = localized_intensity(R, r_p)
    return CoronalPinchReadout(
        J_hot_A_m2=J_hot_A_m2,
        tube_radius_m=tube_radius_m,
        p_pinch_Pa=p,
        compression=comp,
        q_dot_enhancement=comp.heating_enhancement,
    )


def whim_filament_pinch_readout(
    r_spine_m: float,
    R_filament_m: float,
    *,
    J_spine_A_m2: float | None = None,
    n_m3: float | None = None,
    T_K: float | None = None,
    r_pinch_m: float | None = None,
    m_ism: int = 0,
    m_whim: int = 1,
    collapse_threshold: float = 100.0,
    use_coupled_cosmic_closure: bool = True,
    epoch: CosmicFilamentEpoch | None = None,
    n_filaments: int = 1,
) -> WhimFilamentPinchReadout:
    """WHIM filament spine pinch + φ enhancement (galaxy-seeding hypothesis slot)."""
    r_p = r_pinch_m if r_pinch_m is not None else max(r_spine_m * 0.05, 1.0e19)
    ep = epoch if epoch is not None else derive_cosmic_filament_epoch()
    if use_coupled_cosmic_closure and n_m3 is None and T_K is None:
        coupled = coupled_whim_filament_readout(
            R_filament_m,
            r_p,
            epoch=ep,
            m_ism=m_ism,
            m_whim=m_whim,
            n_filaments=n_filaments,
        )
        n, T = coupled.n_m3, coupled.T_K
    else:
        T = T_K if T_K is not None else WHIM_FILAMENT_T_K
        if n_m3 is not None:
            n = n_m3
        else:
            n = whim_equilibrium_density_m3(T, epoch=ep, m_ism=m_ism, m_whim=m_whim)
    J = J_spine_A_m2 if J_spine_A_m2 is not None else bennett_current_density_from_nt(r_spine_m, n, T)
    p = hot_current_pinch_pressure(J, r_spine_m)
    comp = localized_intensity(R_filament_m, r_p)
    shape = solar_whim_boundary_shape(m_ism, m_whim)
    phi_enh = shape * comp.compression_ratio
    collapse = comp.compression_ratio >= collapse_threshold
    return WhimFilamentPinchReadout(
        J_spine_A_m2=J,
        r_spine_m=r_spine_m,
        R_filament_m=R_filament_m,
        r_pinch_m=r_p,
        p_pinch_Pa=p,
        compression=comp,
        phi_whim_shape=shape,
        phi_pinch_enhancement=phi_enh,
        collapse_hypothesis=collapse,
        collapse_threshold=collapse_threshold,
        note=(
            "Pinch focal line: local n and q̇ exceed bulk by compression_ratio; "
            "φ boundary steepens by phi_pinch_enhancement. Collapse hypothesis is "
            "algebraic threshold only — not a derived BH/galaxy mass function."
        ),
    )


def default_coronal_demo() -> dict[str, object]:
    """Coronal β-balance + flux-tube pinch."""
    r_tube = 1.0e5
    beta = beta_pinch_balance_readout(CORONAL_FILAMENT_N_M3, CORONAL_FILAMENT_T_K, r_tube, regime="coronal")
    out = coronal_flux_tube_pinch_readout(beta.current_density_a_m2, r_tube, R_loop_m=1.0e6, r_pinch_m=1.0e4)
    return {
        "regime": "coronal_flux_tube",
        "beta_balance": asdict(beta),
        "J_hot_A_m2": out.J_hot_A_m2,
        "tube_radius_m": out.tube_radius_m,
        "p_pinch_Pa": out.p_pinch_Pa,
        "compression_ratio": out.compression.compression_ratio,
        "q_dot_enhancement": out.q_dot_enhancement,
    }


def default_whim_demo() -> dict[str, object]:
    """WHIM spine + N=4 junction: coupled (n,T), node pinch, Bennett J."""
    R_fil = 3.086e22  # 1 Mpc
    r_spine = 3.086e21  # 100 kpc
    r_pinch = 1.543e20  # 5 kpc
    coupled_spine = coupled_whim_filament_readout(R_fil, r_pinch, n_filaments=1)
    node = coupled_whim_filament_node_readout(r_spine, R_fil, 4, r_pinch_m=r_pinch)
    beta = beta_pinch_balance_readout(node.coupled.n_m3, node.coupled.T_K, r_spine, regime="whim_filament")
    out = whim_filament_pinch_readout(
        r_spine_m=r_spine, R_filament_m=R_fil, r_pinch_m=r_pinch, n_filaments=4
    )
    return {
        "regime": "whim_filament",
        "cosmic_epoch": asdict(node.coupled.epoch),
        "coupled_spine": {
            "n_m3": coupled_spine.n_m3,
            "T_K": coupled_spine.T_K,
            "node_thermal_multiplier": coupled_spine.node_thermal_multiplier,
        },
        "coupled_node_n4": {
            "n_m3": node.coupled.n_m3,
            "T_K": node.coupled.T_K,
            "node_thermal_multiplier": node.coupled.node_thermal_multiplier,
            "node_intensity": node.node_localized_intensity,
            "radiative_ok": node.coupled.radiative_ok,
            "collapse_hypothesis": node.node.collapse_hypothesis,
            "beta_node": asdict(node.beta_node_radius),
        },
        "beta_balance": asdict(beta),
        "J_spine_A_m2": out.J_spine_A_m2,
        "compression_ratio": out.compression.compression_ratio,
        "phi_pinch_enhancement": out.phi_pinch_enhancement,
        "p_pinch_Pa": out.p_pinch_Pa,
        "note": node.note,
    }


def readout_as_dict(obj: CoronalPinchReadout | WhimFilamentPinchReadout) -> dict[str, object]:
    return asdict(obj)


def _default_whim_filament_constants() -> tuple[float, float, float, float, float]:
    ep = derive_cosmic_filament_epoch()
    coupled = coupled_whim_filament_readout(3.086e22, 1.543e20, epoch=ep)
    lam0 = derived_lambda0_baryon_cmb(ep)
    return coupled.T_K, coupled.n_m3, lam0, COOLING_ALPHA, PINCH_HEATING_FRACTION


WHIM_FILAMENT_T_K, WHIM_FILAMENT_N_M3, WHIM_LAMBDA0, WHIM_LAMBDA_ALPHA, WHIM_PINCH_HEATING_FRACTION = (
    _default_whim_filament_constants()
)


if __name__ == "__main__":
    import json

    print(json.dumps({"coronal": default_coronal_demo(), "whim": default_whim_demo()}, indent=2))

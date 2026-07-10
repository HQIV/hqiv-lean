#!/usr/bin/env python3
"""Derived galaxy φ dynamics: Lean algebra + proton-pin age (no case splits).

Replaces activity-index seed/active blending and pinch soft-gates with a single
geometry-driven equation stack:

  1. φ_hom from Route-A wall-clock age
       m_prop = 1/(referenceM · q²) = 1/100
       t_wall = m_prop · latticeSimplexCount(m_T) · t_Pl
       H₀ = 1/t_wall ,  φ_hom = 2 c H₀
     (same proton-pin ``referenceM=4`` used by chemistry; T_CMB is the sole
     external dimensionful input — ``hqiv_cmb_age_lockdown``).

  2. Propagation band ξ = 1 (``OrbitalFlybyScaffold.solarSystemPropagationShell``),
     not the hadron lock-in shell.

  3. Homogeneous curvature dress
       B_hom(ξ, ρ) = 1 + ρ · (B_curv(ξ) − 1)
     with continuous baryon gas fraction ρ ∈ [0,1] from SPARC master fields
     (no Hubble-type cases).

  4. WHIM boundary (Lean ``solarWhimBoundaryShape``)
       φ_bdy = φ_hom · shape · C_geom · envelope(r)
     with geometric coherence C_geom = exp(−τ/γ) from inclination, r/R_d,
     and filament misalignment only (no activity index).

  5. Thermal screen distance (Lean Rindler activity gate)
       ℓ_th = v²/φ_hom ,  A_R = R/ℓ_th ,
       C_th = 1/(1 + (γ/2) A_R)
     Hot late-type dwarfs with ℓ_th ≪ R lose coherent screen range — the
     ~5% SPARC over-screen miss mode.

  6. Inertia / Doppler unchanged:
       φ_full = C_th·(φ_cosmic+φ_bdy) + 6 a_b ε ,  f = a/(a+φ/6) ,  a_HQIV = a_b/f.

Lean modules:
  - ``Hqiv.Physics.HQIVFluidClosureScaffold.hqivFluidInertiaFactor``
  - ``Hqiv.Physics.HQIVFluidClosureScaffold.hqivIRUVVacuumDivergenceLimit`` (Rindler A_R)
  - ``Hqiv.Physics.SolarDynamics.solarWhimBoundaryShape``
  - ``Hqiv.Physics.HomogeneousCurvatureSecondOrder`` / phase-geometry B_hom
  - ``Hqiv.Physics.OrbitalFlybyScaffold`` (propagation ξ = 1)
  - ``Hqiv.Cosmology`` / ``UniverseAge`` via ``hqiv_cmb_age_lockdown``
"""

from __future__ import annotations

import math
from dataclasses import asdict, dataclass
from typing import Protocol

import hqiv_cmb_age_lockdown as _age
import hqiv_filament_environment as _fil
import hqiv_galaxy_rotation as _gal
import hqiv_homogeneous_curvature_feedback as _hcf
import hqiv_lean_physics_primitives as _lean
import hqiv_plasma_pinch_filament as _pinch
import hqiv_scale_witness as _wit

C_LIGHT = _gal.C_LIGHT
KPC = _gal.KPC
GAMMA = _lean.GAMMA
ALPHA = _lean.ALPHA
REFERENCE_M = _lean.REFERENCE_M
XI_PROPAGATION = 1.0  # xiOfShell(0); OrbitalFlybyScaffold.flybyPropagationXi
M_ISM_DEFAULT = 0
M_WHIM_DEFAULT = 1
# Tortuosity → coherence uses Lean γ as the sole scale (no 1.75 fudge).
TORTUOSITY_SCALE = 1.0 / GAMMA  # 5/2
UPSILON_DISK_FIDUCIAL = 0.50
UPSILON_BUL_FIDUCIAL = 0.70


class GalaxyMasterLike(Protocol):
    name: str
    hubble_type: int
    inclination_deg: float
    rdisk_kpc: float
    sb_disk_lsun_pc2: float
    L36_e9_lsun: float
    mhi_e9_msun: float
    rhi_kpc: float
    vflat_kms: float
    distance_mpc: float


@dataclass(frozen=True)
class ProtonPinCosmology:
    """Cosmological floor derived from proton-pin impedance + T_CMB."""

    reference_m: int
    proton_mass_mev: float
    t_cmb_k: float
    m_prop: float
    t_wall_gyr: float
    t_wall_s: float
    h0_si: float
    phi_hom_m_s2: float
    xi_propagation: float
    note: str

    def as_dict(self) -> dict[str, object]:
        return asdict(self)


@dataclass(frozen=True)
class DerivedDynamicsOptions:
    m_ism: int = M_ISM_DEFAULT
    m_whim: int = M_WHIM_DEFAULT
    upsilon_disk: float = UPSILON_DISK_FIDUCIAL
    upsilon_bul: float = UPSILON_BUL_FIDUCIAL
    tortuosity_scale: float = TORTUOSITY_SCALE
    filament_catalog: dict[str, _fil.FilamentEnvironment] | None = None
    use_whim_boundary: bool = True
    use_homogeneous_dress: bool = True
    #: Lean Rindler thermal gate: hot dwarfs with ℓ_th ≪ R lose screen distance.
    use_thermal_screen: bool = True


@dataclass(frozen=True)
class DerivedPhiState:
    radius_kpc: float
    phi_hom_m_s2: float
    phi_cosmic_m_s2: float
    phi_boundary_m_s2: float
    phi_combined_m_s2: float
    gas_fraction: float
    b_hom: float
    solar_whim_boundary_shape: float
    geometric_coherence: float
    geometric_tortuosity: float
    misalignment_sin: float
    filament_radius_kpc: float
    filament_source: str
    xi_propagation: float
    thermal_length_kpc: float
    thermal_activity: float
    thermal_screen_retention: float

    def as_dict(self) -> dict[str, object]:
        return asdict(self)


_COSMOLOGY_CACHE: ProtonPinCosmology | None = None


def proton_pin_cosmology(*, refresh: bool = False) -> ProtonPinCosmology:
    """Derive φ_hom from Route-A impedance age (proton pin + T_CMB)."""
    global _COSMOLOGY_CACHE
    if _COSMOLOGY_CACHE is not None and not refresh:
        return _COSMOLOGY_CACHE
    route = _age.route_a_integer_impedance()
    t_wall_gyr = float(route["predicted_wall_clock_age_Gyr"])
    t_wall_s = t_wall_gyr * _age.GYR_S
    h0 = 1.0 / max(t_wall_s, 1.0)
    phi_hom = 2.0 * C_LIGHT * h0
    try:
        bundle = _wit.load_default_witness_bundle()
        m_p = float(bundle.derived_proton_mass_mev)
    except Exception:
        m_p = 938.272
    _COSMOLOGY_CACHE = ProtonPinCosmology(
        reference_m=REFERENCE_M,
        proton_mass_mev=m_p,
        t_cmb_k=_age.T_CMB_K,
        m_prop=float(route["m_prop"]),
        t_wall_gyr=t_wall_gyr,
        t_wall_s=t_wall_s,
        h0_si=h0,
        phi_hom_m_s2=phi_hom,
        xi_propagation=XI_PROPAGATION,
        note=(
            "φ_hom = 2c/t_wall with t_wall from m_prop=1/(referenceM·q²) and "
            "latticeSimplexCount(T_Pl/T_CMB−1); proton mass is the chemistry "
            "unit anchor (referenceM=4), not a fitted H₀."
        ),
    )
    return _COSMOLOGY_CACHE


def phi_acceleration_homogeneous_derived_si() -> float:
    """Derived homogeneous φ (m/s²); replaces hardcoded 2cH₀_legacy."""
    return proton_pin_cosmology().phi_hom_m_s2


def gas_baryon_fraction(
    master: GalaxyMasterLike,
    *,
    upsilon_disk: float = UPSILON_DISK_FIDUCIAL,
    upsilon_bul: float = UPSILON_BUL_FIDUCIAL,
) -> float:
    """Continuous ρ ∈ [0,1] from SPARC gas vs stellar light (no morphology cases).

    Stellar mass proxy uses the same photometric Υ fiducials as the SPARC
    rotation pipeline (external conversion, not a theory knob).
    """
    m_gas = max(master.mhi_e9_msun, 0.0)
    m_star = upsilon_disk * max(master.L36_e9_lsun, 0.0)
    # Bulge light is not separately tabulated on the master row; disk Υ covers
    # the 3.6 μm luminosity. Keep upsilon_bul in the signature for call-site
    # symmetry with SparcOptions.
    _ = upsilon_bul
    tot = m_gas + m_star
    if tot <= 0.0:
        return 0.0
    return max(0.0, min(1.0, m_gas / tot))


def filament_radius_kpc(master: GalaxyMasterLike) -> float:
    rd = max(master.rdisk_kpc, 0.08)
    if master.rhi_kpc > 0.05:
        return max(master.rhi_kpc, 2.0 * rd)
    return max(3.0 * rd, 1.5)


def geometric_tortuosity(
    master: GalaxyMasterLike,
    radius_kpc: float,
    *,
    options: DerivedDynamicsOptions = DerivedDynamicsOptions(),
) -> tuple[float, float]:
    """Geometry-only tortuosity (no activity / seed class).

    τ = (R_d / r) · (1 + sin²θ_mis) / max(cos i, γ)
    """
    rd = max(master.rdisk_kpc, 0.08)
    r = max(radius_kpc, 0.05)
    inc = max(master.inclination_deg, 5.0)
    cos_i = max(math.cos(math.radians(inc)), GAMMA)
    catalog = options.filament_catalog
    env = _fil.resolve_filament_environment(master, catalog)
    spin = _fil.disk_spin_unit(master.inclination_deg)
    mis = _fil.misalignment_sin(spin, env.unit())
    tort = (rd / r) * (1.0 + mis * mis) / cos_i
    return tort, mis


def geometric_coherence(
    master: GalaxyMasterLike,
    radius_kpc: float,
    *,
    options: DerivedDynamicsOptions = DerivedDynamicsOptions(),
) -> tuple[float, float, float]:
    """C = exp(−τ · (1/γ)); returns (coherence, tortuosity, misalignment_sin)."""
    tort, mis = geometric_tortuosity(master, radius_kpc, options=options)
    return math.exp(-tort * options.tortuosity_scale), tort, mis


def thermal_screen_length_m(
    v_circ_m_s: float,
    *,
    phi_hom: float | None = None,
) -> float:
    """Virial/thermal screen length ℓ_th = v²/φ_hom (m)."""
    ph = phi_hom if phi_hom is not None else phi_acceleration_homogeneous_derived_si()
    v = max(abs(v_circ_m_s), 1.0)
    return (v * v) / max(ph, 1.0e-30)


def local_thermal_hotness(radius_kpc: float, rdisk_kpc: float) -> float:
    """Local hotness from the disk radial gradient: 1 at centre → 0 at edge.

    Isolated disks are hotter toward the centre and colder toward the edge
    (interactions can invert this; not modelled here). Same Kirchhoff factor
    as the cosmic floor envelope.
    """
    rd = max(rdisk_kpc, 0.05)
    r = max(radius_kpc, 0.0)
    return 1.0 / (1.0 + r / rd)


def thermal_scale_radius_kpc(master: GalaxyMasterLike) -> float:
    """Optical/thermal extent for the Rindler gate budget.

    Uses max(R_d, R_eff): exponential-disk scale alone under-states the lit
    half-light region on extended/rising systems (e.g. UGC11557 R_eff ≫ R_d).
    Continuous SPARC geometry — no morphology case.
    """
    rd = max(getattr(master, "rdisk_kpc", 0.0) or 0.0, 0.05)
    reff = max(getattr(master, "reff_kpc", 0.0) or 0.0, 0.0)
    return max(rd, reff, 0.05)


def thermal_screen_retention(
    v_circ_m_s: float,
    radius_kpc: float,
    rdisk_kpc: float,
    *,
    phi_hom: float | None = None,
    scale_radius_kpc: float | None = None,
) -> tuple[float, float, float, float]:
    """Local Lean-style Rindler thermal gate (hot centre, cold edge).

    Galaxy-scale hotness budget from ℓ_th = v²/φ_hom vs thermal scale
    R_th = max(R_d, R_eff), modulated by the local radial gradient so the
    centre loses screen distance first:

        A₀ = max(0, R_th/ℓ_th − 1)
        h(r) = 1/(1 + r/R_d)          # hotness: centre → edge
        A_R(r) = A₀ · h(r)
        C_th(r) = 1 / (1 + (γ/2) A_R)

    Cool/fast disks (ℓ_th ≳ R_th) keep C_th = 1 everywhere. Hot dwarfs suppress
    φ near the centre and recover toward the cold outer disk. Mirrors Lean
    ``galaxyThermalScreenRetention`` / ``c_rindler_shared`` in
    ``OrbitalFlybyScaffold`` / ``hqivIRUVVacuumDivergenceLimit``.

    Returns (C_th, ℓ_th_m, A_R, h).
    """
    l_th = thermal_screen_length_m(v_circ_m_s, phi_hom=phi_hom)
    r_th = max(
        scale_radius_kpc if scale_radius_kpc is not None else rdisk_kpc,
        0.05,
    )
    a0 = max(0.0, (r_th * KPC) / max(l_th, 1.0) - 1.0)
    h = local_thermal_hotness(radius_kpc, rdisk_kpc)
    activity = a0 * h
    c_th = 1.0 / (1.0 + (GAMMA / 2.0) * activity)
    return c_th, l_th, activity, h


def characteristic_circular_speed_m_s(master: GalaxyMasterLike) -> float:
    """Galaxy-scale speed for thermal length when no local V is supplied."""
    if master.vflat_kms > 5.0:
        return master.vflat_kms * 1.0e3
    # Fallback: HI-rich dwarfs often lack Vflat; use a soft floor from L36.
    # Still continuous — no morphology case.
    l36 = max(master.L36_e9_lsun, 0.01)
    return max(15.0, 40.0 * (l36**0.25)) * 1.0e3


def phi_cosmic_radial_derived(
    radius_kpc: float,
    rdisk_kpc: float,
    *,
    phi_hom: float | None = None,
) -> float:
    """Kirchhoff radial floor at propagation band: φ_hom / (1 + r/R_d)."""
    ph = phi_hom if phi_hom is not None else phi_acceleration_homogeneous_derived_si()
    rd = max(rdisk_kpc, 0.05)
    r = max(radius_kpc, 0.05)
    return ph / (1.0 + r / rd)


def derived_phi_part(
    master: GalaxyMasterLike,
    radius_kpc: float,
    *,
    options: DerivedDynamicsOptions = DerivedDynamicsOptions(),
    v_circ_m_s: float | None = None,
) -> DerivedPhiState:
    """Single derived φ equation — geometry + local thermal screen gradient."""
    cosmo = proton_pin_cosmology()
    phi_hom = cosmo.phi_hom_m_s2
    r = max(radius_kpc, 0.05)
    rd = max(master.rdisk_kpc, 0.08)
    r_fil = filament_radius_kpc(master)
    rho = gas_baryon_fraction(
        master,
        upsilon_disk=options.upsilon_disk,
        upsilon_bul=options.upsilon_bul,
    )
    b_hom = (
        _hcf.homogeneous_curvature_budget_at_xi(XI_PROPAGATION, rho)
        if options.use_homogeneous_dress
        else 1.0
    )
    phi_cosmic = phi_cosmic_radial_derived(r, rd, phi_hom=phi_hom) * b_hom
    shape = _pinch.solar_whim_boundary_shape(options.m_ism, options.m_whim)
    coherence, tort, mis = geometric_coherence(master, r, options=options)
    env = _fil.resolve_filament_environment(master, options.filament_catalog)
    envelope = 1.0 / (1.0 + r / r_fil)
    gate = _smooth_radial_gate(r, rd, r_fil)
    if options.use_whim_boundary:
        phi_bdy = phi_hom * shape * coherence * envelope * gate
    else:
        phi_bdy = 0.0

    # Galaxy-scale V for ℓ_th (Vflat / L36); local V only if Vflat missing.
    # Radial gradient is carried by h(r), not by feeding v(r) into ℓ_th.
    v_circ = (
        characteristic_circular_speed_m_s(master)
        if master.vflat_kms > 5.0 or v_circ_m_s is None
        else v_circ_m_s
    )
    r_th = thermal_scale_radius_kpc(master)
    if options.use_thermal_screen:
        c_th, l_th_m, a_th, _hot = thermal_screen_retention(
            v_circ, r, rd, phi_hom=phi_hom, scale_radius_kpc=r_th
        )
    else:
        c_th, l_th_m, a_th = 1.0, thermal_screen_length_m(v_circ, phi_hom=phi_hom), 0.0

    # Hot centre loses screen distance; cold edge recovers (C_th → 1).
    phi_combined = (phi_cosmic + phi_bdy) * c_th
    return DerivedPhiState(
        radius_kpc=r,
        phi_hom_m_s2=phi_hom,
        phi_cosmic_m_s2=phi_cosmic * c_th,
        phi_boundary_m_s2=phi_bdy * c_th,
        phi_combined_m_s2=phi_combined,
        gas_fraction=rho,
        b_hom=b_hom,
        solar_whim_boundary_shape=shape,
        geometric_coherence=coherence,
        geometric_tortuosity=tort,
        misalignment_sin=mis,
        filament_radius_kpc=r_fil,
        filament_source=env.source,
        xi_propagation=XI_PROPAGATION,
        thermal_length_kpc=l_th_m / KPC,
        thermal_activity=a_th,
        thermal_screen_retention=c_th,
    )


def _smooth_radial_gate(r: float, rd: float, r_fil: float) -> float:
    """Smooth gate from disk scale to filament scale; width set by γ."""
    lo = rd
    hi = max(r_fil, rd * (1.0 + 1.0 / GAMMA))
    if hi <= lo:
        return 1.0 if r >= hi else 0.0
    t = max(0.0, min(1.0, (r - lo) / (hi - lo)))
    return t * t * (3.0 - 2.0 * t)


def hqiv_rotation_point_derived(
    radius_m: float,
    a_baryonic_m_s2: float,
    master: GalaxyMasterLike,
    *,
    options: DerivedDynamicsOptions = DerivedDynamicsOptions(),
    projection: float = 1.0,
    support_fraction: float = 1.0,
    use_rindler_denominator: bool = True,
) -> dict[str, float]:
    """Circular-speed point from derived φ + Lean inertia/Doppler."""
    r_m = max(radius_m, 1.0)
    a_b = max(a_baryonic_m_s2, 0.0)
    v_b = math.sqrt(a_b * r_m)
    eps = _gal.mass_horizon_doppler_lapse(
        v_b,
        projection=projection,
        support_fraction=support_fraction,
        use_rindler_denominator=use_rindler_denominator,
    )
    # Local baryonic speed only as fallback when Vflat is missing.
    v_therm = v_b if v_b > 1.0e3 else None
    state = derived_phi_part(
        master, r_m / KPC, options=options, v_circ_m_s=v_therm
    )
    phi_full = state.phi_combined_m_s2 + 6.0 * a_b * eps
    f_full = _gal.hqiv_inertia_factor(a_b, phi_full)
    a_hqiv = a_b / max(f_full, 1.0e-30)
    v_hqiv = math.sqrt(max(a_hqiv * r_m, 0.0))
    return {
        "v_baryonic_kms": v_b / 1.0e3,
        "v_hqiv_kms": v_hqiv / 1.0e3,
        "baryonic_accel_m_s2": a_b,
        "hqiv_accel_m_s2": a_hqiv,
        "inertia_factor_full": f_full,
        "one_minus_f_full": max(0.0, 1.0 - f_full),
        "epsilon_doppler": eps,
        "phi_accel_si": state.phi_combined_m_s2,
        "phi_whim_m_s2": state.phi_boundary_m_s2,
        "phi_hom_m_s2": state.phi_hom_m_s2,
        "gas_fraction": state.gas_fraction,
        "b_hom": state.b_hom,
        "geometric_coherence": state.geometric_coherence,
        "misalignment_sin": state.misalignment_sin,
        "solar_whim_boundary_shape": state.solar_whim_boundary_shape,
        "thermal_screen_retention": state.thermal_screen_retention,
        "thermal_length_kpc": state.thermal_length_kpc,
        "thermal_activity": state.thermal_activity,
    }


def galaxy_derived_metadata(
    master: GalaxyMasterLike,
    *,
    options: DerivedDynamicsOptions = DerivedDynamicsOptions(),
) -> dict[str, object]:
    r_mid = max(master.rdisk_kpc, 0.5)
    state = derived_phi_part(master, r_mid, options=options)
    cosmo = proton_pin_cosmology()
    return {
        "dynamics": "derived_proton_pin",
        "cosmology": cosmo.as_dict(),
        "state_at_rdisk": state.as_dict(),
        "legacy_phi_hom_m_s2": _gal.phi_acceleration_homogeneous_si(),
        "phi_hom_ratio_derived_over_legacy": cosmo.phi_hom_m_s2
        / max(_gal.phi_acceleration_homogeneous_si(), 1.0e-30),
        "lean_modules": [
            "Hqiv.Physics.HQIVFluidClosureScaffold.hqivFluidInertiaFactor",
            "Hqiv.Physics.SolarDynamics.solarWhimBoundaryShape",
            "Hqiv.Physics.HomogeneousCurvatureSecondOrder.homogeneousCurvatureBudgetAtXi",
            "Hqiv.Physics.OrbitalFlybyScaffold.flybyPropagationXi",
            "Hqiv.Geometry.UniverseAge / CosmologicalShellLadder (via cmb_age_lockdown)",
        ],
    }


def main() -> int:
    cosmo = proton_pin_cosmology()
    print("Proton-pin cosmology")
    for k, v in cosmo.as_dict().items():
        print(f"  {k}: {v}")
    print(
        f"  legacy φ_hom: {_gal.phi_acceleration_homogeneous_si():.6e} m/s²  "
        f"ratio derived/legacy: "
        f"{cosmo.phi_hom_m_s2 / _gal.phi_acceleration_homogeneous_si():.4f}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

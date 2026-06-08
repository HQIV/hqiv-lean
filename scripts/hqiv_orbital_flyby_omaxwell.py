#!/usr/bin/env python3
"""
HQIV orbital flyby calculator — rotating body + O-Maxwell probe layer.

Classical core (SI):
  • Newtonian gravity with optional J2 oblateness (spin-aligned z axis)
  • Coriolis + centrifugal terms when integrating in a planet-fixed rotating frame

HQIV layer (mirrors Lean / chart docs; no PDG mass injection):
  • φ(m) = 2(m+1)  (`Hqiv/Geometry/AuxiliaryField.lean`)
  • α = 3/5, γ = 2/5  (`OctonionicLightCone`, fluid F2)
  • Vacuum momentum source g_vac = -(γ/6)(φ ∇dot + dot ∇φ)
  • Inertia screen f(a,φ)=a/(a+φ/6) with **direction-dependent** weighting:
    equatorial |L_z| locks the Brodie channel; polar / low-h_z exits weaken the screen
    (paper main.tex: direction-dependent inertia; hyperboloid fiber latitude).
  • O-Maxwell metric-φ slot; G_eff ratio (φ/φ_ref)^α on Newton (`GRFromMaxwell.lean`)

Purpose: integrate hyperbolic encounters (Earth flybys, quiet interstellar Sun passages)
and report asymptotic Δv so HQIV corrections can be compared to mm/s-scale anomalies.

Oblate / asymptote geometry (spin axis = +z):
  • Inbound asymptote: (inbound_lat_deg, inbound_lon_deg) — e.g. equator = 0°
  • Impact-parameter orientation: b_azimuth_deg in the plane ⊥ to inbound direction
  • Outbound asymptote latitude is a **result** (pole exit maximizes |Δλ| for J₂/HQIV)

Usage:
  python3 scripts/hqiv_orbital_flyby_omaxwell.py --case equator_to_pole
  python3 scripts/hqiv_orbital_flyby_omaxwell.py --scan-oblate
  python3 scripts/hqiv_orbital_flyby_omaxwell.py --case galileo_1990 --inbound-lat 0 --b-azimuth 90
  python3 scripts/hqiv_orbital_flyby_omaxwell.py --catalog interstellar --case oumuamua_2017
  python3 scripts/hqiv_orbital_flyby_omaxwell.py --catalog all --run-all --paper-nominal
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass, field, replace
from datetime import date, datetime, timezone
from functools import lru_cache
from pathlib import Path
from typing import Callable, Iterable, Sequence

from fluid_f2_chart_alignment import vacuum_momentum_source3

try:
    import hqiv_phase_geometry_density as pgd
except ImportError:
    pgd = None  # type: ignore[assignment]

Vec3 = tuple[float, float, float]
Quat = tuple[float, float, float, float]

# --- HQIV constants (Lean mirrors) -------------------------------------------------

ALPHA_HQIV = 3.0 / 5.0
GAMMA_HQIV = 2.0 / 5.0

# Near-pole propagation-shell index for the solar-system band.  Kirchhoff
# (finite_mode_kirchhoff paper, m_prop ~ 0.01 at the CMB observer) separates
# lock-in shell referenceM=4 (hadron mass chart) from the observer propagation
# coordinate shared by all solar-system Doppler / lapse readouts.
SOLAR_SYSTEM_PROP_SHELL = 0


def phi_of_shell(m: int) -> float:
    return 2.0 * (float(m) + 1.0)


def propagation_shell_for_orbitals() -> int:
    """Discrete propagation-shell index for solar-system orbital mechanics."""
    return SOLAR_SYSTEM_PROP_SHELL


def shell_equatorial_fraction_floor(m_shell: int) -> float:
    """
    Minimum equatorial angular-momentum fraction on the discrete ladder.

    Lean: T(m) = 1/(m+1) ⇒ one shell step is Δ(1/T) = 1; floor (h_z/h)²_min = 1/(m+1)².
    """
    m = max(int(m_shell), 0)
    return 1.0 / float(m + 1) ** 2


def polar_fiber_phi_boost(
    h_z: float,
    h: float,
    h_ref: float,
    rho_pol: float,
    m_shell: int,
) -> float:
    """
    Multiplier on φ_loc for the polar inertia channel.

    Shell ladder step (m+1) sets two smooth floors (no max(h_z, ε)):
    * **Asymptotic lock:** h_z,eff² = h_z² + (h_ref/(m+1))² → release when |L_z| is weak vs b v_∞.
    * **Local fiber:** h_z,eff² = h_z² + (h/(m+1))² → release near polar velocity orientation.

    φ_pol/φ_loc = 1 + ρ_pol × max(release_asym, release_loc); each release is
    [h²_*/h_z,eff² − 1]_+ and saturates at (m+1)²−1 when h_z→0.
    """
    m1 = float(max(int(m_shell), 0) + 1)
    h_ref = max(h_ref, 1e-9)
    h = max(h, 1e-9)
    h_z_asym_sq = h_z * h_z + (h_ref / m1) ** 2
    rel_asym = max(0.0, (h_ref * h_ref) / h_z_asym_sq - 1.0)
    h_z_loc_sq = h_z * h_z + (h / m1) ** 2
    rel_loc = max(0.0, (h * h) / h_z_loc_sq - 1.0)
    return 1.0 + rho_pol * max(rel_asym, rel_loc)


def impact_parameter_from_periapsis(q: float, v_inf: float, gm: float) -> float:
    """Hyperbolic impact parameter b from periapsis distance q, v_∞, and GM."""
    if q <= 0.0 or v_inf <= 0.0 or gm <= 0.0:
        return float("nan")
    e_minus_1 = q * v_inf * v_inf / gm
    eccentricity = 1.0 + e_minus_1
    x = math.sqrt(max(eccentricity * eccentricity - 1.0, 0.0))
    return x * gm / (v_inf * v_inf)


def coupling_log(phi: float) -> float:
    """Algebra-first O-Maxwell log slot: log(φ+1) at the evaluation point."""
    return math.log(max(phi, 0.0) + 1.0)


# --- SI Earth defaults -------------------------------------------------------------

GM_EARTH = 3.986004418e14  # m^3/s^2
R_EARTH = 6.378137e6  # m equatorial
J2_EARTH = 1.08263e-3
OMEGA_EARTH = 7.2921159e-5  # rad/s (spin about +z)
GM_SUN = 1.32712440018e20  # m^3/s^2
GM_MOON = 4.9048695e12  # m^3/s^2
R_SUN = 6.957e8  # m
SOLAR_ROTATION_PERIOD_DAYS = 25.38  # sidereal equatorial spin period
OMEGA_SUN = 2.0 * math.pi / (SOLAR_ROTATION_PERIOD_DAYS * 86_400.0)
MOON_SEMIMAJOR_AXIS = 384_400_000.0  # m
AU = 1.495978707e11  # m
V_EARTH_ORBIT = 29_780.0  # m/s
OBLIQUITY_RAD = math.radians(23.439281)
C_LIGHT = 299_792_458.0  # m/s
G_NEWTON = 6.67430e-11  # m^3 kg^-1 s^-2
KPC = 3.0856775814913673e19  # m
M_SUN_KG = 1.98847e30  # kg
GALACTIC_R0 = 8.2 * KPC  # Sun galactocentric radius
GALACTIC_VC = 233_000.0  # m/s circular speed at the Sun
MILKY_WAY_DISK_MASS = 6.0e10 * M_SUN_KG  # representative baryonic disk mass
MILKY_WAY_DISK_SCALE = 2.6 * KPC  # exponential disk scale length
GALACTIC_NORTH_RA_DEG = 192.85948
GALACTIC_NORTH_DEC_DEG = 27.12825
GALACTIC_CENTER_RA_DEG = 266.4051
GALACTIC_CENTER_DEC_DEG = -28.936175
# Hubble rate (s⁻¹); φ_hom ≈ 2cH in the HQVM homogeneous limit (paper main.tex).
H0_SI = 2.27e-18


def _dot(a: Vec3, b: Vec3) -> float:
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]


def _cross(a: Vec3, b: Vec3) -> Vec3:
    return (
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0],
    )


def _norm(a: Vec3) -> float:
    return math.sqrt(_dot(a, a))


def _add(a: Vec3, b: Vec3, scale: float = 1.0) -> Vec3:
    return (a[0] + scale * b[0], a[1] + scale * b[1], a[2] + scale * b[2])


def _scale(a: Vec3, s: float) -> Vec3:
    return (a[0] * s, a[1] * s, a[2] * s)


def _unit(a: Vec3) -> Vec3:
    n = _norm(a)
    if n <= 0.0:
        return (0.0, 0.0, 1.0)
    return _scale(a, 1.0 / n)


def _quat_mul(a: Quat, b: Quat) -> Quat:
    aw, ax, ay, az = a
    bw, bx, by, bz = b
    return (
        aw * bw - ax * bx - ay * by - az * bz,
        aw * bx + ax * bw + ay * bz - az * by,
        aw * by - ax * bz + ay * bw + az * bx,
        aw * bz + ax * by - ay * bx + az * bw,
    )


def _quat_conj(q: Quat) -> Quat:
    return (q[0], -q[1], -q[2], -q[3])


def quat_from_unit_vectors(a: Vec3, b: Vec3) -> Quat:
    """Unit quaternion rotating unit vector `a` into unit vector `b`."""
    au = _unit(a)
    bu = _unit(b)
    c = max(-1.0, min(1.0, _dot(au, bu)))
    if c > 1.0 - 1.0e-14:
        return (1.0, 0.0, 0.0, 0.0)
    if c < -1.0 + 1.0e-14:
        axis = _unit(_cross(au, (1.0, 0.0, 0.0)))
        if _norm(axis) <= 1.0e-12:
            axis = _unit(_cross(au, (0.0, 1.0, 0.0)))
        return (0.0, axis[0], axis[1], axis[2])
    axis = _cross(au, bu)
    s = math.sqrt((1.0 + c) * 2.0)
    inv_s = 1.0 / s
    return (0.5 * s, axis[0] * inv_s, axis[1] * inv_s, axis[2] * inv_s)


def quat_rotate(q: Quat, v: Vec3) -> Vec3:
    """Rotate vector `v` by unit quaternion `q`."""
    rotated = _quat_mul(_quat_mul(q, (0.0, v[0], v[1], v[2])), _quat_conj(q))
    return (rotated[1], rotated[2], rotated[3])


def unit_from_lat_lon(lat_deg: float, lon_deg: float) -> Vec3:
    """Geocentric unit vector (z = spin pole); lat/lon in degrees."""
    lat = math.radians(lat_deg)
    lon = math.radians(lon_deg)
    cl = math.cos(lat)
    return (cl * math.cos(lon), cl * math.sin(lon), math.sin(lat))


def latitude_deg_of_vector(v: Vec3) -> float:
    n = _norm(v)
    if n <= 0.0:
        return 0.0
    return math.degrees(math.asin(max(-1.0, min(1.0, v[2] / n))))


def longitude_deg_of_vector(v: Vec3) -> float:
    return math.degrees(math.atan2(v[1], v[0]))


def angle_between_deg(a: Vec3, b: Vec3) -> float:
    na, nb = _norm(a), _norm(b)
    if na <= 0.0 or nb <= 0.0:
        return 0.0
    c = _dot(a, b) / (na * nb)
    return math.degrees(math.acos(max(-1.0, min(1.0, c))))


def equatorial_phi_hat(r: Vec3) -> Vec3:
    """Azimuthal unit vector (∂/∂φ) in the equatorial sense; zero near the poles."""
    rho = math.hypot(r[0], r[1])
    if rho < 1e-14:
        return (0.0, 0.0, 0.0)
    return (-r[1] / rho, r[0] / rho, 0.0)


def spin_axis_unit(body: "RotatingBody") -> Vec3:
    """Unit spin axis in J2000 equatorial coordinates (+z if unset)."""
    if body.spin_axis_hat is not None:
        return _unit(body.spin_axis_hat)
    return (0.0, 0.0, 1.0)


def spin_colatitude_sin_sq(r: Vec3, body: "RotatingBody") -> float:
    """sin²(colatitude) relative to the body spin axis."""
    r_mag = _norm(r)
    if r_mag <= 0.0:
        return 0.0
    cos_pol = abs(_dot(_scale(r, 1.0 / r_mag), spin_axis_unit(body)))
    return max(0.0, 1.0 - min(1.0, cos_pol * cos_pol))


def co_spin_tangent_hat(r: Vec3, body: "RotatingBody", spin_sign: float = 1.0) -> Vec3:
    """Unit vector along ω×r̂ (frame-drag tangent direction)."""
    r_mag = max(_norm(r), 1.0e-30)
    r_hat = _scale(r, 1.0 / r_mag)
    omega_vec = _scale(body.spin_vector(), spin_sign)
    drag = _cross(omega_vec, r_hat)
    mag = _norm(drag)
    if mag <= 1.0e-30:
        return (0.0, 0.0, 0.0)
    return _scale(drag, 1.0 / mag)


@dataclass(frozen=True)
class VisibleSourceQuadrature:
    """Solid-angle weighted readout over the visible face of an extended source."""

    angular_step_deg: float
    n_visible_samples: int
    angular_radius_deg: float
    angular_diameter_deg: float
    solid_angle_sr: float
    analytic_solid_angle_sr: float
    covered_sky_fraction: float
    visible_hemisphere_fraction: float
    mean_signed_tangent_projection: float
    mean_tangent_projection: float
    mean_corotating_projection: float
    mean_counterrotating_projection: float
    mean_sin2_colatitude: float
    mean_signed_spin_lapse_shape: float
    mean_spin_lapse_shape: float
    mean_counter_spin_lapse_shape: float
    mean_lense_thirring_shape: float


@dataclass(frozen=True)
class CoveredChordQuadrature:
    """Quaternion-projected ray integral through the covered source volume."""

    angular_step_deg: float
    chord_samples: int
    n_rays: int
    angular_radius_deg: float
    angular_diameter_deg: float
    solid_angle_sr: float
    analytic_solid_angle_sr: float
    covered_sky_fraction: float
    mean_chord_length_m: float
    total_volume_weight_m3: float
    mean_near_signed_projection: float
    mean_far_signed_projection: float
    mean_endpoint_net_projection: float
    mean_volume_signed_projection: float
    mean_volume_corotating_projection: float
    mean_volume_counterrotating_projection: float
    mean_volume_signed_spin_shape: float
    mean_volume_spin_shape: float
    total_mass_weight_m3: float


def chord_ray_grid_key(
    r_mag: float,
    body: RotatingBody,
    *,
    angular_step_deg: float,
) -> tuple[int, int]:
    """
    Discrete ray-grid size for ``covered_chord_quadrature`` at this radius.

    Quadrature is repeated only when this key changes (new chords enter the disk).
    """
    radius = max(body.radius, 1.0)
    if r_mag <= radius:
        return (0, 0)
    step = max(float(angular_step_deg), 0.05)
    alpha_deg = math.degrees(math.asin(min(1.0, radius / r_mag)))
    n_rho = max(1, int(math.ceil(alpha_deg / step)))
    n_psi = max(1, int(math.ceil(360.0 / step)))
    return (n_rho, n_psi)


def _surface_signed_tangent_projection(point: Vec3, v_hat: Vec3, omega_vec: Vec3) -> float:
    tangent = _cross(omega_vec, point)
    if _norm(tangent) <= 0.0:
        return 0.0
    return _dot(v_hat, _unit(tangent))


def covered_chord_quadrature(
    r_probe: Vec3,
    v_probe: Vec3,
    body: RotatingBody,
    *,
    angular_step_deg: float = 1.0,
    chord_samples: int = 8,
    spin_sign: float = 1.0,
) -> CoveredChordQuadrature:
    """
    Project angular rays through an extended spherical source and mass-weight the chord.

    Rays are sampled over the apparent angular disk using quaternion rotations from the
    boresight.  Each segment carries uniform-density volume ``dV = s² ds dΩ`` and an
  additional inverse-square weight ``(R_⊕/|r_probe - x|)²`` so the nearest baryonic
    column dominates.  Endpoint moments expose near/far surface cancellation; volume
    moments feed the source-shell gate.
    """
    r_obs = _norm(r_probe)
    radius = max(body.radius, 1.0)
    if r_obs <= radius:
        raise ValueError("probe must be outside the source surface")

    step = max(float(angular_step_deg), 0.05)
    n_rho = max(1, int(math.ceil(math.degrees(math.asin(min(1.0, radius / r_obs))) / step)))
    n_psi = max(1, int(math.ceil(360.0 / step)))
    alpha = math.asin(min(1.0, radius / r_obs))
    q_boresight = quat_from_unit_vectors((0.0, 0.0, 1.0), _scale(_unit(r_probe), -1.0))
    v_hat = _unit(v_probe)
    omega_vec = _scale(body.spin_vector(), spin_sign)
    n_chord = max(1, int(chord_samples))
    r_floor = radius

    solid_angle = 0.0
    chord_weight = 0.0
    endpoint_mass_weight = 0.0
    volume_mass_weight = 0.0
    volume_geom = 0.0
    near_signed = 0.0
    far_signed = 0.0
    endpoint_net = 0.0
    volume_signed = 0.0
    volume_co = 0.0
    volume_counter = 0.0
    volume_signed_shape = 0.0
    volume_abs_shape = 0.0
    n_rays = 0

    for i in range(n_rho):
        rho0 = i * alpha / n_rho
        rho1 = (i + 1) * alpha / n_rho
        rho = 0.5 * (rho0 + rho1)
        d_rho = rho1 - rho0
        sin_rho = math.sin(rho)
        for j in range(n_psi):
            psi = (j + 0.5) * 2.0 * math.pi / n_psi
            local_ray = (sin_rho * math.cos(psi), sin_rho * math.sin(psi), math.cos(rho))
            ray = _unit(quat_rotate(q_boresight, local_ray))
            b = 2.0 * _dot(r_probe, ray)
            c = _dot(r_probe, r_probe) - radius * radius
            disc = b * b - 4.0 * c
            if disc <= 0.0:
                continue
            root = math.sqrt(disc)
            t_near = (-b - root) / 2.0
            t_far = (-b + root) / 2.0
            if t_far <= 0.0 or t_near < 0.0:
                continue

            d_omega = sin_rho * d_rho * (2.0 * math.pi / n_psi)
            chord = t_far - t_near
            near_point = _add(r_probe, ray, t_near)
            far_point = _add(r_probe, ray, t_far)
            near_proj = _surface_signed_tangent_projection(near_point, v_hat, omega_vec)
            far_proj = _surface_signed_tangent_projection(far_point, v_hat, omega_vec)
            near_grav = (radius / max(t_near, r_floor)) ** 2
            far_grav = (radius / max(t_far, r_floor)) ** 2
            d_mass_near = d_omega * chord * near_grav
            d_mass_far = d_omega * chord * far_grav

            solid_angle += d_omega
            chord_weight += d_omega * chord
            endpoint_mass_weight += d_mass_near + d_mass_far
            near_signed += d_mass_near * near_proj
            far_signed += d_mass_far * far_proj
            endpoint_net += 0.5 * (d_mass_near * near_proj + d_mass_far * far_proj)
            n_rays += 1

            dt = chord / n_chord
            for k in range(n_chord):
                t = t_near + (k + 0.5) * dt
                point = _add(r_probe, ray, t)
                proj = _surface_signed_tangent_projection(point, v_hat, omega_vec)
                sin2_colat = 1.0 - (_unit(point)[2] ** 2)
                d_vol_seg = d_omega * t * t * dt
                volume_geom += d_vol_seg
                grav = (radius / max(t, r_floor)) ** 2
                d_mass = d_vol_seg * grav
                volume_mass_weight += d_mass
                volume_signed += d_mass * proj
                volume_co += d_mass * max(0.0, proj)
                volume_counter += d_mass * max(0.0, -proj)
                volume_signed_shape += d_mass * sin2_colat * proj
                volume_abs_shape += d_mass * sin2_colat * abs(proj)

    analytic_solid_angle = 2.0 * math.pi * (1.0 - math.cos(alpha))
    vol_denom = max(volume_mass_weight, 1.0e-30)
    end_denom = max(endpoint_mass_weight, 1.0e-30)
    return CoveredChordQuadrature(
        angular_step_deg=step,
        chord_samples=n_chord,
        n_rays=n_rays,
        angular_radius_deg=math.degrees(alpha),
        angular_diameter_deg=2.0 * math.degrees(alpha),
        solid_angle_sr=solid_angle,
        analytic_solid_angle_sr=analytic_solid_angle,
        covered_sky_fraction=solid_angle / (4.0 * math.pi),
        mean_chord_length_m=chord_weight / max(solid_angle, 1.0e-30),
        total_volume_weight_m3=max(volume_geom, 1.0e-30),
        mean_near_signed_projection=near_signed / end_denom,
        mean_far_signed_projection=far_signed / end_denom,
        mean_endpoint_net_projection=endpoint_net / end_denom,
        mean_volume_signed_projection=volume_signed / vol_denom,
        mean_volume_corotating_projection=volume_co / vol_denom,
        mean_volume_counterrotating_projection=volume_counter / vol_denom,
        mean_volume_signed_spin_shape=volume_signed_shape / vol_denom,
        mean_volume_spin_shape=volume_abs_shape / vol_denom,
        total_mass_weight_m3=volume_mass_weight + endpoint_mass_weight,
    )


def flyby_source_shell_step(m_shell: int) -> float:
    """Lean ``flybySourceShellStep``: baryonic anchor strength ``m+1``."""
    return float(m_shell + 1)


def propagation_xi_for_orbitals() -> float:
    """Continuous propagation coordinate ξ = m + 1 at the solar-system band."""
    return float(propagation_shell_for_orbitals() + 1)


def orbital_phase_witness(body: "RotatingBody", encounter_radius_m: float) -> object:
    """Planetary phase-geometry witness at encounter radius."""
    if pgd is None:
        raise RuntimeError("hqiv_phase_geometry_density is required for orbital phase geometry")
    return pgd.orbital_phase_witness_from_body(
        label=body.name,
        gm=body.gm,
        radius_m=body.radius,
        encounter_radius_m=encounter_radius_m,
    )


def orbital_curvature_density_at(body: "RotatingBody", encounter_radius_m: float) -> float:
    """ρ_orb from inverse-square local curvature (Lean ``orbitalCurvatureDensityFraction``)."""
    if pgd is None:
        return 0.0
    w = orbital_phase_witness(body, encounter_radius_m)
    return pgd.orbital_curvature_density_fraction(w)


def orbital_curvature_mass_delta_at(body: "RotatingBody", encounter_radius_m: float) -> float:
    """Small dimensionless mass/φ delta: B_hom(ξ_prop, ρ_orb) − 1."""
    if pgd is None:
        return 0.0
    w = orbital_phase_witness(body, encounter_radius_m)
    return pgd.orbital_curvature_mass_delta_fraction(propagation_xi_for_orbitals(), w)


def flyby_dynamic_kappa_phi_from_phase(
    body: "RotatingBody",
    encounter_radius_m: float,
    gate: float,
) -> float:
    """Lean ``flybyDynamicKappaPhiFromPhase``: 1 + gate·(B_hom − 1), no shell-4 pin."""
    if pgd is None:
        return flyby_dynamic_kappa_phi(4, gate)
    w = orbital_phase_witness(body, encounter_radius_m)
    return pgd.flyby_dynamic_kappa_phi_from_phase(
        w, gate, xi=propagation_xi_for_orbitals()
    )


def flyby_dynamic_kappa_phi(m_shell: int, gate: float) -> float:
    """Lean ``flybyDynamicKappaPhi`` (legacy shell index). Prefer phase-geometry variant."""
    g = max(0.0, min(1.0, float(gate)))
    step = flyby_source_shell_step(m_shell)
    return 1.0 + g * (step - 1.0)


def source_shell_kappa(
    body: "RotatingBody",
    encounter_radius_m: float,
    gate: float,
    *,
    use_phase_geometry: bool,
    legacy_m_shell: int,
) -> float:
    """Dynamic κ_φ: phase geometry when enabled, else legacy shell index."""
    if use_phase_geometry:
        return flyby_dynamic_kappa_phi_from_phase(body, encounter_radius_m, gate)
    return flyby_dynamic_kappa_phi(legacy_m_shell, gate)


def source_shell_gate_from_chord(q: CoveredChordQuadrature) -> float:
    """
    Geometry gate for the m=4 source-shell slot.

    With inverse-square mass weights the signed moment can be one-sided even when
    co/counter columns balance; ``gate_cancel`` uses the co/counter mass split.
    ``gate_asym`` tracks endpoint net tangent bias.
    """
    denom = max(q.mean_volume_spin_shape, 1.0e-30)
    co = max(q.mean_volume_corotating_projection, 0.0)
    counter = max(q.mean_volume_counterrotating_projection, 0.0)
    total = co + counter
    if total <= 1.0e-30:
        gate_cancel = 0.0
    else:
        gate_cancel = max(0.0, min(1.0, 4.0 * co * counter / (total * total)))
    gate_asym = max(0.0, min(1.0, abs(q.mean_endpoint_net_projection) / denom))
    return gate_cancel * gate_asym


@dataclass
class FrozenChordGate:
    active: bool = False
    kappa_blend: float = 1.0
    r_ca_m: float = float("inf")
    gate: float = 0.0


@dataclass(frozen=True)
class SpinProjectionAudit:
    """Compare +z spin model vs SPICE IAU pole at a chord quadrature node."""

    t_s: float
    r_mag_m: float
    axis_tilt_deg: float
    proj_z: float
    proj_spice: float
    sign_flip: bool
    n_rays: int


@dataclass
class ChordFlybyTrack:
    """Precomputed κ blend vs radius for smooth whole-flyby chord sourcing."""

    active: bool = False
    r_m: tuple[float, ...] = ()
    kappa_blend: tuple[float, ...] = ()
    r_ca_m: float = float("inf")
    r_escape_m: float = float("inf")
    gate_peak: float = 0.0
    n_track_samples: int = 0
    n_quadrature_calls: int = 0
    spin_audits: tuple[SpinProjectionAudit, ...] = ()


_FROZEN_CHORD_GATE = FrozenChordGate()
_CHORD_FLYBY_TRACK = ChordFlybyTrack()


def clear_chord_kappa_cache() -> None:
    global _FROZEN_CHORD_GATE, _CHORD_FLYBY_TRACK
    _FROZEN_CHORD_GATE = FrozenChordGate()
    _CHORD_FLYBY_TRACK = ChordFlybyTrack()


def _interp_linear(x: float, xs: Sequence[float], ys: Sequence[float]) -> float:
    if not xs:
        return 1.0
    if x <= xs[0]:
        return ys[0]
    if x >= xs[-1]:
        return ys[-1]
    for i in range(len(xs) - 1):
        if xs[i] <= x <= xs[i + 1]:
            span = xs[i + 1] - xs[i]
            if span <= 0.0:
                return ys[i + 1]
            t = (x - xs[i]) / span
            return ys[i] * (1.0 - t) + ys[i + 1] * t
    return ys[-1]


def chord_flyby_envelope(
    r_mag: float,
    r_ca: float,
    body_radius: float,
    r_escape: float,
) -> float:
    """Unit weight through the encounter shell; smooth taper only toward ``r_escape``."""
    del r_ca  # exit emphasis is in the track, not a periapsis spike
    if r_mag > r_escape or r_mag < body_radius:
        return 0.0
    r_plateau = 12.0 * body_radius
    if r_mag <= r_plateau:
        return 1.0
    span = max(r_escape - r_plateau, body_radius)
    return math.exp(-0.5 * ((r_mag - r_plateau) / span) ** 2)


def chord_encounter_window(
    r_mag: float,
    r_ca: float,
    body_radius: float,
    *,
    width_radii: float = 2.0,
) -> float:
    """Legacy CA-localized window (used when ``chord_gate_freeze_at_ca``)."""
    dr = (r_mag - r_ca) / max(body_radius, 1.0)
    return math.exp(-0.5 * (dr / max(width_radii, 0.25)) ** 2)


def prepare_frozen_chord_gate(
    case: FlybyCase,
    body: RotatingBody,
    coupling: HQIVOrbitCoupling,
    settings: PropagationSettings,
    spin_sign: float = 1.0,
) -> FrozenChordGate:
    """Find CA with classical propagation, then freeze chord gate/kappa at that geometry."""
    global _FROZEN_CHORD_GATE
    _FROZEN_CHORD_GATE = FrozenChordGate()
    if not coupling.chord_source_gate or not coupling.chord_gate_freeze_at_ca:
        return _FROZEN_CHORD_GATE

    ca_state, r_ca = find_closest_approach_state(case, body, settings, spin_sign)
    try:
        q = covered_chord_quadrature(
            ca_state.r,
            ca_state.v,
            body,
            angular_step_deg=coupling.chord_gate_step_deg,
            chord_samples=coupling.chord_gate_samples,
            spin_sign=spin_sign,
        )
        gate = source_shell_gate_from_chord(q)
        kappa = source_shell_kappa(
            body,
            _norm(ca_state.r),
            gate,
            use_phase_geometry=coupling.phase_geometry_source,
            legacy_m_shell=coupling.source_kappa_m_shell,
        )
        blend = 1.0 + coupling.chord_gate_strength * (kappa - 1.0)
    except ValueError:
        gate = 0.0
        blend = 1.0
    _FROZEN_CHORD_GATE = FrozenChordGate(True, blend, r_ca, gate)
    return _FROZEN_CHORD_GATE


def verify_spin_projection_at_node(
    r: Vec3,
    v: Vec3,
    body: RotatingBody,
    spice_axis_hat: Vec3,
    *,
    spin_sign: float = 1.0,
    t_s: float = 0.0,
    n_rays: int = 0,
) -> SpinProjectionAudit:
    """Signed ω×r̂·v̂ at a quadrature node: nominal +z vs SPICE pole."""
    z_body = body
    spice_body = replace(body, spin_axis_hat=_unit(spice_axis_hat))
    v_hat = _unit(v)
    proj_z = _surface_signed_tangent_projection(
        r, v_hat, _scale(z_body.spin_vector(), spin_sign)
    )
    proj_spice = _surface_signed_tangent_projection(
        r, v_hat, _scale(spice_body.spin_vector(), spin_sign)
    )
    axis_tilt = angle_between_deg((0.0, 0.0, 1.0), _unit(spice_axis_hat))
    sign_flip = proj_z * proj_spice < 0.0 and abs(proj_z) > 1.0e-4 and abs(proj_spice) > 1.0e-4
    return SpinProjectionAudit(
        t_s=t_s,
        r_mag_m=_norm(r),
        axis_tilt_deg=axis_tilt,
        proj_z=proj_z,
        proj_spice=proj_spice,
        sign_flip=sign_flip,
        n_rays=n_rays,
    )


def prepare_chord_flyby_track(
    case: FlybyCase,
    body: RotatingBody,
    coupling: HQIVOrbitCoupling,
    settings: PropagationSettings,
    spin_sign: float = 1.0,
    *,
    spice_spin_axis: Callable[[float], Vec3] | None = None,
) -> ChordFlybyTrack:
    """
    Classical pass: uniform inbound/outbound samples; quadrature only on new chord count.

    Collects states inside the encounter shell, subsamples evenly along the trajectory,
    and reruns ``covered_chord_quadrature`` only when ``q.n_rays`` changes.  Between
    topology plateaus the last κ blend is held while radius samples still advance.
    """
    global _CHORD_FLYBY_TRACK
    _CHORD_FLYBY_TRACK = ChordFlybyTrack()
    if not coupling.chord_source_gate or not coupling.chord_gate_use_track:
        return _CHORD_FLYBY_TRACK

    r_max = coupling.chord_gate_max_radius_factor * max(body.radius, 1.0)
    r_escape = max(settings.r_escape, case.r_start * 0.85)
    collect_stride = max(int(coupling.chord_track_collect_stride), 1)
    n_target = max(int(coupling.chord_track_target_samples), 4)

    state = flyby_initial_state(case, body)
    r_ca = float("inf")
    ca_step = 0
    encounter: list[tuple[float, float, Vec3, Vec3]] = []
    n_steps_max = int(settings.t_max / settings.dt)

    for step in range(n_steps_max):
        r_mag = _norm(state.r)
        radial_motion = _dot(state.r, state.v) / max(r_mag, 1.0)
        if r_mag < r_ca:
            r_ca = r_mag
            ca_step = step
        if r_mag <= r_max and step % collect_stride == 0:
            encounter.append((r_mag, state.t, state.r, state.v))
        state = rk4_step(state, body, None, settings, spin_sign, case)
        if (
            step > ca_step + 20
            and r_mag >= r_escape
            and radial_motion > 0.0
        ):
            break

    if not encounter:
        return _CHORD_FLYBY_TRACK

    n_enc = len(encounter)
    if n_enc <= n_target:
        picks = list(range(n_enc))
    else:
        picks = [
            int(round(k * (n_enc - 1) / (n_target - 1))) for k in range(n_target)
        ]
    ca_enc_idx = min(range(n_enc), key=lambda i: encounter[i][0])
    pick_set = set(picks)
    pick_set.add(ca_enc_idx)
    picks = sorted(pick_set)

    samples_r: list[float] = []
    samples_k: list[float] = []
    audits: list[SpinProjectionAudit] = []
    gate_peak = 0.0
    last_n_rays = -1
    last_grid_key: tuple[int, int] | None = None
    last_blend = 1.0
    n_quadrature_calls = 0
    step_deg = coupling.chord_gate_step_deg

    for idx in picks:
        r_mag, t_s, r_vec, v_vec = encounter[idx]
        grid_key = chord_ray_grid_key(r_mag, body, angular_step_deg=step_deg)
        if grid_key == (0, 0):
            continue
        quad_body = body
        if spice_spin_axis is not None:
            quad_body = replace(body, spin_axis_hat=_unit(spice_spin_axis(t_s)))
        try:
            if last_grid_key is None or grid_key != last_grid_key:
                q = covered_chord_quadrature(
                    r_vec,
                    v_vec,
                    quad_body,
                    angular_step_deg=step_deg,
                    chord_samples=coupling.chord_gate_samples,
                    spin_sign=spin_sign,
                )
                last_grid_key = grid_key
                if q.n_rays != last_n_rays:
                    gate = source_shell_gate_from_chord(q)
                    gate_peak = max(gate_peak, gate)
                    kappa = source_shell_kappa(
                        body,
                        r_mag,
                        gate,
                        use_phase_geometry=coupling.phase_geometry_source,
                        legacy_m_shell=coupling.source_kappa_m_shell,
                    )
                    last_blend = 1.0 + coupling.chord_gate_strength * (kappa - 1.0)
                    last_n_rays = q.n_rays
                    n_quadrature_calls += 1
                if spice_spin_axis is not None:
                    audits.append(
                        verify_spin_projection_at_node(
                            r_vec,
                            v_vec,
                            body,
                            spice_spin_axis(t_s),
                            spin_sign=spin_sign,
                            t_s=t_s,
                            n_rays=q.n_rays,
                        )
                    )
            samples_r.append(r_mag)
            samples_k.append(last_blend)
        except ValueError:
            continue

    if not samples_r:
        return _CHORD_FLYBY_TRACK

    paired = sorted(zip(samples_r, samples_k), key=lambda pair: pair[0])
    r_m = tuple(r for r, _ in paired)
    kappa_blend = tuple(k for _, k in paired)
    _CHORD_FLYBY_TRACK = ChordFlybyTrack(
        active=True,
        r_m=r_m,
        kappa_blend=kappa_blend,
        r_ca_m=r_ca,
        r_escape_m=r_escape,
        gate_peak=gate_peak,
        n_track_samples=len(r_m),
        n_quadrature_calls=n_quadrature_calls,
        spin_audits=tuple(audits),
    )
    return _CHORD_FLYBY_TRACK


def chord_horizon_kappa_factor(
    r: Vec3,
    v: Vec3,
    body: RotatingBody,
    coupling: HQIVOrbitCoupling,
    spin_sign: float = 1.0,
    *,
    settings: PropagationSettings | None = None,
    case: FlybyCase | None = None,
) -> float:
    """Dynamic ``K_φ(m_s,g_s)`` from chord quadrature; unity when gate is off or far."""
    if not coupling.chord_source_gate:
        return 1.0
    r_mag = _norm(r)
    if r_mag > coupling.chord_gate_max_radius_factor * max(body.radius, 1.0):
        return 1.0

    if coupling.chord_gate_use_track and _CHORD_FLYBY_TRACK.active:
        kappa_target = _interp_linear(
            r_mag, _CHORD_FLYBY_TRACK.r_m, _CHORD_FLYBY_TRACK.kappa_blend
        )
        w = chord_flyby_envelope(
            r_mag,
            _CHORD_FLYBY_TRACK.r_ca_m,
            body.radius,
            _CHORD_FLYBY_TRACK.r_escape_m,
        )
        return 1.0 + w * (kappa_target - 1.0)

    if coupling.chord_gate_freeze_at_ca:
        if not _FROZEN_CHORD_GATE.active:
            return 1.0
        w = chord_encounter_window(r_mag, _FROZEN_CHORD_GATE.r_ca_m, body.radius)
        return 1.0 + w * (_FROZEN_CHORD_GATE.kappa_blend - 1.0)

    return 1.0


def visible_source_quadrature(
    r_probe: Vec3,
    v_probe: Vec3,
    body: RotatingBody,
    *,
    angular_step_deg: float = 1.0,
    spin_sign: float = 1.0,
) -> VisibleSourceQuadrature:
    """
    Integrate the angular coverage of an extended rotating source as seen by a probe.

    The quadrature samples the body's surface in latitude/longitude cells and weights
    each visible patch by its apparent solid angle, `dΩ = cos(emission) dA / distance²`.
    This is a diagnostic bridge toward a distributed source-shell gate: Earth at low
    altitude covers a large solid angle, while Sun/Moon-like distant bodies cover tiny
    angular disks.
    """
    r_obs = _norm(r_probe)
    radius = max(body.radius, 1.0)
    if r_obs <= radius:
        raise ValueError("probe must be outside the source surface")

    step = max(float(angular_step_deg), 0.05)
    dtheta = math.radians(step)
    dphi = math.radians(step)
    v_hat = _unit(v_probe)
    omega_vec = _scale(body.spin_vector(), spin_sign)

    solid_angle = 0.0
    weighted_signed_projection = 0.0
    weighted_projection = 0.0
    weighted_corotating_projection = 0.0
    weighted_counterrotating_projection = 0.0
    weighted_sin2 = 0.0
    weighted_signed_spin_shape = 0.0
    weighted_spin_shape = 0.0
    weighted_counter_spin_shape = 0.0
    weighted_lt_shape = 0.0
    n_visible = 0

    n_theta = max(1, int(math.ceil(180.0 / step)))
    n_phi = max(1, int(math.ceil(360.0 / step)))
    for i in range(n_theta):
        theta = (i + 0.5) * math.pi / n_theta  # colatitude
        sin_theta = math.sin(theta)
        cos_theta = math.cos(theta)
        for j in range(n_phi):
            phi = (j + 0.5) * 2.0 * math.pi / n_phi
            normal = (
                sin_theta * math.cos(phi),
                sin_theta * math.sin(phi),
                cos_theta,
            )
            patch = _scale(normal, radius)
            to_probe = _add(r_probe, patch, -1.0)
            distance = _norm(to_probe)
            if distance <= 0.0:
                continue
            cos_emit = _dot(normal, to_probe) / distance
            if cos_emit <= 0.0:
                continue
            d_area = radius * radius * sin_theta * (math.pi / n_theta) * (2.0 * math.pi / n_phi)
            d_omega = cos_emit * d_area / (distance * distance)
            if d_omega <= 0.0:
                continue

            tangent = _cross(omega_vec, patch)
            tangent_hat = _unit(tangent) if _norm(tangent) > 0.0 else (0.0, 0.0, 0.0)
            signed_projection = _dot(v_hat, tangent_hat)
            tangent_projection = abs(signed_projection)
            corotating_projection = max(0.0, signed_projection)
            counterrotating_projection = max(0.0, -signed_projection)
            sin2_colat = 1.0 - normal[2] * normal[2]

            solid_angle += d_omega
            weighted_signed_projection += d_omega * signed_projection
            weighted_projection += d_omega * tangent_projection
            weighted_corotating_projection += d_omega * corotating_projection
            weighted_counterrotating_projection += d_omega * counterrotating_projection
            weighted_sin2 += d_omega * sin2_colat
            weighted_signed_spin_shape += d_omega * sin2_colat * signed_projection
            weighted_spin_shape += d_omega * sin2_colat * tangent_projection
            weighted_counter_spin_shape += d_omega * sin2_colat * counterrotating_projection
            # L-T release keeps the source latitude gate separate from the spacecraft
            # angular-momentum gate, which is handled by `rho_pol` in the trajectory layer.
            weighted_lt_shape += d_omega * sin2_colat
            n_visible += 1

    angular_radius = math.asin(min(1.0, radius / r_obs))
    analytic_solid_angle = 2.0 * math.pi * (1.0 - math.cos(angular_radius))
    denom = max(solid_angle, 1.0e-30)
    return VisibleSourceQuadrature(
        angular_step_deg=step,
        n_visible_samples=n_visible,
        angular_radius_deg=math.degrees(angular_radius),
        angular_diameter_deg=2.0 * math.degrees(angular_radius),
        solid_angle_sr=solid_angle,
        analytic_solid_angle_sr=analytic_solid_angle,
        covered_sky_fraction=solid_angle / (4.0 * math.pi),
        visible_hemisphere_fraction=solid_angle / (2.0 * math.pi),
        mean_signed_tangent_projection=weighted_signed_projection / denom,
        mean_tangent_projection=weighted_projection / denom,
        mean_corotating_projection=weighted_corotating_projection / denom,
        mean_counterrotating_projection=weighted_counterrotating_projection / denom,
        mean_sin2_colatitude=weighted_sin2 / denom,
        mean_signed_spin_lapse_shape=weighted_signed_spin_shape / denom,
        mean_spin_lapse_shape=weighted_spin_shape / denom,
        mean_counter_spin_lapse_shape=weighted_counter_spin_shape / denom,
        mean_lense_thirring_shape=weighted_lt_shape / denom,
    )


def _rotate_ecliptic_to_equatorial(v: Vec3) -> Vec3:
    """Rotate an ecliptic vector into the equatorial frame used by the catalog declinations."""
    x, y, z = v
    ce = math.cos(OBLIQUITY_RAD)
    se = math.sin(OBLIQUITY_RAD)
    return (x, y * ce - z * se, y * se + z * ce)


def day_of_year_fraction(iso_date: str | None) -> float:
    """Fractional year phase; 0 at Jan 1. Uses noon-free calendar approximation."""
    if not iso_date:
        return 0.0
    d = date.fromisoformat(iso_date)
    days = 366 if (d.year % 4 == 0 and (d.year % 100 != 0 or d.year % 400 == 0)) else 365
    return (d.timetuple().tm_yday - 1) / float(days)


def days_since_j2000(iso_date: str | None, t_offset_s: float = 0.0) -> float:
    """Days since J2000.0 with optional seconds offset (advances Sun/Moon during flyby)."""
    if not iso_date:
        return t_offset_s / 86_400.0
    d = date.fromisoformat(iso_date)
    return float(d.toordinal() - date(2000, 1, 1).toordinal()) + t_offset_s / 86_400.0


def _wrap_rad(deg: float) -> float:
    return math.radians(deg % 360.0)


def earth_orbital_velocity_unit(iso_date: str | None) -> Vec3:
    """
    Approximate Earth heliocentric orbital velocity direction in equatorial coordinates.

    λ≈0 at vernal equinox (day 79.5); velocity is +90° ahead in ecliptic longitude.
    This is a seasonal frame diagnostic, not a full ephemeris.
    """
    phase = day_of_year_fraction(iso_date)
    lam = 2.0 * math.pi * (phase - 79.5 / 365.2422)
    v_ecl = (-math.sin(lam), math.cos(lam), 0.0)
    return _unit(_rotate_ecliptic_to_equatorial(v_ecl))


@lru_cache(maxsize=4096)
def sun_position_geocentric(iso_date: str | None, t_offset_s: float = 0.0) -> Vec3:
    """
    Low-precision geocentric Sun vector in equatorial coordinates.

    Good enough for third-body tide scale in this diagnostic calculator; not an ephemeris
    replacement for final orbit determination.
    """
    n = days_since_j2000(iso_date, t_offset_s)
    mean_long = _wrap_rad(280.460 + 0.9856474 * n)
    mean_anom = _wrap_rad(357.528 + 0.9856003 * n)
    ecl_long = mean_long + math.radians(1.915) * math.sin(mean_anom) + math.radians(0.020) * math.sin(2.0 * mean_anom)
    r_au = 1.00014 - 0.01671 * math.cos(mean_anom) - 0.00014 * math.cos(2.0 * mean_anom)
    return _scale(_rotate_ecliptic_to_equatorial((math.cos(ecl_long), math.sin(ecl_long), 0.0)), r_au * AU)


@lru_cache(maxsize=4096)
def moon_position_geocentric(iso_date: str | None, t_offset_s: float = 0.0) -> Vec3:
    """
    Low-precision geocentric Moon vector in equatorial coordinates.

    Uses classic mean-element approximation (few-degree class). This captures lunar third-body
    acceleration scale and phase for anomaly hunting; final work should swap in SPICE/JPL.
    """
    d = days_since_j2000(iso_date, t_offset_s)
    n_node = _wrap_rad(125.1228 - 0.0529538083 * d)
    inc = math.radians(5.1454)
    arg_peri = _wrap_rad(318.0634 + 0.1643573223 * d)
    mean_anom = _wrap_rad(115.3654 + 13.0649929509 * d)
    ecc = 0.0549
    ecc_anom = mean_anom + ecc * math.sin(mean_anom) * (1.0 + ecc * math.cos(mean_anom))
    xv = MOON_SEMIMAJOR_AXIS * (math.cos(ecc_anom) - ecc)
    yv = MOON_SEMIMAJOR_AXIS * math.sqrt(1.0 - ecc * ecc) * math.sin(ecc_anom)
    true_anom = math.atan2(yv, xv)
    r = math.hypot(xv, yv)
    u = true_anom + arg_peri
    x_ecl = r * (math.cos(n_node) * math.cos(u) - math.sin(n_node) * math.sin(u) * math.cos(inc))
    y_ecl = r * (math.sin(n_node) * math.cos(u) + math.cos(n_node) * math.sin(u) * math.cos(inc))
    z_ecl = r * (math.sin(u) * math.sin(inc))
    return _rotate_ecliptic_to_equatorial((x_ecl, y_ecl, z_ecl))


def _unit_from_ra_dec(ra_deg: float, dec_deg: float) -> Vec3:
    ra = math.radians(ra_deg)
    dec = math.radians(dec_deg)
    cd = math.cos(dec)
    return (cd * math.cos(ra), cd * math.sin(ra), math.sin(dec))


def galactic_rotation_unit_equatorial() -> Vec3:
    """
    Approximate local Milky-Way disk rotation direction (l=90, b=0) in equatorial coordinates.

    Built from IAU north galactic pole and Galactic-center direction, avoiding a free phase knob.
    """
    z_gal = _unit(_unit_from_ra_dec(GALACTIC_NORTH_RA_DEG, GALACTIC_NORTH_DEC_DEG))
    x_gal = _unit(_unit_from_ra_dec(GALACTIC_CENTER_RA_DEG, GALACTIC_CENTER_DEC_DEG))
    # Orthogonalize x to the adopted pole, then y = z × x gives l=90.
    x_gal = _unit(_add(x_gal, z_gal, -_dot(x_gal, z_gal)))
    return _unit(_cross(z_gal, x_gal))


def annual_frame_projection(r: Vec3, v: Vec3, iso_date: str | None) -> float:
    """
    Signed annual-frame projection on the local motion.

    Positive means spacecraft motion samples the same seasonal frame direction as Earth's
    heliocentric velocity; negative means the annual frame suppresses the local lapse channel.
    """
    v_hat = _unit(v)
    u_year = earth_orbital_velocity_unit(iso_date)
    return _dot(v_hat, u_year)


def exponential_disk_mass_inside(radius: float, disk_mass: float, scale_length: float) -> float:
    x = max(radius, 0.0) / max(scale_length, 1.0)
    return disk_mass * (1.0 - math.exp(-x) * (1.0 + x))


def galactic_disk_support_fraction() -> float:
    """Comoving disk mass support fraction M_disk(<R0)/M_dyn(<R0)."""
    m_disk = exponential_disk_mass_inside(GALACTIC_R0, MILKY_WAY_DISK_MASS, MILKY_WAY_DISK_SCALE)
    m_dyn = GALACTIC_VC * GALACTIC_VC * GALACTIC_R0 / G_NEWTON
    return max(0.0, min(1.0, m_disk / max(m_dyn, 1.0)))


def galactic_rindler_denominator() -> float:
    """
    Angular-momentum driven Rindler denominator for the local Galactic disk.

    Θ_R/R0 = c²/v_c² for circular support; the shared Rindler detuning is 1 + (γ/2) Θ_R/R0.
    """
    return 1.0 + (GAMMA_HQIV / 2.0) * (C_LIGHT / GALACTIC_VC) ** 2


def galactic_disk_lapse_fraction(iso_date: str | None) -> float:
    """
    Seasonal residual of the comoving Milky-Way disk lapse.

    Baseline disk lapse is comoving with the Solar System and cancels in local dynamics. The
    remaining annual piece is the Earth orbital angular-momentum perturbation projected onto
    Galactic rotation, weighted by the disk mass fraction and suppressed by the disk Rindler horizon.
    """
    annual_h_fraction = (V_EARTH_ORBIT / GALACTIC_VC) * _dot(
        earth_orbital_velocity_unit(iso_date), galactic_rotation_unit_equatorial()
    )
    return (
        2.0
        * (GALACTIC_VC / C_LIGHT)
        * galactic_disk_support_fraction()
        * annual_h_fraction
        / galactic_rindler_denominator()
    )


def perpendicular_unit(reference: Vec3, preferred: Vec3) -> Vec3:
    """Unit vector ⊥ to reference, preferring the plane spanned with preferred."""
    c = _cross(reference, preferred)
    if _norm(c) > 1e-14:
        return _unit(c)
    c2 = _cross(reference, (1.0, 0.0, 0.0))
    if _norm(c2) > 1e-14:
        return _unit(c2)
    return _unit(_cross(reference, (0.0, 1.0, 0.0)))


@dataclass(frozen=True)
class RotatingBody:
    """Central mass (planet, Sun) with optional spin and oblateness; spin about +z."""

    name: str
    gm: float
    radius: float
    j2: float
    omega: float  # rad/s, spin vector = (0, 0, omega)
    m_shell: int = 4  # legacy label; orbital φ uses propagation_shell_for_orbitals()
    phi_ref: float | None = None  # defaults to 1 (homogeneous solar-system reference)
    readout_radius: float | None = None  # lapse scale R in φ/(1+r/R); default `radius`
    #: Optional IAU pole in J2000 equatorial coords (from SPICE); default +z.
    spin_axis_hat: Vec3 | None = None

    def spin_vector(self) -> Vec3:
        axis = spin_axis_unit(self)
        return _scale(axis, self.omega)

    def phi_reference(self) -> float:
        """Homogeneous reference for G_eff ratios (same band system-wide)."""
        return self.phi_ref if self.phi_ref is not None else 1.0

    def lapse_radius(self) -> float:
        return self.readout_radius if self.readout_radius is not None else self.radius


@dataclass
class HQIVOrbitCoupling:
    """Scales for chart-level O-Maxwell / fluid probes."""

    vacuum_scale: float = 1.0  # unity when φ is SI; spin channel off in nominal runs
    metric_phi_scale: float = 1.0  # unity; α/(4π) already in chart formula
    geff_on_newton: bool = True
    #: Apply G_eff = lapse^α as a global time-rescaling on the total 3-vector acceleration
    #: (vectors built first, then scaled). When False, G_eff folds into Newton/J2 source GM.
    geff_as_time_factor: bool = True
    #: Paper inertia factor f(a,φ)=a/(a+φ/6) (Lean `hqivFluidInertiaFactor`).
    paper_inertia_screen: bool = True
    #: Modified geodesic: a_grav ← a_GR / f (main.tex §modified geodesic); not only (1−f) on O-Maxwell.
    modified_inertia_geodesic: bool = True
    #: Add co-spinning lapse-drag contribution to φ_eff using 2ΩR/c and local acceleration.
    lapse_drag_phi: bool = True
    #: Repartition horizon physics: co-spin/annual/galactic ε on metric channel, not φ_eff pump.
    horizon_repartition: bool = True
    #: Weak-field metric horizon: a_horizon ≈ a_GR × ε (first-order match to legacy φ_eff boost).
    horizon_metric_channel: bool = True
    #: When repartitioning, do not feed spin phase into g_vac (avoids double-count with metric ε).
    suppress_vacuum_spin_coupling: bool = True
    #: Add date-dependent annual frame projection (Earth orbit around Sun) to φ_eff diagnostics/dynamics.
    annual_lapse_phi: bool = False
    #: Multiplier for annual frame projection; dimensionless and separate from mission fitting.
    annual_lapse_strength: float = 0.0
    #: Derived Milky-Way disk Rindler lapse: angular-momentum support × comoving disk fraction.
    galactic_disk_lapse_phi: bool = True
    #: Multiplier for the derived galactic disk term; keep 1 for non-fitted runs.
    galactic_disk_lapse_strength: float = 1.0
    #: Radial dilution power for co-spinning frame support: (R/r)^p.
    lapse_drag_power: float = 2.0
    #: Dimensionless multiplier on the derived co-spin lapse fraction; keep 1 unless testing sensitivity.
    lapse_drag_strength: float = 1.0
    #: Latitude-weight ε by sin²θ (rotating-frame tangent vanishes on spin axis).
    lapse_drag_colatitude: bool = True
    #: Add Lense-Thirring-style 3-vector horizon force along ω × r̂ (vanishes at pole).
    lapse_drag_lense_thirring: bool = True
    #: Override for L-T vs isotropic split; None ⇒ derived from γ and geometry (not 0.5).
    lapse_drag_vector_fraction: float | None = None
    #: Require polar-fiber release above γ before opening the L-T vector channel.
    lapse_drag_coherence_gate: bool = False
    #: Weight screen by |L_z|/|L| and colatitude (pole exits less screened than equator).
    angular_momentum_screen: bool = True
    #: Add changing orbital angular rate r|dω_orb/dt| to the local Rindler inertia scale.
    orbital_angular_rindler: bool = True
    #: Lapse/rapidity screen (1−v²/c²) on HQIV slots (mass_well / HQVM narrative).
    velocity_screen: bool = True
    kappa_l: float = 0.0  # optional longitudinal stress along velocity (0 = off)
    density_proxy: float = 1.0  # kg/m³ scale for κ_L channel only
    #: Chord-quadrature gate for Lean ``flybyDynamicKappaPhiFromPhase`` on the horizon boost.
    chord_source_gate: bool = False
    #: Use orbital phase geometry (inverse-square ρ_orb) instead of legacy shell-4 κ.
    phase_geometry_source: bool = True
    source_kappa_m_shell: int = 4  # legacy fallback when ``phase_geometry_source`` is False
    #: Blend toward full dynamic kappa: 1 ⇒ ``K_φ=5`` at gate=1 and m=4; 0 ⇒ point-like.
    chord_gate_strength: float = 1.0
    chord_gate_step_deg: float = 2.0
    chord_gate_samples: int = 4
    chord_gate_max_radius_factor: float = 15.0
    #: Legacy: single CA snapshot (off by default; use track instead).
    chord_gate_freeze_at_ca: bool = False
    #: Coarse classical track + smooth interpolation over the encounter shell.
    chord_gate_use_track: bool = True
    #: States recorded every N steps while inside the encounter shell.
    chord_track_collect_stride: int = 10
    #: Uniform subsample count along the full inbound+outbound encounter.
    chord_track_target_samples: int = 48
    #: Deprecated (unused): kept for API compatibility.
    chord_track_stride_steps: int = 80
    chord_track_min_dr_m: float = 250_000.0


@dataclass(frozen=True)
class FlybyCase:
    """Published-style flyby geometry (approximate; for anomaly probing)."""

    label: str
    v_inf: float  # m/s asymptotic speed magnitude
    impact_parameter: float  # m
    r_start: float  # m, initial distance (should be ≫ radius)
    spin_sign: float = 1.0  # ±1 flips Earth rotation for reversal tests
    #: Asymptotic approach direction (spacecraft starts at r_start along this ray from Earth).
    inbound_lat_deg: float = 0.0
    inbound_lon_deg: float = 0.0
    #: Rotate the impact-parameter vector in the plane ⊥ to inbound (0 = equatorial, 90 = polar tilt).
    b_azimuth_deg: float = 0.0
    reported_anomaly_mm_s: float | None = None
    notes: str = ""
    central_body: str = "earth"  # key in BODIES: earth | sun
    encounter_date: str | None = None  # ISO date for seasonal/annual frame diagnostics


@dataclass
class OrbitState:
    r: Vec3
    v: Vec3
    t: float = 0.0


@dataclass
class PropagationSettings:
    dt: float = 2.0  # s
    t_max: float = 250_000.0
    rotating_frame: bool = False
    use_j2: bool = True
    use_third_bodies: bool = False
    r_escape: float = 40.0 * R_EARTH  # shell where vis-viva reduction is applied
    ca_search_radius: float = 20.0 * R_EARTH  # window for closest approach
    h_reference: float | None = None  # |L| scale, default v_inf × b per case


# --- φ / phase fields tied to spin -------------------------------------------------


def phi_readout(r: Vec3, body: RotatingBody) -> float:
    """Geometric lapse modulation; identical propagation-shell band across the solar system."""
    r_mag = _norm(r)
    r_lapse = body.lapse_radius()
    return 1.0 / (1.0 + r_mag / r_lapse)


def phi_gradient(r: Vec3, body: RotatingBody) -> Vec3:
    """∇ of the geometric φ readout (dimensionless)."""
    r_mag = max(_norm(r), body.lapse_radius() * 1e-6)
    r_lapse = body.lapse_radius()
    denom = (1.0 + r_mag / r_lapse) ** 2
    dphi_dr = -1.0 / r_lapse / denom
    r_hat = _scale(r, 1.0 / r_mag)
    return _scale(r_hat, dphi_dr)


def phi_gradient_si(r: Vec3, body: RotatingBody) -> Vec3:
    """SI gradient of φ_hom × geometric lapse."""
    return _scale(phi_gradient(r, body), phi_acceleration_homogeneous_si())


def dot_theta_prime(r: Vec3, body: RotatingBody, spin_sign: float = 1.0) -> float:
    """
    Signed rotational phase tipping: (ω×r)·ê_φ / (R|ω|), odd in spin direction.

    ê_φ is the equatorial azimuthal direction (peaks at low |latitude|).
  """
    e_phi = equatorial_phi_hat(r)
    if _norm(e_phi) < 1e-20:
        return 0.0
    omega_vec = _scale(body.spin_vector(), spin_sign)
    tangential = _cross(omega_vec, r)
    denom = max(body.radius * abs(body.omega), 1e-12)
    return _dot(tangential, e_phi) / denom


def oblate_latitude_factor(r: Vec3, body: RotatingBody | None = None) -> float:
    """
    J₂ weighting vs colatitude: peaks at equator (sin²θ = 1), vanishes on spin axis.
    Used to report how strongly a trajectory samples oblate coupling.
    """
    if body is not None:
        return spin_colatitude_sin_sq(r, body)
    r_mag = max(_norm(r), 1e-9)
    cos_colat = abs(r[2]) / r_mag
    return 1.0 - cos_colat * cos_colat


def grad_dot_theta_prime(r: Vec3, body: RotatingBody, spin_sign: float = 1.0) -> Vec3:
    """
    Crude spatial gradient of dot_theta_prime (finite-difference style in code).
    Used only for the g_vac cross term.
    """
    eps = 1.0e-3 * body.radius
    out = [0.0, 0.0, 0.0]
    for i in range(3):
        rp = list(r)
        rm = list(r)
        rp[i] += eps
        rm[i] -= eps
        fp = dot_theta_prime(tuple(rp), body, spin_sign)
        fm = dot_theta_prime(tuple(rm), body, spin_sign)
        out[i] = (fp - fm) / (2.0 * eps)
    return (out[0], out[1], out[2])


def hqiv_inertia_factor(a_loc: float, phi: float) -> float:
    """Paper / Lean `hqivFluidInertiaFactor`: f = a_loc / (a_loc + φ/6), 0 < f ≤ 1."""
    return a_loc / (a_loc + phi / 6.0) if a_loc > 0.0 else 1.0


def phi_acceleration_homogeneous_si() -> float:
    """Homogeneous-limit acceleration scale φ ≈ 2cH (paper HQVM; Brodie overlap)."""
    return 2.0 * C_LIGHT * H0_SI


def phi_acceleration_si(r: Vec3, body: RotatingBody) -> float:
    """
    Local φ as an acceleration scale (m/s²) for the inertia screen.

    Uses φ_hom = 2cH modulated by radial geometry.  Solar-system propagation uses
    ξ = 1 (not shell 4).  Earth's local curvature supplies a small multiplicative
    delta from orbital phase geometry when available.
    """
    base = phi_acceleration_homogeneous_si() * phi_readout(r, body)
    delta = orbital_curvature_mass_delta_at(body, _norm(r))
    return base * (1.0 + delta)


def orbital_angular_velocity(r: Vec3, v: Vec3) -> Vec3:
    """Instantaneous orbital angular-rate vector ω_orb = (r×v)/r²."""

    r_mag = max(_norm(r), 1.0)
    return _scale(_cross(r, v), 1.0 / (r_mag * r_mag))


def orbital_angular_acceleration(r: Vec3, v: Vec3, a_probe: Vec3) -> Vec3:
    """Time derivative of ω_orb for the current osculating trajectory."""

    r_mag = max(_norm(r), 1.0)
    r2 = r_mag * r_mag
    omega = orbital_angular_velocity(r, v)
    torque_term = _scale(_cross(r, a_probe), 1.0 / r2)
    radial_sweep = _scale(omega, -2.0 * _dot(r, v) / r2)
    return _add(torque_term, radial_sweep)


def orbital_angular_rindler_scale(r: Vec3, v: Vec3, a_probe: Vec3) -> float:
    """Acceleration scale r|dω_orb/dt| from the changing orbital Rindler horizon."""

    return max(_norm(r), 1.0) * _norm(orbital_angular_acceleration(r, v, a_probe))


def local_acceleration_scale(
    r: Vec3,
    v: Vec3,
    a_grav: Vec3,
    *,
    include_orbital_angular_rindler: bool = False,
) -> float:
    """Proxy for a_loc: gravity, centripetal curvature, and optional angular Rindler scale."""

    r_mag = max(_norm(r), 1.0)
    a_ang = orbital_angular_rindler_scale(r, v, a_grav) if include_orbital_angular_rindler else 0.0
    return max(_norm(a_grav), _norm(v) ** 2 / r_mag, a_ang)


def horizon_lapse_fraction(
    r: Vec3,
    v: Vec3,
    body: RotatingBody,
    coupling: HQIVOrbitCoupling | None,
    case: FlybyCase | None,
    spin_sign: float = 1.0,
) -> float:
    """
    Dimensionless horizon support ε (co-spin + optional annual/galactic).

    Legacy path injects `6 a_loc ε` into φ_eff; repartitioned path uses the same ε on the metric
    channel as a fractional boost `a_GR ← a_GR(1+ε)` (weak field, paper γ(φ/c²)(δ̇θ'/c) g_μν slot).
    """
    if coupling is None or not coupling.lapse_drag_phi:
        return 0.0
    eps = coupling.lapse_drag_strength * co_spin_lapse_fraction(
        r,
        v,
        body,
        coupling.lapse_drag_power,
        use_colatitude=coupling.lapse_drag_colatitude,
        spin_sign=spin_sign,
    )
    if body.name.lower() == "earth" and coupling.annual_lapse_phi and case is not None:
        annual_proj = annual_frame_projection(r, v, case.encounter_date)
        eps += coupling.annual_lapse_strength * (V_EARTH_ORBIT / C_LIGHT) * annual_proj
    if body.name.lower() == "earth" and coupling.galactic_disk_lapse_phi and case is not None:
        eps += coupling.galactic_disk_lapse_strength * galactic_disk_lapse_fraction(
            case.encounter_date
        )
    return max(0.0, eps)


def co_spin_lapse_fraction(
    r: Vec3,
    v_or_body: Vec3 | RotatingBody,
    body: RotatingBody | None = None,
    radial_power: float = 2.0,
    *,
    use_colatitude: bool = True,
    spin_sign: float = 1.0,
) -> float:
    """
    Dimensionless co-spinning mass-horizon Doppler support.

    The Lean-side mass readout uses lapse division; the rotating source shifts that horizon
    by the Doppler projection of the local horizon tangent onto the probe motion. Polar
    trajectories have little tangential projection, so they sample a smaller mass-horizon shift.
    """
    if body is None:
        v = None
        if not isinstance(v_or_body, RotatingBody):
            raise TypeError("body is required when the second argument is a velocity")
        body = v_or_body
    else:
        if isinstance(v_or_body, RotatingBody):
            raise TypeError("velocity must be supplied before body")
        v = v_or_body
    if body.omega == 0.0 or body.radius <= 0.0:
        return 0.0
    r_mag = max(_norm(r), body.radius)
    sin_colat = math.sqrt(spin_colatitude_sin_sq(r, body)) if use_colatitude else 1.0
    v_tangent = abs(body.omega) * body.radius * sin_colat
    if v is None:
        projection = sin_colat if use_colatitude else 1.0
    else:
        tangent_hat = co_spin_tangent_hat(r, body, spin_sign)
        if _norm(tangent_hat) <= 0.0:
            return 0.0
        projection = abs(_dot(_unit(v), tangent_hat))
    eps = 2.0 * (v_tangent / C_LIGHT) * projection * (body.radius / r_mag) ** radial_power
    if use_colatitude:
        eps *= sin_colat
    return eps


def effective_phi_acceleration_si(
    r: Vec3,
    v: Vec3,
    a_grav: Vec3,
    body: RotatingBody,
    coupling: HQIVOrbitCoupling | None,
    case: FlybyCase | None = None,
) -> float:
    """
    φ_eff in acceleration units for modified inertia.

    Base term: homogeneous/lattice φ (`2cH0` modulated by shell readout).
    Local horizon term: a co-spinning lapse fraction ε contributes `φ_drag = 6 a_loc ε`,
    because `f = a/(a+φ/6)` and a small fractional inertia correction is `φ/(6a)`.
    """
    phi = phi_acceleration_si(r, body)
    if coupling is None or not coupling.lapse_drag_phi:
        return phi
    if coupling.horizon_repartition:
        return phi
    a_loc = local_acceleration_scale(
        r,
        v,
        a_grav,
        include_orbital_angular_rindler=coupling.orbital_angular_rindler,
    )
    eps = horizon_lapse_fraction(r, v, body, coupling, case)
    return phi + 6.0 * a_loc * eps


def phi_horizon_boost_acceleration_si(
    r: Vec3,
    v: Vec3,
    a_grav: Vec3,
    body: RotatingBody,
    coupling: HQIVOrbitCoupling | None,
    case: FlybyCase | None,
    spin_sign: float = 1.0,
    settings: PropagationSettings | None = None,
) -> float:
    """Horizon-only φ boost `6 a_loc ε` (metric channel; not in particle φ_eff when repartitioned)."""
    if coupling is None or not coupling.lapse_drag_phi:
        return 0.0
    if not coupling.horizon_repartition:
        return 0.0
    eps = horizon_lapse_fraction(r, v, body, coupling, case, spin_sign=spin_sign)
    boost = 6.0 * local_acceleration_scale(
        r,
        v,
        a_grav,
        include_orbital_angular_rindler=coupling.orbital_angular_rindler,
    ) * eps
    boost *= chord_horizon_kappa_factor(
        r, v, body, coupling, spin_sign, settings=settings, case=case
    )
    return boost


def inertia_factor_blend_at_point(
    r: Vec3,
    v: Vec3,
    a_grav: Vec3,
    body: RotatingBody,
    coupling: HQIVOrbitCoupling,
    settings: PropagationSettings,
    phi_eff: float,
) -> float:
    """Direction-dependent or isotropic inertia factor f at fixed φ_eff (acceleration units)."""
    h_ref = settings.h_reference if settings.h_reference is not None else 1.0
    if coupling.angular_momentum_screen:
        w, _, _ = angular_momentum_inertia_screen_weight(
            r,
            v,
            a_grav,
            body,
            h_ref,
            phi_eff,
            include_orbital_angular_rindler=coupling.orbital_angular_rindler,
        )
        return max(1.0 - w, F_INERTIA_FLOOR)
    a_loc = local_acceleration_scale(
        r,
        v,
        a_grav,
        include_orbital_angular_rindler=coupling.orbital_angular_rindler,
    )
    return max(hqiv_inertia_factor(max(a_loc, 0.0), max(phi_eff, 0.0)), F_INERTIA_FLOOR)


def polar_fiber_release_fraction(r: Vec3, v: Vec3, h_ref: float) -> float:
    """
    Polar-fiber weight ρ_pol = 1 − (h_z/h_ref)² (same ladder as inertia L-screen).

    Low |L_z| / polar-style trajectories release the tangent lapse channel; equatorial lock
    suppresses it.
    """
    h_z = h_z_spin_component(r, v)
    h_ref = max(h_ref, 1e-9)
    L_z_ref_frac = min(1.0, h_z / h_ref)
    return max(0.0, 1.0 - L_z_ref_frac * L_z_ref_frac)


def horizon_vector_coherence_gate(rho_pol: float, threshold: float = GAMMA_HQIV) -> float:
    """Open L-T only when polar-fiber release exceeds the HQIV overlap γ."""
    if threshold >= 1.0:
        return 0.0
    return max(0.0, min(1.0, (rho_pol - threshold) / (1.0 - threshold)))


def derived_horizon_vector_fraction(
    r: Vec3,
    v: Vec3,
    body: RotatingBody,
    coupling: HQIVOrbitCoupling,
    settings: PropagationSettings,
    spin_sign: float = 1.0,
) -> float:
    """
    Dynamic isotropic ↔ L-T split (replaces fixed λ=0.5).

    Lean monogamy ledger: α=3/5 imprint/time (G_eff), γ=2/5 horizon overlap/tangent.
    The vector channel fraction is therefore γ on the unit split, modulated by geometry:

      λ = γ × sin²θ × ρ_pol × g_coh × 𝟙_{ω×r̂≠0}

    where ρ_pol = 1 − (h_z/h_ref)² is the polar-fiber release (low |L_z| ⇒ more 3-vector).
    Optional `g_coh` is zero until ρ_pol exceeds γ, so modest release stays in the
    isotropic trace channel instead of over-rotating asymmetric trajectories.
    Isotropic g_μν trace carries the complement 1 − λ (α-dominated when λ→0).
    """
    if coupling.lapse_drag_vector_fraction is not None:
        return max(0.0, min(1.0, coupling.lapse_drag_vector_fraction))

    if _norm(lense_thirring_direction(r, body, spin_sign)) <= 1.0e-30:
        return 0.0

    h_ref = settings.h_reference if settings.h_reference is not None else max(
        specific_angular_momentum(r, v), 1.0
    )

    sin2 = oblate_latitude_factor(r, body) if coupling.lapse_drag_colatitude else 1.0
    rho_pol = polar_fiber_release_fraction(r, v, h_ref)
    coherence = horizon_vector_coherence_gate(rho_pol) if coupling.lapse_drag_coherence_gate else 1.0

    return max(0.0, min(1.0, GAMMA_HQIV * sin2 * rho_pol * coherence))


def lense_thirring_direction(r: Vec3, body: RotatingBody, spin_sign: float = 1.0) -> Vec3:
    """
    Unit 3-vector along the local frame-drag tangent `ω × r̂`.

    Vanishes on the spin axis (pole); maximal at the equator. Sign carries spin orientation.
    """
    r_mag = max(_norm(r), 1.0)
    r_hat = _scale(r, 1.0 / r_mag)
    omega_vec = _scale(body.spin_vector(), spin_sign)
    drag = _cross(omega_vec, r_hat)
    mag = _norm(drag)
    if mag <= 1.0e-30:
        return (0.0, 0.0, 0.0)
    return _scale(drag, 1.0 / mag)


def horizon_metric_accel(
    r: Vec3,
    v: Vec3,
    a_grav: Vec3,
    body: RotatingBody,
    coupling: HQIVOrbitCoupling | None,
    settings: PropagationSettings,
    case: FlybyCase | None,
    spin_sign: float = 1.0,
) -> Vec3:
    """
    Metric-side horizon stress (repartitioned co-spin / annual / galactic ε) as a 3-vector.

    Two channels:
      * Isotropic g_μν trace: `(a_GR/f_part) × (f_part/f_full − 1)`, scaled by `1 − λ_vec`.
        This matches the legacy weak-field split exactly when `λ_vec = 0`.
      * Lense-Thirring tangent: `λ × |a_GR/f_part| × (f_part/f_full − 1) × (ω×r̂)/|ω×r̂|`,
        with `λ = γ sin²θ ρ_pol` derived (γ=2/5; ρ_pol = 1−(h_z/h_ref)²).
    """
    if (
        coupling is None
        or not coupling.horizon_repartition
        or not coupling.horizon_metric_channel
        or not coupling.lapse_drag_phi
    ):
        return (0.0, 0.0, 0.0)
    phi_part = phi_acceleration_si(r, body)
    phi_full = phi_part + phi_horizon_boost_acceleration_si(
        r, v, a_grav, body, coupling, case, spin_sign, settings
    )
    if phi_full <= phi_part:
        return (0.0, 0.0, 0.0)
    f_part = inertia_factor_blend_at_point(r, v, a_grav, body, coupling, settings, phi_part)
    f_full = inertia_factor_blend_at_point(r, v, a_grav, body, coupling, settings, phi_full)
    ratio = f_part / f_full - 1.0
    if abs(ratio) < 1.0e-18:
        return (0.0, 0.0, 0.0)
    base = _scale(_scale(a_grav, 1.0 / f_part), ratio)

    if not coupling.lapse_drag_lense_thirring:
        return base
    vec_frac = derived_horizon_vector_fraction(
        r, v, body, coupling, settings, spin_sign
    )
    if vec_frac <= 0.0:
        return base
    iso = _scale(base, 1.0 - vec_frac)
    drag_hat = lense_thirring_direction(r, body, spin_sign)
    if _norm(drag_hat) <= 0.0:
        return iso
    drag_mag = _norm(base) * vec_frac
    drag = _scale(drag_hat, drag_mag)
    return _add(iso, drag)


def specific_angular_momentum(r: Vec3, v: Vec3) -> float:
    return _norm(_cross(r, v))


def h_z_spin_component(r: Vec3, v: Vec3) -> float:
    """|L_z| for spin along +z (equatorial component of angular momentum)."""
    return abs(_cross(r, v)[2])


def flyby_h_reference(case: FlybyCase) -> float:
    return case.v_inf * case.impact_parameter


def inertia_screen_weight(a_loc: float, phi_accel: float) -> float:
    """
    Isotropic HQIV weight (1−f), f = a/(a+φ/6).

    High-acceleration (solar system): f→1 ⇒ weight→0.
    """
    f = hqiv_inertia_factor(max(a_loc, 0.0), max(phi_accel, 0.0))
    return max(0.0, 1.0 - f)


# Minimum f for a_GR/f (avoids division blow-up; matches f ~ 6a/φ when a → 0).
F_INERTIA_FLOOR = 1.0e-15


@dataclass(frozen=True)
class ModifiedInertiaReadout:
    """Paper modified inertia at a chart point: f blend and (1−f) slot screen."""

    f_blend: float
    screen_weight: float  # 1 − f_blend
    L_eq_fraction: float
    L_z_over_h_ref: float


def angular_momentum_inertia_screen_weight(
    r: Vec3,
    v: Vec3,
    a_grav: Vec3,
    body: RotatingBody,
    h_ref: float,
    phi_a_override: float | None = None,
    *,
    include_orbital_angular_rindler: bool = False,
) -> tuple[float, float, float]:
    """
    Direction-dependent inertia screen (paper: equatorial lock vs polar fiber).

    * Equatorial channel: a_eq = |g| + (h²/r³ + r|dω_orb/dt|) × (h_z/h)².
      The angular Rindler term tracks changing orbital angular rate without adding probe mass.
    * Polar / low-h_z channel: φ_eff enlarged via h_z,eff² = h_z² + (h_ref/(m+1))²
      (shell transverse floor; no max(h_z, ε) clip).

    Returns (weight, L_eq_fraction, L_z_over_h_ref).
    """
    phi_a = phi_acceleration_si(r, body) if phi_a_override is None else phi_a_override
    r_mag = max(_norm(r), 1.0)
    h = max(specific_angular_momentum(r, v), 1e-9)
    h_z = h_z_spin_component(r, v)
    h_ref = max(h_ref, 1e-9)

    L_eq_frac = min(1.0, (h_z / h) ** 2)
    L_z_ref_frac = min(1.0, h_z / h_ref)

    a_c = h * h / (r_mag**3)
    a_rad = max(_norm(a_grav), 0.0)
    a_ang = (
        orbital_angular_rindler_scale(r, v, a_grav)
        if include_orbital_angular_rindler
        else 0.0
    )

    # Equatorial Brodie / angular Rindler lock
    a_equatorial = a_rad + (a_c + a_ang) * L_eq_frac
    f_eq = hqiv_inertia_factor(a_equatorial, phi_a)

    # Polar fiber: ρ_pol from asymptotic |L_z|; φ boost from h_ref / h_z,eff (ladder floor)
    polar_release = max(0.0, 1.0 - L_z_ref_frac * L_z_ref_frac)
    phi_polar = phi_a * polar_fiber_phi_boost(
        h_z, h, h_ref, polar_release, propagation_shell_for_orbitals()
    )
    f_pol = hqiv_inertia_factor(a_rad, phi_polar)

    sin2_colat = oblate_latitude_factor(r)
    f_blend = sin2_colat * f_eq + (1.0 - sin2_colat) * f_pol
    f_blend = max(f_blend, F_INERTIA_FLOOR)
    return max(0.0, 1.0 - f_blend), L_eq_frac, L_z_ref_frac


def modified_inertia_at_point(
    r: Vec3,
    v: Vec3,
    a_grav: Vec3,
    body: RotatingBody,
    coupling: HQIVOrbitCoupling | None,
    settings: PropagationSettings,
    case: FlybyCase | None = None,
) -> ModifiedInertiaReadout:
    """
    Full modified-inertia readout f(a_loc, φ) with optional L_z / colatitude blend.

    Used for (i) geodesic law a ← a_GR / f and (ii) (1−f) screening of O-Maxwell slots.
    """
    if coupling is None or not coupling.paper_inertia_screen:
        return ModifiedInertiaReadout(1.0, 0.0, 1.0, 1.0)

    h_ref = settings.h_reference if settings.h_reference is not None else 1.0
    phi_a = effective_phi_acceleration_si(r, v, a_grav, body, coupling, case)
    if coupling.angular_momentum_screen:
        w, leq, lzr = angular_momentum_inertia_screen_weight(
            r,
            v,
            a_grav,
            body,
            h_ref,
            phi_a,
            include_orbital_angular_rindler=coupling.orbital_angular_rindler,
        )
        return ModifiedInertiaReadout(max(1.0 - w, F_INERTIA_FLOOR), w, leq, lzr)

    a_loc = local_acceleration_scale(
        r,
        v,
        a_grav,
        include_orbital_angular_rindler=coupling.orbital_angular_rindler,
    )
    f_iso = max(hqiv_inertia_factor(max(a_loc, 0.0), max(phi_a, 0.0)), F_INERTIA_FLOOR)
    return ModifiedInertiaReadout(f_iso, 1.0 - f_iso, min(1.0, a_loc), 1.0)


def velocity_screen_factor(v: Vec3) -> float:
    """(1 − v²/c²) lapse/rapidity screen; ≈1 for planetary flybys."""
    beta2 = min(_dot(v, v) / (C_LIGHT * C_LIGHT), 0.999_999)
    return max(0.0, 1.0 - beta2)


def screened_geff_ratio(phi_dim: float, phi_ref: float, screen_weight: float) -> float:
    """Screen G_eff(φ) toward Newton: 1 + (φ/φ_ref)^α − 1) × (1−f)."""
    raw = geff_ratio(phi_dim, phi_ref)
    return 1.0 + (raw - 1.0) * max(0.0, min(1.0, screen_weight))


def geff_ratio(phi: float, phi_ref: float) -> float:
    if phi_ref <= 0.0:
        return 1.0
    return (phi / phi_ref) ** ALPHA_HQIV


# --- Accelerations -----------------------------------------------------------------


def newton_accel(r: Vec3, body: RotatingBody, geff_scale: float = 1.0) -> Vec3:
    r_mag = _norm(r)
    if r_mag <= 0.0:
        return (0.0, 0.0, 0.0)
    mu = body.gm * geff_scale
    return _scale(r, -mu / (r_mag**3))


def j2_accel(r: Vec3, body: RotatingBody, geff_scale: float = 1.0) -> Vec3:
    if body.j2 == 0.0:
        return (0.0, 0.0, 0.0)
    x, y, z = r
    r_mag = _norm(r)
    if r_mag <= body.radius:
        return (0.0, 0.0, 0.0)
    mu = body.gm * geff_scale
    re2 = body.radius**2
    r2 = r_mag**2
    r5 = r_mag**5
    coef = -1.5 * body.j2 * mu * re2 / r5
    z2_r2 = z * z / r2
    ax = coef * x * (5.0 * z2_r2 - 1.0)
    ay = coef * y * (5.0 * z2_r2 - 1.0)
    az = coef * z * (5.0 * z2_r2 - 3.0)
    return (ax, ay, az)


def third_body_tidal_accel(r: Vec3, body_pos: Vec3, body_gm: float) -> Vec3:
    """
    Differential third-body acceleration in the central-body frame.

    a = GM [(R-r)/|R-r|^3 - R/|R|^3], where R points from Earth to the third body.
    """
    rel = _add(body_pos, r, -1.0)
    rel_mag = max(_norm(rel), 1.0)
    body_mag = max(_norm(body_pos), 1.0)
    direct = _scale(rel, body_gm / (rel_mag**3))
    indirect = _scale(body_pos, body_gm / (body_mag**3))
    return _add(direct, indirect, -1.0)


def earth_third_body_accel(r: Vec3, case: FlybyCase | None, t_offset_s: float = 0.0) -> Vec3:
    """Sun + Moon third-body tide for Earth-centered flybys, with optional time-of-flight offset."""
    if case is None:
        return (0.0, 0.0, 0.0)
    iso = case.encounter_date
    # Snap time to 60-s buckets so the LRU cache hits across nearby substages.
    bucket = round(t_offset_s / 60.0) * 60.0
    return _add(
        third_body_tidal_accel(r, sun_position_geocentric(iso, bucket), GM_SUN),
        third_body_tidal_accel(r, moon_position_geocentric(iso, bucket), GM_MOON),
    )


def rotating_frame_accel(r: Vec3, v: Vec3, body: RotatingBody, spin_sign: float = 1.0) -> Vec3:
    """Coriolis + centrifugal in frame rotating with the planet (+z)."""
    omega = _scale(body.spin_vector(), spin_sign)
    centrifugal = _cross(omega, _cross(omega, r))
    coriolis = _scale(_cross(omega, v), 2.0)
    return _add(centrifugal, coriolis)


def hqiv_perturbation_accel(
    r: Vec3,
    v: Vec3,
    body: RotatingBody,
    coupling: HQIVOrbitCoupling,
    spin_sign: float = 1.0,
    *,
    screen_weight: float = 1.0,
    v_screen: float = 1.0,
) -> Vec3:
    phi_si = phi_acceleration_si(r, body)
    gp = phi_gradient_si(r, body)
    dot = dot_theta_prime(r, body, spin_sign)
    gd = grad_dot_theta_prime(r, body, spin_sign)
    if coupling.horizon_repartition and coupling.suppress_vacuum_spin_coupling:
        dot = 0.0
        gd = (0.0, 0.0, 0.0)

    g_vac = vacuum_momentum_source3(GAMMA_HQIV, phi_si, dot, gp, gd)
    a_vac = _scale(g_vac, coupling.vacuum_scale)

    lam = coupling_log(max(phi_si / max(phi_acceleration_homogeneous_si(), 1e-30), 0.0))
    a_metric = _scale(gp, coupling.metric_phi_scale * (ALPHA_HQIV / (4.0 * math.pi)) * lam)

    a_long = (0.0, 0.0, 0.0)
    if coupling.kappa_l != 0.0:
        v_mag = _norm(v)
        if v_mag > 0.0:
            v_hat = _scale(v, 1.0 / v_mag)
            grad_along = _dot(gp, v_hat)
            coeff = (
                coupling.kappa_l
                * coupling.density_proxy
                * lam
                * grad_along
            )
            a_long = _scale(v_hat, coeff)

    a_hqiv = _add(_add(a_vac, a_metric), a_long)
    return _scale(a_hqiv, screen_weight * v_screen)


def total_accel(
    r: Vec3,
    v: Vec3,
    body: RotatingBody,
    coupling: HQIVOrbitCoupling | None,
    settings: PropagationSettings,
    spin_sign: float = 1.0,
    case: FlybyCase | None = None,
    t_offset_s: float = 0.0,
) -> tuple[Vec3, float, float]:
    """
    Returns (acceleration, screen weight (1−f), inertia factor f).

    Paper modified geodesic (when enabled): m_i a = m_g a_GR with m_i = m_g f ⇒ a = a_GR / f.
    O-Maxwell / chart slots remain ∝ (1−f) and (1−β²).
    `t_offset_s` advances Sun/Moon ephemeris during the integration (per RK4 substage).
    """
    a_grav_probe = newton_accel(r, body, 1.0)
    if settings.use_j2:
        a_grav_probe = _add(a_grav_probe, j2_accel(r, body, 1.0))
    if settings.use_third_bodies and body.name.lower() == "earth":
        a_grav_probe = _add(a_grav_probe, earth_third_body_accel(r, case, t_offset_s))

    mi_particle = modified_inertia_at_point(r, v, a_grav_probe, body, coupling, settings, case)
    if (
        coupling is not None
        and coupling.horizon_repartition
        and coupling.paper_inertia_screen
    ):
        phi_part = phi_acceleration_si(r, body)
        phi_full = phi_part + phi_horizon_boost_acceleration_si(
            r, v, a_grav_probe, body, coupling, case, spin_sign, settings
        )
        if phi_full > phi_part:
            f_hor = inertia_factor_blend_at_point(
                r, v, a_grav_probe, body, coupling, settings, phi_full
            )
            mi_horizon = ModifiedInertiaReadout(
                f_hor,
                max(0.0, 1.0 - f_hor),
                mi_particle.L_eq_fraction,
                mi_particle.L_z_over_h_ref,
            )
        else:
            mi_horizon = mi_particle
    else:
        mi_horizon = mi_particle

    screen_w = mi_horizon.screen_weight
    v_scr = velocity_screen_factor(v) if coupling and coupling.velocity_screen else 1.0

    phi_dim = phi_readout(r, body)
    g_ratio = (
        screened_geff_ratio(phi_dim, body.phi_reference(), screen_w)
        if coupling and coupling.geff_on_newton
        else 1.0
    )
    geff_as_time = coupling is not None and coupling.geff_as_time_factor
    source_scale = 1.0 if geff_as_time else g_ratio

    a = newton_accel(r, body, source_scale)
    if settings.use_j2:
        a = _add(a, j2_accel(r, body, source_scale))
    if settings.use_third_bodies and body.name.lower() == "earth":
        a = _add(a, earth_third_body_accel(r, case, t_offset_s))

    if (
        coupling is not None
        and coupling.paper_inertia_screen
        and coupling.modified_inertia_geodesic
    ):
        a = _scale(a, 1.0 / mi_particle.f_blend)

    if coupling is not None:
        a = _add(
            a,
            horizon_metric_accel(
                r, v, a_grav_probe, body, coupling, settings, case, spin_sign
            ),
        )

    if settings.rotating_frame:
        a = _add(a, rotating_frame_accel(r, v, body, spin_sign))
    if coupling is not None:
        a = _add(
            a,
            hqiv_perturbation_accel(
                r, v, body, coupling, spin_sign, screen_weight=screen_w, v_screen=v_scr
            ),
        )

    if geff_as_time and g_ratio != 1.0:
        a = _scale(a, g_ratio)

    return a, screen_w, mi_particle.f_blend


# --- Initial conditions & propagation ----------------------------------------------


def asymptotic_speed_from_shell(v: Vec3, r_mag: float, gm: float) -> float:
    """Reduce |v| at radius r to v_inf using specific orbital energy (Newtonian)."""
    v2 = _dot(v, v)
    return math.sqrt(max(v2 - 2.0 * gm / max(r_mag, 1.0), 0.0))


def flyby_initial_state(case: FlybyCase, body: RotatingBody) -> OrbitState:
    """
    3D Kepler hyperbola seed along inbound asymptote with impact parameter b.

    Position: r = r_start * k_in (k_in from inbound lat/lon).
    Impact-parameter axis in the plane ⊥ to k_in, rotated by b_azimuth_deg.
    |r×v| = b v_inf, energy v²/2 − GM/r = v_inf²/2.
    """
    k_in = unit_from_lat_lon(case.inbound_lat_deg, case.inbound_lon_deg)
    r = _scale(k_in, case.r_start)
    r_mag = case.r_start

    z_hat = (0.0, 0.0, 1.0)
    e1 = perpendicular_unit(k_in, z_hat)
    e2 = _unit(_cross(k_in, e1))
    az = math.radians(case.b_azimuth_deg)
    b_hat = _unit(_add(_scale(e1, math.cos(az)), _scale(e2, math.sin(az))))

    n_plane = _unit(_cross(k_in, b_hat))
    t_hat = _unit(_cross(n_plane, k_in))

    v_tang = case.impact_parameter * case.v_inf / r_mag
    v2 = case.v_inf * case.v_inf + 2.0 * body.gm / r_mag
    v_radial = -math.sqrt(max(v2 - v_tang * v_tang, 0.0))
    v = _add(_scale(k_in, v_radial), _scale(t_hat, v_tang))
    return OrbitState(r=r, v=v)


def rk4_step(
    state: OrbitState,
    body: RotatingBody,
    coupling: HQIVOrbitCoupling | None,
    settings: PropagationSettings,
    spin_sign: float,
    case: FlybyCase | None = None,
) -> OrbitState:
    dt = settings.dt
    t0 = state.t

    def deriv(r: Vec3, v: Vec3, t_sub: float) -> tuple[Vec3, Vec3]:
        a, _, _ = total_accel(r, v, body, coupling, settings, spin_sign, case, t_sub)
        return v, a

    r, v = state.r, state.v
    k1r, k1v = deriv(r, v, t0)
    r2 = _add(r, k1r, dt / 2.0)
    v2 = _add(v, k1v, dt / 2.0)
    k2r, k2v = deriv(r2, v2, t0 + dt / 2.0)
    r3 = _add(r, k2r, dt / 2.0)
    v3 = _add(v, k2v, dt / 2.0)
    k3r, k3v = deriv(r3, v3, t0 + dt / 2.0)
    r4 = _add(r, k3r, dt)
    v4 = _add(v, k3v, dt)
    k4r, k4v = deriv(r4, v4, t0 + dt)
    r_new = _add(r, _add(k1r, k2r, 2.0), dt / 6.0)
    r_new = _add(r_new, _add(k4r, k3r, 2.0), dt / 6.0)
    v_new = _add(v, _add(k1v, k2v, 2.0), dt / 6.0)
    v_new = _add(v_new, _add(k4v, k3v, 2.0), dt / 6.0)
    return OrbitState(r=r_new, v=v_new, t=state.t + dt)


def find_closest_approach_state(
    case: FlybyCase,
    body: RotatingBody,
    settings: PropagationSettings,
    spin_sign: float = 1.0,
) -> tuple[OrbitState, float]:
    """Lightweight classical pass to locate periapsis for chord-gate freezing."""
    state = flyby_initial_state(case, body)
    r_ca = float("inf")
    state_ca = state
    ca_step = 0
    n_steps_max = int(settings.t_max / settings.dt)
    escape_r_stop = max(settings.r_escape, case.r_start * 0.85)
    for step in range(n_steps_max):
        r_mag = _norm(state.r)
        radial_motion = _dot(state.r, state.v) / max(r_mag, 1.0)
        if r_mag < r_ca:
            r_ca = r_mag
            state_ca = state
            ca_step = step
        state = rk4_step(state, body, None, settings, spin_sign, case)
        if step > ca_step + 20 and r_mag >= escape_r_stop and radial_motion > 0.0:
            break
    return state_ca, r_ca


def propagate_flyby(
    case: FlybyCase,
    body: RotatingBody,
    coupling: HQIVOrbitCoupling | None,
    settings: PropagationSettings | None = None,
) -> dict[str, float | bool | str]:
    base = settings or PropagationSettings()
    settings = replace(
        base,
        h_reference=base.h_reference if base.h_reference is not None else flyby_h_reference(case),
    )
    spin_sign = case.spin_sign
    state = flyby_initial_state(case, body)
    frozen_gate: FrozenChordGate | None = None
    chord_track: ChordFlybyTrack | None = None
    if coupling is not None and coupling.chord_source_gate:
        clear_chord_kappa_cache()
        if coupling.chord_gate_use_track and not coupling.chord_gate_freeze_at_ca:
            chord_track = prepare_chord_flyby_track(
                case, body, coupling, settings, spin_sign
            )
        elif coupling.chord_gate_freeze_at_ca:
            frozen_gate = prepare_frozen_chord_gate(
                case, body, coupling, settings, spin_sign
            )

    r_ca = float("inf")
    t_ca = 0.0
    ca_step = 0
    v_in_samples: list[float] = []
    v_out_samples: list[float] = []
    v_in_vec_samples: list[Vec3] = []
    v_out_vec_samples: list[Vec3] = []
    oblate_samples: list[float] = []
    screen_samples: list[float] = []
    screen_in_samples: list[float] = []
    screen_out_samples: list[float] = []
    f_samples: list[float] = []
    annual_projection_samples: list[float] = []
    L_eq_samples: list[float] = []
    angular_rindler_samples: list[float] = []
    angular_rindler_at_ca = float("nan")

    n_steps_max = int(settings.t_max / settings.dt)
    escape_r_stop = max(settings.r_escape, case.r_start * 0.85)
    steps_taken = 0
    for step in range(n_steps_max):
        steps_taken = step + 1
        r_mag = _norm(state.r)
        radial_motion = _dot(state.r, state.v) / max(r_mag, 1.0)
        if r_mag < r_ca:
            r_ca = r_mag
            t_ca = state.t
            ca_step = step

        oblate_samples.append(oblate_latitude_factor(state.r))
        a_n = newton_accel(state.r, body, 1.0)
        if settings.use_j2:
            a_n = _add(a_n, j2_accel(state.r, body, 1.0))
        if settings.use_third_bodies and body.name.lower() == "earth":
            a_n = _add(a_n, earth_third_body_accel(state.r, case, state.t))
        a_ang = (
            orbital_angular_rindler_scale(state.r, state.v, a_n)
            if coupling is not None and coupling.orbital_angular_rindler
            else 0.0
        )
        angular_rindler_samples.append(a_ang)
        if step == ca_step:
            angular_rindler_at_ca = a_ang
        mi = modified_inertia_at_point(state.r, state.v, a_n, body, coupling, settings, case)
        screen_samples.append(mi.screen_weight)
        f_samples.append(mi.f_blend)
        if coupling and coupling.annual_lapse_phi and body.name.lower() == "earth":
            annual_projection_samples.append(
                annual_frame_projection(state.r, state.v, case.encounter_date)
            )
        if coupling and coupling.angular_momentum_screen:
            L_eq_samples.append(mi.L_eq_fraction)

        if r_mag >= settings.r_escape:
            v_asym = asymptotic_speed_from_shell(state.v, r_mag, body.gm)
            if step <= ca_step and radial_motion < 0.0:
                v_in_samples.append(v_asym)
                v_in_vec_samples.append(state.v)
                screen_in_samples.append(mi.screen_weight)
            elif step > ca_step + 5 and radial_motion > 0.0:
                v_out_samples.append(v_asym)
                v_out_vec_samples.append(state.v)
                screen_out_samples.append(mi.screen_weight)

        state = rk4_step(state, body, coupling, settings, spin_sign, case)

        if (
            step > ca_step + 20
            and len(v_in_samples) >= 5
            and len(v_out_samples) >= 10
            and r_mag >= escape_r_stop
            and radial_motion > 0.0
        ):
            break

    def _mean_vec(samples: list[Vec3]) -> Vec3:
        if not samples:
            return (float("nan"), float("nan"), float("nan"))
        n = float(len(samples))
        return (
            sum(s[0] for s in samples) / n,
            sum(s[1] for s in samples) / n,
            sum(s[2] for s in samples) / n,
        )

    v_in = sum(v_in_samples) / len(v_in_samples) if v_in_samples else float("nan")
    v_out = sum(v_out_samples) / len(v_out_samples) if v_out_samples else float("nan")
    delta_v = v_out - v_in if v_in_samples and v_out_samples else float("nan")

    v_in_vec = _mean_vec(v_in_vec_samples)
    v_out_vec = _mean_vec(v_out_vec_samples)
    lat_in = latitude_deg_of_vector(v_in_vec)
    lat_out = latitude_deg_of_vector(v_out_vec)
    lon_in = longitude_deg_of_vector(v_in_vec)
    lon_out = longitude_deg_of_vector(v_out_vec)
    deflection_deg = angle_between_deg(v_in_vec, v_out_vec)
    lat_exchange = abs(lat_out - lat_in) if not math.isnan(lat_out) and not math.isnan(lat_in) else float("nan")
    mean_oblate = sum(oblate_samples) / len(oblate_samples) if oblate_samples else float("nan")

    return {
        "label": case.label,
        "mode": "hqiv" if coupling else "classical",
        "r_ca_m": r_ca,
        "r_ca_km": r_ca / 1.0e3,
        "t_ca_s": t_ca,
        "v_in_asym_m_s": v_in,
        "v_out_asym_m_s": v_out,
        "delta_v_m_s": delta_v,
        "delta_v_mm_s": delta_v * 1.0e3 if not math.isnan(delta_v) else float("nan"),
        "inbound_lat_deg": case.inbound_lat_deg,
        "inbound_lon_deg": case.inbound_lon_deg,
        "b_azimuth_deg": case.b_azimuth_deg,
        "asymptote_lat_in_deg": lat_in,
        "asymptote_lat_out_deg": lat_out,
        "asymptote_lon_in_deg": lon_in,
        "asymptote_lon_out_deg": lon_out,
        "asymptote_deflection_deg": deflection_deg,
        "latitude_exchange_deg": lat_exchange,
        "mean_oblate_coupling": mean_oblate,
        "mean_one_minus_f": sum(screen_samples) / len(screen_samples) if screen_samples else float("nan"),
        "mean_f_blend": sum(f_samples) / len(f_samples) if f_samples else float("nan"),
        "mean_annual_projection": (
            sum(annual_projection_samples) / len(annual_projection_samples)
            if annual_projection_samples
            else float("nan")
        ),
        "max_one_minus_f": max(screen_samples) if screen_samples else float("nan"),
        "mean_one_minus_f_in": sum(screen_in_samples) / len(screen_in_samples) if screen_in_samples else float("nan"),
        "mean_one_minus_f_out": sum(screen_out_samples) / len(screen_out_samples) if screen_out_samples else float("nan"),
        "mean_L_eq_fraction": sum(L_eq_samples) / len(L_eq_samples) if L_eq_samples else float("nan"),
        "mean_orbital_angular_rindler_m_s2": (
            sum(angular_rindler_samples) / len(angular_rindler_samples)
            if angular_rindler_samples
            else float("nan")
        ),
        "max_orbital_angular_rindler_m_s2": (
            max(angular_rindler_samples) if angular_rindler_samples else float("nan")
        ),
        "orbital_angular_rindler_at_ca_m_s2": angular_rindler_at_ca,
        "h_reference_m2_s": settings.h_reference or flyby_h_reference(case),
        "phi_accel_si_at_ca": phi_acceleration_si(
            _scale(unit_from_lat_lon(case.inbound_lat_deg, case.inbound_lon_deg), r_ca), body
        )
        if r_ca < float("inf")
        else float("nan"),
        "chord_source_gate": (
            float(chord_track.gate_peak)
            if chord_track and chord_track.active
            else float(frozen_gate.gate)
            if frozen_gate and frozen_gate.active
            else float("nan")
        ),
        "chord_kappa_blend": (
            max(chord_track.kappa_blend)
            if chord_track and chord_track.active and chord_track.kappa_blend
            else float(frozen_gate.kappa_blend)
            if frozen_gate and frozen_gate.active
            else float("nan")
        ),
        "chord_track_samples": float(chord_track.n_track_samples)
        if chord_track and chord_track.active
        else 0.0,
        "chord_quadrature_calls": float(chord_track.n_quadrature_calls)
        if chord_track and chord_track.active
        else 0.0,
        "reported_anomaly_mm_s": case.reported_anomaly_mm_s,
        "n_steps": float(steps_taken),
        "n_steps_max": float(n_steps_max),
    }


def compare_classical_vs_hqiv(
    case: FlybyCase,
    body: RotatingBody,
    coupling: HQIVOrbitCoupling,
    settings: PropagationSettings | None = None,
) -> dict[str, object]:
    settings = settings or PropagationSettings()
    classical = propagate_flyby(case, body, None, settings)
    hqiv = propagate_flyby(case, body, coupling, settings)
    dv_c = float(classical["delta_v_mm_s"])
    dv_h = float(hqiv["delta_v_mm_s"])
    return {
        "case": case.label,
        "classical": classical,
        "hqiv": hqiv,
        "hqiv_minus_classical_mm_s": dv_h - dv_c if not (math.isnan(dv_c) or math.isnan(dv_h)) else float("nan"),
        "reported_anomaly_mm_s": case.reported_anomaly_mm_s,
        "notes": case.notes,
    }


# --- Catalog of literature flybys (approximate geometry) ---------------------------

EARTH = RotatingBody(
    name="Earth",
    gm=GM_EARTH,
    radius=R_EARTH,
    j2=J2_EARTH,
    omega=OMEGA_EARTH,
    m_shell=4,
)

FLYBY_CATALOG: dict[str, FlybyCase] = {
    "equator_to_pole": FlybyCase(
        label="Equator inbound → polar outbound (max oblate angle)",
        v_inf=8_890.0,
        impact_parameter=9_570_000.0,
        r_start=80.0 * R_EARTH,
        inbound_lat_deg=0.0,
        inbound_lon_deg=0.0,
        b_azimuth_deg=90.0,
        reported_anomaly_mm_s=None,
        notes="Tilted impact plane: equator approach, largest |Δλ| for J₂/HQIV probe",
    ),
    "equator_to_equator": FlybyCase(
        label="Equator inbound → equator outbound (reference)",
        v_inf=8_890.0,
        impact_parameter=9_570_000.0,
        r_start=80.0 * R_EARTH,
        inbound_lat_deg=0.0,
        inbound_lon_deg=0.0,
        b_azimuth_deg=180.0,
        reported_anomaly_mm_s=None,
        notes="Coplanar equatorial flyby; smaller latitude exchange",
    ),
    "near_1998": FlybyCase(
        label="NEAR Earth flyby (1998-01)",
        v_inf=6_850.0,
        impact_parameter=12_859_514.6,  # from hp=539 km, v_inf=6.85 km/s
        r_start=80.0 * R_EARTH,
        inbound_lat_deg=20.76,  # incoming velocity declination δ_in=-20.76°
        b_azimuth_deg=250.7,  # chosen so Kepler outgoing declination ≈ -71.96°
        reported_anomaly_mm_s=13.46,
        notes="Anderson table: δ_in=-20.76°, δ_out=-71.96°, hp=539 km",
        encounter_date="1998-01-23",
    ),
    "galileo_1990": FlybyCase(
        label="Galileo Earth flyby (1990-12)",
        v_inf=8_890.0,
        impact_parameter=11_307_892.0,  # from hp=960 km, v_inf=8.89 km/s
        r_start=80.0 * R_EARTH,
        inbound_lat_deg=12.52,  # incoming velocity declination δ_in=-12.52°
        b_azimuth_deg=215.0,  # chosen so Kepler outgoing declination ≈ -34.15°
        reported_anomaly_mm_s=3.92,
        notes="Anderson GL-I: δ_in=-12.52°, δ_out=-34.15°, hp=960 km",
        encounter_date="1990-12-08",
    ),
    "cassini_1999": FlybyCase(
        label="Cassini Earth flyby (1999-08)",
        v_inf=16_010.0,
        impact_parameter=8_974_490.0,  # from hp=1175 km, v_inf=16.01 km/s
        r_start=100.0 * R_EARTH,
        inbound_lat_deg=12.92,  # incoming velocity declination δ_in=-12.92°
        b_azimuth_deg=157.9,  # chosen so Kepler outgoing declination ≈ -4.99°
        reported_anomaly_mm_s=-0.5,
        notes="Anderson table: δ_in=-12.92°, δ_out=-4.99°, hp=1175 km",
        encounter_date="1999-08-18",
    ),
    "rosetta_2005": FlybyCase(
        label="Rosetta Earth flyby (2005-03)",
        v_inf=4_450.0,
        # ~1954 km altitude at CA ⇒ r_CA ≈ 8.33×10⁶ m; b ≈ r_CA v_CA/v_∞ (not 5300 km periapsis label).
        impact_parameter=20_122_454.3,
        r_start=80.0 * R_EARTH,
        inbound_lat_deg=2.81,  # incoming velocity declination δ_in=-2.81°
        b_azimuth_deg=325.7,  # chosen so Kepler outgoing declination ≈ -34.29°
        reported_anomaly_mm_s=1.80,
        notes="Anderson/Rosetta-I: δ_in=-2.81°, δ_out=-34.29°, hp≈1955 km",
        encounter_date="2005-03-04",
    ),
    "generic_deep": FlybyCase(
        label="Generic deep flyby (probe)",
        v_inf=10_000.0,
        impact_parameter=15_000_000.0,
        r_start=120.0 * R_EARTH,
        reported_anomaly_mm_s=None,
        notes="Template for parameter scans",
    ),
}

SUN = RotatingBody(
    name="Sun",
    gm=GM_SUN,
    radius=R_SUN,
    j2=0.0,
    omega=OMEGA_SUN,
    m_shell=0,
)

_OUMUAMUA_Q = 0.255 * AU
_OUMUAMUA_V = 26_330.0
_BORISOV_Q = 2.01 * AU
_BORISOV_V = 32_200.0

INTERSTELLAR_CATALOG: dict[str, FlybyCase] = {
    "oumuamua_2017": FlybyCase(
        label="1I/'Oumuamua (2017) — quiet hyperbolic Sun passage",
        v_inf=_OUMUAMUA_V,
        impact_parameter=impact_parameter_from_periapsis(_OUMUAMUA_Q, _OUMUAMUA_V, GM_SUN),
        r_start=35.0 * AU,
        inbound_lat_deg=0.0,
        inbound_lon_deg=0.0,
        b_azimuth_deg=35.0,
        central_body="sun",
        notes="q≈0.255 AU; non-gravitational forces neglected (quiet visitor)",
    ),
    "borisov_2019": FlybyCase(
        label="2I/Borisov (2019) — quiet hyperbolic Sun passage",
        v_inf=_BORISOV_V,
        impact_parameter=impact_parameter_from_periapsis(_BORISOV_Q, _BORISOV_V, GM_SUN),
        r_start=40.0 * AU,
        inbound_lat_deg=5.0,
        b_azimuth_deg=90.0,
        central_body="sun",
        notes="q≈2.01 AU; coma drag not modeled",
    ),
    "interstellar_ecliptic": FlybyCase(
        label="Generic quiet interstellar visitor (ecliptic)",
        v_inf=20_000.0,
        impact_parameter=impact_parameter_from_periapsis(1.0 * AU, 20_000.0, GM_SUN),
        r_start=80.0 * AU,
        inbound_lat_deg=0.0,
        b_azimuth_deg=180.0,
        central_body="sun",
        notes="Template: q=1 AU, v_∞=20 km/s",
    ),
    "interstellar_polar": FlybyCase(
        label="Generic quiet interstellar visitor (high inclination)",
        v_inf=20_000.0,
        impact_parameter=impact_parameter_from_periapsis(1.0 * AU, 20_000.0, GM_SUN),
        r_start=80.0 * AU,
        inbound_lat_deg=60.0,
        b_azimuth_deg=90.0,
        central_body="sun",
        notes="High ecliptic latitude; tests L_eq floor without planetary spin",
    ),
}

BODIES: dict[str, RotatingBody] = {
    "earth": EARTH,
    "sun": SUN,
}

ALL_ENCOUNTER_CATALOG: dict[str, FlybyCase] = {**FLYBY_CATALOG, **INTERSTELLAR_CATALOG}


def catalog_by_name(name: str) -> dict[str, FlybyCase]:
    key = name.lower()
    if key in ("earth", "planet", "flyby"):
        return FLYBY_CATALOG
    if key in ("interstellar", "iso", "sun"):
        return INTERSTELLAR_CATALOG
    if key == "all":
        return ALL_ENCOUNTER_CATALOG
    raise KeyError(f"unknown catalog {name!r}; use earth | interstellar | all")


def resolve_body(case: FlybyCase, body_override: str | None = None) -> RotatingBody:
    key = (body_override or case.central_body).lower()
    if key not in BODIES:
        raise KeyError(f"unknown body {key!r}; use: {', '.join(BODIES)}")
    return BODIES[key]


def propagation_settings_for(body: RotatingBody, case: FlybyCase | None = None) -> PropagationSettings:
    """Body-aware integrator window (Earth flyby vs quiet heliocentric hyperbola)."""
    r_lapse = body.lapse_radius()
    if body.name.lower() == "sun":
        return PropagationSettings(
            dt=86_400.0,  # 1 d steps (quiet ISO; use --dt to refine)
            t_max=6.0e8,
            rotating_frame=False,
            use_j2=False,
            use_third_bodies=False,
            r_escape=5.0 * AU,  # asymptotic readout shell; separate from bunched solar lapse
            ca_search_radius=4.0 * max(r_lapse, AU),
        )
    dt = 4.0 if case and case.v_inf > 12_000.0 else 2.0
    return PropagationSettings(
        dt=dt,
        t_max=250_000.0,
        rotating_frame=False,
        use_j2=body.j2 != 0.0,
        use_third_bodies=body.name.lower() == "earth",
        r_escape=40.0 * r_lapse,
        ca_search_radius=20.0 * r_lapse,
    )


def spin_reversal_test(
    case: FlybyCase,
    body: RotatingBody,
    coupling: HQIVOrbitCoupling,
    settings: PropagationSettings | None = None,
) -> dict[str, float]:
    """HQIV anomaly should flip sign when planet spin is reversed (odd in dot ∝ ω×r)."""
    settings = settings or PropagationSettings()
    pos = propagate_flyby(case, body, coupling, settings)
    neg_case = FlybyCase(
        label=case.label + " (spin flip)",
        v_inf=case.v_inf,
        impact_parameter=case.impact_parameter,
        r_start=case.r_start,
        spin_sign=-case.spin_sign,
        inbound_lat_deg=case.inbound_lat_deg,
        inbound_lon_deg=case.inbound_lon_deg,
        b_azimuth_deg=case.b_azimuth_deg,
        reported_anomaly_mm_s=case.reported_anomaly_mm_s,
        notes=case.notes,
        central_body=case.central_body,
        encounter_date=case.encounter_date,
    )
    neg = propagate_flyby(neg_case, body, coupling, settings)
    return {
        "delta_v_mm_s_spin_pos": float(pos["delta_v_mm_s"]),
        "delta_v_mm_s_spin_neg": float(neg["delta_v_mm_s"]),
        "sum_mm_s": float(pos["delta_v_mm_s"]) + float(neg["delta_v_mm_s"]),
    }


def _print_oblate_geometry(row: dict[str, object]) -> None:
    c = row if "asymptote_lat_in_deg" in row else row.get("classical", row)
    print(
        f"  asymptotes (in→out lat)     : {c.get('asymptote_lat_in_deg', float('nan')):.2f}° → "
        f"{c.get('asymptote_lat_out_deg', float('nan')):.2f}°  "
        f"(|Δλ|={c.get('latitude_exchange_deg', float('nan')):.2f}°, "
        f"deflection={c.get('asymptote_deflection_deg', float('nan')):.2f}°)"
    )
    print(
        f"  IC oblate angles            : inbound lat={c.get('inbound_lat_deg')}°, "
        f"b_azimuth={c.get('b_azimuth_deg')}°, mean J₂ weight={c.get('mean_oblate_coupling', float('nan')):.4f}"
    )


def scan_oblate_asymptote_angles(
    base: FlybyCase,
    body: RotatingBody,
    coupling: HQIVOrbitCoupling | None,
    settings: PropagationSettings | None = None,
    b_azimuths_deg: Iterable[float] = (0.0, 45.0, 90.0, 135.0, 180.0),
    inbound_lats_deg: Iterable[float] = (0.0,),
) -> list[dict[str, object]]:
    """
    Compare Δv and latitude exchange vs inbound latitude and impact-plane tilt.

    Literature pattern: equator approach with tilted oblate plane (b_azimuth ~ 90°)
    tends to maximize |λ_out − λ_in| and the flyby anomaly proxy.
    """
    settings = settings or PropagationSettings()
    rows: list[dict[str, object]] = []
    for lat_in in inbound_lats_deg:
        for b_az in b_azimuths_deg:
            case = FlybyCase(
                label=f"{base.label} lat_in={lat_in} b_az={b_az}",
                v_inf=base.v_inf,
                impact_parameter=base.impact_parameter,
                r_start=base.r_start,
                spin_sign=base.spin_sign,
                inbound_lat_deg=lat_in,
                inbound_lon_deg=base.inbound_lon_deg,
                b_azimuth_deg=b_az,
                reported_anomaly_mm_s=base.reported_anomaly_mm_s,
                notes=base.notes,
                central_body=base.central_body,
                encounter_date=base.encounter_date,
            )
            row = propagate_flyby(case, body, coupling, settings)
            rows.append(row)
    return rows


def run_all_flybys(
    body: RotatingBody,
    coupling: HQIVOrbitCoupling,
    settings: PropagationSettings | None = None,
    *,
    catalog: dict[str, FlybyCase] | None = None,
) -> list[dict[str, object]]:
    """Run every catalog case for this central body: classical + HQIV + comparison row."""
    catalog = catalog or FLYBY_CATALOG
    rows: list[dict[str, object]] = []
    for key, case in catalog.items():
        if case.central_body.lower() != body.name.lower():
            continue
        case_settings = settings or propagation_settings_for(body, case)
        cmp_row = compare_classical_vs_hqiv(case, body, coupling, case_settings)
        c = cmp_row["classical"]
        h = cmp_row["hqiv"]
        rows.append(
            {
                "case_id": key,
                "central_body": case.central_body,
                "label": case.label,
                "reported_anomaly_mm_s": case.reported_anomaly_mm_s,
                "v_inf_m_s": case.v_inf,
                "impact_parameter_km": case.impact_parameter / 1.0e3,
                "inbound_lat_deg": case.inbound_lat_deg,
                "inbound_lon_deg": case.inbound_lon_deg,
                "b_azimuth_deg": case.b_azimuth_deg,
                "classical_delta_v_mm_s": c["delta_v_mm_s"],
                "hqiv_delta_v_mm_s": h["delta_v_mm_s"],
                "hqiv_minus_classical_mm_s": cmp_row["hqiv_minus_classical_mm_s"],
                "r_ca_km": c["r_ca_km"],
                "asymptote_lat_in_deg": c["asymptote_lat_in_deg"],
                "asymptote_lat_out_deg": c["asymptote_lat_out_deg"],
                "latitude_exchange_deg": c["latitude_exchange_deg"],
                "asymptote_deflection_deg": c["asymptote_deflection_deg"],
                "mean_oblate_coupling": c["mean_oblate_coupling"],
                "mean_one_minus_f": h["mean_one_minus_f"],
                "mean_one_minus_f_in": h["mean_one_minus_f_in"],
                "mean_one_minus_f_out": h["mean_one_minus_f_out"],
                "mean_L_eq_fraction": h["mean_L_eq_fraction"],
                "mean_orbital_angular_rindler_m_s2": h["mean_orbital_angular_rindler_m_s2"],
                "max_orbital_angular_rindler_m_s2": h["max_orbital_angular_rindler_m_s2"],
                "orbital_angular_rindler_at_ca_m_s2": h["orbital_angular_rindler_at_ca_m_s2"],
                "max_one_minus_f": h["max_one_minus_f"],
                "hqiv_latitude_exchange_deg": h["latitude_exchange_deg"],
                "notes": case.notes,
            }
        )
    return rows


def paper_nominal_coupling() -> HQIVOrbitCoupling:
    """Coupling documented in papers/orbital_flyby (repartitioned horizon)."""
    return HQIVOrbitCoupling(
        vacuum_scale=1.0,
        metric_phi_scale=1.0,
        geff_on_newton=True,
        paper_inertia_screen=True,
        modified_inertia_geodesic=True,
        lapse_drag_phi=True,
        horizon_repartition=True,
        horizon_metric_channel=True,
        suppress_vacuum_spin_coupling=True,
        annual_lapse_phi=False,
        galactic_disk_lapse_phi=True,
        angular_momentum_screen=True,
        orbital_angular_rindler=True,
        velocity_screen=True,
    )


def paper_chord_source_coupling() -> HQIVOrbitCoupling:
    """Nominal repartitioned horizon plus chord-gated phase-geometry source boost."""
    return replace(
        paper_nominal_coupling(),
        chord_source_gate=True,
        phase_geometry_source=True,
        source_kappa_m_shell=4,
        chord_gate_strength=1.0,
        chord_gate_step_deg=2.0,
        chord_gate_samples=4,
        chord_gate_use_track=True,
        chord_gate_freeze_at_ca=False,
        chord_track_collect_stride=10,
        chord_track_target_samples=48,
        lapse_drag_coherence_gate=True,
    )


def paper_legacy_coupling() -> HQIVOrbitCoupling:
    """Pre-repartition nominal: co-spin in φ_eff, G_eff folded into GM source."""
    return replace(
        paper_nominal_coupling(),
        horizon_repartition=False,
        horizon_metric_channel=False,
        suppress_vacuum_spin_coupling=False,
        lapse_drag_colatitude=False,
        lapse_drag_lense_thirring=False,
        geff_as_time_factor=False,
    )


def _print_run_all_table(rows: list[dict[str, object]]) -> None:
    print(
        f"\n{'case':<22} {'body':>5} {'lit.':>7} {'|Δλ|°':>6} {'r_CA':>9} "
        f"{'⟨1−f⟩out':>9} {'Δv_cls':>10} {'HQIV−cls':>10}"
    )
    print("-" * 96)
    for row in rows:
        lit = row["reported_anomaly_mm_s"]
        lit_s = f"{lit:7.2f}" if lit is not None else "    n/a"
        sw_out = row.get("mean_one_minus_f_out", float("nan"))
        body = row.get("central_body", "?")
        r_ca = row["r_ca_km"]
        r_ca_s = f"{r_ca:9.1f}" if r_ca == r_ca else "      n/a"
        print(
            f"{row['case_id']:<22} {str(body):>5} {lit_s:>7} "
            f"{row['latitude_exchange_deg']:6.2f} {r_ca_s} {sw_out:9.2e} "
            f"{row['classical_delta_v_mm_s']:10.2f} "
            f"{row['hqiv_minus_classical_mm_s']:10.2f}"
        )


def _print_result(row: dict[str, object]) -> None:
    print(f"\n=== {row.get('case', row.get('label', '?'))} ===")
    if "classical" in row:
        c = row["classical"]
        h = row["hqiv"]
        print(f"  classical Δv (asymptotic)     : {c['delta_v_mm_s']:.4f} mm/s")
        print(f"  HQIV Δv (asymptotic)        : {h['delta_v_mm_s']:.4f} mm/s")
        print(f"  HQIV − classical            : {row['hqiv_minus_classical_mm_s']:.4f} mm/s")
        rep = row.get("reported_anomaly_mm_s")
        if rep is not None:
            print(f"  literature target (approx.) : {rep} mm/s")
        print(f"  closest approach            : {c['r_ca_km']:.1f} km")
        _print_oblate_geometry(c)
        print(
            "  note: |classical Δv| is the RK4+J2 baseline (not fitted to data); "
            "use HQIV−classical and --scan-scale to probe O-Maxwell slots."
        )
    else:
        print(f"  mode={row.get('mode')}  Δv={row.get('delta_v_mm_s')} mm/s  r_CA={row.get('r_ca_km')} km")
        _print_oblate_geometry(row)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="HQIV O-Maxwell hyperbolic encounter calculator (Earth flybys + interstellar Sun)"
    )
    parser.add_argument(
        "--catalog",
        default="earth",
        choices=("earth", "interstellar", "all"),
        help="case catalog: earth flybys | interstellar ISO | all",
    )
    parser.add_argument(
        "--body",
        default=None,
        choices=tuple(BODIES.keys()),
        help="override central body (default: per-case central_body)",
    )
    parser.add_argument("--case", default="galileo_1990", help="case id from active --catalog")
    parser.add_argument("--list-cases", action="store_true")
    parser.add_argument("--hqiv-scale", type=float, default=100.0, help="vacuum_scale for g_vac probe")
    parser.add_argument("--metric-scale", type=float, default=1.0e3, help="metric_phi_scale")
    parser.add_argument("--kappa-l", type=float, default=0.0, help="longitudinal stress coefficient")
    parser.add_argument("--no-geff", action="store_true", help="disable (φ/φ_ref)^α on Newton/J2")
    parser.add_argument(
        "--no-screen",
        action="store_true",
        help="disable paper inertia screen (1−f) and velocity screen (1−v²/c²)",
    )
    parser.add_argument(
        "--no-l-screen",
        action="store_true",
        help="disable angular-momentum-dependent screen (isotropic a only)",
    )
    parser.add_argument(
        "--no-angular-rindler",
        action="store_true",
        help="disable changing-orbital-angular-rate Rindler inertia scale",
    )
    parser.add_argument(
        "--no-modified-geodesic",
        action="store_true",
        help="disable a ← a_GR/f (keep (1−f) on O-Maxwell slots only)",
    )
    parser.add_argument(
        "--no-lapse-drag",
        action="store_true",
        help="disable co-spinning lapse-drag contribution to φ_eff",
    )
    parser.add_argument(
        "--no-annual-lapse",
        action="store_true",
        help="disable date-dependent Earth orbital-frame contribution to φ_eff",
    )
    parser.add_argument(
        "--annual-lapse",
        action="store_true",
        help="enable experimental date-dependent Earth orbital-frame contribution to φ_eff",
    )
    parser.add_argument(
        "--annual-lapse-strength",
        type=float,
        default=0.0,
        help="dimensionless multiplier for --annual-lapse (default 0; full v⊕/c is usually too large)",
    )
    parser.add_argument(
        "--no-galactic-disk-lapse",
        action="store_true",
        help="disable derived Milky-Way disk Rindler lapse term",
    )
    parser.add_argument(
        "--dt",
        type=float,
        default=None,
        help="integrator step [s]; default is body-aware (Earth ~2–4 s, Sun ~1 d)",
    )
    parser.add_argument("--rotating-frame", action="store_true")
    parser.add_argument("--no-j2", action="store_true")
    parser.add_argument(
        "--no-third-bodies",
        action="store_true",
        help="disable Sun/Moon third-body tide in Earth-centered flybys",
    )
    parser.add_argument("--spin-test", action="store_true", help="run spin reversal diagnostic")
    parser.add_argument(
        "--scan-scale",
        action="store_true",
        help="log |HQIV−classical| mm/s for vacuum_scale in [0, 10, …, 1e5]",
    )
    parser.add_argument(
        "--scan-oblate",
        action="store_true",
        help="scan b_azimuth and report Δv vs outbound latitude (equator→pole probe)",
    )
    parser.add_argument("--inbound-lat", type=float, default=None, help="override inbound latitude (deg)")
    parser.add_argument("--inbound-lon", type=float, default=None, help="override inbound longitude (deg)")
    parser.add_argument("--b-azimuth", type=float, default=None, help="override impact-plane azimuth (deg)")
    parser.add_argument(
        "--run-all",
        action="store_true",
        help="run every catalog flyby and write a results table (+ optional JSON)",
    )
    parser.add_argument(
        "--output",
        type=str,
        default="",
        help="JSON path for --run-all (default: scripts/artifacts/orbital_flyby_results.json)",
    )
    parser.add_argument(
        "--equations",
        choices=("latex", "md"),
        help="print locked equation sheet and exit",
    )
    parser.add_argument(
        "--paper-table",
        action="store_true",
        help="run catalog with paper nominal coupling; print LaTeX table rows",
    )
    parser.add_argument(
        "--paper-nominal",
        action="store_true",
        help="use nominal coupling (κ=1, φ_hom geometric readout, spin vacuum off)",
    )
    args = parser.parse_args(argv)

    if args.equations:
        from hqiv_flyby_equations import print_equations

        print_equations(args.equations)
        return 0

    active_catalog = catalog_by_name(args.catalog)

    if args.list_cases:
        for key, fc in active_catalog.items():
            rep = fc.reported_anomaly_mm_s
            rep_s = f"{rep} mm/s" if rep is not None else "n/a"
            print(f"  {key:22s}  [{fc.central_body:5s}]  {fc.label}  (reported ~ {rep_s})")
        return 0

    if args.paper_table:
        coupling = paper_nominal_coupling()
        from hqiv_flyby_equations import format_paper_table_latex

        rows: list[dict[str, object]] = []
        if args.catalog == "all":
            for body in BODIES.values():
                rows.extend(
                    run_all_flybys(
                        body,
                        coupling,
                        None,
                        catalog=ALL_ENCOUNTER_CATALOG,
                    )
                )
        else:
            body_key = args.body or ("sun" if args.catalog == "interstellar" else "earth")
            rows = run_all_flybys(BODIES[body_key], coupling, None, catalog=active_catalog)
        print(format_paper_table_latex(rows))
        return 0

    if args.case not in active_catalog:
        parser.error(f"unknown case {args.case!r} in catalog {args.catalog!r}")

    case = active_catalog[args.case]
    body = resolve_body(case, args.body)
    settings = propagation_settings_for(body, case)
    if args.dt is not None:
        settings = replace(settings, dt=args.dt)
    if args.rotating_frame:
        settings = replace(settings, rotating_frame=True)
    if args.no_j2:
        settings = replace(settings, use_j2=False)
    if args.no_third_bodies:
        settings = replace(settings, use_third_bodies=False)
    if args.inbound_lat is not None or args.inbound_lon is not None or args.b_azimuth is not None:
        case = FlybyCase(
            label=case.label,
            v_inf=case.v_inf,
            impact_parameter=case.impact_parameter,
            r_start=case.r_start,
            spin_sign=case.spin_sign,
            inbound_lat_deg=case.inbound_lat_deg if args.inbound_lat is None else args.inbound_lat,
            inbound_lon_deg=case.inbound_lon_deg if args.inbound_lon is None else args.inbound_lon,
            b_azimuth_deg=case.b_azimuth_deg if args.b_azimuth is None else args.b_azimuth,
            reported_anomaly_mm_s=case.reported_anomaly_mm_s,
            notes=case.notes,
            central_body=case.central_body,
            encounter_date=case.encounter_date,
        )
    if args.paper_nominal:
        coupling = paper_nominal_coupling()
        if args.annual_lapse:
            coupling = replace(
                coupling,
                annual_lapse_phi=not args.no_annual_lapse,
                annual_lapse_strength=args.annual_lapse_strength,
            )
    else:
        coupling = HQIVOrbitCoupling(
            vacuum_scale=args.hqiv_scale,
            metric_phi_scale=args.metric_scale,
            kappa_l=args.kappa_l,
            geff_on_newton=not args.no_geff,
            paper_inertia_screen=not args.no_screen,
            modified_inertia_geodesic=not args.no_screen and not args.no_modified_geodesic,
            lapse_drag_phi=not args.no_screen and not args.no_lapse_drag,
            annual_lapse_phi=not args.no_screen and args.annual_lapse and not args.no_annual_lapse,
            annual_lapse_strength=args.annual_lapse_strength,
            galactic_disk_lapse_phi=not args.no_screen and not args.no_galactic_disk_lapse,
            angular_momentum_screen=not args.no_screen and not args.no_l_screen,
            orbital_angular_rindler=not args.no_screen and not args.no_angular_rindler,
            velocity_screen=not args.no_screen,
        )
    if args.no_angular_rindler and args.paper_nominal:
        coupling = replace(coupling, orbital_angular_rindler=False)

    if args.run_all:
        rows = []
        if args.catalog == "all":
            for b in BODIES.values():
                rows.extend(
                    run_all_flybys(b, coupling, settings, catalog=ALL_ENCOUNTER_CATALOG)
                )
        else:
            rows = run_all_flybys(body, coupling, settings, catalog=active_catalog)
        _print_run_all_table(rows)
        out_path = Path(args.output) if args.output else Path(__file__).resolve().parent / "artifacts" / "orbital_flyby_results.json"
        out_path.parent.mkdir(parents=True, exist_ok=True)
        payload = {
            "generated_utc": datetime.now(timezone.utc).isoformat(),
            "settings": {
                "dt": settings.dt,
                "t_max": settings.t_max,
                "use_j2": settings.use_j2,
                "use_third_bodies": settings.use_third_bodies,
                "r_escape_earth_radii": settings.r_escape / R_EARTH,
            },
            "hqiv_coupling": {
                "vacuum_scale": coupling.vacuum_scale,
                "metric_phi_scale": coupling.metric_phi_scale,
                "geff_on_newton": coupling.geff_on_newton,
                "paper_inertia_screen": coupling.paper_inertia_screen,
                "modified_inertia_geodesic": coupling.modified_inertia_geodesic,
                "lapse_drag_phi": coupling.lapse_drag_phi,
                "annual_lapse_phi": coupling.annual_lapse_phi,
                "annual_lapse_strength": coupling.annual_lapse_strength,
                "galactic_disk_lapse_phi": coupling.galactic_disk_lapse_phi,
                "galactic_disk_lapse_strength": coupling.galactic_disk_lapse_strength,
                "galactic_disk_support_fraction": galactic_disk_support_fraction(),
                "galactic_rindler_denominator": galactic_rindler_denominator(),
                "lapse_drag_power": coupling.lapse_drag_power,
                "lapse_drag_strength": coupling.lapse_drag_strength,
                "angular_momentum_screen": coupling.angular_momentum_screen,
                "orbital_angular_rindler": coupling.orbital_angular_rindler,
                "velocity_screen": coupling.velocity_screen,
                "kappa_l": coupling.kappa_l,
            },
            "phi_homogeneous_si_m_s2": phi_acceleration_homogeneous_si(),
            "flybys": rows,
        }
        out_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
        print(f"\nWrote {out_path}")
        return 0

    if args.scan_oblate:
        print(f"\nOblate asymptote scan (base: {case.label})")
        print(
            f"{'b_az°':>6} {'λ_in°':>7} {'λ_out°':>7} {'|Δλ|°':>7} "
            f"{'defl°':>7} {'Δv mm/s':>12} {'J2 wt':>7}"
        )
        rows = scan_oblate_asymptote_angles(case, body, coupling, settings)
        best = max(rows, key=lambda r: float(r.get("latitude_exchange_deg", 0.0)))
        for row in rows:
            print(
                f"{row['b_azimuth_deg']:6.0f} {row['asymptote_lat_in_deg']:7.2f} "
                f"{row['asymptote_lat_out_deg']:7.2f} {row['latitude_exchange_deg']:7.2f} "
                f"{row['asymptote_deflection_deg']:7.2f} {row['delta_v_mm_s']:12.4f} "
                f"{row['mean_oblate_coupling']:7.4f}"
            )
        print(
            f"\nmax |Δλ|: b_azimuth={best['b_azimuth_deg']}°  "
            f"λ_out={best['asymptote_lat_out_deg']:.2f}°  Δv={best['delta_v_mm_s']:.4f} mm/s"
        )
        return 0

    if args.scan_scale:
        print(f"\nScale scan for {case.label} (target {case.reported_anomaly_mm_s} mm/s):")
        for scale in (0.0, 1.0, 10.0, 50.0, 100.0, 500.0, 1000.0, 5000.0, 10000.0):
            c = HQIVOrbitCoupling(vacuum_scale=scale, metric_phi_scale=scale)
            row = compare_classical_vs_hqiv(case, body, c, settings)
            excess = float(row["hqiv_minus_classical_mm_s"])
            print(f"  vacuum_scale={scale:8.0f}  HQIV−classical={excess:12.4f} mm/s")
        return 0

    result = compare_classical_vs_hqiv(case, body, coupling, settings)
    _print_result(result)

    if args.spin_test:
        if body.omega == 0.0:
            print("\n--- spin reversal skipped (non-rotating central body) ---")
        else:
            flip = spin_reversal_test(case, body, coupling, settings)
            print("\n--- spin reversal (HQIV should be approximately odd in ω) ---")
            print(f"  Δv(+ω) = {flip['delta_v_mm_s_spin_pos']:.6f} mm/s")
            print(f"  Δv(−ω) = {flip['delta_v_mm_s_spin_neg']:.6f} mm/s")
            print(f"  sum     = {flip['sum_mm_s']:.6f} mm/s  (→ 0 if odd)")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())

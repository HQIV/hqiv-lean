#!/usr/bin/env python3
"""HQIV wide-binary calculator using the shared mass-horizon / inertia screen."""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from hqiv_galaxy_rotation import (
    G_NEWTON,
    M_SUN_KG,
    hqiv_inertia_factor,
    mass_horizon_doppler_lapse,
    phi_acceleration_homogeneous_si,
)

AU = 1.495978707e11
PC_TO_M = 3.0856775814913673e16
YEAR_S = 365.25 * 86400.0
R_SUN = 6.957e8

Vec3 = tuple[float, float, float]


def phi_of_shell(m: int) -> float:
    return 2.0 * (float(m) + 1.0)


def vec_add(*parts: Vec3) -> Vec3:
    return (
        sum(p[0] for p in parts),
        sum(p[1] for p in parts),
        sum(p[2] for p in parts),
    )


def vec_sub(a: Vec3, b: Vec3) -> Vec3:
    return (a[0] - b[0], a[1] - b[1], a[2] - b[2])


def vec_scale(a: Vec3, s: float) -> Vec3:
    return (a[0] * s, a[1] * s, a[2] * s)


def vec_dot(a: Vec3, b: Vec3) -> float:
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]


def vec_norm(a: Vec3) -> float:
    return math.sqrt(vec_dot(a, a))


def vec_unit(a: Vec3) -> Vec3:
    n = vec_norm(a)
    if n <= 0.0:
        return (0.0, 0.0, 1.0)
    return vec_scale(a, 1.0 / n)


def vec_cross(a: Vec3, b: Vec3) -> Vec3:
    return (
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0],
    )


@dataclass(frozen=True)
class StarComponent:
    mass_kg: float
    radius_m: float = R_SUN
    omega_rad_s: float = 0.0
    phi_shell: int = 0
    lapse_radius_m: float | None = None

    def phi_reference(self) -> float:
        return phi_of_shell(self.phi_shell)

    def lapse_radius(self) -> float:
        return self.lapse_radius_m if self.lapse_radius_m is not None else self.radius_m


@dataclass(frozen=True)
class BinaryElements:
    """Keplerian elements for the relative two-body orbit (orbital plane z=0)."""

    semi_major_axis_m: float
    eccentricity: float
    mean_anomaly_rad: float = 0.0


@dataclass(frozen=True)
class BinaryElements3D:
    """Full Keplerian elements (orbital plane); angles in radians."""

    semi_major_axis_m: float
    eccentricity: float
    inclination_rad: float = 0.0
    longitude_ascending_rad: float = 0.0
    argument_periapsis_rad: float = 0.0
    mean_anomaly_rad: float = 0.0


@dataclass(frozen=True)
class WideBinaryPreset:
    name: str
    star1: StarComponent
    star2: StarComponent
    elements: BinaryElements
    note: str
    reference_separation_au: float | None = None


WIDE_BINARY_PRESETS: dict[str, WideBinaryPreset] = {
    "demo_circular_1au": WideBinaryPreset(
        name="demo_circular_1au",
        star1=StarComponent(mass_kg=1.0 * M_SUN_KG, omega_rad_s=2.0e-6),
        star2=StarComponent(mass_kg=1.0 * M_SUN_KG, omega_rad_s=-2.0e-6),
        elements=BinaryElements(semi_major_axis_m=AU, eccentricity=0.0),
        note="Equal-mass circular orbit at 1 AU for method checks.",
        reference_separation_au=1.0,
    ),
    "demo_wide_eccentric": WideBinaryPreset(
        name="demo_wide_eccentric",
        star1=StarComponent(mass_kg=1.0 * M_SUN_KG, omega_rad_s=1.0e-6),
        star2=StarComponent(mass_kg=0.8 * M_SUN_KG, omega_rad_s=-8.0e-7),
        elements=BinaryElements(semi_major_axis_m=5000.0 * AU, eccentricity=0.4),
        note="Wide, mildly eccentric pair for peri/apo acceleration contrast.",
        reference_separation_au=5000.0,
    ),
    "literature_scale_10kau": WideBinaryPreset(
        name="literature_scale_10kau",
        star1=StarComponent(mass_kg=1.2 * M_SUN_KG, omega_rad_s=2.0e-6),
        star2=StarComponent(mass_kg=0.9 * M_SUN_KG, omega_rad_s=-1.5e-6),
        elements=BinaryElements(semi_major_axis_m=1.0e4 * AU, eccentricity=0.3),
        note="Order-of-magnitude wide-binary parameters (not a specific Gaia solution).",
        reference_separation_au=1.0e4,
    ),
}


def mean_anomaly_to_eccentric_anomaly(mean_anomaly_rad: float, e: float) -> float:
    e = min(max(e, 0.0), 0.999999)
    m = mean_anomaly_rad
    for _ in range(80):
        dm = (m + e * math.sin(m) - mean_anomaly_rad) / (1.0 - e * math.cos(m))
        m -= dm
        if abs(dm) < 1.0e-14:
            break
    return m


def rot_z(angle: float) -> tuple[Vec3, Vec3, Vec3]:
    c, s = math.cos(angle), math.sin(angle)
    return ((c, -s, 0.0), (s, c, 0.0), (0.0, 0.0, 1.0))


def rot_x(angle: float) -> tuple[Vec3, Vec3, Vec3]:
    c, s = math.cos(angle), math.sin(angle)
    return ((1.0, 0.0, 0.0), (0.0, c, -s), (0.0, s, c))


def mat_vec(m: tuple[Vec3, Vec3, Vec3], v: Vec3) -> Vec3:
    return (
        m[0][0] * v[0] + m[0][1] * v[1] + m[0][2] * v[2],
        m[1][0] * v[0] + m[1][1] * v[1] + m[1][2] * v[2],
        m[2][0] * v[0] + m[2][1] * v[1] + m[2][2] * v[2],
    )


def mat_mul(a: tuple[Vec3, Vec3, Vec3], b: tuple[Vec3, Vec3, Vec3]) -> tuple[Vec3, Vec3, Vec3]:
    return (
        mat_vec(a, b[0]),
        mat_vec(a, b[1]),
        mat_vec(a, b[2]),
    )


def relative_orbit_vectors(
    elements: BinaryElements | BinaryElements3D,
    m1: float,
    m2: float,
) -> tuple[Vec3, Vec3]:
    """Relative position and velocity in the orbital plane, then rotated to inertial axes."""
    a = elements.semi_major_axis_m
    e = elements.eccentricity
    e_anom = mean_anomaly_to_eccentric_anomaly(elements.mean_anomaly_rad, e)
    nu = 2.0 * math.atan2(
        math.sqrt(1.0 + e) * math.sin(e_anom / 2.0),
        math.sqrt(1.0 - e) * math.cos(e_anom / 2.0),
    )
    r_mag = a * (1.0 - e * e) / (1.0 + e * math.cos(nu))
    mu = G_NEWTON * (m1 + m2)
    v_mag = math.sqrt(max(mu * (2.0 / r_mag - 1.0 / a), 0.0))
    r_rel = (r_mag * math.cos(nu), r_mag * math.sin(nu), 0.0)
    v_rel = (-v_mag * math.sin(nu), v_mag * math.cos(nu), 0.0)
    if isinstance(elements, BinaryElements3D):
        r_mat = mat_mul(
            rot_z(elements.longitude_ascending_rad),
            mat_mul(rot_x(elements.inclination_rad), rot_z(elements.argument_periapsis_rad)),
        )
        r_rel = mat_vec(r_mat, r_rel)
        v_rel = mat_vec(r_mat, v_rel)
    return r_rel, v_rel


def elements_to_barycentric(
    elements: BinaryElements | BinaryElements3D,
    m1: float,
    m2: float,
) -> tuple[Vec3, Vec3, Vec3, Vec3]:
    """Place star 1 and star 2 on the relative orbit."""
    r_rel, v_rel = relative_orbit_vectors(elements, m1, m2)
    m_tot = m1 + m2
    r1 = vec_scale(r_rel, m2 / m_tot)
    r2 = vec_scale(r_rel, -m1 / m_tot)
    v1 = vec_scale(v_rel, m2 / m_tot)
    v2 = vec_scale(v_rel, -m1 / m_tot)
    return r1, v1, r2, v2


def barycentric_from_observed(
    r_rel: Vec3,
    v_rel: Vec3,
    m1: float,
    m2: float,
) -> tuple[Vec3, Vec3, Vec3, Vec3]:
    """Split relative kinematics into barycentric components (origin at CM)."""
    m_tot = m1 + m2
    r1 = vec_scale(r_rel, m2 / m_tot)
    r2 = vec_scale(r_rel, -m1 / m_tot)
    v1 = vec_scale(v_rel, m2 / m_tot)
    v2 = vec_scale(v_rel, -m1 / m_tot)
    return r1, v1, r2, v2


def newtonian_acceleration_on_body(r_body: Vec3, r_other: Vec3, m_other: float) -> Vec3:
    dr = vec_sub(r_other, r_body)
    d = vec_norm(dr)
    if d <= 0.0:
        return (0.0, 0.0, 0.0)
    return vec_scale(dr, G_NEWTON * m_other / (d * d * d))


def phi_readout_star(r_m: Vec3, star: StarComponent) -> float:
    r = vec_norm(r_m)
    base = phi_of_shell(star.phi_shell)
    return base / (1.0 + r / star.lapse_radius())


def hqiv_effective_acceleration_m_s2(
    r_body: Vec3,
    v_body: Vec3,
    star: StarComponent,
    a_newton: Vec3,
    *,
    use_spin_lapse: bool,
    use_rindler_denominator: bool,
) -> tuple[float, float, float]:
    """
    Return (|a_hqiv|, f, one_minus_f) for one component.

    Same screen as galaxies/flybys: f = a/(a+phi/6), with phi_full including the
  co-spinning mass-horizon Doppler term from stellar rotation projected onto motion.
    """
    a_n = vec_norm(a_newton)
    phi_part = phi_acceleration_homogeneous_si() * (
        phi_readout_star(r_body, star) / max(star.phi_reference(), 1.0e-30)
    )
    eps = 0.0
    if use_spin_lapse and abs(star.omega_rad_s) > 0.0:
        spin_axis = (0.0, 0.0, 1.0 if star.omega_rad_s >= 0.0 else -1.0)
        v_tan = abs(star.omega_rad_s) * star.radius_m
        projection = abs(vec_dot(vec_unit(v_body), vec_unit(vec_cross(spin_axis, r_body))))
        eps = mass_horizon_doppler_lapse(
            v_tan,
            projection=projection,
            support_fraction=1.0,
            use_rindler_denominator=use_rindler_denominator,
        )
    phi_full = phi_part + 6.0 * a_n * eps
    f = hqiv_inertia_factor(a_n, phi_full)
    a_hqiv = a_n / max(f, 1.0e-15)
    return a_hqiv, f, max(0.0, 1.0 - f)


def hqiv_acceleration_vector(
    r_body: Vec3,
    v_body: Vec3,
    r_other: Vec3,
    m_other: float,
    star: StarComponent,
    *,
    use_spin_lapse: bool,
    use_rindler_denominator: bool,
) -> Vec3:
    a_newton = newtonian_acceleration_on_body(r_body, r_other, m_other)
    a_hqiv, _, _ = hqiv_effective_acceleration_m_s2(
        r_body,
        v_body,
        star,
        a_newton,
        use_spin_lapse=use_spin_lapse,
        use_rindler_denominator=use_rindler_denominator,
    )
    return vec_scale(vec_unit(a_newton), a_hqiv)


def period_years(semi_major_m: float, m1_kg: float, m2_kg: float) -> float:
    return 2.0 * math.pi * math.sqrt(semi_major_m**3 / (G_NEWTON * (m1_kg + m2_kg))) / YEAR_S


def rk4_step(
    r1: Vec3,
    v1: Vec3,
    r2: Vec3,
    v2: Vec3,
    m1: float,
    m2: float,
    star1: StarComponent,
    star2: StarComponent,
    dt: float,
    *,
    use_spin_lapse: bool,
    use_rindler_denominator: bool,
    classical_only: bool,
) -> tuple[Vec3, Vec3, Vec3, Vec3]:
    def accel(r1: Vec3, v1: Vec3, r2: Vec3, v2: Vec3) -> tuple[Vec3, Vec3]:
        if classical_only:
            return (
                newtonian_acceleration_on_body(r1, r2, m2),
                newtonian_acceleration_on_body(r2, r1, m1),
            )
        return (
            hqiv_acceleration_vector(
                r1, v1, r2, m2, star1,
                use_spin_lapse=use_spin_lapse,
                use_rindler_denominator=use_rindler_denominator,
            ),
            hqiv_acceleration_vector(
                r2, v2, r1, m1, star2,
                use_spin_lapse=use_spin_lapse,
                use_rindler_denominator=use_rindler_denominator,
            ),
        )

    def deriv(r1: Vec3, v1: Vec3, r2: Vec3, v2: Vec3) -> tuple[Vec3, Vec3, Vec3, Vec3]:
        a1, a2 = accel(r1, v1, r2, v2)
        return v1, a1, v2, a2

    k1 = deriv(r1, v1, r2, v2)
    k2 = deriv(
        vec_add(r1, vec_scale(k1[0], dt / 2)),
        vec_add(v1, vec_scale(k1[1], dt / 2)),
        vec_add(r2, vec_scale(k1[2], dt / 2)),
        vec_add(v2, vec_scale(k1[3], dt / 2)),
    )
    k3 = deriv(
        vec_add(r1, vec_scale(k2[0], dt / 2)),
        vec_add(v1, vec_scale(k2[1], dt / 2)),
        vec_add(r2, vec_scale(k2[2], dt / 2)),
        vec_add(v2, vec_scale(k2[3], dt / 2)),
    )
    k4 = deriv(
        vec_add(r1, vec_scale(k3[0], dt)),
        vec_add(v1, vec_scale(k3[1], dt)),
        vec_add(r2, vec_scale(k3[2], dt)),
        vec_add(v2, vec_scale(k3[3], dt)),
    )
    r1n = vec_add(
        r1,
        vec_scale(k1[0], dt / 6),
        vec_scale(k2[0], dt / 3),
        vec_scale(k3[0], dt / 3),
        vec_scale(k4[0], dt / 6),
    )
    v1n = vec_add(
        v1,
        vec_scale(k1[1], dt / 6),
        vec_scale(k2[1], dt / 3),
        vec_scale(k3[1], dt / 3),
        vec_scale(k4[1], dt / 6),
    )
    r2n = vec_add(
        r2,
        vec_scale(k1[2], dt / 6),
        vec_scale(k2[2], dt / 3),
        vec_scale(k3[2], dt / 3),
        vec_scale(k4[2], dt / 6),
    )
    v2n = vec_add(
        v2,
        vec_scale(k1[3], dt / 6),
        vec_scale(k2[3], dt / 3),
        vec_scale(k3[3], dt / 3),
        vec_scale(k4[3], dt / 6),
    )
    return r1n, v1n, r2n, v2n


def integrate_state(
    r1: Vec3,
    v1: Vec3,
    r2: Vec3,
    v2: Vec3,
    star1: StarComponent,
    star2: StarComponent,
    *,
    t_yr: float = 0.25,
    dt_days: float = 1.0,
    use_spin_lapse: bool = True,
    use_rindler_denominator: bool = True,
    classical_only: bool = False,
) -> dict[str, object]:
    m1 = star1.mass_kg
    m2 = star2.mass_kg
    dt = dt_days * 86400.0
    steps = max(10, int(t_yr * YEAR_S / dt))
    for _ in range(steps):
        r1, v1, r2, v2 = rk4_step(
            r1, v1, r2, v2, m1, m2, star1, star2, dt,
            use_spin_lapse=use_spin_lapse,
            use_rindler_denominator=use_rindler_denominator,
            classical_only=classical_only,
        )
    sep = vec_norm(vec_sub(r2, r1))
    v_rel = vec_norm(vec_sub(v2, v1))
    a_newton = G_NEWTON * (m1 + m2) / max(sep * sep, 1.0)
    return {
        "final_separation_au": sep / AU,
        "final_relative_speed_km_s": v_rel / 1000.0,
        "newton_acceleration_at_separation_m_s2": a_newton,
        "classical_only": classical_only,
        "integration": {"t_yr": t_yr, "dt_days": dt_days, "steps": steps},
    }


def instantaneous_hqiv_readout(
    r1: Vec3,
    v1: Vec3,
    r2: Vec3,
    v2: Vec3,
    star1: StarComponent,
    star2: StarComponent,
    *,
    use_spin_lapse: bool = True,
    use_rindler_denominator: bool = True,
) -> dict[str, object]:
    """HQIV screen on both components at the current state."""
    m2 = star2.mass_kg
    m1 = star1.mass_kg
    a1_n = newtonian_acceleration_on_body(r1, r2, m2)
    a2_n = newtonian_acceleration_on_body(r2, r1, m1)
    a1_h, f1, omf1 = hqiv_effective_acceleration_m_s2(
        r1, v1, star1, a1_n,
        use_spin_lapse=use_spin_lapse,
        use_rindler_denominator=use_rindler_denominator,
    )
    a2_h, f2, omf2 = hqiv_effective_acceleration_m_s2(
        r2, v2, star2, a2_n,
        use_spin_lapse=use_spin_lapse,
        use_rindler_denominator=use_rindler_denominator,
    )
    a1_n_mag = vec_norm(a1_n)
    a2_n_mag = vec_norm(a2_n)
    return {
        "star1": {
            "newton_m_s2": a1_n_mag,
            "hqiv_m_s2": a1_h,
            "gamma_eff": a1_h / max(a1_n_mag, 1.0e-30),
            "f": f1,
            "one_minus_f": omf1,
        },
        "star2": {
            "newton_m_s2": a2_n_mag,
            "hqiv_m_s2": a2_h,
            "gamma_eff": a2_h / max(a2_n_mag, 1.0e-30),
            "f": f2,
            "one_minus_f": omf2,
        },
    }


def full_treatment_chae(
    catalog_key: str,
    *,
    t_yr: float | None = None,
    dt_days: float = 5.0,
    use_spin_lapse: bool = True,
    use_rindler_denominator: bool = True,
    velocity_mode: str = "chae_vovervesc",
) -> dict[str, object]:
    """
    Full HQIV treatment of one Chae (2026) clean-sample binary.

    Uses observed Gaia+RV kinematics as initial conditions, vis-viva semi-major
    estimate, short classical vs HQIV integration, and literature cross-refs.
    """
    from hqiv_wide_binary_catalog import (
        gamma_from_chae_gamma,
        load_chae_catalog,
        observed_relative_kinematics,
        entry_to_stars,
        vis_viva_semi_major,
    )

    catalog = load_chae_catalog()
    if catalog_key not in catalog:
        raise KeyError(f"unknown catalog key {catalog_key!r}; choose from {sorted(catalog)}")
    entry = catalog[catalog_key]
    kin = observed_relative_kinematics(entry)
    star1, star2 = entry_to_stars(entry)
    m1, m2 = star1.mass_kg, star2.mass_kg
    r_rel = kin["r_rel_m"]
    if velocity_mode == "gaia_pm_rv":
        v_rel = kin["v_rel_m_s"]
    elif velocity_mode == "chae_vovervesc":
        v_rel = kin["v_rel_chae_m_s"]
    else:
        raise ValueError(f"unknown velocity_mode {velocity_mode!r}")
    r1, v1, r2, v2 = barycentric_from_observed(r_rel, v_rel, m1, m2)
    a_vis = vis_viva_semi_major(kin["r_obs_m"], vec_norm(v_rel), kin["mass_total_kg"])
    period_yr_est = None
    if a_vis is not None and a_vis > 0.0:
        period_yr_est = period_years(a_vis, m1, m2)
    if t_yr is None:
        # Wide binaries have Myr periods; integrate a short arc only.
        if period_yr_est is not None and period_yr_est > 100.0:
            t_yr = 0.05
        else:
            t_yr = max(0.01, min((period_yr_est or 1.0) * 0.02, 1.0))

    readout = instantaneous_hqiv_readout(
        r1, v1, r2, v2, star1, star2,
        use_spin_lapse=use_spin_lapse,
        use_rindler_denominator=use_rindler_denominator,
    )
    gamma_chae = gamma_from_chae_gamma(entry.gamma_chae)

    return {
        "catalog_key": catalog_key,
        "chae_id": entry.chae_id,
        "gaia_a": entry.gaia_a,
        "gaia_b": entry.gaia_b,
        "literature": {
            "chae_2026": "arXiv:2601.21728",
            "saad_ting_2026": "arXiv:2603.11015",
            "rv_source": entry.rv_source,
            "merits": entry.merits,
            "vobs_over_vesc_chae": entry.vobs_over_vesc,
            "Gamma_chae": entry.gamma_chae,
            "gamma_chae_from_Gamma": gamma_chae,
        },
        "velocity_mode": velocity_mode,
        "observed": {
            "distance_pc": entry.distance_pc,
            "separation_au": kin["separation_au"],
            "separation_proj_au": kin["separation_proj_au"],
            "v_obs_gaia_pm_rv_km_s": kin["v_obs_m_s"] / 1000.0,
            "v_obs_chae_scaled_km_s": kin["v_obs_chae_m_s"] / 1000.0,
            "v_esc_newton_km_s": kin["v_esc_newton_m_s"] / 1000.0,
            "g_newton_m_s2": kin["g_newton_m_s2"],
            "vr_kms": entry.vr_kms,
            "mass_a_msun": entry.mass_a_msun,
            "mass_b_msun": entry.mass_b_msun,
        },
        "vis_viva": {
            "semi_major_au": (a_vis / AU) if a_vis else None,
            "period_yr": period_yr_est,
        },
        "instantaneous_hqiv": readout,
        "integration_classical": integrate_state(
            r1, v1, r2, v2, star1, star2,
            t_yr=t_yr, dt_days=dt_days, classical_only=True,
            use_spin_lapse=use_spin_lapse,
            use_rindler_denominator=use_rindler_denominator,
        ),
        "integration_hqiv": integrate_state(
            r1, v1, r2, v2, star1, star2,
            t_yr=t_yr, dt_days=dt_days, classical_only=False,
            use_spin_lapse=use_spin_lapse,
            use_rindler_denominator=use_rindler_denominator,
        ),
    }


# Default reference system for paper/regression (Chae clean sample #58, HARPS RV).
CHAE_REFERENCE_SYSTEM = "chae2026_58"

ARTIFACTS_DIR = Path(__file__).resolve().parent / "artifacts"


def chae_summary_row(
    catalog_key: str,
    *,
    velocity_mode: str = "chae_vovervesc",
    use_spin_lapse: bool = True,
    use_rindler_denominator: bool = True,
    eccentricity_guess: float = 0.3,
) -> dict[str, object]:
    """Compact HQIV readout for one Chae catalog entry (no long integration)."""
    from hqiv_wide_binary_catalog import (
        gamma_from_chae_gamma,
        load_chae_catalog,
        observed_relative_kinematics,
        entry_to_stars,
        vis_viva_semi_major,
    )

    entry = load_chae_catalog()[catalog_key]
    kin = observed_relative_kinematics(entry)
    star1, star2 = entry_to_stars(entry)
    m1, m2 = star1.mass_kg, star2.mass_kg
    v_rel = kin["v_rel_chae_m_s"] if velocity_mode == "chae_vovervesc" else kin["v_rel_m_s"]
    r1, v1, r2, v2 = barycentric_from_observed(kin["r_rel_m"], v_rel, m1, m2)
    readout = instantaneous_hqiv_readout(
        r1, v1, r2, v2, star1, star2,
        use_spin_lapse=use_spin_lapse,
        use_rindler_denominator=use_rindler_denominator,
    )
    a_vis = vis_viva_semi_major(kin["r_obs_m"], vec_norm(v_rel), kin["mass_total_kg"])
    gamma_eff = 0.5 * (
        readout["star1"]["gamma_eff"] + readout["star2"]["gamma_eff"]
    )
    peri_apo = None
    if a_vis is not None and a_vis > 0.0:
        preset = WideBinaryPreset(
            name=catalog_key,
            star1=star1,
            star2=star2,
            elements=BinaryElements(
                semi_major_axis_m=a_vis,
                eccentricity=eccentricity_guess,
            ),
            note="vis-viva semi-major with eccentricity guess for peri/apo screen",
        )
        pa = peri_apo_acceleration_ratio(
            preset,
            use_spin_lapse=use_spin_lapse,
            use_rindler_denominator=use_rindler_denominator,
        )
        peri_apo = {
            "eccentricity_guess": eccentricity_guess,
            "gamma_eff_peri": pa["periastron"]["hqiv_over_newton"],
            "gamma_eff_apo": pa["apastron"]["hqiv_over_newton"],
        }
    return {
        "catalog_key": catalog_key,
        "chae_id": entry.chae_id,
        "separation_au": kin["separation_au"],
        "g_newton_m_s2": kin["g_newton_m_s2"],
        "v_obs_chae_km_s": kin["v_obs_chae_m_s"] / 1000.0,
        "v_obs_gaia_km_s": kin["v_obs_m_s"] / 1000.0,
        "v_over_vesc_chae": entry.vobs_over_vesc,
        "Gamma_chae": entry.gamma_chae,
        "gamma_chae": gamma_from_chae_gamma(entry.gamma_chae),
        "gamma_eff_hqiv_mean": gamma_eff,
        "one_minus_f_mean": 0.5 * (
            readout["star1"]["one_minus_f"] + readout["star2"]["one_minus_f"]
        ),
        "semi_major_vis_viva_au": (a_vis / AU) if a_vis else None,
        "peri_apo_guess": peri_apo,
    }


def batch_all_chae_systems(
    *,
    velocity_mode: str = "chae_vovervesc",
    use_spin_lapse: bool = True,
    use_rindler_denominator: bool = True,
    eccentricity_guess: float = 0.3,
) -> dict[str, object]:
    """Run compact HQIV summary on all 36 Chae (2026) clean-sample systems."""
    from hqiv_wide_binary_catalog import load_chae_catalog

    catalog = load_chae_catalog()
    rows = [
        chae_summary_row(
            key,
            velocity_mode=velocity_mode,
            use_spin_lapse=use_spin_lapse,
            use_rindler_denominator=use_rindler_denominator,
            eccentricity_guess=eccentricity_guess,
        )
        for key in sorted(catalog, key=lambda k: catalog[k].chae_id)
    ]
    gamma_hqiv = [r["gamma_eff_hqiv_mean"] for r in rows]
    gamma_chae = [r["gamma_chae"] for r in rows if r["gamma_chae"] is not None]
    return {
        "n_systems": len(rows),
        "velocity_mode": velocity_mode,
        "literature": {
            "chae_2026": "arXiv:2601.21728",
            "saad_ting_2026": "arXiv:2603.11015",
            "note": "HQIV gamma_eff is instantaneous screen; Chae gamma is per-system MCMC.",
        },
        "aggregate": {
            "gamma_eff_hqiv_mean_of_systems": sum(gamma_hqiv) / len(gamma_hqiv),
            "gamma_eff_hqiv_min": min(gamma_hqiv),
            "gamma_eff_hqiv_max": max(gamma_hqiv),
            "gamma_chae_median": sorted(gamma_chae)[len(gamma_chae) // 2] if gamma_chae else None,
            "gamma_chae_mean": sum(gamma_chae) / len(gamma_chae) if gamma_chae else None,
        },
        "rows": rows,
    }


def integrate_binary(
    preset: WideBinaryPreset,
    *,
    t_yr: float = 0.25,
    dt_days: float = 1.0,
    use_spin_lapse: bool = True,
    use_rindler_denominator: bool = True,
    classical_only: bool = False,
) -> dict[str, object]:
    m1 = preset.star1.mass_kg
    m2 = preset.star2.mass_kg
    r1, v1, r2, v2 = elements_to_barycentric(preset.elements, m1, m2)
    out = integrate_state(
        r1, v1, r2, v2, preset.star1, preset.star2,
        t_yr=t_yr, dt_days=dt_days,
        use_spin_lapse=use_spin_lapse,
        use_rindler_denominator=use_rindler_denominator,
        classical_only=classical_only,
    )
    return {
        "name": preset.name,
        "note": preset.note,
        "semi_major_au": preset.elements.semi_major_axis_m / AU,
        "eccentricity": preset.elements.eccentricity,
        "period_classical_yr": period_years(preset.elements.semi_major_axis_m, m1, m2),
        "use_spin_lapse": use_spin_lapse,
        "use_rindler_denominator": use_rindler_denominator,
        **out,
    }


def peri_apo_acceleration_ratio(
    preset: WideBinaryPreset,
    *,
    use_spin_lapse: bool = True,
    use_rindler_denominator: bool = True,
) -> dict[str, object]:
    """Compare Newtonian vs HQIV effective |a| at periastron and apastron."""
    el = preset.elements
    m1 = preset.star1.mass_kg
    m2 = preset.star2.mass_kg
    a = el.semi_major_axis_m
    e = el.eccentricity
    r_peri = a * (1.0 - e)
    r_apo = a * (1.0 + e)
    mu = G_NEWTON * (m1 + m2)

    def ratios_at(mean_anomaly: float) -> dict[str, float]:
        r1, v1, r2, v2 = elements_to_barycentric(
            BinaryElements(semi_major_axis_m=a, eccentricity=e, mean_anomaly_rad=mean_anomaly),
            m1,
            m2,
        )
        a_n = newtonian_acceleration_on_body(r1, r2, m2)
        a_h, f, omf = hqiv_effective_acceleration_m_s2(
            r1, v1, preset.star1, a_n,
            use_spin_lapse=use_spin_lapse,
            use_rindler_denominator=use_rindler_denominator,
        )
        a_n_mag = vec_norm(a_n)
        return {
            "separation_au": vec_norm(vec_sub(r2, r1)) / AU,
            "newton_m_s2": a_n_mag,
            "hqiv_m_s2": a_h,
            "hqiv_over_newton": a_h / max(a_n_mag, 1.0e-30),
            "one_minus_f": omf,
            "f": f,
            "a0_m_s2": mu / max((vec_norm(vec_sub(r2, r1))) ** 2, 1.0),
        }

    return {
        "periastron": ratios_at(0.0),
        "apastron": ratios_at(math.pi),
        "a0_peri_m_s2": mu / max(r_peri * r_peri, 1.0),
        "a0_apo_m_s2": mu / max(r_apo * r_apo, 1.0),
    }


def preset_payload(
    name: str,
    *,
    t_yr: float = 0.25,
    dt_days: float = 1.0,
    use_spin_lapse: bool = True,
    use_rindler_denominator: bool = True,
    classical_only: bool = False,
) -> dict[str, object]:
    preset = WIDE_BINARY_PRESETS[name]
    return {
        "preset": name,
        "note": preset.note,
        "reference_separation_au": preset.reference_separation_au,
        "period_classical_yr": period_years(
            preset.elements.semi_major_axis_m,
            preset.star1.mass_kg,
            preset.star2.mass_kg,
        ),
        "integration": integrate_binary(
            preset,
            t_yr=t_yr,
            dt_days=dt_days,
            use_spin_lapse=use_spin_lapse,
            use_rindler_denominator=use_rindler_denominator,
            classical_only=classical_only,
        ),
        "peri_apo": peri_apo_acceleration_ratio(
            preset,
            use_spin_lapse=use_spin_lapse,
            use_rindler_denominator=use_rindler_denominator,
        ),
        "stars": {
            "star1": asdict(preset.star1),
            "star2": asdict(preset.star2),
        },
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="HQIV wide-binary calculator")
    parser.add_argument("--preset", choices=tuple(sorted(WIDE_BINARY_PRESETS)), default=None)
    parser.add_argument("--list-presets", action="store_true")
    parser.add_argument("--chae-id", type=int, default=None, help="Chae (2026) clean-sample ID (1–58)")
    parser.add_argument(
        "--full-treatment",
        action="store_true",
        help="Run observed-state HQIV treatment (requires --chae-id or uses reference #58)",
    )
    parser.add_argument("--list-chae", action="store_true", help="List Chae 2026 catalog entries")
    parser.add_argument(
        "--run-all-chae",
        action="store_true",
        help="Compact HQIV summary for all 36 Chae clean-sample systems",
    )
    parser.add_argument(
        "--output",
        type=str,
        default=None,
        help="Write JSON to this path (--run-all-chae or --full-treatment)",
    )
    parser.add_argument("--t-yr", type=float, default=None)
    parser.add_argument("--dt-days", type=float, default=5.0)
    parser.add_argument("--no-spin-lapse", action="store_true")
    parser.add_argument("--no-rindler-denominator", action="store_true")
    parser.add_argument("--classical-only", action="store_true")
    parser.add_argument(
        "--velocity-mode",
        choices=("chae_vovervesc", "gaia_pm_rv"),
        default="chae_vovervesc",
        help="How to set initial relative speed for --full-treatment",
    )
    args = parser.parse_args(argv)
    if args.run_all_chae:
        payload = batch_all_chae_systems(
            velocity_mode=args.velocity_mode,
            use_spin_lapse=not args.no_spin_lapse,
            use_rindler_denominator=not args.no_rindler_denominator,
        )
        out_path = args.output or str(
            ARTIFACTS_DIR / "wide_binary_chae2026_all_summary.json"
        )
        Path(out_path).parent.mkdir(parents=True, exist_ok=True)
        Path(out_path).write_text(json.dumps(payload, indent=2), encoding="utf-8")
        print(json.dumps(payload, indent=2))
        print(f"\nWrote {out_path}", file=__import__("sys").stderr)
        return 0
    if args.list_chae:
        from hqiv_wide_binary_catalog import load_chae_catalog

        catalog = load_chae_catalog()
        print(
            json.dumps(
                {
                    k: {
                        "chae_id": e.chae_id,
                        "gaia": f"{e.gaia_a}/{e.gaia_b}",
                        "d_pc": e.distance_pc,
                        "v_over_vesc": e.vobs_over_vesc,
                        "Gamma": e.gamma_chae,
                    }
                    for k, e in sorted(catalog.items(), key=lambda kv: kv[1].chae_id)
                },
                indent=2,
            )
        )
        return 0
    if args.full_treatment or args.chae_id is not None:
        from hqiv_wide_binary_catalog import load_chae_catalog

        cid = args.chae_id if args.chae_id is not None else 58
        key = f"chae2026_{cid:02d}"
        if key not in load_chae_catalog():
            parser.error(f"chae_id {cid} not in clean sample")
        payload = full_treatment_chae(
            key,
            t_yr=args.t_yr,
            dt_days=args.dt_days,
            use_spin_lapse=not args.no_spin_lapse,
            use_rindler_denominator=not args.no_rindler_denominator,
            velocity_mode=args.velocity_mode,
        )
        if args.output:
            Path(args.output).parent.mkdir(parents=True, exist_ok=True)
            Path(args.output).write_text(json.dumps(payload, indent=2), encoding="utf-8")
        print(json.dumps(payload, indent=2))
        if args.output:
            print(f"\nWrote {args.output}", file=__import__("sys").stderr)
        return 0
    if args.list_presets:
        print(
            json.dumps(
                {
                    k: {
                        "note": v.note,
                        "a_au": v.elements.semi_major_axis_m / AU,
                        "e": v.elements.eccentricity,
                        "period_yr": period_years(
                            v.elements.semi_major_axis_m,
                            v.star1.mass_kg,
                            v.star2.mass_kg,
                        ),
                    }
                    for k, v in WIDE_BINARY_PRESETS.items()
                },
                indent=2,
            )
        )
        return 0
    if not args.preset:
        parser.error("choose --preset or --list-presets")
    print(
        json.dumps(
            preset_payload(
                args.preset,
                t_yr=args.t_yr,
                dt_days=args.dt_days,
                use_spin_lapse=not args.no_spin_lapse,
                use_rindler_denominator=not args.no_rindler_denominator,
                classical_only=args.classical_only,
            ),
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

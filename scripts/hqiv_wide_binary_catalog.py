#!/usr/bin/env python3
"""
Chae (2026) wide-binary catalog loader and observed 3D kinematics.

Data: scripts/data/wide_binary_chae2026/ (from Saad & Ting 2026 reanalysis repo;
see arXiv:2603.11015 and Chae arXiv:2601.21728).

This module prepares observed separations and velocities for HQIV orbit analysis.
It does not reproduce the PyMC gamma inference; it supplies reproducible inputs.
"""

from __future__ import annotations

import csv
import math
from dataclasses import dataclass
from pathlib import Path

from hqiv_wide_binary import (
    AU,
    M_SUN_KG,
    PC_TO_M,
    StarComponent,
    Vec3,
    vec_add,
    vec_cross,
    vec_dot,
    vec_norm,
    vec_scale,
    vec_sub,
    vec_unit,
)

# km/s per (mas/yr) per pc — IAU convention used in Saad & Ting (2026)
K_PM = 4.74047
G_NEWTON = 6.67430e-11

DATA_DIR = Path(__file__).resolve().parent / "data" / "wide_binary_chae2026"
CLEAN_CSV = DATA_DIR / "chae_2026_data.csv"
GAIA_CSV = DATA_DIR / "chae_2026_gaia.csv"


@dataclass(frozen=True)
class ChaeWideBinaryEntry:
    chae_id: int
    gaia_a: int
    gaia_b: int
    distance_pc: float
    vr_kms: float
    vr_sigma_kms: float
    vobs_over_vesc: float
    vobs_over_vesc_err: float
    mass_a_msun: float
    mass_b_msun: float
    gamma_chae: float | None = None
    gamma_chae_err_lo: float | None = None
    gamma_chae_err_hi: float | None = None
    rv_source: str = ""
    merits: str = ""
    # Gaia astrometry (degrees, mas, mas/yr)
    ra_a_deg: float = 0.0
    dec_a_deg: float = 0.0
    ra_b_deg: float = 0.0
    dec_b_deg: float = 0.0
    parallax_a_mas: float = 0.0
    parallax_b_mas: float = 0.0
    pmra_a_masyr: float = 0.0
    pmdec_a_masyr: float = 0.0
    pmra_b_masyr: float = 0.0
    pmdec_b_masyr: float = 0.0
    gaia_rv_a_kms: float | None = None
    gaia_rv_b_kms: float | None = None

    @property
    def name(self) -> str:
        return f"chae2026_{self.chae_id:02d}"

    @property
    def gaia_label(self) -> str:
        return f"{self.gaia_a}_{self.gaia_b}"


def _read_csv_rows(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as fh:
        return list(csv.DictReader(fh))


def load_chae_catalog(
    clean_path: Path | None = None,
    gaia_path: Path | None = None,
) -> dict[str, ChaeWideBinaryEntry]:
    """Merge Chae clean sample with Gaia astrometry; key = chae2026_XX."""
    clean_path = clean_path or CLEAN_CSV
    gaia_path = gaia_path or GAIA_CSV
    clean_rows = {int(r["chae_id"]): r for r in _read_csv_rows(clean_path)}
    gaia_by_pair: dict[tuple[int, int], dict[str, str]] = {}
    for row in _read_csv_rows(gaia_path):
        key = (int(row["gaia_a"]), int(row["gaia_b"]))
        gaia_by_pair[key] = row

    out: dict[str, ChaeWideBinaryEntry] = {}
    for cid, crow in sorted(clean_rows.items()):
        gaia_a = int(crow["gaia_a"])
        gaia_b = int(crow["gaia_b"])
        grow = gaia_by_pair.get((gaia_a, gaia_b))
        if grow is None:
            raise KeyError(f"no Gaia row for chae_id={cid}")
        gamma = grow.get("Gamma", "")
        entry = ChaeWideBinaryEntry(
            chae_id=cid,
            gaia_a=gaia_a,
            gaia_b=gaia_b,
            distance_pc=float(crow["d_M_pc"]),
            vr_kms=float(crow["vr_kms"]),
            vr_sigma_kms=float(crow["vr_sigma_kms"]),
            vobs_over_vesc=float(crow["vobs_over_vesc"]),
            vobs_over_vesc_err=float(crow["vobs_vesc_err"]),
            mass_a_msun=_mass_msun(crow, grow, "a"),
            mass_b_msun=_mass_msun(crow, grow, "b"),
            gamma_chae=float(gamma) if gamma not in ("", None) else None,
            gamma_chae_err_lo=float(grow["Gamma_err_lower"]) if grow.get("Gamma_err_lower") else None,
            gamma_chae_err_hi=float(grow["Gamma_err_upper"]) if grow.get("Gamma_err_upper") else None,
            rv_source=str(crow.get("rv_source", "")),
            merits=str(crow.get("merits", "")),
            ra_a_deg=float(grow["ra_a"]),
            dec_a_deg=float(grow["dec_a"]),
            ra_b_deg=float(grow["ra_b"]),
            dec_b_deg=float(grow["dec_b"]),
            parallax_a_mas=float(grow["parallax_a"]),
            parallax_b_mas=float(grow["parallax_b"]),
            pmra_a_masyr=float(grow["pmra_a"]),
            pmdec_a_masyr=float(grow["pmdec_a"]),
            pmra_b_masyr=float(grow["pmra_b"]),
            pmdec_b_masyr=float(grow["pmdec_b"]),
            gaia_rv_a_kms=_optional_float(grow.get("gaia_rv_a")),
            gaia_rv_b_kms=_optional_float(grow.get("gaia_rv_b")),
        )
        out[entry.name] = entry
    return out


def _optional_float(value: str | None) -> float | None:
    if value is None or value == "":
        return None
    return float(value)


def _mass_msun(clean_row: dict[str, str], grow: dict[str, str], component: str) -> float:
    key = f"mass_{component}"
    flame_key = f"mass_flame_{component}"
    raw = (clean_row.get(key) or "").strip()
    if raw:
        return float(raw)
    flame = (grow.get(flame_key) or "").strip()
    if flame:
        return float(flame)
    return 1.0


def icrs_triad(ra_rad: float, dec_rad: float) -> tuple[Vec3, Vec3, Vec3]:
    """Unit triad (r_hat, e_hat, n_hat) at ICRS position."""
    cdec, sdec = math.cos(dec_rad), math.sin(dec_rad)
    cra, sra = math.cos(ra_rad), math.sin(ra_rad)
    r_hat = (cdec * cra, cdec * sra, sdec)
    e_hat = (-sra, cra, 0.0)
    n_hat = (-sdec * cra, -sdec * sra, cdec)
    return r_hat, e_hat, n_hat


def star_velocity_icrs(
    entry: ChaeWideBinaryEntry,
    *,
    component: str,
) -> Vec3:
    """ICRS velocity (m/s) for component A or B from PM and radial velocity."""
    if component == "a":
        ra = math.radians(entry.ra_a_deg)
        dec = math.radians(entry.dec_a_deg)
        d_pc = 1000.0 / entry.parallax_a_mas
        pmra, pmdec = entry.pmra_a_masyr, entry.pmdec_a_masyr
        rv_kms = entry.gaia_rv_a_kms
    else:
        ra = math.radians(entry.ra_b_deg)
        dec = math.radians(entry.dec_b_deg)
        d_pc = 1000.0 / entry.parallax_b_mas
        pmra, pmdec = entry.pmra_b_masyr, entry.pmdec_b_masyr
        rv_kms = entry.gaia_rv_b_kms
    rhat, ehat, nhat = icrs_triad(ra, dec)
    if rv_kms is None and component == "b":
        rv_kms = (entry.gaia_rv_a_kms or 0.0) + entry.vr_kms
    if rv_kms is None:
        rv_kms = 0.0
    v_tan = vec_add(
        vec_scale(ehat, pmra * K_PM * 1000.0 * d_pc),
        vec_scale(nhat, pmdec * K_PM * 1000.0 * d_pc),
    )
    return vec_add(v_tan, vec_scale(rhat, rv_kms * 1000.0))


def observed_relative_kinematics(entry: ChaeWideBinaryEntry) -> dict[str, float | Vec3]:
    """
    Instantaneous separation and relative velocity (Chae / Saad & Ting convention).

    Separation uses sky-projected ``r_obs = d_mean * sep_rad`` (not photocenter
    line-of-sight depth difference). Velocities combine differential PM and RV.

    Frame: ICRS Cartesian (m, m/s). Relative vector points A → B.
    """
    ra_a = math.radians(entry.ra_a_deg)
    dec_a = math.radians(entry.dec_a_deg)
    ra_b = math.radians(entry.ra_b_deg)
    dec_b = math.radians(entry.dec_b_deg)
    delta_ra = (ra_b - ra_a) * math.cos(0.5 * (dec_a + dec_b))
    delta_dec = dec_b - dec_a
    sep_rad = math.sqrt(delta_ra * delta_ra + delta_dec * delta_dec)
    d_mean_pc = 0.5 * (1000.0 / entry.parallax_a_mas + 1000.0 / entry.parallax_b_mas)
    d_mean_m = d_mean_pc * PC_TO_M
    r_obs = d_mean_m * sep_rad

    rhat_a, ehat_a, nhat_a = icrs_triad(ra_a, dec_a)
    if sep_rad > 0.0:
        r_dir = vec_add(
            vec_scale(ehat_a, delta_ra / sep_rad),
            vec_scale(nhat_a, delta_dec / sep_rad),
        )
    else:
        r_dir = ehat_a
    r_rel = vec_scale(vec_unit(r_dir), r_obs)

    dpmra = entry.pmra_b_masyr - entry.pmra_a_masyr
    dpmdec = entry.pmdec_b_masyr - entry.pmdec_a_masyr
    v_tang = vec_add(
        vec_scale(ehat_a, dpmra * K_PM * 1000.0 * d_mean_pc),
        vec_scale(nhat_a, dpmdec * K_PM * 1000.0 * d_mean_pc),
    )
    v_rad = vec_scale(rhat_a, entry.vr_kms * 1000.0)
    v_rel = vec_add(v_tang, v_rad)
    v_obs = vec_norm(v_rel)

    m_tot = (entry.mass_a_msun + entry.mass_b_msun) * M_SUN_KG
    g_newton = G_NEWTON * m_tot / max(r_obs * r_obs, 1.0)

    v_esc_newton = math.sqrt(max(2.0 * G_NEWTON * m_tot / r_obs, 0.0))
    v_chae = entry.vobs_over_vesc * v_esc_newton
    v_rel_chae = vec_scale(vec_unit(v_rel) if v_obs > 0.0 else r_dir, v_chae)

    return {
        "r_rel_m": r_rel,
        "v_rel_m_s": v_rel,
        "v_rel_chae_m_s": v_rel_chae,
        "r_obs_m": r_obs,
        "r_proj_m": r_obs,
        "v_obs_m_s": v_obs,
        "v_obs_chae_m_s": v_chae,
        "v_esc_newton_m_s": v_esc_newton,
        "separation_au": r_obs / AU,
        "separation_proj_au": r_obs / AU,
        "g_newton_m_s2": g_newton,
        "mass_total_kg": m_tot,
        "sep_rad": sep_rad,
        "d_mean_pc": d_mean_pc,
    }


def gamma_from_chae_gamma(chae_gamma: float | None) -> float | None:
    """Chae Γ = log10(sqrt(G_eff/G_N)) ⇒ γ = 10^(2Γ)."""
    if chae_gamma is None:
        return None
    return 10.0 ** (2.0 * chae_gamma)


def entry_to_stars(entry: ChaeWideBinaryEntry) -> tuple[StarComponent, StarComponent]:
    return (
        StarComponent(mass_kg=entry.mass_a_msun * M_SUN_KG, omega_rad_s=2.0e-6),
        StarComponent(mass_kg=entry.mass_b_msun * M_SUN_KG, omega_rad_s=-1.5e-6),
    )


def vis_viva_semi_major(r_m: float, v_m_s: float, mu_kg: float) -> float | None:
    """a from instantaneous vis-viva v² = μ(2/r − 1/a)."""
    if mu_kg <= 0.0 or r_m <= 0.0:
        return None
    inv_a = 2.0 / r_m - (v_m_s * v_m_s) / (G_NEWTON * mu_kg)
    if inv_a <= 0.0:
        return None
    return 1.0 / inv_a

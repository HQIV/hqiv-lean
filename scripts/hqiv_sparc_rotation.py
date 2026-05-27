#!/usr/bin/env python3
"""HQIV rotation-curve test against the SPARC catalog.

This module imports the SPARC release files produced by Lelli, McGaugh & Schombert
(2016, AJ 152, 157) and applies the same HQIV modified-inertia and mass-horizon
Doppler equations used by ``hqiv_galaxy_rotation.py`` and the flyby paper. No dark
halo, no fitted potential, no theory-tunable knob: only constituent baryons
(SPARC `V_gas`, `V_disk`, `V_bul`) screened by the HQIV inertia factor

    f(a, phi) = a / (a + phi/6)

with horizon repartition

    a_HQIV = a_baryonic / f.

Mass-to-light ratios at 3.6 micron use the SPARC literature fiducials
``Upsilon_disk = 0.5 Msun/Lsun`` and ``Upsilon_bul = 0.7 Msun/Lsun`` (Lelli+2016,
McGaugh+2016 PRL 117, 201101). These are external photometric conversions, not
theory-tunable parameters; the HQIV layer adds no free degrees of freedom.

CLI examples::

    python hqiv_sparc_rotation.py --list-galaxies
    python hqiv_sparc_rotation.py --galaxy NGC3198
    python hqiv_sparc_rotation.py --run-all --quality-cut 2 --min-inclination 30 \
        --write artifacts/sparc_hqiv_full.json
"""

from __future__ import annotations

import argparse
import json
import math
import os
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Iterable

import hqiv_galaxy_rotation as _gal

C_LIGHT = _gal.C_LIGHT
KPC = _gal.KPC
M_SUN_KG = _gal.M_SUN_KG
GAMMA_HQIV = _gal.GAMMA_HQIV

UPSILON_DISK_FIDUCIAL = 0.50  # Msun / Lsun at 3.6 micron (Lelli+2016, MLS+2016 RAR)
UPSILON_BUL_FIDUCIAL = 0.70   # Msun / Lsun at 3.6 micron (same references)

DEFAULT_DATA_DIR = Path(__file__).resolve().parent / "data" / "sparc"
HUBBLE_TYPE_LABELS = {
    0: "S0", 1: "Sa", 2: "Sab", 3: "Sb", 4: "Sbc", 5: "Sc",
    6: "Scd", 7: "Sd", 8: "Sdm", 9: "Sm", 10: "Im", 11: "BCD",
}

# Late-type / gas-rich SPARC rows used for diffuse-galaxy $R^2$ reporting.
DIFFUSE_HUBBLE_TYPES = {8, 9, 10, 11}  # Sdm, Sm, Im, BCD


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class SparcMaster:
    """One row of ``SPARC_Lelli2016c.mrt``."""
    name: str
    hubble_type: int
    distance_mpc: float
    e_distance_mpc: float
    distance_method: int
    inclination_deg: float
    e_inclination_deg: float
    L36_e9_lsun: float
    e_L36_e9_lsun: float
    reff_kpc: float
    sb_eff_lsun_pc2: float
    rdisk_kpc: float
    sb_disk_lsun_pc2: float
    mhi_e9_msun: float
    rhi_kpc: float
    vflat_kms: float
    e_vflat_kms: float
    quality: int
    references: str

    @property
    def hubble_label(self) -> str:
        return HUBBLE_TYPE_LABELS.get(self.hubble_type, str(self.hubble_type))


@dataclass(frozen=True)
class RotmodRow:
    """One radius from a ``*_rotmod.dat`` file."""
    rad_kpc: float
    v_obs_kms: float
    e_v_kms: float
    v_gas_kms: float
    v_disk_kms: float
    v_bul_kms: float
    sb_disk_lpc2: float
    sb_bul_lpc2: float


@dataclass(frozen=True)
class SparcGalaxy:
    master: SparcMaster
    rotmod: tuple[RotmodRow, ...]


# ---------------------------------------------------------------------------
# Loaders
# ---------------------------------------------------------------------------


_MASTER_NUMERIC_FIELDS = (
    "hubble_type",
    "distance_mpc",
    "e_distance_mpc",
    "distance_method",
    "inclination_deg",
    "e_inclination_deg",
    "L36_e9_lsun",
    "e_L36_e9_lsun",
    "reff_kpc",
    "sb_eff_lsun_pc2",
    "rdisk_kpc",
    "sb_disk_lsun_pc2",
    "mhi_e9_msun",
    "rhi_kpc",
    "vflat_kms",
    "e_vflat_kms",
    "quality",
)
_MASTER_INT_FIELDS = {"hubble_type", "distance_method", "quality"}


def _parse_master_line(line: str) -> SparcMaster | None:
    """Whitespace-tokenised parse; SPARC galaxy names contain no spaces."""
    tokens = line.split()
    # Need: name + 17 numeric fields + at least one reference token.
    if len(tokens) < 18:
        return None
    name = tokens[0]
    if not name or name.startswith("-") or name.startswith("="):
        return None
    try:
        values: dict[str, object] = {"name": name}
        for label, raw in zip(_MASTER_NUMERIC_FIELDS, tokens[1:18]):
            values[label] = int(raw) if label in _MASTER_INT_FIELDS else float(raw)
    except ValueError:
        return None
    values["references"] = " ".join(tokens[18:])
    return SparcMaster(**values)  # type: ignore[arg-type]


def load_sparc_master(path: str | os.PathLike[str]) -> dict[str, SparcMaster]:
    """Parse the MRT master table into a name-keyed dict.

    The MRT file mixes a byte-by-byte description block with a tail of data
    rows. We skip header sections by detecting the final ``------`` rule and
    rely on whitespace tokenisation for the data rows.
    """
    masters: dict[str, SparcMaster] = {}
    with open(path, encoding="utf-8") as fh:
        lines = fh.read().splitlines()
    # Use the LAST hyphen-rule as the start of the data block; everything before
    # is metadata, byte descriptions, and reference legends.
    data_start = 0
    for idx, line in enumerate(lines):
        stripped = line.strip()
        if stripped.startswith("---") and len(set(stripped)) <= 2:
            data_start = idx + 1
    for line in lines[data_start:]:
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        row = _parse_master_line(line)
        if row is not None:
            masters[row.name] = row
    return masters


def load_sparc_rotmod(path: str | os.PathLike[str]) -> list[RotmodRow]:
    """Parse a ``*_rotmod.dat`` file into RotmodRow records."""
    rows: list[RotmodRow] = []
    with open(path, encoding="utf-8") as fh:
        for raw in fh:
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split()
            if len(parts) < 8:
                continue
            try:
                rows.append(
                    RotmodRow(
                        rad_kpc=float(parts[0]),
                        v_obs_kms=float(parts[1]),
                        e_v_kms=float(parts[2]),
                        v_gas_kms=float(parts[3]),
                        v_disk_kms=float(parts[4]),
                        v_bul_kms=float(parts[5]),
                        sb_disk_lpc2=float(parts[6]),
                        sb_bul_lpc2=float(parts[7]),
                    )
                )
            except ValueError:
                continue
    return rows


def _rotmod_name(filename: str) -> str:
    base = os.path.basename(filename)
    if base.endswith("_rotmod.dat"):
        return base[: -len("_rotmod.dat")]
    return base.split(".")[0]


def load_sparc_catalog(
    data_dir: str | os.PathLike[str] | None = None,
) -> dict[str, SparcGalaxy]:
    """Read the master table plus every ``*_rotmod.dat`` file under ``data_dir``."""
    root = Path(data_dir) if data_dir is not None else DEFAULT_DATA_DIR
    master_path = root / "SPARC_Lelli2016c.mrt"
    rotmod_dir = root / "rotmod"
    if not master_path.exists() or not rotmod_dir.exists():
        raise FileNotFoundError(
            f"SPARC data not found under {root}. Run scripts/download_sparc_data.sh first."
        )
    masters = load_sparc_master(master_path)
    galaxies: dict[str, SparcGalaxy] = {}
    for file in sorted(rotmod_dir.glob("*_rotmod.dat")):
        name = _rotmod_name(file.name)
        master = masters.get(name)
        if master is None:
            continue
        rows = load_sparc_rotmod(file)
        if not rows:
            continue
        galaxies[name] = SparcGalaxy(master=master, rotmod=tuple(rows))
    return galaxies


# ---------------------------------------------------------------------------
# HQIV pipeline applied to a single SPARC row
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class SparcOptions:
    upsilon_disk: float = UPSILON_DISK_FIDUCIAL
    upsilon_bul: float = UPSILON_BUL_FIDUCIAL
    upsilon_gas: float = 1.0  # SPARC already encodes the gas contribution in V_gas
    phi_shell: int = 0
    support_fraction: float = 1.0
    projection: float = 1.0
    use_rindler_denominator: bool = True


@dataclass(frozen=True)
class SparcRotationRow:
    radius_kpc: float
    v_obs_kms: float
    e_v_kms: float
    v_gas_kms: float
    v_disk_kms: float
    v_bul_kms: float
    v_baryonic_kms: float
    v_hqiv_kms: float
    baryonic_accel_m_s2: float
    hqiv_accel_m_s2: float
    inertia_factor_full: float
    one_minus_f_full: float
    epsilon_doppler: float
    phi_accel_si: float


def baryonic_v_squared_kms2(
    v_gas_kms: float,
    v_disk_kms: float,
    v_bul_kms: float,
    *,
    upsilon_disk: float = UPSILON_DISK_FIDUCIAL,
    upsilon_bul: float = UPSILON_BUL_FIDUCIAL,
    upsilon_gas: float = 1.0,
) -> float:
    """Signed baryonic squared circular speed at SPARC fiducials.

    V_gas can be negative when the gas density profile has a central hole; SPARC
    stores the signed contribution so that ``V_bar^2`` = sum of signed squares.
    """
    gas = upsilon_gas * math.copysign(v_gas_kms * v_gas_kms, v_gas_kms)
    disk = upsilon_disk * v_disk_kms * v_disk_kms
    bul = upsilon_bul * v_bul_kms * v_bul_kms
    return gas + disk + bul


def _phi_accel_si(radius_m: float, lapse_radius_m: float, phi_shell: int) -> float:
    """Same shell modulator as ``hqiv_galaxy_rotation.phi_acceleration_si``."""
    phi_ref = _gal.phi_of_shell(phi_shell)
    shell_mod = _gal.phi_of_shell(phi_shell) / (1.0 + radius_m / max(lapse_radius_m, 1.0))
    shell_mod /= max(phi_ref, 1.0e-30)
    return _gal.phi_acceleration_homogeneous_si() * shell_mod


def hqiv_rotation_point_sparc(
    row: RotmodRow,
    master: SparcMaster,
    *,
    options: SparcOptions = SparcOptions(),
) -> SparcRotationRow:
    """Per-radius HQIV speed using SPARC's measured V_gas/V_disk/V_bul."""
    r_m = max(row.rad_kpc * KPC, 1.0)
    v_b2 = baryonic_v_squared_kms2(
        row.v_gas_kms,
        row.v_disk_kms,
        row.v_bul_kms,
        upsilon_disk=options.upsilon_disk,
        upsilon_bul=options.upsilon_bul,
        upsilon_gas=options.upsilon_gas,
    )
    v_b_si = math.sqrt(max(v_b2, 0.0)) * 1.0e3
    a_b = (v_b_si * v_b_si) / r_m if r_m > 0.0 else 0.0
    eps = _gal.mass_horizon_doppler_lapse(
        v_b_si,
        projection=options.projection,
        support_fraction=options.support_fraction,
        use_rindler_denominator=options.use_rindler_denominator,
    )
    lapse_radius_m = max(master.rdisk_kpc, 0.05) * KPC  # disk scale length sets the shell width
    phi_part = _phi_accel_si(r_m, lapse_radius_m, options.phi_shell)
    phi_full = phi_part + 6.0 * a_b * eps
    f_full = _gal.hqiv_inertia_factor(a_b, phi_full)
    a_hqiv = a_b / max(f_full, 1.0e-30)
    v_hqiv_si = math.sqrt(max(a_hqiv * r_m, 0.0))
    return SparcRotationRow(
        radius_kpc=row.rad_kpc,
        v_obs_kms=row.v_obs_kms,
        e_v_kms=row.e_v_kms,
        v_gas_kms=row.v_gas_kms,
        v_disk_kms=row.v_disk_kms,
        v_bul_kms=row.v_bul_kms,
        v_baryonic_kms=v_b_si / 1.0e3,
        v_hqiv_kms=v_hqiv_si / 1.0e3,
        baryonic_accel_m_s2=a_b,
        hqiv_accel_m_s2=a_hqiv,
        inertia_factor_full=f_full,
        one_minus_f_full=max(0.0, 1.0 - f_full),
        epsilon_doppler=eps,
        phi_accel_si=phi_part,
    )


# ---------------------------------------------------------------------------
# Per-galaxy and catalog summaries
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class GalaxySummary:
    name: str
    quality: int
    hubble_label: str
    distance_mpc: float
    inclination_deg: float
    rdisk_kpc: float
    vflat_obs_kms: float
    n_points: int
    chi2_hqiv: float
    chi2_baryonic: float
    chi2_red_hqiv: float
    chi2_red_baryonic: float
    rms_hqiv_kms: float
    rms_baryonic_kms: float
    mean_residual_hqiv_kms: float
    mean_residual_baryonic_kms: float
    mean_one_minus_f: float
    v_hqiv_outer_kms: float
    v_obs_outer_kms: float
    outer_radius_kpc: float


def _safe_div(num: float, denom: float) -> float:
    return num / denom if denom > 0.0 else float("inf")


def evaluate_galaxy(
    galaxy: SparcGalaxy,
    *,
    options: SparcOptions = SparcOptions(),
) -> dict[str, object]:
    """Compute HQIV vs baryonic-only fits and per-galaxy chi^2 statistics."""
    rows: list[SparcRotationRow] = [
        hqiv_rotation_point_sparc(r, galaxy.master, options=options)
        for r in galaxy.rotmod
    ]
    chi2_h = 0.0
    chi2_b = 0.0
    sq_h = 0.0
    sq_b = 0.0
    sum_res_h = 0.0
    sum_res_b = 0.0
    sum_one_minus_f = 0.0
    valid = 0
    for r in rows:
        if r.e_v_kms <= 0.0 or not math.isfinite(r.v_obs_kms):
            continue
        res_h = r.v_hqiv_kms - r.v_obs_kms
        res_b = r.v_baryonic_kms - r.v_obs_kms
        chi2_h += (res_h / r.e_v_kms) ** 2
        chi2_b += (res_b / r.e_v_kms) ** 2
        sq_h += res_h * res_h
        sq_b += res_b * res_b
        sum_res_h += res_h
        sum_res_b += res_b
        sum_one_minus_f += r.one_minus_f_full
        valid += 1
    n = max(valid, 1)
    outer = rows[-1] if rows else None
    summary = GalaxySummary(
        name=galaxy.master.name,
        quality=galaxy.master.quality,
        hubble_label=galaxy.master.hubble_label,
        distance_mpc=galaxy.master.distance_mpc,
        inclination_deg=galaxy.master.inclination_deg,
        rdisk_kpc=galaxy.master.rdisk_kpc,
        vflat_obs_kms=galaxy.master.vflat_kms,
        n_points=valid,
        chi2_hqiv=chi2_h,
        chi2_baryonic=chi2_b,
        chi2_red_hqiv=_safe_div(chi2_h, n),
        chi2_red_baryonic=_safe_div(chi2_b, n),
        rms_hqiv_kms=math.sqrt(sq_h / n),
        rms_baryonic_kms=math.sqrt(sq_b / n),
        mean_residual_hqiv_kms=sum_res_h / n,
        mean_residual_baryonic_kms=sum_res_b / n,
        mean_one_minus_f=sum_one_minus_f / n,
        v_hqiv_outer_kms=outer.v_hqiv_kms if outer is not None else 0.0,
        v_obs_outer_kms=outer.v_obs_kms if outer is not None else 0.0,
        outer_radius_kpc=outer.radius_kpc if outer is not None else 0.0,
    )
    return {
        "summary": asdict(summary),
        "rows": [asdict(r) for r in rows],
        "options": asdict(options),
    }


def _median(values: list[float]) -> float:
    if not values:
        return float("nan")
    s = sorted(values)
    mid = len(s) // 2
    if len(s) % 2 == 1:
        return s[mid]
    return 0.5 * (s[mid - 1] + s[mid])


def is_diffuse_galaxy(summary: dict[str, object]) -> bool:
    """Gas-rich / late-type SPARC galaxies (Im, Sm, BCD, Sdm, DDO)."""
    name = str(summary.get("name", ""))
    if name.upper().startswith("DDO"):
        return True
    label = str(summary.get("hubble_label", ""))
    return label in {"Sdm", "Sm", "Im", "BCD"}


def r_squared(observed: list[float], predicted: list[float]) -> float:
    """Coefficient of determination $R^2$ for paired $(v_{\rm obs}, v_{\rm HQIV})$ samples."""
    pairs = [
        (o, p)
        for o, p in zip(observed, predicted)
        if math.isfinite(o) and math.isfinite(p) and o > 0.0
    ]
    if len(pairs) < 2:
        return float("nan")
    obs = [o for o, _ in pairs]
    pred = [p for _, p in pairs]
    mean_obs = sum(obs) / len(obs)
    ss_tot = sum((o - mean_obs) ** 2 for o in obs)
    if ss_tot <= 0.0:
        return float("nan")
    ss_res = sum((o - p) ** 2 for o, p in pairs)
    return 1.0 - ss_res / ss_tot


def collect_rotation_points(
    per_galaxy: list[dict[str, object]],
    *,
    diffuse_only: bool = False,
) -> tuple[list[float], list[float], list[float], list[float]]:
    """Flatten catalog to (v_obs, v_hqiv, v_baryonic, weights 1/sigma)."""
    v_obs: list[float] = []
    v_hqiv: list[float] = []
    v_bar: list[float] = []
    for entry in per_galaxy:
        summary = entry.get("summary")
        if not isinstance(summary, dict):
            continue
        if diffuse_only and not is_diffuse_galaxy(summary):
            continue
        rows = entry.get("rows")
        if not isinstance(rows, list):
            continue
        for raw in rows:
            if not isinstance(raw, dict):
                continue
            vo = float(raw.get("v_obs_kms", 0.0))
            vh = float(raw.get("v_hqiv_kms", 0.0))
            vb = float(raw.get("v_baryonic_kms", 0.0))
            ev = float(raw.get("e_v_kms", 0.0))
            if ev <= 0.0 or not math.isfinite(vo):
                continue
            v_obs.append(vo)
            v_hqiv.append(vh)
            v_bar.append(vb)
    return v_obs, v_hqiv, v_bar, []


def r_squared_block(
    per_galaxy: list[dict[str, object]],
) -> dict[str, object]:
    """$R^2$ for full catalog, diffuse subset, and baryonic baseline."""
    vo_all, vh_all, vb_all, _ = collect_rotation_points(per_galaxy, diffuse_only=False)
    vo_d, vh_d, vb_d, _ = collect_rotation_points(per_galaxy, diffuse_only=True)
    n_diffuse = sum(
        1
        for e in per_galaxy
        if isinstance(e.get("summary"), dict) and is_diffuse_galaxy(e["summary"])  # type: ignore[arg-type]
    )
    return {
        "n_points_all": len(vo_all),
        "n_points_diffuse": len(vo_d),
        "n_galaxies_diffuse": n_diffuse,
        "r2_hqiv_all": r_squared(vo_all, vh_all),
        "r2_baryonic_all": r_squared(vo_all, vb_all),
        "r2_hqiv_diffuse": r_squared(vo_d, vh_d),
        "r2_baryonic_diffuse": r_squared(vo_d, vb_d),
        "median_v_obs_diffuse_kms": _median(vo_d),
        "median_v_hqiv_diffuse_kms": _median(vh_d),
    }


def plot_sparc_map(
    per_galaxy: list[dict[str, object]],
    output_path: str | os.PathLike[str],
    *,
    title: str = "SPARC: HQIV vs observed circular speed",
) -> None:
    """Scatter $v_{\rm obs}$ vs $v_{\rm HQIV}$ with 1:1 line; diffuse galaxies highlighted."""
    try:
        import matplotlib.pyplot as plt
    except ImportError as exc:
        raise SystemExit(
            "matplotlib required for --plot-figure. Install with: python3 -m pip install matplotlib"
        ) from exc

    vo_all: list[float] = []
    vh_all: list[float] = []
    vo_d: list[float] = []
    vh_d: list[float] = []
    for entry in per_galaxy:
        summary = entry.get("summary")
        if not isinstance(summary, dict):
            continue
        diffuse = is_diffuse_galaxy(summary)
        rows = entry.get("rows")
        if not isinstance(rows, list):
            continue
        for raw in rows:
            if not isinstance(raw, dict):
                continue
            vo = float(raw.get("v_obs_kms", 0.0))
            vh = float(raw.get("v_hqiv_kms", 0.0))
            ev = float(raw.get("e_v_kms", 0.0))
            if ev <= 0.0 or not math.isfinite(vo) or vo <= 0.0:
                continue
            vo_all.append(vo)
            vh_all.append(vh)
            if diffuse:
                vo_d.append(vo)
                vh_d.append(vh)

    fig, ax = plt.subplots(figsize=(6.5, 6.5), dpi=150)
    ax.scatter(vo_all, vh_all, s=8, alpha=0.25, c="#4477aa", label="all SPARC points", rasterized=True)
    if vo_d:
        ax.scatter(vo_d, vh_d, s=14, alpha=0.75, c="#cc3311", label="diffuse (Im/Sm/BCD/DDO)", rasterized=True)
    vmax = max(vo_all + vh_all + [1.0])
    ax.plot([0.0, vmax], [0.0, vmax], "k--", lw=1.0, label="1:1")
    r2_all = r_squared(vo_all, vh_all)
    r2_d = r_squared(vo_d, vh_d) if vo_d else float("nan")
    ax.set_xlabel(r"$v_{\rm obs}$ [km/s]")
    ax.set_ylabel(r"$v_{\rm HQIV}$ [km/s]")
    ax.set_title(title)
    ax.set_aspect("equal", adjustable="box")
    ax.legend(loc="upper left", fontsize=8)
    ax.text(
        0.04,
        0.96,
        rf"$R^2_{{\rm all}}$ = {r2_all:.3f}" + "\n"
        + (rf"$R^2_{{\rm diffuse}}$ = {r2_d:.3f}" if math.isfinite(r2_d) else ""),
        transform=ax.transAxes,
        va="top",
        ha="left",
        fontsize=9,
        bbox=dict(boxstyle="round", facecolor="white", alpha=0.85),
    )
    fig.tight_layout()
    out = Path(output_path)
    out.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out)
    plt.close(fig)


def summarize_catalog(per_galaxy: list[dict[str, object]]) -> dict[str, object]:
    """Aggregate chi^2 / RMS / improvement statistics over the catalog."""
    if not per_galaxy:
        return {"n_galaxies": 0}
    chi2_h: list[float] = []
    chi2_b: list[float] = []
    chi2_red_h: list[float] = []
    chi2_red_b: list[float] = []
    rms_h: list[float] = []
    rms_b: list[float] = []
    by_quality: dict[int, dict[str, list[float]]] = {}
    n_rows = 0
    sum_chi2_h = 0.0
    sum_chi2_b = 0.0
    n_hqiv_better = 0
    n_hqiv_10x_better = 0
    one_minus_f_means: list[float] = []
    for entry in per_galaxy:
        s = entry["summary"]
        if not isinstance(s, dict):
            continue
        chi_h = float(s["chi2_hqiv"])
        chi_b = float(s["chi2_baryonic"])
        chi2_h.append(chi_h)
        chi2_b.append(chi_b)
        chi2_red_h.append(float(s["chi2_red_hqiv"]))
        chi2_red_b.append(float(s["chi2_red_baryonic"]))
        rms_h.append(float(s["rms_hqiv_kms"]))
        rms_b.append(float(s["rms_baryonic_kms"]))
        n_rows += int(s["n_points"])
        sum_chi2_h += chi_h
        sum_chi2_b += chi_b
        if chi_h < chi_b:
            n_hqiv_better += 1
        if chi_h < 0.1 * chi_b:
            n_hqiv_10x_better += 1
        one_minus_f_means.append(float(s["mean_one_minus_f"]))
        q = int(s["quality"])
        bucket = by_quality.setdefault(q, {"chi2_red_hqiv": [], "chi2_red_bar": [], "n_better": [0.0]})
        bucket["chi2_red_hqiv"].append(float(s["chi2_red_hqiv"]))
        bucket["chi2_red_bar"].append(float(s["chi2_red_baryonic"]))
        if chi_h < chi_b:
            bucket["n_better"][0] += 1.0
    ranked = sorted(
        per_galaxy,
        key=lambda e: float(e["summary"]["chi2_red_hqiv"]),  # type: ignore[index]
    )
    best = [
        {
            "name": e["summary"]["name"],  # type: ignore[index]
            "quality": e["summary"]["quality"],  # type: ignore[index]
            "chi2_red_hqiv": e["summary"]["chi2_red_hqiv"],  # type: ignore[index]
            "chi2_red_baryonic": e["summary"]["chi2_red_baryonic"],  # type: ignore[index]
            "rms_hqiv_kms": e["summary"]["rms_hqiv_kms"],  # type: ignore[index]
        }
        for e in ranked[:10]
    ]
    worst = [
        {
            "name": e["summary"]["name"],  # type: ignore[index]
            "quality": e["summary"]["quality"],  # type: ignore[index]
            "chi2_red_hqiv": e["summary"]["chi2_red_hqiv"],  # type: ignore[index]
            "chi2_red_baryonic": e["summary"]["chi2_red_baryonic"],  # type: ignore[index]
            "rms_hqiv_kms": e["summary"]["rms_hqiv_kms"],  # type: ignore[index]
        }
        for e in ranked[-10:][::-1]
    ]
    per_quality = {
        str(q): {
            "n_galaxies": len(d["chi2_red_hqiv"]),
            "n_hqiv_better": int(d["n_better"][0]),
            "median_chi2_red_hqiv": _median(d["chi2_red_hqiv"]),
            "median_chi2_red_baryonic": _median(d["chi2_red_bar"]),
        }
        for q, d in sorted(by_quality.items())
    }
    return {
        "n_galaxies": len(per_galaxy),
        "n_rotmod_points": n_rows,
        "n_hqiv_better_than_baryonic": n_hqiv_better,
        "n_hqiv_more_than_10x_better": n_hqiv_10x_better,
        "fraction_hqiv_better": n_hqiv_better / max(len(per_galaxy), 1),
        "sum_chi2_hqiv": sum_chi2_h,
        "sum_chi2_baryonic": sum_chi2_b,
        "ratio_sum_chi2_hqiv_over_baryonic": _safe_div(sum_chi2_h, sum_chi2_b),
        "median_chi2_red_hqiv": _median(chi2_red_h),
        "median_chi2_red_baryonic": _median(chi2_red_b),
        "median_rms_hqiv_kms": _median(rms_h),
        "median_rms_baryonic_kms": _median(rms_b),
        "median_mean_one_minus_f": _median(one_minus_f_means),
        "per_quality": per_quality,
        "best_hqiv": best,
        "worst_hqiv": worst,
    }


def select_galaxies(
    catalog: dict[str, SparcGalaxy],
    *,
    quality_cut: int | None = None,
    min_inclination_deg: float | None = None,
    min_points: int = 1,
) -> dict[str, SparcGalaxy]:
    out: dict[str, SparcGalaxy] = {}
    for name, gal in catalog.items():
        if quality_cut is not None and gal.master.quality > quality_cut:
            continue
        if (
            min_inclination_deg is not None
            and gal.master.inclination_deg < min_inclination_deg
        ):
            continue
        if len(gal.rotmod) < min_points:
            continue
        out[name] = gal
    return out


def run_catalog(
    catalog: dict[str, SparcGalaxy],
    *,
    options: SparcOptions = SparcOptions(),
) -> list[dict[str, object]]:
    return [
        evaluate_galaxy(catalog[name], options=options)
        for name in sorted(catalog)
    ]


def list_galaxies(catalog: dict[str, SparcGalaxy]) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for name, gal in sorted(catalog.items()):
        m = gal.master
        rows.append(
            {
                "name": name,
                "hubble_label": m.hubble_label,
                "quality": m.quality,
                "distance_mpc": m.distance_mpc,
                "inclination_deg": m.inclination_deg,
                "rdisk_kpc": m.rdisk_kpc,
                "vflat_kms": m.vflat_kms,
                "n_rotmod": len(gal.rotmod),
            }
        )
    return rows


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _make_options(args: argparse.Namespace) -> SparcOptions:
    return SparcOptions(
        upsilon_disk=args.upsilon_disk,
        upsilon_bul=args.upsilon_bul,
        upsilon_gas=args.upsilon_gas,
        phi_shell=args.phi_shell,
        support_fraction=args.support_fraction,
        projection=args.projection,
        use_rindler_denominator=not args.no_rindler_denominator,
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="HQIV rotation-curve test on the SPARC catalog")
    parser.add_argument("--data-dir", default=str(DEFAULT_DATA_DIR))
    parser.add_argument("--list-galaxies", action="store_true")
    parser.add_argument("--galaxy", default=None, help="evaluate a single SPARC galaxy")
    parser.add_argument("--run-all", action="store_true")
    parser.add_argument("--quality-cut", type=int, default=None, help="keep galaxies with Q <= cut (1=high)")
    parser.add_argument("--min-inclination", type=float, default=None)
    parser.add_argument("--min-points", type=int, default=1)
    parser.add_argument("--upsilon-disk", type=float, default=UPSILON_DISK_FIDUCIAL)
    parser.add_argument("--upsilon-bul", type=float, default=UPSILON_BUL_FIDUCIAL)
    parser.add_argument("--upsilon-gas", type=float, default=1.0)
    parser.add_argument("--phi-shell", type=int, default=0)
    parser.add_argument("--support-fraction", type=float, default=1.0)
    parser.add_argument("--projection", type=float, default=1.0)
    parser.add_argument("--no-rindler-denominator", action="store_true")
    parser.add_argument("--write", default=None, help="dump full JSON payload to this path")
    parser.add_argument(
        "--plot-figure",
        default=None,
        help="write SPARC v_obs vs v_HQIV scatter PDF/PNG (requires matplotlib)",
    )
    parser.add_argument("--summary-only", action="store_true", help="print only the catalog summary")
    parser.add_argument("--indent", type=int, default=2)
    args = parser.parse_args(argv)

    catalog = load_sparc_catalog(args.data_dir)

    if args.list_galaxies:
        print(json.dumps(list_galaxies(catalog), indent=args.indent))
        return 0

    if args.galaxy is not None:
        if args.galaxy not in catalog:
            raise SystemExit(f"unknown SPARC galaxy {args.galaxy!r}")
        payload = evaluate_galaxy(catalog[args.galaxy], options=_make_options(args))
        if args.write:
            Path(args.write).parent.mkdir(parents=True, exist_ok=True)
            Path(args.write).write_text(json.dumps(payload, indent=args.indent))
        print(json.dumps(payload, indent=args.indent))
        return 0

    if args.run_all:
        filtered = select_galaxies(
            catalog,
            quality_cut=args.quality_cut,
            min_inclination_deg=args.min_inclination,
            min_points=args.min_points,
        )
        per_galaxy = run_catalog(filtered, options=_make_options(args))
        summary = summarize_catalog(per_galaxy)
        r2_block = r_squared_block(per_galaxy)
        payload: dict[str, object] = {
            "n_in_catalog": len(catalog),
            "n_evaluated": len(per_galaxy),
            "filters": {
                "quality_cut": args.quality_cut,
                "min_inclination_deg": args.min_inclination,
                "min_points": args.min_points,
            },
            "options": asdict(_make_options(args)),
            "summary": summary,
            "r_squared": r2_block,
            "lapse_model": "phi_hom / (1 + R/R_d); single radial exponent, no halo fit",
        }
        if args.plot_figure:
            plot_sparc_map(per_galaxy, args.plot_figure)
            payload["figure"] = str(args.plot_figure)
        if not args.summary_only:
            payload["per_galaxy"] = per_galaxy
        if args.write:
            Path(args.write).parent.mkdir(parents=True, exist_ok=True)
            Path(args.write).write_text(json.dumps(payload, indent=args.indent))
        if args.summary_only:
            print(json.dumps({k: v for k, v in payload.items() if k != "per_galaxy"}, indent=args.indent))
        else:
            print(json.dumps(payload, indent=args.indent))
        return 0

    parser.print_help()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

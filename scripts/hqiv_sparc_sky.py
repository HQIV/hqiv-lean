#!/usr/bin/env python3
"""Sky coordinates and disk-orientation helpers for SPARC galaxies.

SPARC master tables omit RA/Dec. Positions are cached in
``data/sparc_filament/sparc_sky_positions.json`` (SIMBAD lookups) and merged
into ``SparcMaster`` via ``enrich_sparc_master``.
"""

from __future__ import annotations

import json
import math
import re
import time
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Protocol

DEFAULT_SKY_PATH = Path(__file__).resolve().parent / "data" / "sparc_filament" / "sparc_sky_positions.json"
DEFAULT_ALIASES_PATH = Path(__file__).resolve().parent / "data" / "sparc_filament" / "sparc_sky_aliases.json"
VIZIER_SPARC_TABLE = "J/ApJS/247/31/galaxies"

SIMBAD_URL = "https://simbad.cds.unistra.fr/simbad/sim-id"
COORD_RE = re.compile(
    r"Coordinates\(ICRS,ep=J2000,eq=2000\):\s+"
    r"(\d+)\s+(\d+)\s+([\d.]+)\s+([+-]\d+)\s+(\d+)\s+([\d.]+)"
)


class SparcMasterLike(Protocol):
    name: str
    inclination_deg: float


@dataclass(frozen=True)
class SkyPosition:
    name: str
    ra_deg: float
    dec_deg: float
    position_angle_deg: float | None = None
    source: str = "simbad"

    def as_dict(self) -> dict[str, object]:
        return asdict(self)


def _normalize_ra(ra_deg: float) -> float:
    x = ra_deg % 360.0
    return x if x >= 0.0 else x + 360.0


def sexagesimal_to_deg(h: int, m: int, s: float, sign: int) -> float:
    dec = abs(h) + m / 60.0 + s / 3600.0
    return dec if sign >= 0 else -dec


def parse_simbad_icrs(text: str) -> tuple[float, float] | None:
    match = COORD_RE.search(text)
    if not match:
        return None
    ra_h, ra_m, ra_s, dec_sign, dec_d, dec_m = match.groups()
    ra_deg = (int(ra_h) + int(ra_m) / 60.0 + float(ra_s) / 3600.0) * 15.0
    dec_d_val = int(dec_sign)
    sign = 1 if dec_d_val >= 0 else -1
    dec_deg = sexagesimal_to_deg(abs(dec_d_val), int(dec_d), float(dec_m), sign)
    return _normalize_ra(ra_deg), dec_deg


def load_sky_aliases(path: str | Path | None = None) -> dict[str, str]:
    alias_path = Path(path) if path is not None else DEFAULT_ALIASES_PATH
    if not alias_path.exists():
        return {}
    raw = json.loads(alias_path.read_text(encoding="utf-8"))
    return {str(k): str(v) for k, v in raw.items() if isinstance(v, str)}


def resolve_simbad_ident(name: str, aliases: dict[str, str] | None = None) -> str:
    table = aliases if aliases is not None else load_sky_aliases()
    return table.get(name, name)


def fetch_simbad_coordinates(
    name: str,
    *,
    timeout_s: float = 20.0,
    aliases: dict[str, str] | None = None,
) -> SkyPosition | None:
    """Query SIMBAD for ICRS coordinates of a SPARC galaxy name."""
    ident = resolve_simbad_ident(name, aliases)
    query = urllib.parse.urlencode({"Ident": ident, "output.format": "ASCII"})
    url = f"{SIMBAD_URL}?{query}"
    req = urllib.request.Request(url, headers={"User-Agent": "HQIV-Orbital/1.0"})
    try:
        with urllib.request.urlopen(req, timeout=timeout_s) as resp:
            text = resp.read().decode("utf-8", errors="replace")
    except (urllib.error.URLError, TimeoutError):
        return None
    coords = parse_simbad_icrs(text)
    if coords is None:
        return None
    ra_deg, dec_deg = coords
    return SkyPosition(name=name, ra_deg=ra_deg, dec_deg=dec_deg, source="simbad")


def fetch_vizier_sparc_positions(*, timeout_s: float = 60.0) -> dict[str, SkyPosition]:
    """Bulk-fetch J2000 positions for all SPARC galaxies from VizieR (Li+2020 table)."""
    url = (
        "https://vizier.cds.unistra.fr/viz-bin/asu-tsv?"
        "-source=J/ApJS/247/31/galaxies&"
        "-out=Name&-out=_RA&-out=_DE&-out.max=200"
    )
    req = urllib.request.Request(url, headers={"User-Agent": "HQIV-Orbital/1.0"})
    with urllib.request.urlopen(req, timeout=timeout_s) as resp:
        text = resp.read().decode("utf-8", errors="replace")
    positions: dict[str, SkyPosition] = {}
    for line in text.splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) < 3:
            continue
        name = parts[0].strip()
        if not name or name in ("Name", "----"):
            continue
        try:
            ra_deg = float(parts[1])
            dec_deg = float(parts[2])
        except ValueError:
            continue
        positions[name] = SkyPosition(
            name=name,
            ra_deg=_normalize_ra(ra_deg),
            dec_deg=dec_deg,
            source="vizier_j_apjs_247_31",
        )
    return positions


def load_sky_positions(path: str | Path | None = None) -> dict[str, SkyPosition]:
    sky_path = Path(path) if path is not None else DEFAULT_SKY_PATH
    if not sky_path.exists():
        return {}
    raw = json.loads(sky_path.read_text(encoding="utf-8"))
    out: dict[str, SkyPosition] = {}
    for name, row in raw.items():
        if not isinstance(row, dict):
            continue
        out[str(name)] = SkyPosition(
            name=str(name),
            ra_deg=float(row["ra_deg"]),
            dec_deg=float(row["dec_deg"]),
            position_angle_deg=float(row["position_angle_deg"])
            if row.get("position_angle_deg") is not None
            else None,
            source=str(row.get("source", "catalog")),
        )
    return out


def save_sky_positions(positions: dict[str, SkyPosition], path: str | Path | None = None) -> Path:
    sky_path = Path(path) if path is not None else DEFAULT_SKY_PATH
    sky_path.parent.mkdir(parents=True, exist_ok=True)
    payload = {name: pos.as_dict() for name, pos in sorted(positions.items())}
    sky_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return sky_path


def fetch_sparc_sky_catalog(
    names: list[str],
    *,
    path: str | Path | None = None,
    delay_s: float = 0.15,
    skip_existing: bool = True,
    prefer_vizier: bool = True,
) -> dict[str, SkyPosition]:
    """Fetch sky coordinates for SPARC names (VizieR bulk, then SIMBAD gaps)."""
    positions = load_sky_positions(path) if skip_existing else {}
    aliases = load_sky_aliases()

    if prefer_vizier:
        try:
            vizier = fetch_vizier_sparc_positions()
            for name in names:
                if skip_existing and name in positions:
                    continue
                if name in vizier:
                    positions[name] = vizier[name]
        except (urllib.error.URLError, TimeoutError, OSError):
            pass

    for name in names:
        if skip_existing and name in positions:
            continue
        pos = fetch_simbad_coordinates(name, aliases=aliases)
        if pos is not None:
            positions[name] = pos
        elif delay_s > 0.0:
            time.sleep(delay_s)
    save_sky_positions(positions, path)
    return positions


def unit_from_ra_dec(ra_deg: float, dec_deg: float) -> tuple[float, float, float]:
    ra = math.radians(ra_deg)
    dec = math.radians(dec_deg)
    cdec = math.cos(dec)
    return (cdec * math.cos(ra), cdec * math.sin(ra), math.sin(dec))


def icrs_triad(ra_deg: float, dec_deg: float) -> tuple[tuple[float, float, float], tuple[float, float, float], tuple[float, float, float]]:
    """Return (east, north, radial) unit vectors at (RA, Dec) in ICRS."""
    r_hat = unit_from_ra_dec(ra_deg, dec_deg)
    north_pole = (0.0, 0.0, 1.0)
    east = (
        north_pole[1] * r_hat[2] - north_pole[2] * r_hat[1],
        north_pole[2] * r_hat[0] - north_pole[0] * r_hat[2],
        north_pole[0] * r_hat[1] - north_pole[1] * r_hat[0],
    )
    n_east = math.sqrt(east[0] ** 2 + east[1] ** 2 + east[2] ** 2)
    if n_east <= 0.0:
        east = (1.0, 0.0, 0.0)
    else:
        east = (east[0] / n_east, east[1] / n_east, east[2] / n_east)
    north = (
        r_hat[1] * east[2] - r_hat[2] * east[1],
        r_hat[2] * east[0] - r_hat[0] * east[2],
        r_hat[0] * east[1] - r_hat[1] * east[0],
    )
    return east, north, r_hat


def filament_spine_from_angle(ra_deg: float, dec_deg: float, angle_deg: float) -> tuple[float, float, float]:
    """Filament tangent on the sky from Carrón ``Angle`` (deg CCW from RA parallel)."""
    east, north, _ = icrs_triad(ra_deg, dec_deg)
    ang = math.radians(angle_deg)
    fx = math.cos(ang) * east[0] + math.sin(ang) * north[0]
    fy = math.cos(ang) * east[1] + math.sin(ang) * north[1]
    fz = math.cos(ang) * east[2] + math.sin(ang) * north[2]
    n = math.sqrt(fx * fx + fy * fy + fz * fz)
    if n <= 0.0:
        return east
    return (fx / n, fy / n, fz / n)


def angular_separation_deg(
    ra1_deg: float,
    dec1_deg: float,
    ra2_deg: float,
    dec2_deg: float,
) -> float:
    r1 = unit_from_ra_dec(ra1_deg, dec1_deg)
    r2 = unit_from_ra_dec(ra2_deg, dec2_deg)
    dot = max(-1.0, min(1.0, r1[0] * r2[0] + r1[1] * r2[1] + r1[2] * r2[2]))
    return math.degrees(math.acos(dot))


def disk_intrinsic_triad(
    inclination_deg: float,
    position_angle_deg: float,
) -> tuple[tuple[float, float, float], tuple[float, float, float], tuple[float, float, float]]:
    """Intrinsic disk frame: z = spin, x = major axis, y = minor (SPARC conventions).

    Inclination is angle between line-of-sight and disk plane normal (90° = edge-on).
    Position angle is of the receding major axis, measured east from north on the sky.
    """
    inc = math.radians(max(inclination_deg, 1.0))
    pa = math.radians(position_angle_deg)
    # Sky-projected major axis in observer x-y (RA/Dec tangent) plane.
    x_sky = (math.sin(pa), math.cos(pa), 0.0)
    z_sky = (math.sin(inc) * math.cos(pa), math.sin(inc) * math.sin(pa), math.cos(inc))
    y_sky = (
        z_sky[1] * x_sky[2] - z_sky[2] * x_sky[1],
        z_sky[2] * x_sky[0] - z_sky[0] * x_sky[2],
        z_sky[0] * x_sky[1] - z_sky[1] * x_sky[0],
    )
    n = math.sqrt(y_sky[0] ** 2 + y_sky[1] ** 2 + y_sky[2] ** 2)
    if n > 0.0:
        y_sky = (y_sky[0] / n, y_sky[1] / n, y_sky[2] / n)
    return x_sky, y_sky, z_sky


def vector_to_disk_frame(
    vec_icrs: tuple[float, float, float],
    inclination_deg: float,
    position_angle_deg: float,
) -> tuple[float, float, float]:
    """Express an ICRS unit vector in the disk intrinsic frame."""
    x_d, y_d, z_d = disk_intrinsic_triad(inclination_deg, position_angle_deg)
    vx, vy, vz = vec_icrs
    return (
        vx * x_d[0] + vy * x_d[1] + vz * x_d[2],
        vx * y_d[0] + vy * y_d[1] + vz * y_d[2],
        vx * z_d[0] + vy * z_d[1] + vz * z_d[2],
    )

#!/usr/bin/env python3
"""Filament spine vectors and environment data for SPARC galaxies.

When a curated cross-match is unavailable, ``infer_filament_proxy`` builds a
deterministic HI-geometry proxy from SPARC master-table fields (R_HI/R_d,
inclination, morphology). External catalogs (Carrón+2021 SDSS filaments,
Tempel+ Bisous) can be ingested via ``load_filament_catalog`` once galaxies
are cross-matched to sky position.

Catalog format (JSON object keyed by SPARC name)::

    {
      "NGC3198": {
        "unit": [0.82, 0.55, 0.12],
        "distance_to_spine_mpc": 0.6,
        "inflow_speed_kms": 85,
        "spine_angle_deg": 34.0,
        "source": "carrón2021_block1"
      }
    }

``unit`` is the filament spine direction in a right-handed frame where +z is
the disk angular-momentum axis (intrinsic), +x is the major axis, and +y
completes the triad.
"""

from __future__ import annotations

import hashlib
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Protocol

DEFAULT_CATALOG_PATH = Path(__file__).resolve().parent / "data" / "sparc_filament" / "filament_vectors.json"


class GalaxyMasterLike(Protocol):
    name: str
    hubble_type: int
    inclination_deg: float
    rdisk_kpc: float
    rhi_kpc: float
    vflat_kms: float
    distance_mpc: float


@dataclass(frozen=True)
class FilamentEnvironment:
    name: str
    unit_x: float
    unit_y: float
    unit_z: float
    distance_to_spine_mpc: float
    inflow_speed_kms: float
    spine_angle_deg: float | None
    source: str

    def unit(self) -> tuple[float, float, float]:
        return (self.unit_x, self.unit_y, self.unit_z)

    def as_dict(self) -> dict[str, object]:
        return asdict(self)


def _normalize(x: float, y: float, z: float) -> tuple[float, float, float]:
    n = math.sqrt(x * x + y * y + z * z)
    if n <= 0.0:
        return (1.0, 0.0, 0.0)
    return (x / n, y / n, z / n)


def _stable_phase(name: str) -> float:
    """Reproducible pseudo position angle [rad] when no external catalog."""
    digest = hashlib.sha256(name.encode()).hexdigest()
    return (int(digest[:8], 16) / 0xFFFFFFFF) * 2.0 * math.pi


def disk_spin_unit(inclination_deg: float) -> tuple[float, float, float]:
    """Unit spin axis in observer frame; intrinsic L along z, tilted by inclination."""
    inc = math.radians(max(inclination_deg, 1.0))
    # Line-of-sight in x–z plane; L perpendicular to disk plane.
    return _normalize(math.sin(inc), 0.0, math.cos(inc))


def load_filament_catalog(path: str | Path | None = None) -> dict[str, FilamentEnvironment]:
    """Load curated filament vectors; returns empty dict if file missing."""
    catalog_path = Path(path) if path is not None else DEFAULT_CATALOG_PATH
    if not catalog_path.exists():
        return {}
    raw = json.loads(catalog_path.read_text(encoding="utf-8"))
    out: dict[str, FilamentEnvironment] = {}
    for name, row in raw.items():
        if not isinstance(row, dict):
            continue
        unit = row.get("unit", [1.0, 0.0, 0.0])
        if not isinstance(unit, list) or len(unit) != 3:
            continue
        ux, uy, uz = _normalize(float(unit[0]), float(unit[1]), float(unit[2]))
        out[str(name)] = FilamentEnvironment(
            name=str(name),
            unit_x=ux,
            unit_y=uy,
            unit_z=uz,
            distance_to_spine_mpc=float(row.get("distance_to_spine_mpc", 1.0)),
            inflow_speed_kms=float(row.get("inflow_speed_kms", 0.0)),
            spine_angle_deg=float(row["spine_angle_deg"]) if row.get("spine_angle_deg") is not None else None,
            source=str(row.get("source", "catalog")),
        )
    return out


def infer_filament_proxy(master: GalaxyMasterLike) -> FilamentEnvironment:
    """HI-geometry proxy when no sky cross-match is available."""
    rd = max(master.rdisk_kpc, 0.08)
    elong = master.rhi_kpc / rd if master.rhi_kpc > 0.05 else max(2.0, 1.0 + 0.15 * (11 - master.hubble_type))
    pa = _stable_phase(master.name)
    # Major-axis filament in disk plane; weak z from accretion onto inclined disk.
    inc = math.radians(max(master.inclination_deg, 5.0))
    fx = math.cos(pa)
    fy = math.sin(pa)
    fz = 0.08 * math.sin(inc) / max(elong, 1.0)
    ux, uy, uz = _normalize(fx, fy, fz)
    v_in = max(0.35 * master.vflat_kms, 15.0) if master.vflat_kms > 0.0 else 25.0
    d_spine = max(0.15, min(2.5, master.distance_mpc * 0.08 / max(elong ** 0.5, 1.0)))
    return FilamentEnvironment(
        name=master.name,
        unit_x=ux,
        unit_y=uy,
        unit_z=uz,
        distance_to_spine_mpc=d_spine,
        inflow_speed_kms=v_in,
        spine_angle_deg=math.degrees(pa),
        source="sparc_hi_proxy",
    )


def resolve_filament_environment(
    master: GalaxyMasterLike,
    catalog: dict[str, FilamentEnvironment] | None = None,
) -> FilamentEnvironment:
    if catalog and master.name in catalog:
        return catalog[master.name]
    return infer_filament_proxy(master)


def misalignment_sin(
    spin_unit: tuple[float, float, float],
    filament_unit: tuple[float, float, float],
) -> float:
    """|sin θ| between spin axis and filament spine (0 = parallel, 1 = perpendicular)."""
    sx, sy, sz = spin_unit
    fx, fy, fz = filament_unit
    dot = max(-1.0, min(1.0, sx * fx + sy * fy + sz * fz))
    return math.sqrt(max(0.0, 1.0 - dot * dot))


def filament_environment_metadata(
    master: GalaxyMasterLike,
    catalog: dict[str, FilamentEnvironment] | None = None,
) -> dict[str, object]:
    env = resolve_filament_environment(master, catalog)
    spin = disk_spin_unit(master.inclination_deg)
    mis = misalignment_sin(spin, env.unit())
    return {
        **env.as_dict(),
        "spin_unit": spin,
        "misalignment_sin": mis,
    }

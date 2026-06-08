#!/usr/bin/env python3
"""Carrón+2022 (J/A+A/659/A166) cosmic filament catalog access.

Builds a coarse HEALPix-style sky grid index from ``block1.dat.gz`` so SPARC
galaxies can be matched to the nearest filament spine without loading 1.9M rows
into RAM per query.
"""

from __future__ import annotations

import gzip
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path

import hqiv_sparc_sky as _sky

DEFAULT_BLOCK1_PATH = (
    Path(__file__).resolve().parent / "data" / "sparc_filament" / "raw" / "block1.dat.gz"
)
DEFAULT_INDEX_PATH = (
    Path(__file__).resolve().parent / "data" / "sparc_filament" / "raw" / "block1_index.json"
)
BLOCK1_URL = "https://cdsarc.cds.unistra.fr/ftp/cats/J/A+A/659/A166/block1.dat.gz"
BIN_SIZE_DEG = 0.2


@dataclass(frozen=True)
class CarronFilamentPoint:
    index: int
    ra_deg: float
    dec_deg: float
    dens: float
    e_pos_deg: float
    grad_ra: float
    grad_de: float
    angle_deg: float
    z_low: float
    z_high: float

    def spine_unit_icrs(self) -> tuple[float, float, float]:
        return _sky.filament_spine_from_angle(self.ra_deg, self.dec_deg, self.angle_deg)


def parse_carron_line(line: str) -> CarronFilamentPoint | None:
    """Parse one fixed-width row (197 bytes) from block1/2/3."""
    if len(line) < 178:
        return None
    try:
        return CarronFilamentPoint(
            index=int(line[0:7].strip()),
            ra_deg=float(line[8:30]),
            dec_deg=float(line[31:54]),
            dens=float(line[55:73]),
            e_pos_deg=float(line[74:93]),
            grad_ra=float(line[94:117]),
            grad_de=float(line[118:141]),
            angle_deg=float(line[142:166]),
            z_low=float(line[167:172]),
            z_high=float(line[173:178]),
        )
    except ValueError:
        return None


def _bin_key(ra_deg: float, dec_deg: float) -> tuple[int, int]:
    ra = _sky._normalize_ra(ra_deg)
    dec = max(-90.0, min(90.0, dec_deg))
    return (int(ra / BIN_SIZE_DEG), int((dec + 90.0) / BIN_SIZE_DEG))


def build_block1_index(
    block1_path: str | Path,
    *,
    index_path: str | Path | None = None,
    stride: int = 1,
) -> dict[str, object]:
    """Single pass: keep highest-density point per sky bin."""
    path = Path(block1_path)
    if not path.exists():
        raise FileNotFoundError(f"Carrón block1 not found: {path}")
    bins: dict[str, dict[str, object]] = {}
    n_read = 0
    opener = gzip.open if str(path).endswith(".gz") else open
    with opener(path, "rt", encoding="ascii", errors="replace") as fh:
        for line_num, line in enumerate(fh, start=1):
            if stride > 1 and (line_num - 1) % stride != 0:
                continue
            pt = parse_carron_line(line)
            if pt is None:
                continue
            n_read += 1
            key = _bin_key(pt.ra_deg, pt.dec_deg)
            key_s = f"{key[0]}:{key[1]}"
            prev = bins.get(key_s)
            if prev is None or pt.dens > float(prev["dens"]):
                bins[key_s] = {
                    "index": pt.index,
                    "ra_deg": pt.ra_deg,
                    "dec_deg": pt.dec_deg,
                    "dens": pt.dens,
                    "e_pos_deg": pt.e_pos_deg,
                    "grad_ra": pt.grad_ra,
                    "grad_de": pt.grad_de,
                    "angle_deg": pt.angle_deg,
                    "z_low": pt.z_low,
                    "z_high": pt.z_high,
                }
    payload = {
        "bin_size_deg": BIN_SIZE_DEG,
        "n_bins": len(bins),
        "n_rows_read": n_read,
        "stride": stride,
        "bins": bins,
    }
    out = Path(index_path) if index_path is not None else DEFAULT_INDEX_PATH
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload), encoding="utf-8")
    return payload


def load_block1_index(path: str | Path | None = None) -> dict[str, object] | None:
    idx_path = Path(path) if path is not None else DEFAULT_INDEX_PATH
    if not idx_path.exists():
        return None
    return json.loads(idx_path.read_text(encoding="utf-8"))


def nearest_filament_point(
    ra_deg: float,
    dec_deg: float,
    index: dict[str, object],
    *,
    search_bins: int = 2,
) -> tuple[CarronFilamentPoint, float] | None:
    """Return (point, angular_separation_deg) or None if index empty."""
    bins: dict[str, dict[str, object]] = index.get("bins", {})  # type: ignore[assignment]
    if not bins:
        return None
    ira, idec = _bin_key(ra_deg, dec_deg)
    best: CarronFilamentPoint | None = None
    best_sep = 1.0e9
    for dra in range(-search_bins, search_bins + 1):
        for ddec in range(-search_bins, search_bins + 1):
            key = f"{ira + dra}:{idec + ddec}"
            row = bins.get(key)
            if row is None:
                continue
            pt = CarronFilamentPoint(
                index=int(row["index"]),
                ra_deg=float(row["ra_deg"]),
                dec_deg=float(row["dec_deg"]),
                dens=float(row["dens"]),
                e_pos_deg=float(row["e_pos_deg"]),
                grad_ra=float(row["grad_ra"]),
                grad_de=float(row["grad_de"]),
                angle_deg=float(row["angle_deg"]),
                z_low=float(row["z_low"]),
                z_high=float(row["z_high"]),
            )
            sep = _sky.angular_separation_deg(ra_deg, dec_deg, pt.ra_deg, pt.dec_deg)
            if sep < best_sep:
                best_sep = sep
                best = pt
    if best is None:
        return None
    return best, best_sep


def download_block1(dest: str | Path | None = None) -> Path:
    import urllib.request

    out = Path(dest) if dest is not None else DEFAULT_BLOCK1_PATH
    out.parent.mkdir(parents=True, exist_ok=True)
    if out.exists() and out.stat().st_size > 1_000_000:
        return out
    urllib.request.urlretrieve(BLOCK1_URL, out)
    return out

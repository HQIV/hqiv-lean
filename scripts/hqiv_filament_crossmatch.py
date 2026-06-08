#!/usr/bin/env python3
"""Cross-match SPARC galaxies to Carrón+2022 filament spines.

Writes ``filament_vectors.json`` entries with spine unit vectors in the disk
intrinsic frame, distance to spine, and inflow speed estimates.

Usage::

    python hqiv_filament_crossmatch.py --fetch-sky
    python hqiv_filament_crossmatch.py --download-block1 --build-index
    python hqiv_filament_crossmatch.py --crossmatch --max-sep-deg 1.5
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path

import hqiv_carron_filament as _carron
import hqiv_filament_environment as _fil
import hqiv_sparc_rotation as _sparc
import hqiv_sparc_sky as _sky

DEFAULT_VECTORS_PATH = _fil.DEFAULT_CATALOG_PATH
DEFAULT_SKY_PATH = _sky.DEFAULT_SKY_PATH
DEFAULT_MAX_SEP_DEG = 2.25
DEFAULT_LOCAL_MAX_SEP_DEG = 4.5
LOCAL_VOLUME_DEC_DEG = 55.0


def _stable_pa(name: str) -> float:
    digest = hashlib.sha256(name.encode()).hexdigest()
    return (int(digest[8:16], 16) / 0xFFFFFFFF) * 180.0


def crossmatch_galaxy(
    master: _sparc.SparcMaster,
    sky: _sky.SkyPosition,
    index: dict[str, object],
    *,
    max_sep_deg: float,
    local_max_sep_deg: float,
) -> dict[str, object] | None:
    high_lat = abs(sky.dec_deg) >= LOCAL_VOLUME_DEC_DEG
    search_bins = 25 if high_lat else 8
    hit = _carron.nearest_filament_point(
        sky.ra_deg, sky.dec_deg, index, search_bins=search_bins
    )
    if hit is None:
        return None
    pt, sep_deg = hit
    sep_limit = local_max_sep_deg if high_lat else max_sep_deg
    if sep_deg > sep_limit:
        return None
    spine_icrs = pt.spine_unit_icrs()
    pa = sky.position_angle_deg if sky.position_angle_deg is not None else _stable_pa(master.name)
    ux, uy, uz = _sky.vector_to_disk_frame(spine_icrs, master.inclination_deg, pa)
    n = math.sqrt(ux * ux + uy * uy + uz * uz)
    if n > 0.0:
        ux, uy, uz = ux / n, uy / n, uz / n
    d_spine_mpc = master.distance_mpc * math.radians(sep_deg)
    v_in = max(0.35 * master.vflat_kms, 15.0) if master.vflat_kms > 0.0 else 25.0
    source = "carron2022_block1_local" if high_lat and sep_deg > max_sep_deg else "carron2022_block1"
    return {
        "unit": [ux, uy, uz],
        "distance_to_spine_mpc": round(d_spine_mpc, 4),
        "inflow_speed_kms": round(v_in, 2),
        "spine_angle_deg": round(pt.angle_deg, 2),
        "carron_sep_deg": round(sep_deg, 4),
        "carron_z_low": pt.z_low,
        "carron_z_high": pt.z_high,
        "ra_deg": sky.ra_deg,
        "dec_deg": sky.dec_deg,
        "position_angle_deg": pa,
        "source": source,
    }


def run_crossmatch(
    *,
    max_sep_deg: float = DEFAULT_MAX_SEP_DEG,
    local_max_sep_deg: float = DEFAULT_LOCAL_MAX_SEP_DEG,
    sky_path: Path = DEFAULT_SKY_PATH,
    vectors_path: Path = DEFAULT_VECTORS_PATH,
    index_path: Path | None = None,
) -> dict[str, object]:
    catalog = _sparc.load_sparc_catalog()
    sky_positions = _sky.load_sky_positions(sky_path)
    index = _carron.load_block1_index(index_path)
    if index is None:
        raise FileNotFoundError(
            "Carrón block1 index missing. Run with --download-block1 --build-index first."
        )
    existing: dict[str, object] = {}
    if vectors_path.exists():
        existing = json.loads(vectors_path.read_text(encoding="utf-8"))
    matched = 0
    skipped = 0
    for name, galaxy in sorted(catalog.items()):
        sky = sky_positions.get(name)
        if sky is None:
            skipped += 1
            continue
        row = crossmatch_galaxy(
            galaxy.master,
            sky,
            index,
            max_sep_deg=max_sep_deg,
            local_max_sep_deg=local_max_sep_deg,
        )
        if row is not None:
            existing[name] = row
            matched += 1
        elif name in existing and str(existing[name].get("source", "")).startswith("carron2022"):
            del existing[name]
    vectors_path.parent.mkdir(parents=True, exist_ok=True)
    vectors_path.write_text(json.dumps(existing, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return {
        "n_sparc": len(catalog),
        "n_sky": len(sky_positions),
        "n_matched": matched,
        "n_skipped_no_sky": skipped,
        "vectors_path": str(vectors_path),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="SPARC ↔ Carrón filament cross-match")
    parser.add_argument("--fetch-sky", action="store_true", help="Fetch SIMBAD coordinates for SPARC")
    parser.add_argument("--download-block1", action="store_true", help="Download Carrón block1.dat.gz")
    parser.add_argument("--build-index", action="store_true", help="Build sky-bin index from block1")
    parser.add_argument("--crossmatch", action="store_true", help="Write filament_vectors.json")
    parser.add_argument("--max-sep-deg", type=float, default=DEFAULT_MAX_SEP_DEG)
    parser.add_argument(
        "--local-max-sep-deg",
        type=float,
        default=DEFAULT_LOCAL_MAX_SEP_DEG,
        help="wider match for |Dec|>=55 deg (local volume / BOSS footprint edge)",
    )
    parser.add_argument("--fetch-vizier", action="store_true", help="bulk VizieR sky positions only")
    parser.add_argument("--stride", type=int, default=1, help="Subsample block1 rows when indexing")
    parser.add_argument("--sky-path", type=Path, default=DEFAULT_SKY_PATH)
    parser.add_argument("--vectors-path", type=Path, default=DEFAULT_VECTORS_PATH)
    parser.add_argument("--block1-path", type=Path, default=_carron.DEFAULT_BLOCK1_PATH)
    parser.add_argument("--index-path", type=Path, default=_carron.DEFAULT_INDEX_PATH)
    args = parser.parse_args()

    if args.fetch_vizier:
        positions = _sky.fetch_vizier_sparc_positions()
        _sky.save_sky_positions(positions, args.sky_path)
        print(json.dumps({"n_vizier": len(positions), "path": str(args.sky_path)}, indent=2))

    if args.fetch_sky:
        names = sorted(_sparc.load_sparc_catalog().keys())
        positions = _sky.fetch_sparc_sky_catalog(names, path=args.sky_path)
        print(json.dumps({"n_fetched": len(positions), "path": str(args.sky_path)}, indent=2))

    if args.download_block1:
        path = _carron.download_block1(args.block1_path)
        print(json.dumps({"block1_path": str(path), "bytes": path.stat().st_size}, indent=2))

    if args.build_index:
        summary = _carron.build_block1_index(args.block1_path, index_path=args.index_path, stride=args.stride)
        print(json.dumps({k: summary[k] for k in ("n_bins", "n_rows_read", "stride")}, indent=2))

    if args.crossmatch:
        summary = run_crossmatch(
            max_sep_deg=args.max_sep_deg,
            local_max_sep_deg=args.local_max_sep_deg,
            sky_path=args.sky_path,
            vectors_path=args.vectors_path,
            index_path=args.index_path,
        )
        print(json.dumps(summary, indent=2))

    if not any((args.fetch_sky, args.fetch_vizier, args.download_block1, args.build_index, args.crossmatch)):
        parser.print_help()


if __name__ == "__main__":
    main()

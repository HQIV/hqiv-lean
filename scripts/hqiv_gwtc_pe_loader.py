#!/usr/bin/env python3
"""
GWTC-5.0 parameter-estimation helpers (Zenodo PE releases + GWOSC).

Official references (May 2026):
  https://gwosc.org/GWTC-5.0/
  PE Part 1: https://zenodo.org/records/20348005  (includes PESummaryTable.hdf5)
  PE Part 2: https://zenodo.org/records/20348006
  Candidates: https://zenodo.org/records/20276130
  Notebook: https://doi.org/10.5281/zenodo.20276105

The lightweight ``PESummaryTable.hdf5`` (~200 KB) holds per-event PE medians
(final mass, final spin, χ_eff, …). Full per-event ``combined_PEDataRelease.hdf5``
files hold posterior samples (hundreds of MB each).
"""

from __future__ import annotations

import json
import urllib.error
import urllib.request
from dataclasses import dataclass
from pathlib import Path
from typing import Any

GWOSC_GWTC_PAGE = "https://gwosc.org/GWTC-5.0/"
ZENODO_PE_PART1 = "https://zenodo.org/records/20348005"
ZENODO_PE_PART2 = "https://zenodo.org/records/20348006"
ZENODO_CANDIDATES = "https://zenodo.org/records/20276130"
ZENODO_NOTEBOOK = "https://doi.org/10.5281/zenodo.20276105"

PE_SUMMARY_FILENAME = "IGWN-GWTC5p0-29ebe06b7_25-PESummaryTable.hdf5"
PE_SUMMARY_ZENODO_URL = (
    f"https://zenodo.org/api/records/20348005/files/{PE_SUMMARY_FILENAME}/content"
)

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PE_CACHE = REPO_ROOT / "data" / "gwtc5_pe"


def official_links() -> dict[str, str]:
    return {
        "gwosc_catalog": GWOSC_GWTC_PAGE,
        "zenodo_pe_part1": ZENODO_PE_PART1,
        "zenodo_pe_part2": ZENODO_PE_PART2,
        "zenodo_candidates": ZENODO_CANDIDATES,
        "zenodo_notebook": ZENODO_NOTEBOOK,
        "pe_summary_table_url": PE_SUMMARY_ZENODO_URL,
    }


def _decode_str(value: Any) -> str:
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return str(value)


def _require_h5py():
    try:
        import h5py  # type: ignore
    except ImportError as exc:
        raise RuntimeError(
            "h5py is required for GWTC PE HDF5 files. "
            "Install: python3 -m venv .venv-gw && .venv-gw/bin/pip install h5py"
        ) from exc
    return h5py


@dataclass(frozen=True)
class PeSummaryRow:
    gw_name: str
    result_label: str
    final_mass_msun: float
    final_mass_lower_msun: float | None
    final_mass_upper_msun: float | None
    final_spin: float | None
    final_spin_lower: float | None
    final_spin_upper: float | None
    chi_eff: float | None
    snr: float | None


def download_pe_summary_table(
    dest_dir: Path | None = None,
    *,
    force: bool = False,
) -> Path:
    dest_dir = dest_dir or DEFAULT_PE_CACHE
    dest_dir.mkdir(parents=True, exist_ok=True)
    out = dest_dir / "PESummaryTable.hdf5"
    if out.is_file() and not force:
        return out
    try:
        with urllib.request.urlopen(PE_SUMMARY_ZENODO_URL, timeout=120) as resp:
            out.write_bytes(resp.read())
    except (urllib.error.URLError, TimeoutError) as exc:
        raise RuntimeError(f"failed to download PE summary table: {exc}") from exc
    return out


def load_pe_summary_table(path: Path | str) -> list[PeSummaryRow]:
    h5py = _require_h5py()
    rows: list[PeSummaryRow] = []
    with h5py.File(str(path), "r") as f:
        table = f["summary_info"]
        for rec in table:
            if rec["final_mass_source_median.mask"]:
                continue
            spin = None
            spin_lo = None
            spin_up = None
            if not rec["final_spin_median.mask"]:
                spin = float(rec["final_spin_median"])
                if not rec["final_spin_lower.mask"]:
                    spin_lo = float(rec["final_spin_lower"])
                if not rec["final_spin_upper.mask"]:
                    spin_up = float(rec["final_spin_upper"])
            snr = None
            if not rec["network_matched_filter_snr_median.mask"]:
                snr = float(rec["network_matched_filter_snr_median"])
            rows.append(
                PeSummaryRow(
                    gw_name=_decode_str(rec["gw_name"]),
                    result_label=_decode_str(rec["result_label"]),
                    final_mass_msun=float(rec["final_mass_source_median"]),
                    final_mass_lower_msun=(
                        float(rec["final_mass_source_lower"])
                        if not rec["final_mass_source_lower.mask"]
                        else None
                    ),
                    final_mass_upper_msun=(
                        float(rec["final_mass_source_upper"])
                        if not rec["final_mass_source_upper.mask"]
                        else None
                    ),
                    final_spin=spin,
                    final_spin_lower=spin_lo,
                    final_spin_upper=spin_up,
                    chi_eff=float(rec["chi_eff_median"]),
                    snr=snr,
                )
            )
    return rows


def pe_summary_spin_proxy(row: PeSummaryRow) -> float:
    if row.final_spin is not None:
        return max(0.0, min(0.99, row.final_spin))
    if row.chi_eff is not None:
        return max(0.0, min(0.99, row.chi_eff))
    return 0.0


def load_combined_pe_posterior_medians(
    path: Path | str,
    *,
    analysis_label: str | None = None,
) -> dict[str, float]:
    """
    Read one ``combined_PEDataRelease.hdf5`` and return medians for common parameters.

    Uses h5py only (no pesummary dependency). Prefers a label containing
    ``Combined`` when ``analysis_label`` is omitted.
    """
    h5py = _require_h5py()
    path = Path(path)
    with h5py.File(str(path), "r") as f:
        labels = [k for k in f.keys() if k != "version"]
        if not labels:
            raise ValueError(f"no analysis labels in {path}")
        label = analysis_label
        if label is None:
            combined = [lb for lb in labels if "Combined" in lb or "combined" in lb.lower()]
            label = combined[0] if combined else labels[0]
        if label not in f:
            raise KeyError(f"analysis {label!r} not in {path}; have {labels[:5]}")
        grp = f[label]
        if "posterior_samples" not in grp:
            raise KeyError(f"no posterior_samples under {label}")
        data = grp["posterior_samples"]
        # Structured numpy array stored as HDF5 compound dataset
        import numpy as np

        samples = np.array(data)
        names = samples.dtype.names or ()
        out: dict[str, float] = {}
        wanted = (
            "final_mass_source",
            "final_mass",
            "final_spin",
            "chi_eff",
            "f_220",
            "omega_220",
            "tau_220",
        )
        for name in wanted:
            if name in names:
                col = samples[name]
                out[f"{name}_median"] = float(np.median(col))
        return {"analysis_label": label, "sample_count": len(samples), **out}


def pe_summary_rows_for_catalog(
    *,
    cache_dir: Path | None = None,
    download: bool = True,
    min_final_mass_msun: float = 5.0,
    max_events: int = 50,
) -> list[dict[str, object]]:
    """PE summary rows formatted for ``hqiv_gw_ringdown``."""
    cache = cache_dir or DEFAULT_PE_CACHE
    summary_path = cache / "PESummaryTable.hdf5"
    if download and not summary_path.is_file():
        download_pe_summary_table(cache)
    if not summary_path.is_file():
        raise FileNotFoundError(
            f"missing {summary_path}; run with download=True or place PESummaryTable.hdf5 there"
        )

    rows = load_pe_summary_table(summary_path)
    rows.sort(key=lambda r: r.final_mass_msun, reverse=True)
    out: list[dict[str, object]] = []
    for row in rows:
        if row.final_mass_msun < min_final_mass_msun:
            continue
        spin = pe_summary_spin_proxy(row)
        out.append(
            {
                "commonName": row.gw_name,
                "catalog": "GWTC-5.0",
                "catalog_final_mass_msun": row.final_mass_msun,
                "catalog_final_mass_lower_msun": row.final_mass_lower_msun,
                "catalog_final_mass_upper_msun": row.final_mass_upper_msun,
                "pe_final_spin": row.final_spin,
                "chi_eff": row.chi_eff,
                "final_spin_proxy": spin,
                "snr": row.snr,
                "pe_result_label": row.result_label,
                "notes": "PE summary medians from Zenodo PESummaryTable.hdf5",
            }
        )
        if len(out) >= max_events:
            break
    return out


def write_pe_manifest(cache_dir: Path | None = None) -> Path:
    cache = cache_dir or DEFAULT_PE_CACHE
    cache.mkdir(parents=True, exist_ok=True)
    manifest = {
        "official_links": official_links(),
        "local_files": {
            "pe_summary_table": str(cache / "PESummaryTable.hdf5"),
            "combined_pe_pattern": "IGWN-GWTC5p0-29ebe06b7_25-{event}-combined_PEDataRelease.hdf5",
        },
        "usage": {
            "summary_table": "python3 scripts/hqiv_gw_ringdown.py --pe-summary",
            "single_pe_file": "python3 scripts/hqiv_gw_ringdown.py --pe-hdf5 path/to/combined_PEDataRelease.hdf5",
            "ringdown_inputs": "python3 scripts/hqiv_gw_ringdown.py --f 251 --tau-ms 4",
        },
    }
    out = cache / "manifest.json"
    out.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    return out

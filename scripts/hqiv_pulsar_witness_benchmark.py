#!/usr/bin/env python3
"""
Fetch the ATNF pulsar catalog and compare HQIV compact-object / slip-torque witnesses.

Catalog source: XAO mirror of the ATNF Pulsar Catalogue (IVO cone search, CSV).
Mass overlay: ``data/pulsar_mass_measurements.json`` (NICER + Shapiro-delay literature).

Derived dipole field (standard spindown):
  ``B_G = 3.2 × 10^19 √(P Ṗ)`` with ``P`` in s and ``Ṗ`` in s/s (Gauss).

Run:
  python3 scripts/hqiv_pulsar_witness_benchmark.py
  python3 scripts/hqiv_pulsar_witness_benchmark.py --refresh-catalog
  python3 scripts/hqiv_pulsar_witness_benchmark.py --json
"""

from __future__ import annotations

import argparse
import csv
import io
import json
import math
import re
import sys
import urllib.request
from dataclasses import asdict, dataclass
from pathlib import Path

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(_ROOT / "scripts"))

from hqiv_compact_object_mass import (  # noqa: E402
    M_SUN_KG,
    breakup_omega_rad_s,
    compare_spindown_charm_to_pulsar_dataset,
    radius_uniform_density,
    RHO_NUCLEAR_KG_M3,
    slip_torque_balance_for_star,
)

CATALOG_URL = (
    "http://data.xao.ac.cn/pulsarcatalog/q/cone/scs.xml"
    "?VERB=2&RA=0&DEC=0&SR=180&MAXREC=20000&responseformat=csv"
)
DEFAULT_CATALOG_JSON = _ROOT / "data" / "pulsar_catalog.json"
DEFAULT_MASS_JSON = _ROOT / "data" / "pulsar_mass_measurements.json"
DEFAULT_COMPARE_JSON = _ROOT / "data" / "pulsar_witness_comparison.json"
DEFAULT_MASS_MSUN = 1.4
MIN_B_G = 1.0e8
MAX_B_G = 1.0e13
MS_PERIOD_S = 0.03
CANONICAL_B_G = 1.0e12


def mass_literature_spindown_rows(
    mass_table: dict[str, dict[str, object]],
) -> list[dict[str, object]]:
    """Build spindown rows from mass table when catalog lacks Pdot (showcase overlay)."""
    rows: list[dict[str, object]] = []
    seen: set[str] = set()
    for entry in mass_table.values():
        name = str(entry["name"])
        norm = normalize_pulsar_name(name)
        if norm in seen:
            continue
        seen.add(norm)
        period = entry.get("period_s")
        period_dot = entry.get("period_dot_s_per_s")
        if period is None or period_dot is None:
            continue
        period_f = float(period)
        pdot_f = float(period_dot)
        if period_f <= 0.0 or pdot_f <= 0.0:
            continue
        b_g = dipole_b_field_gauss(period_f, pdot_f)
        if b_g < MIN_B_G or b_g > MAX_B_G:
            continue
        mass_msun = float(entry["mass_msun"])
        mass_kg = mass_msun * M_SUN_KG
        r_sph = radius_uniform_density(mass_kg, RHO_NUCLEAR_KG_M3)
        omega_break_hz = breakup_omega_rad_s(mass_kg, r_sph) / (2.0 * math.pi)
        freq_hz = 1.0 / period_f
        rows.append(
            {
                "name": name,
                "name_normalized": norm,
                "period_s": period_f,
                "period_dot_s_per_s": pdot_f,
                "period_error_s": None,
                "period_dot_error": None,
                "dm_pc_cm3": None,
                "dm_error": None,
                "freq_hz": freq_hz,
                "b_field_gauss": b_g,
                "b_field_t": b_g * 1.0e-4,
                "characteristic_age_yr": characteristic_age_yr(period_f, pdot_f),
                "mass_msun": mass_msun,
                "mass_err_msun": entry.get("mass_err_msun"),
                "mass_source": str(entry.get("source", "literature")),
                "omega_over_breakup": freq_hz / omega_break_hz if omega_break_hz > 0 else None,
                "is_millisecond": period_f < MS_PERIOD_S,
                "literature_overlay": True,
            }
        )
    return rows


def normalize_pulsar_name(name: str) -> str:
    s = name.strip().upper()
    s = re.sub(r"\s+", "", s)
    if not s.startswith("PSR"):
        s = f"PSR{s}" if s.startswith("J") or s.startswith("B") else f"PSR{s}"
    return s


def dipole_b_field_gauss(period_s: float, period_dot_s_per_s: float) -> float:
    """Surface dipole field in Gauss from spindown (canonical)."""
    if period_s <= 0.0 or period_dot_s_per_s <= 0.0:
        return 0.0
    return 3.2e19 * math.sqrt(period_s * period_dot_s_per_s)


def characteristic_age_yr(period_s: float, period_dot_s_per_s: float) -> float:
    if period_s <= 0.0 or period_dot_s_per_s <= 0.0:
        return float("nan")
    return period_s / (2.0 * period_dot_s_per_s) / (365.25 * 24.0 * 3600.0)


def fetch_catalog_csv() -> str:
    with urllib.request.urlopen(CATALOG_URL, timeout=120) as resp:
        return resp.read().decode("utf-8", errors="replace")


def load_mass_table(path: Path) -> dict[str, dict[str, object]]:
    data = json.loads(path.read_text())
    table: dict[str, dict[str, object]] = {}
    for entry in data.get("entries", []):
        keys = [normalize_pulsar_name(entry["name"])]
        for alias in entry.get("aliases", []):
            keys.append(normalize_pulsar_name(alias))
        for key in keys:
            table[key] = entry
    return table


def parse_catalog_csv(text: str) -> list[dict[str, object]]:
    reader = csv.DictReader(io.StringIO(text))
    rows: list[dict[str, object]] = []
    for row in reader:
        name = (row.get("name") or "").strip()
        if not name:
            continue
        period = _float_or_none(row.get("period"))
        period_dot = _float_or_none(row.get("period_dot"))
        dm = _float_or_none(row.get("dm"))
        rows.append(
            {
                "name": name,
                "name_normalized": normalize_pulsar_name(name),
                "period_s": period,
                "period_dot_s_per_s": period_dot,
                "period_error_s": _float_or_none(row.get("period_error")),
                "period_dot_error": _float_or_none(row.get("period_dot_error")),
                "dm_pc_cm3": dm,
                "dm_error": _float_or_none(row.get("dm_error")),
            }
        )
    return rows


def _float_or_none(value: str | None) -> float | None:
    if value is None or str(value).strip() == "":
        return None
    try:
        return float(value)
    except ValueError:
        return None


def enrich_catalog_rows(
    rows: list[dict[str, object]],
    mass_table: dict[str, dict[str, object]],
) -> list[dict[str, object]]:
    enriched: list[dict[str, object]] = []
    for row in rows:
        period = row.get("period_s")
        period_dot = row.get("period_dot_s_per_s")
        if not isinstance(period, float) or not isinstance(period_dot, float):
            continue
        if period <= 0.0 or period_dot <= 0.0:
            continue

        b_g = dipole_b_field_gauss(period, period_dot)
        if b_g < MIN_B_G or b_g > MAX_B_G:
            continue

        norm = str(row["name_normalized"])
        mass_entry = mass_table.get(norm)
        mass_msun = DEFAULT_MASS_MSUN
        mass_source = "canonical_1.4Msun_default"
        mass_err = None
        if mass_entry:
            mass_msun = float(mass_entry["mass_msun"])
            mass_source = str(mass_entry.get("source", "literature"))
            err = mass_entry.get("mass_err_msun")
            mass_err = float(err) if err is not None else None

        freq_hz = 1.0 / period
        mass_kg = mass_msun * M_SUN_KG
        r_sph = radius_uniform_density(mass_kg, RHO_NUCLEAR_KG_M3)
        omega_break_hz = breakup_omega_rad_s(mass_kg, r_sph) / (2.0 * math.pi)

        enriched.append(
            {
                **row,
                "freq_hz": freq_hz,
                "b_field_gauss": b_g,
                "b_field_t": b_g * 1.0e-4,
                "characteristic_age_yr": characteristic_age_yr(period, period_dot),
                "mass_msun": mass_msun,
                "mass_err_msun": mass_err,
                "mass_source": mass_source,
                "omega_over_breakup": freq_hz / omega_break_hz if omega_break_hz > 0 else None,
                "is_millisecond": period < MS_PERIOD_S,
            }
        )
    return enriched


@dataclass(frozen=True)
class WitnessCompareRow:
    name: str
    mass_msun: float
    mass_source: str
    period_ms: float
    freq_hz: float
    b_field_gauss: float
    omega_over_breakup: float
    psi_shear_deg: float
    psi_long_deg: float
    delta_b_over_b: float
    alpha_equilibrium_b_eff_deg: float
    alpha_equilibrium_closed_loop_deg: float
    alpha_equilibrium_aligning_enhanced_deg: float
    alpha_equilibrium_canonical_b_deg: float
    torque_ratio_b_eff: float
    torque_ratio_aligning_enhanced: float
    closes_with_b_eff: bool
    closes_closed_loop: bool
    closes_with_aligning_enhanced: bool
    in_mass_table: bool


def witness_row_for_pulsar(entry: dict[str, object]) -> WitnessCompareRow | None:
    mass_msun = float(entry["mass_msun"])
    freq_hz = float(entry["freq_hz"])
    b_t = float(entry["b_field_t"])
    name = str(entry["name"])
    try:
        slip = slip_torque_balance_for_star(
            mass_msun,
            freq_hz,
            name,
            B_surface_t=b_t,
        )
        slip_b12 = slip_torque_balance_for_star(
            mass_msun,
            freq_hz,
            name,
            B_surface_t=CANONICAL_B_G * 1.0e-4,
        )
    except (ValueError, RuntimeError):
        return None

    return WitnessCompareRow(
        name=name,
        mass_msun=mass_msun,
        mass_source=str(entry["mass_source"]),
        period_ms=float(entry["period_s"]) * 1000.0,
        freq_hz=freq_hz,
        b_field_gauss=float(entry["b_field_gauss"]),
        omega_over_breakup=float(entry.get("omega_over_breakup") or 0.0),
        psi_shear_deg=slip.psi_shear_deg,
        psi_long_deg=slip.psi_long_deg,
        delta_b_over_b=slip.delta_b_over_b,
        alpha_equilibrium_b_eff_deg=slip.alpha_equilibrium_b_eff_deg,
        alpha_equilibrium_closed_loop_deg=slip.alpha_equilibrium_closed_loop_deg,
        alpha_equilibrium_aligning_enhanced_deg=slip.alpha_equilibrium_aligning_enhanced_deg,
        alpha_equilibrium_canonical_b_deg=slip_b12.alpha_equilibrium_aligning_enhanced_deg,
        torque_ratio_b_eff=slip.torque_ratio_b_eff,
        torque_ratio_aligning_enhanced=slip.torque_ratio_aligning_enhanced,
        closes_with_b_eff=slip.closes_with_b_eff,
        closes_closed_loop=slip.closes_closed_loop,
        closes_with_aligning_enhanced=slip.closes_with_aligning_enhanced,
        in_mass_table=str(entry["mass_source"]) != "canonical_1.4Msun_default",
    )


def summarize_comparison(rows: list[WitnessCompareRow]) -> dict[str, object]:
    ms = [r for r in rows if r.period_ms < MS_PERIOD_S * 1000.0]
    measured = [r for r in rows if r.in_mass_table]
    closes_b_eff = [r for r in rows if r.closes_with_b_eff]
    closes_enhanced = [r for r in rows if r.closes_with_aligning_enhanced]

    def _mean(vals: list[float]) -> float:
        return sum(vals) / len(vals) if vals else 0.0

    return {
        "total_with_witness": len(rows),
        "millisecond_count": len(ms),
        "mass_measured_count": len(measured),
        "closes_b_eff_count": len(closes_b_eff),
        "closes_b_eff_fraction": len(closes_b_eff) / len(rows) if rows else 0.0,
        "closes_aligning_enhanced_count": len(closes_enhanced),
        "closes_aligning_enhanced_fraction": len(closes_enhanced) / len(rows) if rows else 0.0,
        "mean_psi_shear_deg_all": _mean([r.psi_shear_deg for r in rows]),
        "mean_psi_shear_deg_ms": _mean([r.psi_shear_deg for r in ms]),
        "mean_alpha_eq_b_eff_deg_ms": _mean([r.alpha_equilibrium_b_eff_deg for r in ms]),
        "mean_alpha_eq_aligning_enhanced_deg_ms": _mean(
            [r.alpha_equilibrium_aligning_enhanced_deg for r in ms]
        ),
        "mean_torque_ratio_b_eff_ms": _mean([r.torque_ratio_b_eff for r in ms]),
        "mean_torque_ratio_aligning_enhanced_ms": _mean(
            [r.torque_ratio_aligning_enhanced for r in ms]
        ),
        "mean_omega_over_breakup_ms": _mean([r.omega_over_breakup for r in ms]),
    }


def build_benchmark(
    *,
    refresh_catalog: bool = False,
) -> dict[str, object]:
    mass_table = load_mass_table(DEFAULT_MASS_JSON)

    if refresh_catalog or not DEFAULT_CATALOG_JSON.exists():
        csv_text = fetch_catalog_csv()
        raw_rows = parse_catalog_csv(csv_text)
        catalog_rows = enrich_catalog_rows(raw_rows, mass_table)
        catalog_payload = {
            "source_url": CATALOG_URL,
            "catalog_mirror": "XAO ATNF pulsar catalog cone search",
            "row_count_raw": len(raw_rows),
            "row_count_spindown_valid": len(catalog_rows),
            "rows": catalog_rows,
        }
        DEFAULT_CATALOG_JSON.write_text(json.dumps(catalog_payload, indent=2) + "\n")
    else:
        catalog_payload = json.loads(DEFAULT_CATALOG_JSON.read_text())
        catalog_rows = catalog_payload["rows"]

    overlay_rows = mass_literature_spindown_rows(mass_table)
    catalog_by_name = {str(r["name_normalized"]): r for r in catalog_rows}
    for row in overlay_rows:
        norm = str(row["name_normalized"])
        if norm not in catalog_by_name:
            catalog_rows.append(row)
        else:
            # Prefer literature overlay when catalog lacks spindown derivative.
            cat = catalog_by_name[norm]
            if cat.get("period_dot_s_per_s") is None or float(cat.get("period_dot_s_per_s") or 0) <= 0:
                catalog_rows.remove(cat)
                catalog_rows.append(row)

    compare_rows: list[WitnessCompareRow] = []
    for entry in catalog_rows:
        row = witness_row_for_pulsar(entry)
        if row is not None:
            compare_rows.append(row)

    showcase = sorted(
        [r for r in compare_rows if r.in_mass_table],
        key=lambda r: r.mass_msun,
    )

    summary = summarize_comparison(compare_rows)
    ms_rows = sorted(
        [r for r in compare_rows if r.period_ms < MS_PERIOD_S * 1000.0],
        key=lambda r: r.freq_hz,
        reverse=True,
    )

    spindown_charm_ms = compare_spindown_charm_to_pulsar_dataset(millisecond_only=True)
    spindown_charm_mass = compare_spindown_charm_to_pulsar_dataset(mass_measured_only=True)

    return {
        "description": (
            "HQIV slip-torque witness compared to ATNF pulsar spindown parameters. "
            "B_field from dipole formula; mass from literature table or 1.4 M☉ default."
        ),
        "catalog_path": str(DEFAULT_CATALOG_JSON),
        "mass_table_path": str(DEFAULT_MASS_JSON),
        "hqiv_witness_module": "scripts/hqiv_compact_object_mass.py",
        "summary": summary,
        "spindown_charm_comparison_ms": spindown_charm_ms,
        "spindown_charm_comparison_mass_measured": spindown_charm_mass,
        "showcase_mass_measured": [asdict(r) for r in showcase],
        "fastest_ms_pulsars": [asdict(r) for r in ms_rows[:15]],
        "all_rows": [asdict(r) for r in compare_rows],
    }


def print_report(data: dict[str, object]) -> None:
    summary = data["summary"]
    print("Pulsar catalog vs HQIV slip-torque witness")
    print(f"  Catalog: {data['catalog_path']}")
    print(f"  Pulsars with witness: {summary['total_with_witness']}")
    print(f"  Millisecond: {summary['millisecond_count']}")
    print(f"  Mass-measured overlay: {summary['mass_measured_count']}")
    print(
        f"  Closes τ balance (B_eff): {summary['closes_b_eff_count']} "
        f"({summary['closes_b_eff_fraction']:.1%})"
    )
    print(
        f"  Closes τ balance (aligning enhanced): "
        f"{summary['closes_aligning_enhanced_count']} "
        f"({summary['closes_aligning_enhanced_fraction']:.1%})"
    )
    print(
        f"  Mean ψ_shear (all): {summary['mean_psi_shear_deg_all']:.3f}°  "
        f"(ms: {summary['mean_psi_shear_deg_ms']:.3f}°)"
    )
    print(
        f"  Mean α_eq (B_eff, ms): {summary['mean_alpha_eq_b_eff_deg_ms']:.1f}°  "
        f"(enhanced: {summary['mean_alpha_eq_aligning_enhanced_deg_ms']:.1f}°)  "
        f"mean Ω/Ω_break (ms): {summary['mean_omega_over_breakup_ms']:.3f}"
    )
    sp_ms = data.get("spindown_charm_comparison_ms", {})
    sp_mass = data.get("spindown_charm_comparison_mass_measured", {})
    if sp_ms:
        print()
        print("Spindown/charm dynamics (catalog overlay):")
        print(
            f"  ms mean τ_char/τ_spin_drain={sp_ms.get('mean_integration_over_spin_drain', 0):.4g}  "
            f"charm/dipole={sp_ms.get('mean_charm_weak_over_dipole', 0):.4g}  "
            f"mean Δm={sp_ms.get('mean_delta_mass_total_msun', 0):.4g} M☉"
        )
        if sp_mass:
            print(
                f"  mass-measured mean Δm={sp_mass.get('mean_delta_mass_total_msun', 0):.4g} M☉  "
                f"max Δm={sp_mass.get('max_delta_mass_total_msun', 0):.4g} M☉"
            )
    print()
    print("Showcase (mass-measured):")
    for row in data["showcase_mass_measured"]:
        print(
            f"  {row['name']}: M={row['mass_msun']:.2f} M☉, "
            f"P={row['period_ms']:.3f} ms, B={row['b_field_gauss']:.2e} G, "
            f"ψ_shear={row['psi_shear_deg']:.2f}°, "
            f"α_eq(B_cat)={row['alpha_equilibrium_b_eff_deg']:.1f}°, "
            f"α_eq(B=10¹²G)={row['alpha_equilibrium_canonical_b_deg']:.1f}°"
        )
    print()
    print("Fastest ms pulsars (witness):")
    for row in data["fastest_ms_pulsars"][:8]:
        print(
            f"  {row['name']}: f={row['freq_hz']:.0f} Hz, "
            f"Ω/Ω_break={row['omega_over_breakup']:.3f}, "
            f"α_eq(enh)={row['alpha_equilibrium_aligning_enhanced_deg']:.1f}°, "
            f"τ_ratio={row['torque_ratio_aligning_enhanced']:.2f}"
        )


def main() -> None:
    parser = argparse.ArgumentParser(description="Pulsar catalog vs HQIV witness")
    parser.add_argument(
        "--refresh-catalog",
        action="store_true",
        help="re-download ATNF mirror CSV into data/pulsar_catalog.json",
    )
    parser.add_argument("--json", action="store_true", help="write data/pulsar_witness_comparison.json")
    args = parser.parse_args()

    data = build_benchmark(refresh_catalog=args.refresh_catalog)
    print_report(data)
    if args.json:
        DEFAULT_COMPARE_JSON.write_text(json.dumps(data, indent=2) + "\n")
        print(f"\nWrote {DEFAULT_COMPARE_JSON}")


if __name__ == "__main__":
    main()

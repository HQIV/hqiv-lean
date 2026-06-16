#!/usr/bin/env python3
"""
GW ringdown inference: measured f₂₂₀ and τ₂₂₀ → remnant mass (GR vs HQIV).

Detectors measure ringdown frequency and damping time; mass is inferred from those
via Kerr (2,2,0) QNM fits. This script runs that inversion twice:

  • **GR inference** — standard Kerr map from (f, τ) to M_f, a*.
  • **HQIV inference** — unmap horizon scaling slots then same Kerr inversion, so
    the same measured (f, τ) correspond to a different remnant mass.

Lean: `Hqiv.Physics.GravitationalWaveRingdownScaffold`
Python: `hqiv_compact_object_mass` (G_eff, induction η, charm mass tail).

GWTC-5.0: loads official PE medians from Zenodo ``PESummaryTable.hdf5``, derives Kerr
(f, τ) from PE (M_f, a*), then inverts to M_GR and M_HQIV.

Official links: https://gwosc.org/GWTC-5.0/ ; Zenodo PE Part 1/2 (see ``hqiv_gwtc_pe_loader``).

Run:
  python3 scripts/hqiv_gw_ringdown.py --pe-summary --json
  python3 scripts/hqiv_gw_ringdown.py --f 251 --tau-ms 4.0
  python3 scripts/hqiv_gw_ringdown.py --pe-hdf5 path/to/combined_PEDataRelease.hdf5
"""

from __future__ import annotations

import argparse
import json
import math
import sys
import urllib.error
import urllib.request
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Literal

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(_ROOT / "scripts"))

from hqiv_compact_object_mass import (  # noqa: E402
    C_LIGHT,
    EPS_HORIZON,
    G_NEWTON,
    GAMMA,
    M_SUN_KG,
    NS_SURFACE_T_K,
    RHO_NUCLEAR_KG_M3,
    ALPHA,
    charmed_tail_mass_oblate,
    induction_resistivity_eta_from_environment,
    outside_geff_modulator_from_epsilon,
    radius_uniform_density,
)

GWOSC_GWTC_URL = "https://gwosc.org/eventapi/json/GWTC/"
MERGER_HOT_SURFACE_T_K = 1.0e11
HMNS_MASS_THRESHOLD_MSUN = 3.5
GR_TAIL_EXPONENT = 4.0

_KERR_220_SPIN_TABLE: tuple[tuple[float, float, float], ...] = (
    (0.00, 0.373676, -0.089472),
    (0.10, 0.410000, -0.088900),
    (0.20, 0.436000, -0.088200),
    (0.30, 0.465000, -0.087300),
    (0.40, 0.482000, -0.086200),
    (0.50, 0.499000, -0.085000),
    (0.60, 0.518000, -0.083200),
    (0.68, 0.523975, -0.081513),
    (0.80, 0.546000, -0.079000),
    (0.90, 0.568000, -0.076500),
    (0.95, 0.579000, -0.074500),
    (0.99, 0.588000, -0.071500),
)

# Literature / ringdown-pipeline anchors (f₂₂₀ Hz, τ₂₂₀ ms) — detection inputs.
LANDMARK_EVENTS: tuple[dict[str, object], ...] = (
    {
        "commonName": "GW150914",
        "catalog": "GWTC-1.0",
        "f_220_hz": 251.0,
        "tau_220_ms": 4.0,
        "catalog_final_mass_msun": 65.0,
        "notes": "Literature Kerr-fit f₂₂₀; GR inference ≈ catalog M_f",
    },
    {
        "commonName": "GW190521",
        "catalog": "GWTC-2.1",
        "f_220_hz": 64.0,
        "tau_220_ms": 9.5,
        "catalog_final_mass_msun": 142.0,
        "notes": "High-mass BBH schematic ringdown witness",
    },
    {
        "commonName": "GW170817",
        "catalog": "GWTC-1.0",
        "f_220_hz": 1850.0,
        "tau_220_ms": 0.12,
        "catalog_final_mass_msun": 2.74,
        "notes": "HMNS / merger remnant — Kerr overlay schematic only",
    },
)


@dataclass(frozen=True)
class RingdownMeasurement:
    f_220_hz: float
    tau_220_s: float
    omega_ratio: float  # 2π f τ = Re(Mω)/|Im(Mω)|


@dataclass(frozen=True)
class KerrMassInference:
    final_mass_msun: float
    final_spin: float
    mass_from_frequency_msun: float
    mass_from_damping_msun: float
    omega_M_real: float
    omega_M_imag: float


@dataclass(frozen=True)
class HqivScalingSlots:
    horizon_epsilon: float
    horizon_lapse: float
    geff_modulator: float
    freq_scale: float
    damp_scale_base: float
    damp_scale_with_eta: float
    eta_merger: float
    eta_lockin_surface: float
    tail_exponent: float


@dataclass(frozen=True)
class RingdownMassInferenceRow:
    common_name: str
    catalog: str
    measurement: RingdownMeasurement
    gr_inference: KerrMassInference
    hqiv_inference: KerrMassInference
    hqiv_slots: HqivScalingSlots
    mass_tail_delta_msun: float
    effective_mass_msun: float
    catalog_final_mass_msun: float | None
    chi_eff: float | None
    snr: float | None
    remnant_class: Literal["BBH", "HMNS_candidate", "intermediate"]
    measurement_source: Literal[
        "literature_ringdown",
        "user_cli",
        "pe_kerr_ringdown_from_pe_mass_spin",
        "pe_hdf5_posterior",
        "synthetic_from_catalog",
    ]
    mass_ratio_gr_over_catalog: float | None
    mass_ratio_hqiv_over_catalog: float | None
    notes: str


def _linear_interp(x: float, xs: list[float], ys: list[float]) -> float:
    if x <= xs[0]:
        return ys[0]
    if x >= xs[-1]:
        return ys[-1]
    for i in range(len(xs) - 1):
        if xs[i] <= x <= xs[i + 1]:
            t = (x - xs[i]) / (xs[i + 1] - xs[i])
            return ys[i] + t * (ys[i + 1] - ys[i])
    return ys[-1]


def kerr_220_dimensionless_omega(final_spin: float) -> tuple[float, float]:
    a = max(0.0, min(0.99, final_spin))
    spins = [row[0] for row in _KERR_220_SPIN_TABLE]
    re_vals = [row[1] for row in _KERR_220_SPIN_TABLE]
    im_vals = [row[2] for row in _KERR_220_SPIN_TABLE]
    return _linear_interp(a, spins, re_vals), _linear_interp(a, spins, im_vals)


def kerr_220_omega_ratio(final_spin: float) -> float:
    om_r, om_i = kerr_220_dimensionless_omega(final_spin)
    return om_r / abs(om_i)


def ringdown_measurement(f_hz: float, tau_s: float) -> RingdownMeasurement:
    if f_hz <= 0.0 or tau_s <= 0.0:
        raise ValueError("f and τ must be positive")
    return RingdownMeasurement(
        f_220_hz=f_hz,
        tau_220_s=tau_s,
        omega_ratio=2.0 * math.pi * f_hz * tau_s,
    )


def infer_spin_from_omega_ratio(omega_ratio: float) -> float:
    """Match Re(Mω)/|Im(Mω)| = 2π f τ on the Kerr (2,2,0) table."""
    spins = [row[0] for row in _KERR_220_SPIN_TABLE]
    ratios = [row[1] / abs(row[2]) for row in _KERR_220_SPIN_TABLE]
    if omega_ratio <= ratios[0]:
        return spins[0]
    if omega_ratio >= ratios[-1]:
        return spins[-1]
    best_a = spins[0]
    best_err = float("inf")
    for a in spins:
        err = abs(kerr_220_omega_ratio(a) - omega_ratio)
        if err < best_err:
            best_err = err
            best_a = a
    return best_a


def gr_ringdown_params(final_mass_msun: float, final_spin: float) -> tuple[float, float, float]:
    """Return (f_220_hz, tau_220_s, mf_geo_s) for Kerr (2,2,0)."""
    om_r, om_i = kerr_220_dimensionless_omega(final_spin)
    mass_kg = final_mass_msun * M_SUN_KG
    mf = G_NEWTON * mass_kg / C_LIGHT**3
    f_hz = om_r * C_LIGHT**3 / (2.0 * math.pi * G_NEWTON * mass_kg)
    tau_s = mf / abs(om_i)
    return f_hz, tau_s, mf


def kerr_ringdown_from_mass_spin(final_mass_msun: float, final_spin: float) -> tuple[float, float]:
    f_hz, tau_s, _ = gr_ringdown_params(final_mass_msun, final_spin)
    return f_hz, tau_s


def infer_kerr_mass_from_ringdown(f_hz: float, tau_s: float) -> KerrMassInference:
    """
    Standard Kerr inference: measured (f, τ) → M_f and a*.

    ``M = |Im(Mω)| · τ · c³/G`` and ``M = Re(Mω) · c³ / (2π G f)``; spin from ``2π f τ``.
    """
    meas = ringdown_measurement(f_hz, tau_s)
    spin = infer_spin_from_omega_ratio(meas.omega_ratio)
    om_r, om_i = kerr_220_dimensionless_omega(spin)
    mass_from_tau_kg = abs(om_i) * tau_s * C_LIGHT**3 / G_NEWTON
    mass_from_f_kg = om_r * C_LIGHT**3 / (2.0 * math.pi * G_NEWTON * f_hz)
    mass_kg = mass_from_tau_kg
    return KerrMassInference(
        final_mass_msun=mass_kg / M_SUN_KG,
        final_spin=spin,
        mass_from_frequency_msun=mass_from_f_kg / M_SUN_KG,
        mass_from_damping_msun=mass_from_tau_kg / M_SUN_KG,
        omega_M_real=om_r,
        omega_M_imag=om_i,
    )


def hqiv_horizon_slots() -> HqivScalingSlots:
    eps = EPS_HORIZON
    lapse = 1.0 - eps
    geff = outside_geff_modulator_from_epsilon(eps)
    freq_scale = math.sqrt(geff) / lapse**ALPHA
    damp_base = lapse / geff
    eta_merger = induction_resistivity_eta_from_environment(
        EPS_HORIZON, MERGER_HOT_SURFACE_T_K
    )
    eta_lockin = induction_resistivity_eta_from_environment(0.0, NS_SURFACE_T_K)
    eta_ratio = eta_merger / eta_lockin if eta_lockin > 0.0 else 1.0
    damp_with_eta = damp_base * (1.0 + eta_ratio)
    tail_offset = GAMMA * (1.0 - lapse) + ALPHA * (geff - 1.0)
    return HqivScalingSlots(
        horizon_epsilon=eps,
        horizon_lapse=lapse,
        geff_modulator=geff,
        freq_scale=freq_scale,
        damp_scale_base=damp_base,
        damp_scale_with_eta=damp_with_eta,
        eta_merger=eta_merger,
        eta_lockin_surface=eta_lockin,
        tail_exponent=GR_TAIL_EXPONENT + tail_offset,
    )


def hqiv_mass_tail_delta_msun(core_mass_msun: float) -> float:
    mass_kg = core_mass_msun * M_SUN_KG
    r_sph = radius_uniform_density(mass_kg, RHO_NUCLEAR_KG_M3)
    m_tail, _, _, _, _ = charmed_tail_mass_oblate(mass_kg, 0.0, spherical_radius_m=r_sph)
    return max(0.0, (m_tail - mass_kg) / M_SUN_KG)


def remnant_class_for_mass(mass_msun: float) -> Literal["BBH", "HMNS_candidate", "intermediate"]:
    if mass_msun < HMNS_MASS_THRESHOLD_MSUN:
        return "HMNS_candidate"
    if mass_msun < 8.0:
        return "intermediate"
    return "BBH"


def hqiv_unmap_to_kerr_frequencies(
    f_hz: float,
    tau_s: float,
    slots: HqivScalingSlots,
    *,
    core_mass_msun: float,
    mass_tail_msun: float,
) -> tuple[float, float]:
    """
    Inverse of the HQIV forward map: detector (f, τ) → effective Kerr (f_kerr, τ_kerr).

    Forward (BBH): ``f = f_kerr · s_f``, ``τ = τ_kerr · s_τ``.
    Forward (HMNS): also ``f ∝ M/M_eff``, ``τ ∝ M_eff/M``.
    """
    m_eff = core_mass_msun + mass_tail_msun
    if core_mass_msun <= 0.0:
        return f_hz / slots.freq_scale, tau_s / slots.damp_scale_with_eta
    mass_ratio = core_mass_msun / m_eff
    f_kerr = f_hz / slots.freq_scale / mass_ratio
    tau_kerr = tau_s / slots.damp_scale_with_eta / (m_eff / core_mass_msun)
    return f_kerr, tau_kerr


def infer_hqiv_mass_from_ringdown(
    f_hz: float,
    tau_s: float,
    *,
    slots: HqivScalingSlots | None = None,
    allow_mass_tail: bool = True,
) -> tuple[KerrMassInference, float, float]:
    """
    HQIV inference: unmap (f, τ) through horizon slots (+ HMNS mass-tail fixed point).
    """
    slots = slots or hqiv_horizon_slots()

    # GR inference on raw measurement (what a Kerr analyst reports).
    gr_on_raw = infer_kerr_mass_from_ringdown(f_hz, tau_s)
    remnant = remnant_class_for_mass(gr_on_raw.final_mass_msun)

    mass_tail = 0.0
    if allow_mass_tail and remnant == "HMNS_candidate":
        core = gr_on_raw.final_mass_msun
        for _ in range(12):
            mass_tail = hqiv_mass_tail_delta_msun(core)
            f_k, tau_k = hqiv_unmap_to_kerr_frequencies(
                f_hz, tau_s, slots, core_mass_msun=core, mass_tail_msun=mass_tail
            )
            core_new = infer_kerr_mass_from_ringdown(f_k, tau_k).final_mass_msun
            if abs(core_new - core) < 1e-4:
                core = core_new
                break
            core = core_new
        m_eff = core + mass_tail
    else:
        core = infer_kerr_mass_from_ringdown(
            *hqiv_unmap_to_kerr_frequencies(
                f_hz,
                tau_s,
                slots,
                core_mass_msun=gr_on_raw.final_mass_msun,
                mass_tail_msun=0.0,
            )
        ).final_mass_msun
        mass_tail = 0.0
        m_eff = core

    f_k, tau_k = hqiv_unmap_to_kerr_frequencies(
        f_hz, tau_s, slots, core_mass_msun=core, mass_tail_msun=mass_tail
    )
    hqiv_inf = infer_kerr_mass_from_ringdown(f_k, tau_k)
    return hqiv_inf, mass_tail, m_eff


def forward_hqiv_ringdown(
    true_mass_msun: float,
    final_spin: float,
    *,
    slots: HqivScalingSlots | None = None,
) -> RingdownMeasurement:
    """What a detector would measure if remnant mass/spin were HQIV truth."""
    slots = slots or hqiv_horizon_slots()
    om_r, om_i = kerr_220_dimensionless_omega(final_spin)
    f_gr = om_r * C_LIGHT**3 / (2.0 * math.pi * G_NEWTON * true_mass_msun * M_SUN_KG)
    tau_gr = G_NEWTON * true_mass_msun * M_SUN_KG / (abs(om_i) * C_LIGHT**3)

    remnant = remnant_class_for_mass(true_mass_msun)
    mass_tail = (
        hqiv_mass_tail_delta_msun(true_mass_msun) if remnant == "HMNS_candidate" else 0.0
    )
    m_eff = true_mass_msun + mass_tail
    mass_ratio = true_mass_msun / m_eff if m_eff > 0 else 1.0

    f_meas = f_gr * slots.freq_scale * mass_ratio
    tau_meas = tau_gr * slots.damp_scale_with_eta / mass_ratio
    return ringdown_measurement(f_meas, tau_meas)


def synthetic_ringdown_tail_waveform(
    t_s: float,
    t0_s: float,
    f_hz: float,
    tau_s: float,
    amplitude: float,
    tail_exponent: float,
    *,
    tail_start_factor: float = 3.0,
) -> float:
    if t_s < t0_s:
        return 0.0
    t_rel = t_s - t0_s
    ring = amplitude * math.exp(-t_rel / tau_s) * math.cos(2.0 * math.pi * f_hz * t_rel)
    tail_start = tail_start_factor * tau_s
    if t_rel <= tail_start:
        return ring
    tail_t = max(t_rel / tail_start, 1.0)
    ring_at_tail = amplitude * math.exp(-tail_start / tau_s)
    return ring_at_tail * tail_t ** (-tail_exponent)


def ascii_waveform_plot(
    meas: RingdownMeasurement,
    tail_exponent: float,
    *,
    duration_s: float = 0.05,
    n_cols: int = 60,
) -> str:
    lines = [
        "Ringdown + tail sketch from measured (f, τ)",
        f"f={meas.f_220_hz:.1f} Hz  τ={meas.tau_220_s*1000:.2f} ms  ν_tail={tail_exponent:.2f}",
        "",
    ]
    pts = [
        synthetic_ringdown_tail_waveform(
            duration_s * i / n_cols, 0.0, meas.f_220_hz, meas.tau_220_s, 1.0, tail_exponent
        )
        for i in range(n_cols + 1)
    ]
    max_abs = max(max(abs(x) for x in pts), 1e-12)
    height = 10
    for row in range(height, -1, -1):
        threshold = (row / height - 0.5) * 2.0 * max_abs
        lines.append("".join("#" if pts[i] >= threshold else " " for i in range(n_cols + 1)))
    lines.append("0 ms" + " " * (n_cols - 10) + f"{duration_s*1000:.0f} ms")
    return "\n".join(lines)


def fetch_gwtc_events(
    *,
    catalog: str = "GWTC-5.0",
    min_final_mass_msun: float = 5.0,
    max_events: int = 40,
) -> list[dict[str, object]]:
    try:
        with urllib.request.urlopen(GWOSC_GWTC_URL, timeout=30) as resp:
            payload = json.loads(resp.read().decode("utf-8"))
    except (urllib.error.URLError, TimeoutError, json.JSONDecodeError) as exc:
        return [{"_fetch_error": str(exc)}]

    rows: list[dict[str, object]] = []
    for _key, ev in payload.get("events", {}).items():
        if ev.get("catalog.shortName") != catalog:
            continue
        m_f = ev.get("final_mass_source")
        if m_f is None:
            continue
        m_f = float(m_f)
        if m_f < min_final_mass_msun:
            continue
        chi = ev.get("chi_eff")
        chi_f = float(chi) if chi is not None else None
        spin_proxy = max(0.0, min(0.99, chi_f if chi_f is not None else 0.0))
        rows.append(
            {
                "commonName": ev.get("commonName", _key),
                "catalog": catalog,
                "catalog_final_mass_msun": m_f,
                "chi_eff": chi_f,
                "final_spin_proxy": spin_proxy,
                "snr": ev.get("network_matched_filter_snr"),
            }
        )
    rows.sort(key=lambda r: float(r["catalog_final_mass_msun"]), reverse=True)
    return rows[:max_events]


def analyze_event_row(row: dict[str, object], slots: HqivScalingSlots) -> RingdownMassInferenceRow:
    name = str(row["commonName"])
    catalog = str(row.get("catalog", "GWTC"))
    notes = str(row.get("notes", ""))

    if row.get("f_220_hz") is not None:
        f_hz = float(row["f_220_hz"])
        tau_s = float(row.get("tau_220_s", row.get("tau_220_ms", 0.0) / 1000.0))
        source: Literal[
            "literature_ringdown",
            "user_cli",
            "pe_kerr_ringdown_from_pe_mass_spin",
            "pe_hdf5_posterior",
            "synthetic_from_catalog",
        ] = "literature_ringdown"
    elif row.get("pe_ringdown_f_hz") is not None:
        f_hz = float(row["pe_ringdown_f_hz"])
        tau_s = float(row["pe_ringdown_tau_s"])
        source = "pe_hdf5_posterior"
    else:
        m_cat = float(row.get("catalog_final_mass_msun", row.get("final_mass_source_msun", 0.0)))
        spin = float(row.get("final_spin_proxy", row.get("chi_eff") or 0.0))
        spin = max(0.0, min(0.99, spin))
        f_hz, tau_s = kerr_ringdown_from_mass_spin(m_cat, spin)
        if row.get("pe_result_label"):
            source = "pe_kerr_ringdown_from_pe_mass_spin"
            notes = str(row.get("notes", ""))
        else:
            source = "synthetic_from_catalog"
            notes = (str(row.get("notes", "")) + "; f,τ from catalog M_f Kerr map").strip("; ")

    meas = ringdown_measurement(f_hz, tau_s)
    gr_inf = infer_kerr_mass_from_ringdown(f_hz, tau_s)
    hqiv_inf, mass_tail, m_eff = infer_hqiv_mass_from_ringdown(f_hz, tau_s, slots=slots)

    m_cat_raw = row.get("catalog_final_mass_msun", row.get("final_mass_source_msun"))
    m_cat = float(m_cat_raw) if m_cat_raw is not None else None
    chi = row.get("chi_eff")
    chi_f = float(chi) if chi is not None else None

    remnant = remnant_class_for_mass(hqiv_inf.final_mass_msun)
    ratio_gr = gr_inf.final_mass_msun / m_cat if m_cat else None
    ratio_hqiv = hqiv_inf.final_mass_msun / m_cat if m_cat else None

    return RingdownMassInferenceRow(
        common_name=name,
        catalog=catalog,
        measurement=meas,
        gr_inference=gr_inf,
        hqiv_inference=hqiv_inf,
        hqiv_slots=slots,
        mass_tail_delta_msun=mass_tail,
        effective_mass_msun=m_eff,
        catalog_final_mass_msun=m_cat,
        chi_eff=chi_f,
        snr=float(row["snr"]) if row.get("snr") is not None else None,
        remnant_class=remnant,
        measurement_source=source,
        mass_ratio_gr_over_catalog=ratio_gr,
        mass_ratio_hqiv_over_catalog=ratio_hqiv,
        notes=notes,
    )


def ringdown_witness_bundle(
    *,
    catalog: str = "GWTC-5.0",
    max_events: int = 25,
    include_landmarks: bool = True,
    use_pe_summary: bool = True,
    pe_cache_dir: Path | None = None,
) -> dict[str, object]:
    from hqiv_gwtc_pe_loader import official_links, pe_summary_rows_for_catalog, write_pe_manifest

    slots = hqiv_horizon_slots()
    fetch_error = None
    catalog_rows: list[dict[str, object]] = []

    if use_pe_summary and catalog == "GWTC-5.0":
        try:
            catalog_rows = pe_summary_rows_for_catalog(
                cache_dir=pe_cache_dir,
                download=True,
                max_events=max_events,
            )
            write_pe_manifest(pe_cache_dir)
        except (OSError, RuntimeError, FileNotFoundError) as exc:
            fetch_error = f"PE summary: {exc}"
            catalog_rows = fetch_gwtc_events(catalog=catalog, max_events=max_events)
    else:
        catalog_rows = fetch_gwtc_events(catalog=catalog, max_events=max_events)
        if catalog_rows and "_fetch_error" in catalog_rows[0]:
            fetch_error = catalog_rows[0]["_fetch_error"]
            catalog_rows = []

    event_inputs: list[dict[str, object]] = []
    if include_landmarks:
        event_inputs.extend(LANDMARK_EVENTS)
    event_inputs.extend(catalog_rows)

    analyzed = [analyze_event_row(row, slots) for row in event_inputs]
    seen: set[str] = set()
    unique: list[RingdownMassInferenceRow] = []
    for row in analyzed:
        if row.common_name in seen:
            continue
        seen.add(row.common_name)
        unique.append(row)

    return {
        "lean_modules": [
            "Hqiv.Physics.GravitationalWaveRingdownScaffold",
            "Hqiv.Physics.CompactObjectRotatingCrustScaffold",
            "Hqiv.Physics.NuclearOutsideTemperatureDynamics",
        ],
        "python_module": "scripts/hqiv_gw_ringdown.py",
        "flow": "measured (f₂₂₀, τ₂₂₀) → inferred M_f (GR Kerr vs HQIV-unmapped Kerr)",
        "catalog_filter": catalog,
        "gwosc_url": GWOSC_GWTC_URL,
        "official_links": official_links(),
        "fetch_error": fetch_error,
        "hqiv_horizon_slots": asdict(slots),
        "lattice_constants": {
            "alpha": ALPHA,
            "gamma": GAMMA,
            "gr_tail_exponent": GR_TAIL_EXPONENT,
            "merger_hot_surface_T_K": MERGER_HOT_SURFACE_T_K,
        },
        "interpretation": {
            "detection_inputs": "f₂₂₀ (Hz) and τ₂₂₀ (s) — primary inputs to mass inference",
            "gwtc5_pe_summary": (
                "Zenodo PESummaryTable.hdf5 supplies M_f and a* medians; "
                "Kerr f,τ computed from those when ringdown PE not loaded"
            ),
            "gr_inference": "Kerr (2,2,0) inversion: spin from 2πfτ, mass from τ and f",
            "hqiv_inference": "unmap f,τ through horizon slots then same Kerr inversion",
            "mass_tail": "charmed-core ΔM for HMNS-class inferred masses only",
        },
        "event_count": len(unique),
        "events": [
            {
                "common_name": r.common_name,
                "catalog": r.catalog,
                "measurement": asdict(r.measurement),
                "measurement_source": r.measurement_source,
                "gr_inference": asdict(r.gr_inference),
                "hqiv_inference": asdict(r.hqiv_inference),
                "hqiv_slots": asdict(r.hqiv_slots),
                "mass_tail_delta_msun": r.mass_tail_delta_msun,
                "effective_mass_msun": r.effective_mass_msun,
                "catalog_final_mass_msun": r.catalog_final_mass_msun,
                "chi_eff": r.chi_eff,
                "snr": r.snr,
                "remnant_class": r.remnant_class,
                "mass_ratio_gr_over_catalog": r.mass_ratio_gr_over_catalog,
                "mass_ratio_hqiv_over_catalog": r.mass_ratio_hqiv_over_catalog,
                "notes": r.notes,
            }
            for r in unique
        ],
    }


def print_report(data: dict[str, object]) -> None:
    slots = data["hqiv_horizon_slots"]
    print("HQIV GW ringdown mass inference (f, τ → M_f)")
    print(f"  catalog: {data['catalog_filter']}  events: {data['event_count']}")
    if data.get("fetch_error"):
        print(f"  GWOSC fetch note: {data['fetch_error']}")
    print(
        f"  horizon ε={slots['horizon_epsilon']:.3f}  lapse={slots['horizon_lapse']:.3f}  "
        f"G_eff={slots['geff_modulator']:.4f}  f_unmap÷{slots['freq_scale']:.3f}  "
        f"τ_unmap÷{slots['damp_scale_with_eta']:.3f}"
    )
    print()
    print(
        f"{'Event':<22} {'f Hz':>6} {'τ ms':>6} {'M_GR':>7} {'M_HQIV':>7} "
        f"{'M_PE':>7} {'a*_GR':>6} src"
    )
    for ev in data["events"]:
        m = ev["measurement"]
        gr = ev["gr_inference"]
        hq = ev["hqiv_inference"]
        m_cat = ev.get("catalog_final_mass_msun")
        m_cat_s = f"{m_cat:7.1f}" if m_cat is not None else "     —"
        src = str(ev["measurement_source"])[:4]
        print(
            f"{ev['common_name']:<22} {m['f_220_hz']:6.1f} {m['tau_220_s']*1000:6.2f} "
            f"{gr['final_mass_msun']:7.1f} {hq['final_mass_msun']:7.1f} {m_cat_s} "
            f"{gr['final_spin']:6.2f} {src}"
        )


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Infer remnant mass from ringdown f₂₂₀ and τ₂₂₀ (GR vs HQIV)"
    )
    parser.add_argument("--catalog", default="GWTC-5.0")
    parser.add_argument("--max-events", type=int, default=25)
    parser.add_argument(
        "--pe-summary",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="use Zenodo PESummaryTable.hdf5 for GWTC-5.0 (default: on)",
    )
    parser.add_argument(
        "--pe-hdf5",
        type=Path,
        help="inspect one combined_PEDataRelease.hdf5",
    )
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--f", type=float, help="measured f₂₂₀ in Hz")
    parser.add_argument("--tau-ms", type=float, help="measured τ₂₂₀ in milliseconds")
    parser.add_argument("--waveform-ascii", action="store_true")
    args = parser.parse_args()

    if args.f is not None and args.tau_ms is not None:
        slots = hqiv_horizon_slots()
        f_hz = args.f
        tau_s = args.tau_ms / 1000.0
        gr = infer_kerr_mass_from_ringdown(f_hz, tau_s)
        hq, mass_tail, m_eff = infer_hqiv_mass_from_ringdown(f_hz, tau_s, slots=slots)
        meas = ringdown_measurement(f_hz, tau_s)
        print(f"Input: f={f_hz:.2f} Hz  τ={args.tau_ms:.3f} ms  (2πfτ={meas.omega_ratio:.4f})")
        print(f"GR inference:   M_f={gr.final_mass_msun:.2f} M☉  a*={gr.final_spin:.3f}")
        print(f"HQIV inference: M_f={hq.final_mass_msun:.2f} M☉  a*={hq.final_spin:.3f}")
        if mass_tail > 0:
            print(f"  HMNS mass tail ΔM={mass_tail:.3f} M☉  M_eff={m_eff:.2f} M☉")
        if args.waveform_ascii:
            print()
            print(ascii_waveform_plot(meas, slots.tail_exponent))
        return

    if args.pe_hdf5 is not None:
        from hqiv_gwtc_pe_loader import load_combined_pe_posterior_medians

        med = load_combined_pe_posterior_medians(args.pe_hdf5)
        print(json.dumps(med, indent=2))
        f_med = med.get("f_220_median")
        tau_med = med.get("tau_220_median")
        if f_med is not None and tau_med is not None:
            gr = infer_kerr_mass_from_ringdown(f_med, tau_med)
            hq, _, _ = infer_hqiv_mass_from_ringdown(f_med, tau_med)
            print(f"GR inference:   M_f={gr.final_mass_msun:.2f} M☉")
            print(f"HQIV inference: M_f={hq.final_mass_msun:.2f} M☉")
        return

    data = ringdown_witness_bundle(
        catalog=args.catalog,
        max_events=args.max_events,
        use_pe_summary=args.pe_summary,
    )
    if args.json:
        out = _ROOT / "data" / "gw_ringdown_witness.json"
        out.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
        print(f"Wrote {out}", file=sys.stderr)
    else:
        print_report(data)


if __name__ == "__main__":
    main()

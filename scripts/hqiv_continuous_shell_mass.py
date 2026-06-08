#!/usr/bin/env python3
"""
Continuous-ξ shell-chart mass calculators for HQIV trapped-Planck readouts.

The null carrier is not assumed to sit exactly on integer shell labels. Integer
`m` values are readout samples, while ξ = m + 1 is the continuous motion chart
used to evaluate phase offsets and smearing between samples.
Lean anchors:
  • curvatureDensity, continuousCurvaturePrimitive — OctonionicLightCone / ContinuousXiCoupling
  • metaHorizonTrappedInsideRatio — MetaHorizonTrappedPlanckMass.lean
  • metaHorizonTrappedPlanckMassPhaseReadout — MetaHorizonContinuousShellMass.lean
  • xiOfShell, ContinuousXiPath chart bridges

Readout modes:
  discrete   — integer m = referenceM + n + ℓ (existing hqiv_excited_states)
  interp     — linear interpolation of discrete inside ratio between integer m
  primitive  — analytic K(ξ) volume + ∫ 4 dξ trapped budget (slice = 4 for ξ ≥ 1)
  split      — ξ_eff = ξ_lock + Δξ_rad(n) + Δξ_orb(ℓ) via trapped-curve inversion
  smeared    — Gaussian weights on neighboring integer shells around ξ_eff

Run:
  python3 scripts/hqiv_continuous_shell_mass.py
  python3 scripts/hqiv_continuous_shell_mass.py --json
  python3 scripts/hqiv_continuous_shell_mass.py --mode split --pdg
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import asdict, dataclass
from enum import Enum
from pathlib import Path
from typing import Literal

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(_ROOT / "scripts"))

import hqiv_excited_states as hes  # noqa: E402

ALPHA = hes.ALPHA
REFERENCE_M = hes.REFERENCE_M
XI_LOCK = float(REFERENCE_M + 1)
PROTON_MEV = 938.27208816

PDG_MEV = {
    "proton": PROTON_MEV,
    "Delta(1232)": 1232.0,
    "N(1520)": 1515.0,
    "N(1440)": 1440.0,
    "N(1535)": 1535.0,
    "rho": 775.26,
    "omega": 782.65,
}


class ContinuousReadout(str, Enum):
    DISCRETE = "discrete"
    INTERP = "interp"
    PRIMITIVE = "primitive"
    SPLIT = "split"
    SMEARED = "smeared"
    PHASE = "phase"


def xi_from_m(m: float) -> float:
    return m + 1.0


def m_from_xi(xi: float) -> float:
    return xi - 1.0


def curvature_density(xi: float) -> float:
    if xi <= 0.0:
        return float("nan")
    return (1.0 / xi) * (1.0 + ALPHA * math.log(xi))


def curvature_primitive(xi: float) -> float:
    """Lean `continuousCurvaturePrimitive ξ`."""
    if xi <= 0.0:
        return float("nan")
    lx = math.log(xi)
    return lx + (ALPHA / 2.0) * lx * lx


def trapped_planck_slice_at_xi(xi: float) -> float:
    """
    Continuous extension of `shellModeMultiplicity m * shellOmega m / 2`.

    For integer shells m ≥ 0 this equals 4; the extension keeps N(ξ)·ω(ξ)/2 smooth in ξ.
    """
    if xi < 1.0:
        return float("nan")
    m = m_from_xi(xi)
    nm = 8.0 if m <= 0.0 else 8.0 * (m + 1.0)
    return nm / (2.0 * xi)


def trapped_budget_continuous(xi: float, *, steps: int = 4000) -> float:
    """Riemann ∫_1^ξ N(ξ')ω(ξ')/2 dξ'."""
    if xi <= 1.0:
        return 0.0
    a, b = 1.0, xi
    h = (b - a) / steps
    total = 0.0
    for i in range(steps):
        x0 = a + i * h
        x1 = x0 + h
        total += 0.5 * h * (trapped_planck_slice_at_xi(x0) + trapped_planck_slice_at_xi(x1))
    return total


def inside_ratio_discrete(m_exc: float, m_ref: float = float(REFERENCE_M)) -> float:
    m_lo = int(math.floor(m_exc))
    m_hi = m_lo + 1
    if m_exc == m_lo:
        return hes.meta_horizon_trapped_inside_ratio(m_lo, int(m_ref))
    t = m_exc - m_lo
    r_lo = hes.meta_horizon_trapped_inside_ratio(m_lo, int(m_ref))
    r_hi = hes.meta_horizon_trapped_inside_ratio(m_hi, int(m_ref))
    return (1.0 - t) * r_lo + t * r_hi


def xi_ref_from_chart_shell(chart_shell: int) -> float:
    """Continuous ξ anchor for a Beltrami chart row `m = chart_shell`."""
    return xi_from_m(float(chart_shell))


def trapped_mass_at_chart(
    xi_exc: float,
    *,
    ground_mev: float,
    chart_shell: int,
    mode: ContinuousReadout = ContinuousReadout.INTERP,
) -> float:
    """Trapped readout on an arbitrary TUFT chart: `g · R_in(m(ξ), m_ref)`."""
    xi_ref = xi_ref_from_chart_shell(chart_shell)
    if abs(xi_exc - xi_ref) < 1e-12:
        return ground_mev
    if mode != ContinuousReadout.INTERP:
        raise ValueError("trapped_mass_at_chart supports INTERP only")
    r = inside_ratio_discrete(m_from_xi(xi_exc), float(chart_shell))
    return ground_mev * r


def invert_delta_m_to_delta_xi_chart(
    delta_m_mev: float,
    *,
    ground_mev: float,
    chart_shell: int,
    mode: ContinuousReadout = ContinuousReadout.INTERP,
    xi_hi_offset: float = 4.0,
) -> float:
    """Invert Beltrami/trapped ΔM on the chart trapped curve (returns Δξ above chart ground)."""
    xi_ref = xi_ref_from_chart_shell(chart_shell)
    target = ground_mev + delta_m_mev
    lo, hi = xi_ref, xi_ref + xi_hi_offset
    if trapped_mass_at_chart(lo, ground_mev=ground_mev, chart_shell=chart_shell, mode=mode) > target:
        lo = xi_ref - 0.5
    if trapped_mass_at_chart(hi, ground_mev=ground_mev, chart_shell=chart_shell, mode=mode) < target:
        hi = xi_ref + 8.0
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        if trapped_mass_at_chart(mid, ground_mev=ground_mev, chart_shell=chart_shell, mode=mode) < target:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi) - xi_ref


def trapped_inside_ratio_slope_at_chart(chart_shell: int) -> float:
    """Local slope ∂R/∂m at chart ground: R(m_ref+1, m_ref) − 1."""
    import hqiv_excited_states as hes

    return hes.meta_horizon_trapped_inside_ratio(chart_shell + 1, chart_shell) - 1.0


def beltrami_delta_to_xi_offset(
    delta_m_mev: float,
    *,
    ground_mev: float,
    chart_shell: int,
) -> float:
    """
    First-order Beltrami → ξ offset on the trapped curve.

    M(ξ) ≈ g · R_in(ξ−1, m_ref) ⇒ ΔM ≈ g · (∂R/∂m) · Δξ at the chart ground.
    Matches bisection inversion in `effective_xi_split_on_chart` at all tested ξ.
    """
    if delta_m_mev <= 0.0:
        return 0.0
    slope = trapped_inside_ratio_slope_at_chart(chart_shell)
    return delta_m_mev / (ground_mev * slope)


def effective_xi_split_on_chart(
    n: int,
    ell: int,
    *,
    chart_shell: int,
    ground_mev: float,
    radial_delta_mev: float,
    orbital_delta_mev: float,
    trapped_to_increment_scale: float = 1.0,
    mode: ContinuousReadout = ContinuousReadout.INTERP,
) -> float:
    """
    ξ_eff = ξ_chart + Δξ_rad(n) + Δξ_orb(ℓ) via trapped-curve first-order inversion.

    Radial and orbital Beltrami increments are inverted separately — breaks n vs ℓ
    degeneracy at fixed n+ℓ.  `mode` is retained for API compatibility (INTERP only).
    """
    del mode  # first-order closed form; bisection equivalent
    xi_ref = xi_ref_from_chart_shell(chart_shell)
    if n == 0 and ell == 0:
        return xi_ref
    scale = trapped_to_increment_scale
    dxi = 0.0
    if n:
        dxi += beltrami_delta_to_xi_offset(
            scale * radial_delta_mev, ground_mev=ground_mev, chart_shell=chart_shell
        )
    if ell:
        dxi += beltrami_delta_to_xi_offset(
            scale * orbital_delta_mev, ground_mev=ground_mev, chart_shell=chart_shell
        )
    return xi_ref + dxi


def inside_ratio_primitive(xi_exc: float, xi_ref: float = XI_LOCK) -> float:
    vol = curvature_primitive(xi_exc) / curvature_primitive(xi_ref)
    bud = trapped_budget_continuous(xi_exc) / trapped_budget_continuous(xi_ref)
    return vol * bud


def inside_ratio_at_xi(
    xi_exc: float,
    *,
    xi_ref: float = XI_LOCK,
    mode: ContinuousReadout = ContinuousReadout.INTERP,
    smear_width: float = 0.35,
) -> float:
    if abs(xi_exc - xi_ref) < 1e-12:
        return 1.0
    if mode == ContinuousReadout.DISCRETE:
        m = round(m_from_xi(xi_exc))
        return hes.meta_horizon_trapped_inside_ratio(m, REFERENCE_M)
    if mode == ContinuousReadout.INTERP:
        return inside_ratio_discrete(m_from_xi(xi_exc), float(REFERENCE_M))
    if mode == ContinuousReadout.PRIMITIVE:
        return inside_ratio_primitive(xi_exc, xi_ref)
    if mode == ContinuousReadout.SMEARED:
        return _inside_ratio_smeared(xi_exc, xi_ref=xi_ref, width=smear_width)
    if mode == ContinuousReadout.PHASE:
        raise ValueError("inside_ratio_at_xi: use effective_m_phase + INTERP instead")
    raise ValueError(f"inside_ratio_at_xi does not support mode={mode!r}")


def _inside_ratio_smeared(xi_center: float, *, xi_ref: float, width: float) -> float:
    m_center = m_from_xi(xi_center)
    m_lo = max(0, int(math.floor(m_center)) - 2)
    m_hi = int(math.ceil(m_center)) + 2
    weights: list[float] = []
    ratios: list[float] = []
    for m in range(m_lo, m_hi + 1):
        xi = xi_from_m(float(m))
        w = math.exp(-0.5 * ((xi - xi_center) / width) ** 2)
        weights.append(w)
        ratios.append(hes.meta_horizon_trapped_inside_ratio(m, REFERENCE_M))
    s = sum(weights)
    return sum(w * r for w, r in zip(weights, ratios)) / s


def trapped_mass_at_xi(
    xi_exc: float,
    *,
    derived_proton_mev: float = PROTON_MEV,
    xi_ref: float = XI_LOCK,
    mode: ContinuousReadout = ContinuousReadout.INTERP,
    smear_width: float = 0.35,
) -> float:
    ratio = inside_ratio_at_xi(
        xi_exc, xi_ref=xi_ref, mode=mode, smear_width=smear_width
    )
    return derived_proton_mev * ratio


def phase_deficit_m(n: int, ell: int, *, chart_shell: int | None = None) -> float:
    """
    Fractional shell pull-back from incomplete Compton closure on the null lattice.

    Each excitation quantum borrows 1/(4ξ) of a shell (quarter-turn / 2π budget at ξ)
    as the carrier moves between discrete null points rather than sitting on one.

    `chart_shell`: Beltrami chart ground row (default HQIV `REFERENCE_M`; use
    `TUFT_HEAVY_CHART_SHELL` for TUFT hadron readouts).
    """
    base = REFERENCE_M if chart_shell is None else chart_shell
    exc = n + ell
    if exc == 0:
        return 0.0
    total = 0.0
    for j in range(1, exc + 1):
        xi_j = xi_from_m(float(base + j))
        total += 1.0 / (4.0 * xi_j)
    return total


def effective_m_phase(n: int, ell: int, *, chart_shell: int | None = None) -> float:
    """Continuous m coordinate with Compton phase deficit."""
    if chart_shell is None:
        m_total = hes.total_mode_shell(n, ell)
    else:
        m_total = chart_shell + n + ell
    return float(m_total) - phase_deficit_m(n, ell, chart_shell=chart_shell)


def invert_delta_m_to_delta_xi(
    delta_m_mev: float,
    *,
    derived_proton_mev: float = PROTON_MEV,
    mode: ContinuousReadout = ContinuousReadout.INTERP,
    xi_lo: float = XI_LOCK,
    xi_hi: float = XI_LOCK + 4.0,
) -> float:
    """Find Δξ such that trapped_mass(ξ_lock + Δξ) − m_p = delta_m_mev."""
    target = derived_proton_mev + delta_m_mev
    lo, hi = xi_lo, xi_hi
    if trapped_mass_at_xi(lo, derived_proton_mev=derived_proton_mev, mode=mode) > target:
        lo = XI_LOCK - 0.5
    if trapped_mass_at_xi(hi, derived_proton_mev=derived_proton_mev, mode=mode) < target:
        hi = XI_LOCK + 8.0
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        if trapped_mass_at_xi(mid, derived_proton_mev=derived_proton_mev, mode=mode) < target:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi) - XI_LOCK


def trapped_channel_delta_mev(
    n: int,
    ell: int,
    *,
    derived_proton_mev: float = PROTON_MEV,
) -> float:
    """Total trapped-Planck ΔM above ground for tagged channel (n, ℓ)."""
    return (
        trapped_mass_at_xi(
            xi_from_m(float(hes.total_mode_shell(n, ell))),
            derived_proton_mev=derived_proton_mev,
            mode=ContinuousReadout.INTERP,
        )
        - derived_proton_mev
    )


def _trapped_to_surface_scale() -> float:
    """Trapped excess / operational radial at (n=1, ℓ=0) — geometry bridge, not PDG fit."""
    trapped_d = trapped_channel_delta_mev(1, 0)
    rad_op = hes.delta_m_radial_operational_mev(1, derived_proton_mev=PROTON_MEV)
    if rad_op <= 0.0:
        return 1.0
    return trapped_d / rad_op


def _mode_trapped_delta_mev(n: int, ell: int) -> float:
    """Trapped-native ΔM attributed to radial (n) or orbital (ℓ) mode alone."""
    scale = _trapped_to_surface_scale()
    dr = hes.delta_m_radial_operational_mev(n, derived_proton_mev=PROTON_MEV) if n else 0.0
    do = hes.delta_m_orbital_operational_mev(ell, derived_proton_mev=PROTON_MEV) if ell else 0.0
    return scale * (dr + do)


def effective_xi_split(
    n: int | float,
    ell: int | float,
    *,
    derived_proton_mev: float = PROTON_MEV,
    mode: ContinuousReadout = ContinuousReadout.INTERP,
) -> float:
    """
    ξ_eff = ξ_lock + Δξ_rad(n) + Δξ_orb(ℓ).

    Radial and orbital operational increments are scaled to trapped-native units,
    then inverted separately on the continuous trapped curve.
    """
    ni, ei = int(n), int(ell)
    if ni == 0 and ei == 0:
        return XI_LOCK

    scale = _trapped_to_surface_scale()
    dxi = 0.0
    if ni:
        dm_r = scale * hes.delta_m_radial_operational_mev(ni, derived_proton_mev=derived_proton_mev)
        dxi += invert_delta_m_to_delta_xi(
            dm_r, derived_proton_mev=derived_proton_mev, mode=mode
        )
    if ei:
        dm_o = scale * hes.delta_m_orbital_operational_mev(ei, derived_proton_mev=derived_proton_mev)
        dxi += invert_delta_m_to_delta_xi(
            dm_o, derived_proton_mev=derived_proton_mev, mode=mode
        )
    return XI_LOCK + dxi


def effective_xi_for_channel(
    n: int,
    ell: int,
    *,
    mode: ContinuousReadout,
    derived_proton_mev: float = PROTON_MEV,
) -> float:
    if mode == ContinuousReadout.DISCRETE:
        return xi_from_m(float(hes.total_mode_shell(n, ell)))
    if mode == ContinuousReadout.SPLIT:
        return effective_xi_split(n, ell, derived_proton_mev=derived_proton_mev, mode=ContinuousReadout.INTERP)
    if mode == ContinuousReadout.PHASE:
        return xi_from_m(effective_m_phase(n, ell))
    if mode in (ContinuousReadout.INTERP, ContinuousReadout.PRIMITIVE, ContinuousReadout.SMEARED):
        return xi_from_m(float(hes.total_mode_shell(n, ell)))
    raise ValueError(f"unknown mode {mode!r}")


def trapped_mass_continuous(
    n: int,
    ell: int,
    *,
    derived_proton_mev: float = PROTON_MEV,
    mode: ContinuousReadout = ContinuousReadout.INTERP,
    smear_width: float = 0.35,
) -> float:
    if mode == ContinuousReadout.DISCRETE:
        return hes.meta_horizon_trapped_planck_mass_mev(
            n, ell, derived_proton_mev=derived_proton_mev
        )
    if mode == ContinuousReadout.SPLIT:
        xi = effective_xi_split(n, ell, derived_proton_mev=derived_proton_mev)
        return trapped_mass_at_xi(
            xi, derived_proton_mev=derived_proton_mev, mode=ContinuousReadout.INTERP
        )
    if mode == ContinuousReadout.PHASE:
        m_eff = effective_m_phase(n, ell)
        return derived_proton_mev * inside_ratio_discrete(m_eff, float(REFERENCE_M))
    xi = xi_from_m(float(hes.total_mode_shell(n, ell)))
    return trapped_mass_at_xi(
        xi,
        derived_proton_mev=derived_proton_mev,
        mode=mode,
        smear_width=smear_width,
    )


@dataclass(frozen=True)
class MassRow:
    label: str
    n: int
    ell: int
    mode: str
    m_eff: float
    xi_eff: float
    mass_mev: float
    pdg_mev: float | None
    ratio_pdg: float | None
    err_pct: float | None


def _err_pct(mass: float, pdg: float | None) -> float | None:
    if pdg is None or pdg <= 0.0:
        return None
    return 100.0 * (mass / pdg - 1.0)


def comparison_rows(
    *,
    derived_proton_mev: float = PROTON_MEV,
    n_max: int = 2,
    ell_max: int = 1,
    modes: list[ContinuousReadout] | None = None,
    pdg_tags: dict[tuple[int, int], str] | None = None,
) -> list[MassRow]:
    if modes is None:
        modes = [
            ContinuousReadout.DISCRETE,
            ContinuousReadout.INTERP,
            ContinuousReadout.PHASE,
            ContinuousReadout.SPLIT,
        ]
    if pdg_tags is None:
        pdg_tags = {
            (0, 0): "proton",
            (1, 0): "Delta(1232)",
            (0, 1): "rho",
            (2, 0): "N(1520)",
        }
    rows: list[MassRow] = []
    for n in range(n_max + 1):
        for ell in range(ell_max + 1):
            pdg_key = pdg_tags.get((n, ell))
            pdg = PDG_MEV.get(pdg_key) if pdg_key else None
            for mode in modes:
                mass = trapped_mass_continuous(
                    n, ell, derived_proton_mev=derived_proton_mev, mode=mode
                )
                if mode == ContinuousReadout.SPLIT:
                    xi = effective_xi_split(n, ell, derived_proton_mev=derived_proton_mev)
                elif mode == ContinuousReadout.PHASE:
                    m_eff = effective_m_phase(n, ell)
                    xi = xi_from_m(m_eff)
                else:
                    xi = effective_xi_for_channel(
                        n, ell, mode=mode, derived_proton_mev=derived_proton_mev
                    )
                m_eff = m_from_xi(xi) if mode != ContinuousReadout.PHASE else effective_m_phase(n, ell)
                rows.append(
                    MassRow(
                        label=pdg_key or f"(n={n},ℓ={ell})",
                        n=n,
                        ell=ell,
                        mode=mode.value,
                        m_eff=m_eff,
                        xi_eff=xi,
                        mass_mev=mass,
                        pdg_mev=pdg,
                        ratio_pdg=(mass / pdg if pdg else None),
                        err_pct=_err_pct(mass, pdg),
                    )
                )
    return rows


def print_comparison_table(rows: list[MassRow]) -> None:
    print()
    print(
        f"Continuous shell mass readouts (m_p = {PROTON_MEV:.4f} MeV, "
        f"referenceM = {REFERENCE_M}, ξ_lock = {XI_LOCK:.1f})"
    )
    print(
        f"  {'tag':<12} {'n':>2} {'ℓ':>2} {'mode':<10} {'m_eff':>7} {'ξ_eff':>7} "
        f"{'M [MeV]':>10} {'PDG':>10} {'err%':>8}"
    )
    print("  " + "-" * 78)
    for r in rows:
        pdg_s = f"{r.pdg_mev:10.2f}" if r.pdg_mev is not None else f"{'—':>10}"
        err_s = f"{r.err_pct:+7.2f}" if r.err_pct is not None else f"{'—':>8}"
        print(
            f"  {r.label:<12} {r.n:2d} {r.ell:2d} {r.mode:<10} "
            f"{r.m_eff:7.3f} {r.xi_eff:7.3f} {r.mass_mev:10.2f} {pdg_s} {err_s}"
        )


def print_mode_legend() -> None:
    print()
    print("Readout modes:")
    print("  discrete   — integer m = referenceM + n + ℓ")
    print("  interp     — linear interp of discrete trapped inside ratio in m")
    print("  primitive  — K(ξ) curvature primitive + Riemann trapped budget")
    print("  split      — ξ_lock + inverted Δξ from radial/orbital trapped-native ΔM")
    print("  phase      — m_eff = m_int − Σ 1/(4ξ_j) Compton quarter-leak per excitation")
    print("  smeared    — Gaussian average of integer-shell ratios around ξ_eff")


def main() -> None:
    p = argparse.ArgumentParser(description="HQIV continuous-ξ shell mass calculator")
    p.add_argument("--json", action="store_true", help="emit JSON rows")
    p.add_argument("--pdg", action="store_true", help="PDG-tagged channels only")
    p.add_argument(
        "--mode",
        choices=[m.value for m in ContinuousReadout],
        action="append",
        help="readout mode(s); default: discrete, interp, primitive, split",
    )
    p.add_argument("--n-max", type=int, default=2)
    p.add_argument("--ell-max", type=int, default=1)
    p.add_argument("--smear-width", type=float, default=0.35)
    p.add_argument(
        "--scan",
        type=str,
        metavar="n,ell",
        help="scan fractional m_eff and print mass curve (e.g. 1,0)",
    )
    p.add_argument("--proton-mev", type=float, default=PROTON_MEV)
    args = p.parse_args()

    if args.scan:
        n_s, ell_s = (int(x.strip()) for x in args.scan.split(","))
        print(f"\nMass scan for channel (n={n_s}, ℓ={ell_s}) — interp readout vs fractional m:")
        m_tag = float(hes.total_mode_shell(n_s, ell_s))
        print(f"  {'m_eff':>8} {'ξ':>8} {'M [MeV]':>10}")
        for dm in [i * 0.05 for i in range(-4, 5)]:
            m_eff = m_tag + dm
            mass = args.proton_mev * inside_ratio_discrete(m_eff, float(REFERENCE_M))
            mark = " ← tag" if abs(dm) < 1e-9 else ""
            print(f"  {m_eff:8.3f} {xi_from_m(m_eff):8.3f} {mass:10.2f}{mark}")
        m_phase = effective_m_phase(n_s, ell_s)
        mass_phase = trapped_mass_continuous(
            n_s, ell_s, derived_proton_mev=args.proton_mev, mode=ContinuousReadout.PHASE
        )
        print(f"  phase m_eff={m_phase:.4f} → {mass_phase:.2f} MeV")
        return

    modes = [ContinuousReadout(m) for m in args.mode] if args.mode else None
    pdg_tags = (
        {(0, 0): "proton", (1, 0): "Delta(1232)", (0, 1): "rho", (2, 0): "N(1520)"}
        if args.pdg
        else None
    )
    rows = comparison_rows(
        derived_proton_mev=args.proton_mev,
        n_max=args.n_max,
        ell_max=args.ell_max,
        modes=modes,
        pdg_tags=pdg_tags,
    )

    if args.json:
        print(json.dumps([asdict(r) for r in rows], indent=2))
        return

    print_mode_legend()
    print_comparison_table(rows)


if __name__ == "__main__":
    main()

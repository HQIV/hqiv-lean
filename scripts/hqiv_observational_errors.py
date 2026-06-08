#!/usr/bin/env python3
"""Observational uncertainty helpers for HQIV orbital comparisons."""

from __future__ import annotations

import math
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from hqiv_wide_binary_catalog import ChaeWideBinaryEntry

# Anderson / ESA Earth-flyby tracking uncertainties (mm/s at infinity).
FLYBY_LITERATURE_SIGMA_MM_S: dict[str, float] = {
    "galileo_1990": 0.08,
    "near_1998": 0.13,
    "cassini_1999": 3.0,
    "rosetta_2005": 0.05,
    "messenger_2005": 0.01,
    "rosetta_2007": 0.05,
    "rosetta_2009": 0.05,
    "juno_2013": 0.8,
}


def flyby_literature_sigma_mm_s(case_id: str, *, fallback: float = 2.0) -> float:
    return float(FLYBY_LITERATURE_SIGMA_MM_S.get(case_id, fallback))


def gamma_from_chae_gamma(chae_gamma: float | None) -> float | None:
    if chae_gamma is None:
        return None
    return 10.0 ** (2.0 * float(chae_gamma))


def gamma_chae_interval(entry: ChaeWideBinaryEntry) -> dict[str, float | None]:
    """
    Map Chae MCMC Γ = log10(sqrt(γ)) posteriors to γ intervals.

    ``Gamma_err_lower/upper`` are offsets on Γ (same units as the catalog CSV).
    """
    if entry.gamma_chae is None:
        return {
            "gamma": None,
            "gamma_lo": None,
            "gamma_hi": None,
            "Gamma": None,
            "Gamma_lo": None,
            "Gamma_hi": None,
            "sigma_gamma_log10": None,
        }
    gamma = gamma_from_chae_gamma(entry.gamma_chae)
    g_lo = g_hi = None
    if entry.gamma_chae_err_lo is not None:
        g_lo = gamma_from_chae_gamma(entry.gamma_chae - entry.gamma_chae_err_lo)
    if entry.gamma_chae_err_hi is not None:
        g_hi = gamma_from_chae_gamma(entry.gamma_chae + entry.gamma_chae_err_hi)
    if g_lo is not None and g_hi is not None and gamma is not None and gamma > 0.0:
        sigma_log = 0.5 * (math.log10(g_hi) - math.log10(g_lo))
    else:
        sigma_log = None
    return {
        "gamma": gamma,
        "gamma_lo": g_lo,
        "gamma_hi": g_hi,
        "Gamma": entry.gamma_chae,
        "Gamma_lo": (entry.gamma_chae - entry.gamma_chae_err_lo)
        if entry.gamma_chae_err_lo is not None
        else None,
        "Gamma_hi": (entry.gamma_chae + entry.gamma_chae_err_hi)
        if entry.gamma_chae_err_hi is not None
        else None,
        "sigma_gamma_log10": sigma_log,
    }


def percentile(values: list[float], q: float) -> float:
    if not values:
        return float("nan")
    xs = sorted(values)
    pos = (len(xs) - 1) * q
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return xs[lo]
    return xs[lo] * (hi - pos) + xs[hi] * (pos - lo)


def distribution_summary(values: list[float]) -> dict[str, float | None]:
    """Median and 16–84% spread (same spirit as 1σ for ranked samples)."""
    clean = [float(v) for v in values if math.isfinite(float(v))]
    if not clean:
        return {
            "median": None,
            "mean": None,
            "lo68": None,
            "hi68": None,
            "min": None,
            "max": None,
        }
    return {
        "median": percentile(clean, 0.5),
        "mean": sum(clean) / len(clean),
        "lo68": percentile(clean, 0.16),
        "hi68": percentile(clean, 0.84),
        "min": min(clean),
        "max": max(clean),
    }


def hqiv_falsifies_chae_gamma(
    *,
    gamma_hqiv_lo: float,
    gamma_hqiv_hi: float,
    gamma_chae: float | None,
    gamma_chae_lo: float | None,
    gamma_chae_hi: float | None,
    high_boost_threshold: float = 1.1,
) -> dict[str, object]:
    """
    Check whether the HQIV envelope sits inside/outside the Chae MCMC band.

    ``falsified`` applies when Chae's 68% lower bound exceeds ``high_boost_threshold``
    and the entire HQIV envelope (including spin sweep) stays below that bound.
    """
    if gamma_chae is None:
        return {"status": "no_chae_gamma", "separation_log10_gamma": None}
    chae_lo = gamma_chae_lo if gamma_chae_lo is not None else gamma_chae
    chae_hi = gamma_chae_hi if gamma_chae_hi is not None else gamma_chae
    sep = math.log10(max(chae_lo, 1.0e-30)) - math.log10(max(gamma_hqiv_hi, 1.0e-30))
    claims_high = chae_lo >= high_boost_threshold
    falsified = claims_high and gamma_hqiv_hi < chae_lo
    return {
        "status": "falsified" if falsified else ("chae_not_claiming_high_boost" if not claims_high else "inside_or_overlaps"),
        "claims_high_boost": claims_high,
        "high_boost_threshold": high_boost_threshold,
        "hqiv_envelope_inside_chae_68": gamma_hqiv_hi <= chae_hi and gamma_hqiv_lo >= chae_lo,
        "hqiv_max_below_chae_lo": gamma_hqiv_hi < chae_lo,
        "separation_log10_gamma": sep,
        "hqiv_ppm_max": (gamma_hqiv_hi - 1.0) * 1.0e6,
        "chae_central_ppm": (gamma_chae - 1.0) * 1.0e6,
    }

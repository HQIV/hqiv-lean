#!/usr/bin/env python3
"""
TUFT shell chart ontology — mirrors `Hqiv/Physics/TuftShellChart.lean`.

Use TUFT chart shells for hadron / Beltrami spectroscopy.
Use HQIV `REFERENCE_M` only for cosmology, CMB, and legacy export witnesses.
"""

from __future__ import annotations

import hqiv_excited_states as hes

# HQIV lock-in (substrate pin) — not the primary hadron index name
REFERENCE_M = hes.REFERENCE_M

# TUFT Hopf windings
TUFT_WEAK_HOPF_WINDING = 1
TUFT_STRONG_HOPF_WINDING = 2
TUFT_HEAVY_HOPF_WINDING = 3

# TUFT Beltrami chart rows m = winding + 1
TUFT_WEAK_CHART_SHELL = TUFT_WEAK_HOPF_WINDING + 1
TUFT_STRONG_CHART_SHELL = TUFT_STRONG_HOPF_WINDING + 1
TUFT_HEAVY_CHART_SHELL = TUFT_HEAVY_HOPF_WINDING + 1

# Legacy aliases
TUFT_WEAK_HOPF_SHELL_INDEX = TUFT_WEAK_HOPF_WINDING
TUFT_STRONG_HOPF_SHELL_INDEX = TUFT_STRONG_HOPF_WINDING
HADRON_IJK_SORTED_TRIPLE_BUDGET = 9


def tuft_hadron_radial_shell(n: int) -> int:
    """Lean `tuftHadronRadialShell`."""
    return TUFT_HEAVY_CHART_SHELL + n


def tuft_hadron_orbital_shell(ell: int) -> int:
    """Lean `tuftHadronOrbitalShell`."""
    return TUFT_HEAVY_CHART_SHELL + ell


def tuft_hadron_mode_shell(n: int, ell: int) -> int:
    """Lean `tuftHadronModeShell` — canonical baryon excitation channel tag."""
    return TUFT_HEAVY_CHART_SHELL + n + ell


def tuft_hadron_xi_of_mode_shell(n: int, ell: int) -> float:
    """Continuous horizon coordinate ξ = m + 1 on the heavy TUFT chart."""
    return float(tuft_hadron_mode_shell(n, ell) + 1)


def reference_m_eq_tuft_heavy_chart_numeric() -> bool:
    """Lean `referenceM_eq_tuftHeavyChartShell_numeric` (today's pins)."""
    return REFERENCE_M == TUFT_HEAVY_CHART_SHELL


def tuft_meson_radial_shell(n: int) -> int:
    """Lean `tuftMesonRadialShell`."""
    return TUFT_STRONG_CHART_SHELL + n


def tuft_meson_orbital_shell(ell: int) -> int:
    """Lean `tuftMesonOrbitalShell`."""
    return TUFT_STRONG_CHART_SHELL + ell


def tuft_meson_mode_shell(n: int, ell: int) -> int:
    """Lean `tuftMesonModeShell` — canonical meson excitation channel tag."""
    return TUFT_STRONG_CHART_SHELL + n + ell


def tuft_meson_xi_of_mode_shell(n: int, ell: int) -> float:
    """Continuous horizon coordinate ξ = m + 1 on the strong TUFT chart."""
    return float(tuft_meson_mode_shell(n, ell) + 1)

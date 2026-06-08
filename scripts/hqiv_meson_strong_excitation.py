#!/usr/bin/env python3
"""
Strong-chart meson excitations — delegates to `hqiv_tuft_global_hadron_readout`.

All production readouts use `tuft_excited_mass_global_at_xi_mev`.
"""

from __future__ import annotations

import hqiv_meson_flavor_content as mfc
import hqiv_tuft_global_hadron_readout as tgh
import hqiv_tuft_shell_chart as tsc

TUFT_STRONG_CHART_SHELL = tsc.TUFT_STRONG_CHART_SHELL
MESON_EXCITED_GRID = mfc.MESON_EXCITED_GRID
TuftExcitationChannel = tgh.TuftExcitationChannel


def _meson_channel(n: int, ell: int, n_strange: int = 0) -> tgh.TuftExcitationChannel:
    return tgh.TuftExcitationChannel.meson(n, ell, n_strange)


def tuft_meson_excited_mass_at_xi_mev(xi: float, n: int, ell: int) -> float:
    return tgh.tuft_excited_mass_global_at_xi_mev(xi, _meson_channel(n, ell))


def tuft_meson_excited_mass_flavor_beltrami_at_xi_mev(
    xi: float, n: int, ell: int, n_strange: int
) -> float:
    return tgh.tuft_excited_mass_global_at_xi_mev(xi, _meson_channel(n, ell, n_strange))


def tuft_meson_excited_mass_unified_inside_at_xi_mev(xi: float, n: int, ell: int) -> float:
    return tgh.tuft_excited_mass_global_at_xi_mev(xi, _meson_channel(n, ell))


def tuft_meson_excited_mass_unified_split_flavor_at_xi_mev(
    xi: float, n: int, ell: int, n_strange: int
) -> float:
    return tgh.tuft_excited_mass_global_at_xi_mev(xi, _meson_channel(n, ell, n_strange))


def tuft_meson_excited_mass_unified_inside_flavor_at_xi_mev(
    xi: float, n: int, ell: int, n_strange: int
) -> float:
    return tgh.tuft_excited_mass_global_at_xi_mev(xi, _meson_channel(n, ell, n_strange))


def tuft_meson_excited_mass_unified_split_at_xi_mev(xi: float, n: int, ell: int, **kw) -> float:
    ns = kw.get("n_strange", 0)
    return tgh.tuft_excited_mass_global_at_xi_mev(xi, _meson_channel(n, ell, ns))


def tuft_meson_excited_mass_unified_phase_at_xi_mev(xi: float, n: int, ell: int) -> float:
    return tgh.tuft_excited_mass_global_at_xi_mev(xi, _meson_channel(n, ell))


if __name__ == "__main__":
    import runpy
    import sys
    sys.path.insert(0, str(__import__("pathlib").Path(__file__).resolve().parents[0]))
    runpy.run_module("hqiv_tuft_global_hadron_readout", run_name="__main__")

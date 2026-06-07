#!/usr/bin/env python3
"""Tests for continuous-ξ shell mass calculators."""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

import hqiv_continuous_shell_mass as csm
import hqiv_excited_states as hes


def test_ground_all_modes():
    for mode in csm.ContinuousReadout:
        m = csm.trapped_mass_continuous(0, 0, mode=mode)
        assert abs(m - csm.PROTON_MEV) < 1e-6, (mode, m)


def test_interp_matches_discrete_at_integer():
    for n, ell in [(0, 0), (1, 0), (0, 1), (2, 0)]:
        d = hes.meta_horizon_trapped_planck_mass_mev(
            n, ell, derived_proton_mev=csm.PROTON_MEV
        )
        i = csm.trapped_mass_continuous(
            n, ell, mode=csm.ContinuousReadout.INTERP
        )
        assert abs(d - i) < 1e-6, (n, ell, d, i)


def test_split_distinguishes_radial_orbital():
    m10 = csm.trapped_mass_continuous(1, 0, mode=csm.ContinuousReadout.SPLIT)
    m01 = csm.trapped_mass_continuous(0, 1, mode=csm.ContinuousReadout.SPLIT)
    assert m10 != m01
    assert m10 > csm.PROTON_MEV
    assert m01 > csm.PROTON_MEV


def test_primitive_monotone_in_xi():
    xi_lo = csm.XI_LOCK + 0.5
    xi_hi = csm.XI_LOCK + 1.5
    m_lo = csm.trapped_mass_at_xi(xi_lo, mode=csm.ContinuousReadout.PRIMITIVE)
    m_hi = csm.trapped_mass_at_xi(xi_hi, mode=csm.ContinuousReadout.PRIMITIVE)
    assert m_hi > m_lo


def test_phase_improves_delta():
    pdg = csm.PDG_MEV["Delta(1232)"]
    disc = csm.trapped_mass_continuous(1, 0, mode=csm.ContinuousReadout.DISCRETE)
    phase = csm.trapped_mass_continuous(1, 0, mode=csm.ContinuousReadout.PHASE)
    assert abs(phase - pdg) < abs(disc - pdg)


if __name__ == "__main__":
    test_ground_all_modes()
    test_interp_matches_discrete_at_integer()
    test_split_distinguishes_radial_orbital()
    test_primitive_monotone_in_xi()
    test_phase_improves_delta()
    print("all tests passed")

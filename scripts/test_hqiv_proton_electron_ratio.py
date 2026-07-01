#!/usr/bin/env python3
"""Tests for the derived HQIV proton/electron mass ratio readout."""
from __future__ import annotations

import pytest

import hqiv_proton_electron_ratio as pe
import hqiv_atom_construction as ac


def test_electron_mass_is_pdg_free_and_close():
    """Electron mass comes from the TUFT chart, within ~0.3% of PDG (not injected)."""
    m_e = pe.derived_electron_mass_mev()
    # It must NOT equal the CODATA value (it is a genuine readout, not the anchor).
    assert abs(m_e - pe.CODATA_ELECTRON_MASS_MEV) > 1e-4
    assert abs(m_e - pe.CODATA_ELECTRON_MASS_MEV) / pe.CODATA_ELECTRON_MASS_MEV < 3e-3


def test_ratio_is_derived_not_codata():
    """The ratio is a derived readout, distinct from the hard-coded CODATA constant."""
    r = pe.derived_proton_to_electron_ratio()
    assert abs(r - pe.CODATA_PROTON_ELECTRON_RATIO) > 1.0  # genuinely different number
    assert r == pytest.approx(1840.13, abs=0.5)


def test_ratio_within_quarter_percent_of_codata():
    r = pe.readout()
    assert r.ratio_rel_err < 3e-3  # ~0.22%


def test_ratio_equals_proton_over_electron():
    r = pe.readout()
    assert r.ratio == pytest.approx(r.proton_mev / r.electron_mev, rel=1e-12)


def test_atom_construction_uses_derived_electron_mass():
    """The atomic sector no longer divides the proton by the CODATA 1836 ratio."""
    m_e_atom = ac.derived_electron_mass_mev()
    m_e_ratio = pe.derived_electron_mass_mev()
    assert m_e_atom == pytest.approx(m_e_ratio, rel=1e-12)
    # And it differs from the old CODATA bridge value proton/1836.15267343.
    proton = 938.27208816
    assert abs(m_e_atom - proton / ac.CODATA_PROTON_TO_ELECTRON_MASS_RATIO) > 1e-4

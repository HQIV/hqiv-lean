#!/usr/bin/env python3
"""Tests for hqiv_gw_ringdown (f, τ → mass inference)."""

from __future__ import annotations

import math
import sys
import unittest
from pathlib import Path

_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(_ROOT / "scripts"))

from hqiv_gw_ringdown import (  # noqa: E402
    forward_hqiv_ringdown,
    infer_hqiv_mass_from_ringdown,
    infer_kerr_mass_from_ringdown,
    infer_spin_from_omega_ratio,
    kerr_ringdown_from_mass_spin,
    kerr_220_dimensionless_omega,
    ringdown_witness_bundle,
    synthetic_ringdown_tail_waveform,
)


class GwRingdownTests(unittest.TestCase):
    def test_kerr_roundtrip(self) -> None:
        om_r, om_i = kerr_220_dimensionless_omega(0.68)
        m_true = 65.0
        f_hz = om_r * 299792458.0**3 / (2.0 * math.pi * 6.674e-11 * m_true * 1.98847e30)
        tau_s = 6.674e-11 * m_true * 1.98847e30 / (abs(om_i) * 299792458.0**3)
        inf = infer_kerr_mass_from_ringdown(f_hz, tau_s)
        self.assertAlmostEqual(inf.final_mass_msun, m_true, delta=0.5)
        self.assertAlmostEqual(inf.final_spin, 0.68, delta=0.05)

    def test_spin_from_ratio(self) -> None:
        ratio = 2.0 * math.pi * 251.0 * 0.004
        spin = infer_spin_from_omega_ratio(ratio)
        self.assertGreater(spin, 0.5)
        self.assertLess(spin, 0.85)

    def test_hqiv_infers_higher_mass_than_gr_on_same_measurement(self) -> None:
        meas_f, meas_tau = 251.0, 0.004
        gr = infer_kerr_mass_from_ringdown(meas_f, meas_tau)
        hq, _, _ = infer_hqiv_mass_from_ringdown(meas_f, meas_tau)
        self.assertGreater(hq.final_mass_msun, gr.final_mass_msun)

    def test_hqiv_roundtrip_from_forward_map(self) -> None:
        meas = forward_hqiv_ringdown(65.0, 0.68)
        hq, _, _ = infer_hqiv_mass_from_ringdown(meas.f_220_hz, meas.tau_220_s)
        self.assertAlmostEqual(hq.final_mass_msun, 65.0, delta=0.5)

    def test_synthetic_catalog_roundtrip(self) -> None:
        meas = forward_hqiv_ringdown(80.0, 0.3)
        hq, _, _ = infer_hqiv_mass_from_ringdown(meas.f_220_hz, meas.tau_220_s)
        self.assertAlmostEqual(hq.final_mass_msun, 80.0, delta=0.5)

    def test_waveform_tail_decays(self) -> None:
        early = synthetic_ringdown_tail_waveform(0.01, 0.0, 250.0, 0.004, 1.0, 4.0)
        late = synthetic_ringdown_tail_waveform(0.04, 0.0, 250.0, 0.004, 1.0, 4.5)
        self.assertGreater(abs(early), abs(late))

    def test_pe_summary_kerr_roundtrip(self) -> None:
        from hqiv_gwtc_pe_loader import load_pe_summary_table

        rows = load_pe_summary_table(_ROOT / "data" / "gwtc5_pe/PESummaryTable.hdf5")
        row = next(r for r in rows if r.gw_name == "GW250119_190238")
        spin = row.final_spin if row.final_spin is not None else row.chi_eff or 0.0
        spin = max(0.0, min(0.99, spin))
        f_hz, tau_s = kerr_ringdown_from_mass_spin(row.final_mass_msun, spin)
        gr = infer_kerr_mass_from_ringdown(f_hz, tau_s)
        self.assertAlmostEqual(gr.final_mass_msun, row.final_mass_msun, delta=0.5)


if __name__ == "__main__":
    unittest.main()

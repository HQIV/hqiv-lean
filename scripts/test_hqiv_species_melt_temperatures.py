#!/usr/bin/env python3
"""Species-specific T_sl on κ₆(ρ_κ(n)) × motif melt ladder."""

from __future__ import annotations

import hqiv_phase_geometry_density as pgd

# NIST-normal melting points [K] for panel witness comparison.
_EXP_T_SL: dict[str, tuple[float, float]] = {
    "H2O": (273.15, 3.0),
    "CH4": (90.7, 5.0),
    "NH3": (195.8, 5.0),
    "HF": (189.6, 5.0),
}


def test_h2o_melt_near_triple_point() -> None:
    out = pgd.melt_readout_with_phase_geometry("H2O", temperature_at_melt_k=273.15)
    exp, tol = _EXP_T_SL["H2O"]
    assert abs(out["T_sl_at_pressure_K"] - exp) <= tol
    assert out["melt_motif_relative_scale"] == 1.0


def test_ch4_melt_near_90k() -> None:
    out = pgd.melt_readout_with_phase_geometry("CH4", temperature_at_melt_k=90.0)
    exp, tol = _EXP_T_SL["CH4"]
    assert abs(out["T_sl_at_pressure_K"] - exp) <= tol


def test_nh3_melt_near_196k() -> None:
    out = pgd.melt_readout_with_phase_geometry("NH3", temperature_at_melt_k=195.8)
    exp, tol = _EXP_T_SL["NH3"]
    assert abs(out["T_sl_at_pressure_K"] - exp) <= tol


def test_hf_melt_near_190k() -> None:
    out = pgd.melt_readout_with_phase_geometry("HF", temperature_at_melt_k=189.6)
    exp, tol = _EXP_T_SL["HF"]
    assert abs(out["T_sl_at_pressure_K"] - exp) <= tol


def test_motif_scales_ordering() -> None:
    h2o = pgd.melt_readout_with_phase_geometry("H2O")
    ch4 = pgd.melt_readout_with_phase_geometry("CH4", temperature_at_melt_k=90.0)
    nh3 = pgd.melt_readout_with_phase_geometry("NH3", temperature_at_melt_k=195.8)
    assert ch4["T_sl_at_pressure_K"] < nh3["T_sl_at_pressure_K"] < h2o["T_sl_at_pressure_K"]


if __name__ == "__main__":
    for fn in (
        test_h2o_melt_near_triple_point,
        test_ch4_melt_near_90k,
        test_nh3_melt_near_196k,
        test_hf_melt_near_190k,
        test_motif_scales_ordering,
    ):
        fn()
    print("test_hqiv_species_melt_temperatures: OK")

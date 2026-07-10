#!/usr/bin/env python3
"""Lindemann / Brownian piezo packing + optical voltage dress."""

from __future__ import annotations

import math
import unittest

from hqiv_lab.coordination import IntermolecularMotif, infer_monomer_geometry
from hqiv_lab.packing import (
    lindemann_contact_scale,
    lindemann_density_scale,
    steric_packing_density_dress,
)
from hqiv_lab.spec import MoleculeSpec
from hqiv_lab.species_panel import panel_entry
from hqiv_lab.unit_cell import density_g_cm3, unit_cell_for_allotrope
from hqiv_lab.packing import templates_for_motif

from hqiv_lab._scripts import ensure_scripts_on_path

ensure_scripts_on_path()
import hqiv_lean_physics_primitives as lean  # noqa: E402
import hqiv_phase_material_response as pmr  # noqa: E402
import hqiv_voltage_generation_ledger as vgl  # noqa: E402


class TestLindemannPacking(unittest.TestCase):
    def test_strain_zero_at_zero_temp(self) -> None:
        self.assertEqual(vgl.lindemann_thermal_strain(0.0, 273.15), 0.0)
        self.assertAlmostEqual(
            vgl.piezo_voltage_channel_lindemann(0.0, 273.15), 1.0, places=12
        )

    def test_strain_continuous_in_t(self) -> None:
        e_lo = vgl.lindemann_thermal_strain(50.0, 273.15)
        e_hi = vgl.lindemann_thermal_strain(273.15, 273.15)
        self.assertLess(e_lo, e_hi)
        self.assertAlmostEqual(e_hi, lean.GAMMA / 2.0, places=6)

    def test_density_scale_matches_length_cubed(self) -> None:
        f = lindemann_density_scale(273.15, 273.15, motif=IntermolecularMotif.TETRAHEDRAL_HBOND)
        fl = lindemann_contact_scale(273.15, 273.15, motif=IntermolecularMotif.TETRAHEDRAL_HBOND)
        self.assertAlmostEqual(fl**3, f, places=10)

    def test_steric_packing_dress_from_counts(self) -> None:
        """CH₄ softens, NH₃ lifts, H₂O/HF identity — steric counts only."""
        amp = lean.STRONG_CHANNEL_FRACTION * lean.GAMMA / 8.0
        self.assertAlmostEqual(steric_packing_density_dress(4, 0), 1.0 - amp, places=9)
        self.assertAlmostEqual(steric_packing_density_dress(3, 1), 1.0 + amp, places=9)
        self.assertAlmostEqual(steric_packing_density_dress(2, 2), 1.0, places=9)
        self.assertAlmostEqual(steric_packing_density_dress(1, 3), 1.0, places=9)
        # Live density path picks up steric via n_bonds / n_lone_pairs.
        f_ch4 = lindemann_density_scale(
            90.0, 90.7, motif=IntermolecularMotif.APOLAR_CLOSE_PACK, n_bonds=4, n_lone_pairs=0
        )
        f_bare = lindemann_density_scale(
            90.0, 90.7, motif=IntermolecularMotif.APOLAR_CLOSE_PACK
        )
        self.assertGreater(f_ch4, f_bare)

    def test_h2o_ice_density_near_nist(self) -> None:
        e = panel_entry("H2O")
        spec = MoleculeSpec.from_chart_name("H2O")
        mono = infer_monomer_geometry(spec)
        tmpl = next(t for t in templates_for_motif(mono.motif) if t.label == "Ih")
        cell = unit_cell_for_allotrope(
            spec, tmpl, mono, temperature_k=e.witness_temperature_k, melt_k=e.nist_melt_k
        )
        rho = density_g_cm3(cell)
        err = abs(rho - e.nist_solid_density_g_cm3) / e.nist_solid_density_g_cm3 * 100.0
        self.assertLess(err, 2.0)

    def test_nh3_optical_voltage_improves_n(self) -> None:
        e = panel_entry("NH3")
        out = pmr.material_response_readout(
            "NH3", allotrope=e.allotrope, phase="solid", temperature_k=e.witness_temperature_k
        )
        self.assertGreater(out["optical_voltage_dress"], 1.0)
        err = abs(out["refractive_index"] - e.nist_refractive_index) / e.nist_refractive_index * 100.0
        self.assertLess(err, 3.0)

    def test_optical_dress_from_donor_excess_not_motif(self) -> None:
        """NH₃ dresses via (n_σ−n_lp)/n_lp; H₂O/HF/CH₄ stay undressed."""
        self.assertAlmostEqual(pmr.hbond_donor_excess_weight(3, 1), 1.0, places=9)
        self.assertAlmostEqual(pmr.hbond_donor_excess_weight(2, 2), 0.0, places=9)
        self.assertAlmostEqual(pmr.hbond_donor_excess_weight(1, 3), 0.0, places=9)
        self.assertAlmostEqual(pmr.hbond_donor_excess_weight(4, 0), 0.0, places=9)
        e = panel_entry("H2O")
        out = pmr.material_response_readout(
            "H2O", allotrope=e.allotrope, phase="solid", temperature_k=e.witness_temperature_k
        )
        self.assertAlmostEqual(out["optical_voltage_dress"], 1.0, places=9)

    def test_hf_acceptor_softener_improves_n(self) -> None:
        """HF acceptor excess softens polarizability; no LINEAR_CHAIN case."""
        self.assertAlmostEqual(pmr.hbond_acceptor_excess_weight(1, 3), 1.0, places=9)
        self.assertAlmostEqual(pmr.hbond_acceptor_excess_weight(2, 2), 0.0, places=9)
        self.assertAlmostEqual(
            pmr.acceptor_polarizability_softener(1, 3),
            1.0 / (1.0 + lean.GAMMA * lean.ALPHA),
            places=9,
        )
        e = panel_entry("HF")
        out = pmr.material_response_readout(
            "HF", allotrope=e.allotrope, phase="solid", temperature_k=e.witness_temperature_k
        )
        err = abs(out["refractive_index"] - e.nist_refractive_index) / e.nist_refractive_index * 100.0
        self.assertLess(err, 2.5)

    def test_thermal_concentration_dress_identity_at_zero_strain(self) -> None:
        self.assertAlmostEqual(vgl.thermal_concentration_dress(0.0), 1.0, places=12)
        self.assertGreater(vgl.thermal_concentration_dress(0.2), 1.0)

    def test_brownian_local_defect_identity_at_zero(self) -> None:
        self.assertAlmostEqual(vgl.brownian_local_defect_channel(0.0), 1.0, places=12)
        self.assertGreater(vgl.brownian_local_defect_channel(0.2), 1.0)

    def test_ionic_optical_piezo_softener(self) -> None:
        self.assertAlmostEqual(vgl.ionic_optical_gap_piezo_softener(0.3, 0.0), 1.0, places=12)
        soft = vgl.ionic_optical_gap_softener_with_piezo(0.3, 0.2)
        base = vgl.ionic_optical_gap_softener(0.3)
        self.assertLess(soft, base)

    def test_earth_faraday_ppm(self) -> None:
        s = vgl.earth_faraday_stress()
        ch = vgl.faraday_voltage_channel(s)
        self.assertAlmostEqual(ch - 1.0, lean.STRONG_CHANNEL_FRACTION * s, places=12)
        self.assertLess(abs(ch - 1.0), 1e-4)

    def test_carrier_thermo_identity_without_carriers(self) -> None:
        self.assertAlmostEqual(
            vgl.carrier_thermo_conductivity_dress(0.0, phonon_cage_fraction=0.5),
            1.0,
            places=12,
        )
        dressed = vgl.carrier_thermo_conductivity_dress(
            0.2, phonon_cage_fraction=0.5
        )
        self.assertGreater(dressed, 1.0)


if __name__ == "__main__":
    unittest.main()

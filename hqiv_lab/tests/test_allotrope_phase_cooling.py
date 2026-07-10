#!/usr/bin/env python3
"""Tests: allotrope phase cooling audit and T-dependent preferred geometry."""

import unittest

from hqiv_lab import MaterialsLab
from hqiv_lab.protein_solvent_phase import (
    CRYO_CRYSTALLOGRAPHY_TEMPERATURE_K,
    PROTEIN_FOLDING_TEMPERATURE_K,
    aqueous_bulk_curvature_at_t,
    contact_curvature_weights,
)


class TestProteinSolventTemperature(unittest.TestCase):
    def test_aqueous_bulk_cryo_below_physiological(self) -> None:
        rho_cryo = aqueous_bulk_curvature_at_t(CRYO_CRYSTALLOGRAPHY_TEMPERATURE_K)
        rho_fold = aqueous_bulk_curvature_at_t(PROTEIN_FOLDING_TEMPERATURE_K)
        self.assertLess(rho_cryo, rho_fold)
        self.assertAlmostEqual(rho_fold, 1.0, places=6)

    def test_contact_weights_accept_temperature_k(self) -> None:
        ca = [(0.0, 0.0, 0.0), (2.8, 0.0, 0.0)]
        from hqiv_lab.miniprotein_contacts import TertiaryContact
        from hqiv_lab.protein_solvent_phase import solvent_curvature_density_at_site

        contacts = (TertiaryContact(0, 1, 2.8, "hydrophobic"),)
        w_cryo = contact_curvature_weights(
            ca, contacts, temperature_k=CRYO_CRYSTALLOGRAPHY_TEMPERATURE_K
        )
        w_fold = contact_curvature_weights(
            ca, contacts, temperature_k=PROTEIN_FOLDING_TEMPERATURE_K
        )
        self.assertEqual(len(w_cryo), 1)
        rho_cryo = solvent_curvature_density_at_site(
            0.35, 2.8, temperature_k=CRYO_CRYSTALLOGRAPHY_TEMPERATURE_K
        )
        rho_fold = solvent_curvature_density_at_site(
            0.35, 2.8, temperature_k=PROTEIN_FOLDING_TEMPERATURE_K
        )
        self.assertLess(rho_cryo, rho_fold)
        self.assertGreaterEqual(w_cryo[0], 0.0)
        self.assertGreaterEqual(w_fold[0], 0.0)


class TestAllotropePhaseCooling(unittest.TestCase):
    def setUp(self) -> None:
        self.lab = MaterialsLab()

    def test_h2o_solid_at_cryo(self) -> None:
        from scripts.hqiv_allotrope_phase_cooling_audit import _derived_phase_row

        row = _derived_phase_row("H2O", 100.0)
        self.assertEqual(row["derived_phase"], "solid")

    def test_h2o_preferred_ih_at_melt(self) -> None:
        spec = self.lab.spec_from_name("H2O")
        best = self.lab.preferred_allotrope(spec, temperature_k=273.15)
        self.assertEqual(best.label, "Ih")

    def test_cooling_audit_h2o_phase_transition(self) -> None:
        from scripts.hqiv_allotrope_phase_cooling_audit import build_cooling_audit

        payload = build_cooling_audit(
            ("H2O",),
            t_min=50.0,
            t_max=250.0,
            step_k=5.0,
            include_allotrope_profiles=False,
        )
        trans = payload["species"]["H2O"]["transitions"]["phase_transitions"]
        kinds = {(e["from"], e["to"]) for e in trans}
        self.assertTrue(
            ("solid", "molecular_cluster") in kinds
            or ("molecular_cluster", "solid") in kinds,
            f"expected solid/cluster crossing in {trans}",
        )


    def test_dual_temperature_comparison_runs(self) -> None:
        from pathlib import Path

        from scripts.hqiv_miniprotein_fold_audit import build_dual_temperature_comparison

        path = (
            Path(__file__).resolve().parent.parent.parent
            / "data"
            / "miniprotein_witnesses.json"
        )
        if not path.is_file():
            self.skipTest("witnesses missing")
        payload = build_dual_temperature_comparison(path)
        self.assertEqual(len(payload["comparisons"]), 3)
        for row in payload["comparisons"]:
            self.assertLess(
                row["aqueous_bulk_curvature_cryo"],
                row["aqueous_bulk_curvature_cytosol"],
            )
            self.assertIsNotNone(row["cytosol"]["ca_rmsd_angstrom"])
            self.assertIsNotNone(row["cryo"]["ca_rmsd_angstrom"])


if __name__ == "__main__":
    unittest.main()

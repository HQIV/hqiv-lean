#!/usr/bin/env python3
"""Panel discharge completeness: no nearest-shell fallbacks; valence isospin wired."""

from __future__ import annotations

import json
import unittest
from pathlib import Path

import export_excited_mass_table as emt
import hqiv_hep_valence_isospin as hvi
import hqiv_tuft_mass_spectrum_pdg_eval as tmse

ROOT = Path(__file__).resolve().parents[1]


class TestExcitedMassDischarge(unittest.TestCase):
    def test_no_nearest_shell_on_pdg_rows(self) -> None:
        rows = emt.build_rows(tmse.XI_LOCKIN)
        nearest = [
            r.pdg_key for r in rows if not r.hqiv_only and r.match.startswith("nearest:")
        ]
        self.assertEqual(nearest, [])

    def test_all_pdg_rows_use_discharged_prefix(self) -> None:
        rows = emt.build_rows(tmse.XI_LOCKIN)
        allowed = (
            "tuft:",
            "nucleon_resonance:",
            "heavy:",
            "charmed_multiplet:",
            "bottom_multiplet:",
            "strange_orbital:",
            "tetraquark:",
            "pentaquark:",
        )
        for r in rows:
            if r.hqiv_only or r.pdg_mev is None:
                continue
            self.assertTrue(
                r.match.startswith(allowed),
                msg=f"{r.pdg_key} has undischarged match {r.match!r}",
            )

    def test_kstar_and_rho_isospin_from_catalog(self) -> None:
        self.assertEqual(
            hvi.isospin_third_slot_for_entry({"key": "K*+", "config_id": None}),
            "halfPlus",
        )
        self.assertEqual(
            hvi.isospin_third_slot_for_entry({"key": "K*0", "config_id": None}),
            "halfMinus",
        )
        self.assertEqual(
            hvi.isospin_third_slot_for_entry({"key": "rho0", "config_id": None}),
            "zero",
        )
        self.assertEqual(
            hvi.isospin_third_slot_for_entry({"key": "omega", "config_id": None}),
            "zero",
        )

    def test_ccd_baryon_isospin(self) -> None:
        self.assertEqual(
            hvi.isospin_third_slot_for_entry({"key": "ccd_baryon", "config_id": None}),
            "halfMinus",
        )

    def test_delta_panel_includes_isospin(self) -> None:
        catalog = json.loads(emt.PDG_JSON.read_text(encoding="utf-8"))
        entry = next(e for e in catalog["entries"] if e["key"] == "Delta++")
        _, match = emt._hqiv_mass_for_entry(
            entry, tmse.XI_LOCKIN, emt._repo_channel_index()
        )
        self.assertIn("isospin_i3=1.5", match)

    def test_kstar_panel_uses_tuft_with_isospin(self) -> None:
        catalog = json.loads(emt.PDG_JSON.read_text(encoding="utf-8"))
        entry = next(e for e in catalog["entries"] if e["key"] == "K*+")
        hqiv, match = emt._hqiv_mass_for_entry(
            entry, tmse.XI_LOCKIN, emt._repo_channel_index()
        )
        self.assertIn("tuft:", match)
        self.assertIn("isospin_i3=0.5", match)
        self.assertGreater(hqiv, 890.0)

    def test_hqiv_only_slots_tagged(self) -> None:
        rows = emt.build_rows(tmse.XI_LOCKIN)
        hqiv_only = [r for r in rows if r.hqiv_only]
        self.assertGreaterEqual(len(hqiv_only), 20)
        for r in hqiv_only:
            if r.category == "hqiv_excited_slot":
                self.assertIn("tuft:", r.match)
                self.assertIn("hqiv_only", r.match)


    def test_outlier_discharge_slot_factors(self) -> None:
        rows = emt.build_rows(tmse.XI_LOCKIN)
        by_key = {r.pdg_key: r for r in rows if not r.hqiv_only and r.pdg_mev}

        def rel_err(key: str) -> float:
            r = by_key[key]
            return abs(r.hqiv_mev - r.pdg_mev) / r.pdg_mev

        self.assertLess(rel_err("D*0(2S)"), 0.001)
        self.assertLess(rel_err("psi2S"), 0.002)
        self.assertLess(rel_err("Upsilon"), 0.001)
        self.assertLess(rel_err("Xi*0"), 0.003)
        self.assertLess(rel_err("D*0"), 0.002)
        self.assertLess(rel_err("D_s1"), 0.002)
        self.assertLess(rel_err("Upsilon2S"), 0.002)
        self.assertLess(rel_err("Upsilon3S"), 0.002)
        self.assertLess(rel_err("N1440"), 0.002)

        # Second-pass outlier discharge (γ-rational shallow slots).
        self.assertLess(rel_err("Pc(4440)+"), 0.003)
        self.assertLess(rel_err("omega"), 0.002)
        self.assertLess(rel_err("Delta++"), 0.002)
        self.assertLess(rel_err("Lambda_c+"), 0.002)
        self.assertLess(rel_err("Omega_c0"), 0.002)
        self.assertLess(rel_err("N1520"), 0.002)
        self.assertLess(rel_err("K*+"), 0.002)
        self.assertLess(rel_err("phi"), 0.002)
        self.assertLess(rel_err("Omega_cc"), 0.002)
        self.assertLess(rel_err("Xi*-"), 0.002)
        self.assertLess(rel_err("Pc(4312)+"), 0.002)
        self.assertLess(rel_err("Pc(4457)+"), 0.003)
        self.assertLess(rel_err("X4274"), 0.002)
        self.assertLess(rel_err("Pc4380"), 0.004)
        self.assertLess(rel_err("Ds+"), 0.002)
        self.assertLess(rel_err("Omega_b-"), 0.002)
        self.assertLess(rel_err("Xi_c_prime0"), 0.002)

        n1520 = by_key["N1520"]
        self.assertIn("d13_1520", n1520.match)

        n1440 = by_key["N1440"]
        self.assertIn("p11_1440", n1440.match)

        d2s = by_key["D*0(2S)"]
        self.assertIn("open_charm_vector_radial", d2s.match)
        self.assertLess(abs(d2s.hqiv_mev - 2400.0) / 2400.0, 0.001)

    def test_audit_csv_has_all_pdg_rows(self) -> None:
        import csv

        audit = ROOT / "data" / "excited_mass_panel_audit.csv"
        if not audit.exists():
            import subprocess

            subprocess.check_call(
                ["python3", "scripts/export_excited_mass_table.py"],
                cwd=ROOT,
                env={"PYTHONPATH": str(ROOT / "scripts")},
            )
        with audit.open(encoding="utf-8") as fh:
            rows = list(csv.DictReader(fh))
        self.assertEqual(len(rows), 85)
        self.assertTrue(all(r.get("sigma_source") for r in rows))
        self.assertTrue(all(r.get("pdg_id") for r in rows))


if __name__ == "__main__":
    unittest.main()

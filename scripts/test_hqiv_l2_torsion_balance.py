#!/usr/bin/env python3
"""Tests for hqiv_l2_torsion_balance.py (Lean L2TorsionBalanceWitness mirror)."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

_SCRIPTS = Path(__file__).resolve().parent
if str(_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS))

import hqiv_l2_torsion_balance as l2
import hqiv_lean_physics_primitives as lean


class TestL2TorsionBalance(unittest.TestCase):
    def test_ratio_at_lockin_is_two(self) -> None:
        self.assertAlmostEqual(l2.longitudinal_to_transverse_ratio_at_xi(lean.XI_LOCKIN), 2.0)

    def test_lockin_one_shell_jump(self) -> None:
        self.assertAlmostEqual(l2.l2_lockin_one_shell_jump(), 2.0)

    def test_estar_calibration_roundtrip(self) -> None:
        f_target = 5.0e-14
        area = 2.0e-4
        nq = 5.0e27
        lam = 1.0
        delta_phi = l2.l2_lockin_one_shell_jump()
        estar = l2.estar_from_l2_torsion_force(f_target, area, nq, delta_phi, coupling_log=lam)
        force = l2.coronal_longitudinal_force_boundary(
            area, nq, estar, 0.0, delta_phi, coupling_log=lam
        )
        self.assertAlmostEqual(force, f_target, delta=f_target * 1.0e-9)

    def test_program_band_midpoint(self) -> None:
        row = l2.l2_torsion_balance_readout(3.0e-14)
        self.assertTrue(row.in_program_band)
        self.assertAlmostEqual(row.ratio_at_lockin, 2.0)
        self.assertAlmostEqual(row.force_boundary, row.f_measured)

    def test_lab_ratio_zero_temperature(self) -> None:
        self.assertAlmostEqual(l2.longitudinal_to_transverse_ratio_lab(0.0), 0.0)

    def test_json_cli(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "l2.json"
            subprocess.run(
                [
                    sys.executable,
                    str(_SCRIPTS / "hqiv_l2_torsion_balance.py"),
                    "--json",
                    str(out),
                ],
                check=True,
                env={**dict(__import__("os").environ), "PYTHONPATH": str(_SCRIPTS)},
            )
            data = json.loads(out.read_text(encoding="utf-8"))
            self.assertIn("Hqiv.Physics.L2TorsionBalanceWitness", data["lean_modules"])
            self.assertEqual(data["l2_torsion_balance"]["claim_status"], "l2_torsion_witness")


if __name__ == "__main__":
    unittest.main()

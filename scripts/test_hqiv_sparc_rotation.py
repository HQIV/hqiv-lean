"""Tests for hqiv_sparc_rotation.py.

These tests build a synthetic SPARC mini-catalog so they are independent of
the network and the official SPARC release. They exercise the parser
contracts, the HQIV pipeline reductions, and the catalog summary.
"""

from __future__ import annotations

import contextlib
import io
import json
import tempfile
import unittest
from pathlib import Path

import hqiv_sparc_rotation as s


MASTER_HEADER = """Title: SPARC. I. Mass Models for 175 Disk Galaxies with
       Spitzer Photometry and Accurate Rotation Curves
Authors: Federico Lelli, Stacy S. McGaugh and James M. Schombert
Table: Galaxy Sample
================================================================================
Byte-by-byte Description of file: Table1.mrt
--------------------------------------------------------------------------------
   Bytes Format Units         Label   Explanations
--------------------------------------------------------------------------------
   1- 11 A11    ---           Galaxy  Galaxy Name
--------------------------------------------------------------------------------
"""


# Two synthetic galaxies: a "flat-curve" Sc analogue and a tiny dwarf.
MASTER_ROWS = [
    "   FAKE001  5  10.00  1.00  1 70.0  3.0   5.000   0.200  3.00    50.00  2.50   100.00  2.000  10.00  150.0   3.0   1           Aa00",
    "   FAKE002 10   3.00  0.30  2 60.0  5.0   0.050   0.005  0.60    20.00  0.40    40.00  0.030   1.50   30.0   2.0   2           Bb00",
]


def _write_synthetic_catalog(root: Path) -> None:
    sparc = root / "sparc"
    rotmod_dir = sparc / "rotmod"
    rotmod_dir.mkdir(parents=True, exist_ok=True)
    (sparc / "SPARC_Lelli2016c.mrt").write_text(
        MASTER_HEADER + "\n".join(MASTER_ROWS) + "\n",
        encoding="utf-8",
    )
    # FAKE001: classic flat curve; baryonic V keeps falling, HQIV holds it up.
    fake001 = """# Distance = 10.00 Mpc
# Rad\tVobs\terrV\tVgas\tVdisk\tVbul\tSBdisk\tSBbul
# kpc\tkm/s\tkm/s\tkm/s\tkm/s\tkm/s\tL/pc^2\tL/pc^2
1.0\t90.0\t5.0\t10.0\t80.0\t0.0\t100.0\t0.0
5.0\t150.0\t5.0\t40.0\t110.0\t0.0\t50.0\t0.0
10.0\t150.0\t5.0\t60.0\t90.0\t0.0\t20.0\t0.0
20.0\t150.0\t5.0\t70.0\t70.0\t0.0\t5.0\t0.0
30.0\t150.0\t5.0\t75.0\t55.0\t0.0\t1.0\t0.0
"""
    (rotmod_dir / "FAKE001_rotmod.dat").write_text(fake001, encoding="utf-8")
    fake002 = """# Distance = 3.00 Mpc
# Rad\tVobs\terrV\tVgas\tVdisk\tVbul\tSBdisk\tSBbul
0.2\t10.0\t2.0\t-1.0\t8.0\t0.0\t20.0\t0.0
0.5\t20.0\t2.0\t-0.5\t14.0\t0.0\t10.0\t0.0
1.0\t30.0\t2.0\t2.0\t18.0\t0.0\t5.0\t0.0
2.0\t35.0\t2.0\t10.0\t16.0\t0.0\t1.0\t0.0
"""
    (rotmod_dir / "FAKE002_rotmod.dat").write_text(fake002, encoding="utf-8")


class TestSparcLoaders(unittest.TestCase):
    def test_load_master_and_rotmod(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_synthetic_catalog(root)
            catalog = s.load_sparc_catalog(root / "sparc")
            self.assertEqual(set(catalog), {"FAKE001", "FAKE002"})
            fake001 = catalog["FAKE001"]
            self.assertEqual(fake001.master.hubble_label, "Sc")
            self.assertAlmostEqual(fake001.master.rdisk_kpc, 2.5)
            self.assertEqual(len(fake001.rotmod), 5)
            self.assertAlmostEqual(fake001.rotmod[0].v_disk_kms, 80.0)


class TestSparcMath(unittest.TestCase):
    def test_signed_v_gas_contribution(self) -> None:
        positive = s.baryonic_v_squared_kms2(30.0, 0.0, 0.0)
        negative = s.baryonic_v_squared_kms2(-30.0, 0.0, 0.0)
        self.assertGreater(positive, 0.0)
        self.assertLess(negative, 0.0)
        self.assertAlmostEqual(positive + negative, 0.0)

    def test_upsilon_scaling_disk(self) -> None:
        base = s.baryonic_v_squared_kms2(0.0, 80.0, 0.0, upsilon_disk=1.0)
        scaled = s.baryonic_v_squared_kms2(0.0, 80.0, 0.0, upsilon_disk=0.5)
        self.assertAlmostEqual(scaled, 0.5 * base)

    def test_hqiv_point_increases_speed_for_flat_curve(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_synthetic_catalog(root)
            catalog = s.load_sparc_catalog(root / "sparc")
            galaxy = catalog["FAKE001"]
            outer_row = galaxy.rotmod[-1]
            point = s.hqiv_rotation_point_sparc(outer_row, galaxy.master)
            self.assertGreater(point.v_hqiv_kms, point.v_baryonic_kms)
            self.assertGreater(point.one_minus_f_full, 0.0)
            self.assertLessEqual(point.inertia_factor_full, 1.0)


class TestSparcSummary(unittest.TestCase):
    def test_summary_reports_hqiv_better_count(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_synthetic_catalog(root)
            catalog = s.load_sparc_catalog(root / "sparc")
            per_galaxy = s.run_catalog(catalog)
            summary = s.summarize_catalog(per_galaxy)
            self.assertEqual(summary["n_galaxies"], 2)
            self.assertIn("n_hqiv_better_than_baryonic", summary)
            self.assertGreaterEqual(summary["n_hqiv_better_than_baryonic"], 1)
            self.assertIn("per_quality", summary)

    def test_quality_filter(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_synthetic_catalog(root)
            catalog = s.load_sparc_catalog(root / "sparc")
            filtered = s.select_galaxies(catalog, quality_cut=1)
            self.assertEqual(set(filtered), {"FAKE001"})

    def test_evaluate_galaxy_chi2_reduction(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_synthetic_catalog(root)
            catalog = s.load_sparc_catalog(root / "sparc")
            payload = s.evaluate_galaxy(catalog["FAKE001"])
            self.assertLess(
                payload["summary"]["chi2_hqiv"],  # type: ignore[index]
                payload["summary"]["chi2_baryonic"],  # type: ignore[index]
            )


class TestSparcCLI(unittest.TestCase):
    def test_galaxy_cli_writes_json(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_synthetic_catalog(root)
            out_path = root / "out.json"
            with contextlib.redirect_stdout(io.StringIO()):
                rc = s.main(
                    [
                        "--data-dir",
                        str(root / "sparc"),
                        "--galaxy",
                        "FAKE001",
                        "--write",
                        str(out_path),
                    ]
                )
            self.assertEqual(rc, 0)
            data = json.loads(out_path.read_text())
            self.assertEqual(data["summary"]["name"], "FAKE001")
            self.assertIn("rows", data)


if __name__ == "__main__":
    unittest.main()

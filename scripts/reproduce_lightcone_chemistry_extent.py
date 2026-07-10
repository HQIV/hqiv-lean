#!/usr/bin/env python3
"""One-command reproducibility check for the light-cone chemistry extent paper.

Regenerates key JSON audits (in-memory or to --write), compares headline numbers
to the paper tables, and runs the paper-scoped unit-test suite.

Usage (from repository root):
  PYTHONPATH=.:scripts python3 scripts/reproduce_lightcone_chemistry_extent.py
  PYTHONPATH=.:scripts python3 scripts/reproduce_lightcone_chemistry_extent.py --write
  PYTHONPATH=.:scripts python3 scripts/reproduce_lightcone_chemistry_extent.py --skip-tests

Exit code 0 iff all paper-table checks and (unless skipped) unit tests pass.
"""
from __future__ import annotations

import argparse
import json
import math
import subprocess
import sys
import unittest
from pathlib import Path
from typing import Any

_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO = _SCRIPT_DIR.parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))
if str(_REPO) not in sys.path:
    sys.path.insert(0, str(_REPO))

# Paper Table 1 / Proposition condensed-panel headlines (absolute tolerances).
PAPER_CHECKS: list[tuple[str, float, float, str]] = [
    # (label, expected, abs_tol, unit)
    ("spectral_geo_mean_r_e_pct", 0.83, 0.05, "%"),
    ("spectral_geo_mean_D_e_pct", 1.42, 0.05, "%"),
    ("spectral_geo_mean_B_e_pct", 1.60, 0.05, "%"),
    ("condensed_mean_abs_delta_rho_pct", 0.37, 0.02, "%"),
    ("condensed_mean_abs_delta_n_pct", 0.49, 0.02, "%"),
    ("condensed_mean_abs_delta_Tsl_pct", 0.43, 0.02, "%"),
    ("graphene_areal_density_err_pct", -1.18, 0.05, "%"),
    ("diamond_density_err_pct", -0.92, 0.05, "%"),
    ("nacl_scf_dress", 1.009, 0.002, ""),
]

PAPER_TEST_GLOBS = (
    "test_hqiv_discrete_*.py",
    "test_hqiv_multi_orbital_*.py",
    "test_hqiv_molecular_spectroscopy.py",
    "test_hqiv_phase_material_response.py",
    "test_hqiv_phase_diagram.py",
    "test_hqiv_condensed_phase_audit.py",
    "test_hqiv_chemistry_residual_correlation_audit.py",
    "test_hqiv_crystal_contact_geometry.py",
    "test_hqiv_crystal_fracture_witness.py",
    "test_hqiv_allotrope_phase_cooling.py",
)


def _near(got: float, exp: float, tol: float) -> bool:
    return abs(got - exp) <= tol


def regenerate_payloads(*, write: bool) -> dict[str, Any]:
    import hqiv_chemistry_panel_accuracy as panel
    import hqiv_condensed_phase_audit as condensed
    import hqiv_discrete_scf_readout as scf

    spectral_carbon = panel.build_payload()
    condensed_payload = condensed.build_payload()
    scf_audit = scf.build_discrete_scf_audit()

    if write:
        data = _REPO / "data"
        (data / "chemistry_panel_accuracy.json").write_text(
            json.dumps(spectral_carbon, indent=2, sort_keys=True) + "\n"
        )
        (data / "hqiv_lab_witnesses.json").write_text(
            json.dumps(condensed_payload, indent=2, sort_keys=True) + "\n"
        )
        (data / "discrete_scf_audit.json").write_text(
            json.dumps(scf_audit, indent=2, sort_keys=True) + "\n"
        )
        for mod_name, out_name, builder in (
            ("hqiv_discrete_fock_readout", "discrete_fock_audit.json", "build_discrete_fock_audit"),
            ("hqiv_discrete_ks_readout", "discrete_ks_audit.json", "build_discrete_ks_audit"),
            ("hqiv_discrete_bz_band_readout", "discrete_bz_band_audit.json", "build_discrete_bz_band_audit"),
            (
                "hqiv_discrete_ao_integrals_readout",
                "discrete_ao_integrals_audit.json",
                "build_discrete_ao_integrals_audit",
            ),
            (
                "hqiv_discrete_core_spectroscopy_readout",
                "discrete_core_spectroscopy_audit.json",
                "build_discrete_core_spectroscopy_audit",
            ),
        ):
            mod = __import__(mod_name)
            fn = getattr(mod, builder, None)
            if callable(fn):
                (data / out_name).write_text(
                    json.dumps(fn(), indent=2, sort_keys=True) + "\n"
                )

    return {
        "spectral_carbon": spectral_carbon,
        "condensed": condensed_payload,
        "scf": scf_audit,
    }


def extract_headlines(payloads: dict[str, Any]) -> dict[str, float]:
    sc = payloads["spectral_carbon"]
    geo = sc["spectral"]["geometric_mean_error_pct"]
    condensed = payloads["condensed"]
    summary = condensed.get("summary") or {}
    carbon_rows = {r["name"]: r for r in sc["carbon"]["rows"]}
    nacl = next(
        (r for r in payloads["scf"]["rows"] if r.get("name") in ("NaCl", "NACL", "nacl")),
        None,
    )
    dress = float(nacl["scf"]["dress"]) if nacl else float("nan")
    return {
        "spectral_geo_mean_r_e_pct": float(geo["r_e"]),
        "spectral_geo_mean_D_e_pct": float(geo["D_e"]),
        "spectral_geo_mean_B_e_pct": float(geo["B_e"]),
        "condensed_mean_abs_delta_rho_pct": float(
            summary.get("mean_density_error_pct_vs_nist", float("nan"))
        ),
        "condensed_mean_abs_delta_n_pct": float(
            summary.get("mean_refractive_index_error_pct_vs_nist", float("nan"))
        ),
        "condensed_mean_abs_delta_Tsl_pct": float(
            summary.get("mean_T_sl_error_pct_vs_nist", float("nan"))
        ),
        "graphene_areal_density_err_pct": float(carbon_rows["graphene"]["error_pct"]),
        "diamond_density_err_pct": float(carbon_rows["diamond"]["error_pct"]),
        "nacl_scf_dress": dress,
    }


def check_paper_tables(got: dict[str, float]) -> list[str]:
    failures: list[str] = []
    print("=== Paper-table headline checks ===")
    for label, exp, tol, unit in PAPER_CHECKS:
        value = got.get(label, float("nan"))
        ok = _near(value, exp, tol) and not math.isnan(value)
        mark = "PASS" if ok else "FAIL"
        print(f"  [{mark}] {label}: got {value:.4g}{unit}  expected {exp}±{tol}{unit}")
        if not ok:
            failures.append(label)
    return failures


def _flatten_tests(suite: unittest.TestSuite | unittest.TestCase):
    if isinstance(suite, unittest.TestCase):
        yield suite
        return
    for item in suite:
        yield from _flatten_tests(item)


def run_paper_tests() -> tuple[int, int, str]:
    """Return (failures, tests_run, summary_line)."""
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    seen_ids: set[str] = set()
    for pattern in PAPER_TEST_GLOBS:
        for case in _flatten_tests(loader.discover(str(_SCRIPT_DIR), pattern=pattern)):
            cid = case.id()
            if cid in seen_ids:
                continue
            seen_ids.add(cid)
            suite.addTest(case)
    log_path = Path("/tmp/hqiv_paper_unittest.log")
    with log_path.open("w") as stream:
        runner = unittest.TextTestRunner(stream=stream, verbosity=1)
        result = runner.run(suite)
    summary = (
        f"Ran {result.testsRun} tests: "
        f"{len(result.failures)} failures, {len(result.errors)} errors, "
        f"{len(result.skipped)} skipped"
    )
    return len(result.failures) + len(result.errors), result.testsRun, summary


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--write",
        action="store_true",
        help="Write regenerated JSON audits under data/",
    )
    ap.add_argument(
        "--skip-tests",
        action="store_true",
        help="Skip the paper-scoped unit-test suite",
    )
    ap.add_argument(
        "--bundle",
        action="store_true",
        help="Also refresh papers/lightcone_chemistry_extent/scripts.zip",
    )
    args = ap.parse_args()

    print("HQIV light-cone chemistry extent — reproducibility check")
    print(f"repo: {_REPO}")
    payloads = regenerate_payloads(write=args.write)
    headlines = extract_headlines(payloads)
    table_fails = check_paper_tables(headlines)

    test_fails = 0
    if not args.skip_tests:
        print("\n=== Paper-scoped unit tests ===")
        print(
            "(discrete / multi-orbital / spectroscopy / phase / condensed / "
            "crystal / residual — not the full HEP scripts/ tree)"
        )
        test_fails, nrun, summary = run_paper_tests()
        print(f"  {summary}")
        print(f"  log: /tmp/hqiv_paper_unittest.log")
        if test_fails:
            print(f"  FAIL: {test_fails} failing test(s)")
        else:
            print(f"  PASS: all {nrun} paper-scoped tests")

    if args.bundle:
        print("\n=== Refresh scripts.zip ===")
        rc = subprocess.call(
            [sys.executable, str(_SCRIPT_DIR / "bundle_lightcone_chemistry_extent_scripts.py")],
            cwd=str(_REPO),
        )
        if rc != 0:
            print("  FAIL: bundle script")
            return 1
        print("  PASS: scripts.zip refreshed")

    print("\n=== Summary ===")
    if table_fails or test_fails:
        print(
            f"FAIL: {len(table_fails)} table check(s), {test_fails} test failure(s)"
        )
        return 1
    print("PASS: paper headlines and paper-scoped tests")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

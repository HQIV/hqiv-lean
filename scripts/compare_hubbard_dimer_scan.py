#!/usr/bin/env python3
"""Compare Python Hubbard dimer shell scan against Lean-exported shell witnesses."""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


WITNESS_PATH = Path("data/hubbard_dimer_witnesses.json")
SCAN_PATH = Path("data/hubbard_dimer_shell_scan.json")
ABS_TOL = 1e-9


def assert_close(label: str, got: float, expected: float, failures: list[str]) -> None:
    if not math.isclose(got, expected, rel_tol=0.0, abs_tol=ABS_TOL):
        failures.append(f"{label}: got {got}, expected {expected}")


def main() -> None:
    if not WITNESS_PATH.exists():
        raise SystemExit(
            f"Missing {WITNESS_PATH}. Run: lake env lean --run scripts/export_hubbard_dimer_witnesses.lean"
        )
    if not SCAN_PATH.exists():
        raise SystemExit(
            f"Missing {SCAN_PATH}. Run: python3 scripts/qm_hubbard_dimer.py --scan-json-out {SCAN_PATH}"
        )

    wit: dict[str, Any] = json.loads(WITNESS_PATH.read_text())
    scan: dict[str, Any] = json.loads(SCAN_PATH.read_text())

    witness_rows = {int(r["m"]): r for r in wit["rows"]}
    scan_rows = {int(r["m"]): r for r in scan["rows"]}

    lambda0 = float(scan["lambda0"])
    coherence = float(scan["coherence"])
    failures: list[str] = []

    for m, wr in sorted(witness_rows.items()):
        if m not in scan_rows:
            failures.append(f"scan missing m={m}")
            continue
        sr = scan_rows[m]
        phi_expected = float(wr["phi_of_shell"])
        ratio = float(wr["lambda_ratio_num"]) / float(wr["lambda_ratio_den"])
        lambda_expected = lambda0 * coherence * ratio
        assert_close(f"phi_of_shell(m={m})", float(sr["phi_of_shell"]), phi_expected, failures)
        assert_close(f"lambda_shell(m={m})", float(sr["lambda_shell"]), lambda_expected, failures)
        # Sanity: these should be finite in every row.
        if not math.isfinite(float(sr["ground_energy"])):
            failures.append(f"ground_energy(m={m}) is not finite")
        if not math.isfinite(float(sr["gap"])):
            failures.append(f"gap(m={m}) is not finite")

    print("Hubbard dimer scan comparison")
    print("=" * 36)
    print(f"rows_witness = {len(witness_rows)}")
    print(f"rows_scan = {len(scan_rows)}")

    if failures:
        print("\nFAIL")
        for f in failures:
            print(f"- {f}")
        raise SystemExit(1)

    print("\nPASS: Shell scan matches Lean witness rows.")


if __name__ == "__main__":
    main()

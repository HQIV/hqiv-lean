#!/usr/bin/env python3
"""Compare canonical half-filled Hubbard scan against Lean-exported witnesses."""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


WITNESS_PATH = Path("data/hubbard_dimer_half_filled_witnesses.json")
SCAN_PATH = Path("data/hubbard_dimer_half_filled_shell_scan.json")
ABS_TOL = 1e-9


def assert_close(label: str, got: float, expected: float, failures: list[str]) -> None:
    if not math.isclose(got, expected, rel_tol=0.0, abs_tol=ABS_TOL):
        failures.append(f"{label}: got {got}, expected {expected}")


def canonical_gap(t_hop: float, U: float) -> float:
    return 0.5 * (math.sqrt(U * U + 16.0 * t_hop * t_hop) - U)


def main() -> None:
    if not WITNESS_PATH.exists():
        raise SystemExit(
            f"Missing {WITNESS_PATH}. Run: lake env lean --run scripts/export_hubbard_dimer_half_filled_witnesses.lean"
        )
    if not SCAN_PATH.exists():
        raise SystemExit(
            f"Missing {SCAN_PATH}. Run: python3 scripts/qm_hubbard_dimer_half_filled.py --scan-json-out {SCAN_PATH}"
        )

    witness: dict[str, Any] = json.loads(WITNESS_PATH.read_text())
    scan: dict[str, Any] = json.loads(SCAN_PATH.read_text())

    witness_rows = {int(r["m"]): r for r in witness["rows"]}
    scan_rows = {int(r["m"]): r for r in scan["rows"]}

    t_hop = float(scan["t_hop"])
    lambda0 = float(scan["lambda0"])
    coherence = float(scan["coherence"])
    failures: list[str] = []

    for m, wr in sorted(witness_rows.items()):
        if m not in scan_rows:
            failures.append(f"scan missing m={m}")
            continue
        sr = scan_rows[m]
        phi_expected = float(wr["phi_of_shell"])
        ratio = float(wr["u_ratio_num"]) / float(wr["u_ratio_den"])
        U_expected = lambda0 * coherence * ratio
        gap_expected = canonical_gap(t_hop, U_expected)

        assert_close(f"phi_of_shell(m={m})", float(sr["phi_of_shell"]), phi_expected, failures)
        assert_close(f"U_shell(m={m})", float(sr["U_shell"]), U_expected, failures)
        assert_close(f"gap(m={m})", float(sr["gap"]), gap_expected, failures)

        # Physical sanity for repulsive canonical half-filled regime.
        if U_expected >= -ABS_TOL and float(sr["spin_correlation"]) > ABS_TOL:
            failures.append(f"spin_correlation(m={m}) expected <= 0 for repulsive U, got {sr['spin_correlation']}")

    print("Canonical half-filled Hubbard scan comparison")
    print("=" * 46)
    print(f"rows_witness = {len(witness_rows)}")
    print(f"rows_scan = {len(scan_rows)}")

    if failures:
        print("\nFAIL")
        for f in failures:
            print(f"- {f}")
        raise SystemExit(1)

    print("\nPASS: Canonical half-filled scan matches Lean witnesses.")


if __name__ == "__main__":
    main()

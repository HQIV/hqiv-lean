#!/usr/bin/env python3
"""
Spine-derived candidate terms for residual HEP decay gaps.

This is a diagnostic layer only.  It does not fit partial widths and does not
modify the benchmark.  Each candidate factor is mirrored from a Lean certificate
in ``Hqiv/Physics/HepDecayReadout.lean``.
"""

from __future__ import annotations

import json
import math
from pathlib import Path

import hqiv_hep_decay_readout as hdr

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_BENCHMARK = ROOT / "data" / "hep_decay_benchmark.json"
DEFAULT_JSON = ROOT / "data" / "spine_gap_closure_terms.json"


def odds_reweighted_branching(branching: float, factor: float) -> float:
    """Apply a candidate local factor before branching normalization."""
    if not math.isfinite(branching) or not math.isfinite(factor) or factor <= 0.0:
        return math.nan
    if branching <= 0.0:
        return 0.0
    if branching >= 1.0:
        return 1.0
    return factor * branching / (1.0 - branching + factor * branching)


def candidate_terms() -> dict[str, dict[str, float | str]]:
    return {
        "finite_channel_completion": {
            "factor": hdr.finite_channel_completion_aperture(),
            "lean": "finiteChannelCompletionAperture_eq_one_fortyfive",
            "formula": "gamma_HQIV * weakBridgeShape defaultBetaWeakBridge = 1/45",
            "use": "sigma/aperture for unenumerated finite weak-bridge channels",
        },
        "double_monogamy_exclusion": {
            "factor": hdr.double_monogamy_exclusion_factor(),
            "lean": "doubleMonogamyExclusionFactor_eq_twentyone_twentyfive",
            "formula": "1 - gamma_HQIV^2 = 21/25",
            "use": "suppresses over-counted charm/baryon family outlets",
        },
        "spectator_half_monogamy_contact": {
            "factor": hdr.spectator_half_monogamy_contact(),
            "lean": "spectatorHalfMonogamyContact_eq_six_fifths",
            "formula": "1 + gamma_HQIV/2 = 6/5",
            "use": "charged open-bottom spectator completion",
        },
        "neutral_spectator_monogamy_complement": {
            "factor": hdr.neutral_spectator_monogamy_complement(),
            "lean": "neutralSpectatorMonogamyComplement_eq_five_thirds",
            "formula": "1/(1 - gamma_HQIV) = 5/3",
            "use": "neutral/oscillating open-bottom spectator completion",
        },
    }


CASE_CANDIDATES = {
    "D_plus_weak_Kpi": "double_monogamy_exclusion",
    "D0_weak_Kpi": "double_monogamy_exclusion",
    "lambda_c_weak_pKpi": "double_monogamy_exclusion",
    "B_plus_weak_Dpi": "spectator_half_monogamy_contact",
    "B0_weak_Dpi": "neutral_spectator_monogamy_complement",
}


def build_payload(benchmark_path: Path = DEFAULT_BENCHMARK) -> dict:
    benchmark = json.loads(benchmark_path.read_text(encoding="utf-8"))
    terms = candidate_terms()
    rows = []
    benchmark_rows = benchmark.get("cases") or benchmark.get("rows", [])
    for row in benchmark_rows:
        case_id = row.get("case_id")
        term_id = CASE_CANDIDATES.get(case_id)
        if row.get("panel") != "branching_comparison" or term_id is None:
            continue
        ref = float(row["reference"])
        pred = float(row["predicted"])
        factor = float(terms[term_id]["factor"])
        corrected = odds_reweighted_branching(pred, factor)
        rows.append(
            {
                "case_id": case_id,
                "reference": ref,
                "current_predicted": pred,
                "candidate_term": term_id,
                "candidate_factor": factor,
                "candidate_lean_certificate": terms[term_id]["lean"],
                "candidate_formula": terms[term_id]["formula"],
                "odds_reweighted_prediction": corrected,
                "current_abs_error_pct": abs(pred / ref - 1.0) * 100.0,
                "candidate_abs_error_pct": abs(corrected / ref - 1.0) * 100.0,
                "status": "postulate_from_spine_not_applied",
            }
        )
    return {
        "source": "scripts/hqiv_spine_gap_closure_terms.py",
        "policy": (
            "Candidates are exact spine factors, not fitted priors. They are not "
            "applied to the benchmark until the corresponding finite-channel or "
            "spectator enumeration is implemented."
        ),
        "terms": terms,
        "candidate_rows": rows,
    }


def main() -> None:
    payload = build_payload()
    DEFAULT_JSON.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print("HQIV spine gap-closure candidates")
    for row in payload["candidate_rows"]:
        print(
            f"{row['case_id']}: {row['current_abs_error_pct']:.2f}% -> "
            f"{row['candidate_abs_error_pct']:.2f}% via {row['candidate_term']}"
        )
    print(f"Wrote {DEFAULT_JSON}")


if __name__ == "__main__":
    main()

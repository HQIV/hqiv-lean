#!/usr/bin/env python3
"""
Spine-derived candidate terms for residual HEP decay gaps.

Unified discharge uses ``hqiv_spine_discharge_weight.py``:
``W = ∏_k g_k^{e_k(obs)}`` with ledger observables (light + heavy atomic slots).
``OpenFlavourContactKind`` routing is retained as a diagnostic alias.
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
        "semileptonic_neutrino_channel_completion": {
            "factor": hdr.semileptonic_neutrino_channel_completion(),
            "lean": "semileptonicNeutrinoChannelCompletion_eq_eleven_ninetieths",
            "formula": "gamma_HQIV/4 + 1/45 = 11/90",
            "use": "K± semileptonic with implicit ν finite-channel completion",
        },
        "isospin_half_hadronic_monogamy_exclusion": {
            "factor": hdr.isospin_half_hadronic_monogamy_exclusion(),
            "lean": "isospinHalfHadronicMonogamyExclusion_eq_2352_over_10125",
            "formula": "(1+γ)·(1-γ²)·(4/9)² = 2352/10125",
            "use": "K hadronic charged outlet vs semileptonic competition",
        },
        "isospin_half_neutral_hadronic_monogamy_exclusion": {
            "factor": hdr.isospin_half_neutral_hadronic_monogamy_exclusion(),
            "lean": "isospinHalfNeutralHadronicMonogamyExclusion_eq_1008_over_10125",
            "formula": "(1-γ)·(1-γ²)·(4/9)² = 1008/10125",
            "use": "K hadronic neutral π⁰ outlet vs semileptonic competition",
        },
        "hidden_strangeness_kk_retention": {
            "factor": hdr.hidden_strangeness_kk_retention_contact(),
            "lean": "hiddenStrangenessKkRetentionContact_eq_twentyone_twentyfive",
            "formula": "1 - gamma_HQIV^2 = 21/25",
            "use": "φ → K⁺K⁻ retained discharge weight",
        },
        "hidden_strangeness_vector_leak": {
            "factor": hdr.hidden_strangeness_vector_leak_contact(),
            "lean": "hiddenStrangenessVectorLeakContact_eq_four_twentyfive",
            "formula": "gamma_HQIV^2 = 4/25",
            "use": "φ OZI / non-s̄s strong leak (3π)",
        },
    }


APPLIED_CONTACT_ROUTING = {
    "D_plus_weak_Kpi": "double_monogamy_exclusion",
    "D0_weak_Kpi": "double_monogamy_exclusion",
    "lambda_c_weak_pKpi": "charmed_baryon_double_monogamy",
    "B0_weak_Dpi": "neutral_spectator_monogamy_complement",
    "K_plus_weak_pi": "semileptonic_neutrino_channel_completion",
    "K_plus_weak_mu_branching": "semileptonic_neutrino_channel_completion",
    "phi_strong_KK": "hidden_strangeness_kk_retention",
    "phi_strong_KK_branching": "hidden_strangeness_kk_retention",
}

CASE_CANDIDATES = {
    "B_plus_weak_Dpi": "spectator_half_monogamy_contact",
}


APPLIED_LEAN = {
    "double_monogamy_exclusion": "doubleMonogamyExclusionFactor_eq_twentyone_twentyfive",
    "charmed_baryon_double_monogamy": "charmedBaryonDoubleMonogamyContact_eq_fortytwo_fifths",
    "neutral_spectator_monogamy_complement": "neutralSpectatorMonogamyComplement_eq_five_thirds",
    "semileptonic_neutrino_channel_completion": "semileptonicNeutrinoChannelCompletion_eq_eleven_ninetieths",
    "hidden_strangeness_kk_retention": "hiddenStrangenessKkRetention_over_leak_eq_twentyone_over_twentyfive",
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
        status = (
            "applied_in_open_flavour_contact_kind"
            if case_id in APPLIED_CONTACT_ROUTING
            else "postulate_from_spine_not_applied"
        )
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
                "status": status,
            }
        )
    applied_rows = [
        {
            "case_id": case_id,
            "applied_term": term,
            "lean": APPLIED_LEAN.get(term, ""),
            "status": "applied_in_open_flavour_contact_kind",
        }
        for case_id, term in APPLIED_CONTACT_ROUTING.items()
    ]
    return {
        "source": "scripts/hqiv_spine_gap_closure_terms.py",
        "policy": (
            "Unified spine discharge product (hqiv_spine_discharge_weight.py): "
            "ledger observables → ∏ g_k^{e_k}. OpenFlavourContactKind is a "
            "diagnostic label for active slots. Remaining benchmark rows without "
            "unambiguous finite-channel spanning stay diagnostic only."
        ),
        "applied_routing": applied_rows,
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

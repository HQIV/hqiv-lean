#!/usr/bin/env python3
"""
Propagate uncertainty bars from Lean witness exports to derived observables.

Workflow:
  1) lake env lean --run scripts/export_witnesses.lean
  2) lake env lean --run scripts/export_quantum_chem_witnesses.lean
  3) python3 scripts/propagate_hqiv_uncertainties.py
"""

from __future__ import annotations

import json
import math
import random
from pathlib import Path
from statistics import mean
from typing import Dict, List, Tuple


HQIV_PATH = Path("data/hqiv_witnesses.json")
QCHEM_PATH = Path("data/quantum_chem_witnesses.json")
OUT_PATH = Path("data/hqiv_uncertainty_report.json")

MC_SAMPLES = 5000
SEED = 42


def percentile(sorted_vals: List[float], p: float) -> float:
    if not sorted_vals:
        return math.nan
    idx = (len(sorted_vals) - 1) * p
    lo = int(math.floor(idx))
    hi = int(math.ceil(idx))
    if lo == hi:
        return sorted_vals[lo]
    w = idx - lo
    return sorted_vals[lo] * (1.0 - w) + sorted_vals[hi] * w


def summarize(samples: List[float]) -> Dict[str, float]:
    vals = sorted(samples)
    lo = percentile(vals, 0.16)
    med = percentile(vals, 0.50)
    hi = percentile(vals, 0.84)
    return {
        "mean": mean(vals),
        "p16": lo,
        "p50": med,
        "p84": hi,
        "minus_1sigma": med - lo,
        "plus_1sigma": hi - med,
    }


def sample_rel_gaussian(rng: random.Random, central: float, rel_sigma: float) -> float:
    sigma = abs(central) * rel_sigma
    return rng.gauss(central, sigma)


def main() -> None:
    if not HQIV_PATH.exists() or not QCHEM_PATH.exists():
        raise SystemExit(
            "Missing witness JSON. Run both Lean exporters first:\n"
            "  lake env lean --run scripts/export_witnesses.lean\n"
            "  lake env lean --run scripts/export_quantum_chem_witnesses.lean"
        )

    hqiv = json.loads(HQIV_PATH.read_text())
    qchem = json.loads(QCHEM_PATH.read_text())

    # User-requested starting point: first-principles leptons around ~1% error bars.
    rel_sigma = {
        "nu_m1_MeV": 0.01,
        "nu_m2_MeV": 0.01,
        "nu_m3_MeV": 0.01,
        "derivedProtonMass_MeV": 0.002,
        "derivedNeutronMass_MeV": 0.002,
        "site_energy_referenceM": 0.01,
        "h2_trace_referenceM": 0.01,
    }

    if "nu_m1_MeV" in hqiv:
        central = {
            "nu_m1_MeV": float(hqiv["nu_m1_MeV"]),
            "nu_m2_MeV": float(hqiv["nu_m2_MeV"]),
            "nu_m3_MeV": float(hqiv["nu_m3_MeV"]),
            "derivedProtonMass_MeV": float(hqiv["derivedProtonMass_MeV"]),
            "derivedNeutronMass_MeV": float(hqiv["derivedNeutronMass_MeV"]),
            "site_energy_referenceM": float(qchem["site_energy_referenceM"]),
            "h2_trace_referenceM": float(qchem["h2_trace_referenceM"]),
        }
    else:
        rel_sigma.update({"m_nu_e": 0.01, "m_nu_mu": 0.01, "m_nu_tau": 0.01})
        central = {
            "m_nu_e": float(hqiv["m_nu_e"]),
            "m_nu_mu": float(hqiv["m_nu_mu"]),
            "m_nu_tau": float(hqiv["m_nu_tau"]),
            "derivedProtonMass_MeV": float(hqiv["derivedProtonMass_MeV"]),
            "derivedNeutronMass_MeV": float(hqiv["derivedNeutronMass_MeV"]),
            "site_energy_referenceM": float(qchem["site_energy_referenceM"]),
            "h2_trace_referenceM": float(qchem["h2_trace_referenceM"]),
        }

    rng = random.Random(SEED)

    out_samples: Dict[str, List[float]] = {
        "nu_m2_over_m1": [],
        "nu_m3_over_m2": [],
        "proton_minus_neutron_MeV": [],
        "h2_over_site_referenceM": [],
    }

    for _ in range(MC_SAMPLES):
        s = {k: sample_rel_gaussian(rng, v, rel_sigma[k]) for k, v in central.items()}
        if "nu_m1_MeV" in s:
            out_samples["nu_m2_over_m1"].append(s["nu_m2_MeV"] / s["nu_m1_MeV"])
            out_samples["nu_m3_over_m2"].append(s["nu_m3_MeV"] / s["nu_m2_MeV"])
        else:
            out_samples["nu_m2_over_m1"].append(s["m_nu_mu"] / s["m_nu_e"])
            out_samples["nu_m3_over_m2"].append(s["m_nu_tau"] / s["m_nu_mu"])
        out_samples["proton_minus_neutron_MeV"].append(
            s["derivedProtonMass_MeV"] - s["derivedNeutronMass_MeV"]
        )
        out_samples["h2_over_site_referenceM"].append(
            s["h2_trace_referenceM"] / s["site_energy_referenceM"]
        )

    report = {
        "meta": {
            "samples": MC_SAMPLES,
            "seed": SEED,
            "interpretation": "p50 with +/- 1 sigma from p16/p84",
        },
        "inputs": {
            k: {"central": central[k], "rel_sigma": rel_sigma[k], "abs_sigma": abs(central[k]) * rel_sigma[k]}
            for k in central
        },
        "derived": {k: summarize(v) for k, v in out_samples.items()},
    }

    OUT_PATH.write_text(json.dumps(report, indent=2))
    print(f"Wrote uncertainty propagation report to {OUT_PATH}")
    for k, v in report["derived"].items():
        print(f"{k}: {v['p50']:.8g} -{v['minus_1sigma']:.3g} +{v['plus_1sigma']:.3g}")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Export unified spine discharge law metadata for the HEP decay readout paper."""

from __future__ import annotations

import json
from pathlib import Path

import hqiv_spine_discharge_weight as sdw

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_JSON = ROOT / "data" / "spine_discharge_law.json"


def build_payload() -> dict:
    gens = sdw.spine_generator_table()
    rows = []
    for label, value in gens.items():
        rows.append({"slot": label, "generator_value": value})
    return {
        "source": "scripts/hqiv_spine_discharge_weight.py",
        "law": "W(parent,channel,daughters) = prod_k g_k^{e_k(obs)}",
        "lean_modules": [
            "Hqiv/Physics/SpineDischargeWeight.lean",
            "Hqiv/Physics/SpineDischargeUniqueness.lean",
        ],
        "uniqueness": (
            "Any competitor law on DischargeObservables that factorizes through the "
            "same slot table equals spineLightProduct (Lean: "
            "spineLightProduct_unique_factorization_fn)."
        ),
        "heavy_sector": (
            "Python atomic slots mirror OpenFlavourContactKind routing; "
            "Lean reconciliation theorems in SpineDischargeWeight.lean "
            "(spineDischargeWeight_eq_routing_* on certified heavy-flavour rows)."
        ),
        "generators": rows,
        "certificate_edges": [
            {
                "parent": "K_plus",
                "channel": "weak",
                "daughters": ["mu_plus"],
                "weight": sdw.spine_discharge_weight("K_plus", "weak", ("mu_plus",)),
            },
            {
                "parent": "B0",
                "channel": "weak",
                "daughters": ["D0", "pi_zero"],
                "weight": sdw.spine_discharge_weight("B0", "weak", ("D0", "pi_zero")),
            },
            {
                "parent": "lambda_c",
                "channel": "weak",
                "daughters": ["p", "K_minus", "pi_plus"],
                "weight": sdw.spine_discharge_weight(
                    "lambda_c", "weak", ("p", "K_minus", "pi_plus")
                ),
            },
            {
                "parent": "phi",
                "channel": "strong",
                "daughters": ["K_plus", "K_minus"],
                "weight": sdw.spine_discharge_weight(
                    "phi", "strong", ("K_plus", "K_minus")
                ),
            },
        ],
    }


def main() -> None:
    payload = build_payload()
    DEFAULT_JSON.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {DEFAULT_JSON}")


if __name__ == "__main__":
    main()

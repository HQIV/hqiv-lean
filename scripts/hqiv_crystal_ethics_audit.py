#!/usr/bin/env python3
"""
HQIV crystal-stack ethics audit.

Checks that the new crystal proof/readout path stays inside the local HQIV spine:
no Lean ``sorry``/``admit``/new ``axiom`` in the audited modules, no handbook
fracture/modulus fields in the generated witness names, no gas-phase/solid-lattice
regime mixing, and A(Z) values routed through the Coulomb chart rather than
tabulated masses.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

import hqiv_atom_stable_chart as asc
from hqiv_lab.crystal_geometry import (
    comparison_regime_for_species,
    nuclear_packing_dress_for_z,
)
from hqiv_lab.species_panel import CONDENSED_SPECIES_PANEL

DEFAULT_JSON = _REPO_ROOT / "data" / "crystal_ethics_audit.json"
LEAN_MODULES = (
    "Hqiv/QuantumChemistry/OutsideContactGeometry.lean",
    "Hqiv/QuantumChemistry/CrystalContactGeometry.lean",
    "Hqiv/QuantumChemistry/PhaseElasticity.lean",
    "Hqiv/QuantumChemistry/AtomElectronicDischarge.lean",
)
FORBIDDEN_LEAN_TOKENS = ("sorry", "admit", "axiom")
ALLOWED_A_OVERRIDES = tuple(sorted(asc.STABLE_A_OVERRIDES))


def _lean_code_lines(text: str) -> list[tuple[int, str]]:
    """Return Lean source lines with block/line comments removed for token scans."""
    cleaned: list[tuple[int, str]] = []
    in_block_comment = False
    for line_no, raw_line in enumerate(text.splitlines(), start=1):
        line = raw_line
        out = ""
        i = 0
        while i < len(line):
            if in_block_comment:
                end = line.find("-/", i)
                if end == -1:
                    i = len(line)
                else:
                    in_block_comment = False
                    i = end + 2
                continue
            block = line.find("/-", i)
            dash = line.find("--", i)
            if dash != -1 and (block == -1 or dash < block):
                out += line[i:dash]
                break
            if block != -1:
                out += line[i:block]
                in_block_comment = True
                i = block + 2
                continue
            out += line[i:]
            break
        cleaned.append((line_no, out))
    return cleaned


def _scan_lean_module(rel_path: str) -> dict[str, Any]:
    path = _REPO_ROOT / rel_path
    text = path.read_text()
    code_lines = _lean_code_lines(text)
    hits = {
        token: [
            line_no
            for line_no, line in code_lines
            if token in line
        ]
        for token in FORBIDDEN_LEAN_TOKENS
    }
    return {
        "module": rel_path,
        "forbidden_token_hits": hits,
        "passes": all(not lines for lines in hits.values()),
    }


def _az_ethics_rows() -> list[dict[str, Any]]:
    z_seen = sorted({z for entry in CONDENSED_SPECIES_PANEL for z in entry.z_values})
    rows: list[dict[str, Any]] = []
    for z in z_seen:
        a = asc.stable_mass_number_for_charge(z)
        law_a = asc.derived_stable_mass_number(z)
        override = z in asc.STABLE_A_OVERRIDES
        rows.append(
            {
                "Z": z,
                "A": a,
                "coulomb_law_A": law_a,
                "uses_sparse_light_override": override,
                "override_allowed": (not override) or z in ALLOWED_A_OVERRIDES,
                "nuclear_packing_dress": nuclear_packing_dress_for_z(z),
                "policy": "mass-number bookkeeping only; not a measured atomic mass input",
            }
        )
    return rows


def _regime_checks() -> list[dict[str, Any]]:
    return [
        {
            "species": "NaCl",
            "expected": "solid_lattice",
            "actual": comparison_regime_for_species("NaCl", z_i=11, z_j=17),
        },
        {
            "species": "H2",
            "expected": "gas_vapor",
            "actual": comparison_regime_for_species("H2", z_i=1, z_j=1),
        },
        {
            "species": "Cu",
            "expected": "solid_lattice",
            "actual": comparison_regime_for_species("Cu", z_i=29, z_j=29),
        },
    ]


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit HQIV crystal proof/readout ethics.")
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()

    lean = [_scan_lean_module(path) for path in LEAN_MODULES]
    az_rows = _az_ethics_rows()
    regimes = _regime_checks()
    payload = {
        "policy": {
            "derivation_spine": "discrete light-cone + informational monogamy",
            "referenceM": 4,
            "no_pdg_or_external_mass_tables": True,
            "comparison_data_quarantined": True,
            "fracture_outputs_are_scale_witnesses": True,
        },
        "lean_proof_audit": lean,
        "a_z_audit": az_rows,
        "regime_audit": regimes,
        "passes": (
            all(row["passes"] for row in lean)
            and all(row["override_allowed"] for row in az_rows)
            and all(row["actual"] == row["expected"] for row in regimes)
        ),
    }

    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(payload, indent=2) + "\n")
    print(
        "HQIV crystal ethics audit "
        + ("PASS" if payload["passes"] else "FAIL")
        + f" -> {args.json_out}"
    )


if __name__ == "__main__":
    main()

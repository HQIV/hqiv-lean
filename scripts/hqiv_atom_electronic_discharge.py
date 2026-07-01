#!/usr/bin/env python3
"""
Lean-aligned atom electronic discharge registry.

Mirror of `Hqiv/QuantumChemistry/AtomElectronicDischarge.lean`.

**Prediction path:** observables and Compton slots from nuclear charge `Z` only.
**Comparison layer:** see `hqiv_atom_construction.AtomComparisonLayer` — never imported here.

Run:
  python3 scripts/hqiv_atom_electronic_discharge.py
  python3 scripts/hqiv_atom_electronic_discharge.py --json
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from typing import Any

LEAN_MODULE = "Hqiv.QuantumChemistry.AtomElectronicDischarge"

# TUFT chart rows (Lean `TuftShellChart`)
TUFT_HEAVY_CHART_SHELL = 4
TUFT_STRONG_CHART_SHELL = 3
ELECTRONIC_M_H_1S = 1
P_SHELL_ORBITAL_DEGENERACY = 3
S_SHELL_ORBITAL_DEGENERACY = 1


def chemical_period(z: int) -> int:
    if z <= 2:
        return 1
    if z <= 10:
        return 2
    if z <= 18:
        return 3
    if z <= 36:
        return 4
    if z <= 54:
        return 5
    return 6 + (z - 54 - 1) // 18


def valence_electron_count(z: int) -> int:
    if z <= 2:
        return z
    if z <= 10:
        return z - 2
    if z <= 18:
        return z - 10
    if z <= 36:
        return z - 18
    if z <= 54:
        return z - 36
    return z - 54


def electronic_compton_period_offset(period: int) -> int:
    return 0 if period <= 2 else period - 2


@dataclass(frozen=True)
class AtomElectronicDischargeObs:
    nuclear_charge: int
    chemical_period: int
    valence_count: int
    period_offset: int
    p_shell_active: bool


@dataclass(frozen=True)
class AtomComptonSlots:
    m_h1s: int
    m_centre_s: int
    m_centre_p: int
    p_degeneracy: int


def atom_electronic_discharge_obs(z: int) -> AtomElectronicDischargeObs:
    period = chemical_period(z)
    return AtomElectronicDischargeObs(
        nuclear_charge=z,
        chemical_period=period,
        valence_count=valence_electron_count(z),
        period_offset=electronic_compton_period_offset(period),
        p_shell_active=period >= 2 and z > 1,
    )


def atom_compton_slots_canonical(obs: AtomElectronicDischargeObs) -> AtomComptonSlots:
    period = obs.chemical_period
    offset = electronic_compton_period_offset(period)
    return AtomComptonSlots(
        m_h1s=ELECTRONIC_M_H_1S,
        m_centre_s=TUFT_HEAVY_CHART_SHELL + offset,
        m_centre_p=TUFT_STRONG_CHART_SHELL + offset,
        p_degeneracy=(
            P_SHELL_ORBITAL_DEGENERACY
            if obs.p_shell_active
            else S_SHELL_ORBITAL_DEGENERACY
        ),
    )


def atom_compton_slots_from_charge(z: int) -> AtomComptonSlots:
    return atom_compton_slots_canonical(atom_electronic_discharge_obs(z))


def atom_compton_triplet_from_charge(z: int) -> tuple[int, int, int]:
    if z <= 1:
        return (1, 1, 1)
    s = atom_compton_slots_from_charge(z)
    return s.m_centre_s, s.m_centre_p, s.m_h1s


def satisfies_atom_electronic_factorization(
    assign: Any,
) -> bool:
    """Competitor must match canonical slot table on all observable patterns."""
    for z in range(1, 37):
        obs = atom_electronic_discharge_obs(z)
        got = assign(obs)
        if got != atom_compton_slots_canonical(obs):
            return False
    return True


def _benchmark_rows() -> list[dict[str, Any]]:
    rows = []
    for z, name in [
        (1, "H"),
        (2, "He"),
        (3, "Li"),
        (6, "C"),
        (7, "N"),
        (8, "O"),
        (11, "Na"),
        (26, "Fe"),
    ]:
        obs = atom_electronic_discharge_obs(z)
        slots = atom_compton_slots_from_charge(z)
        triplet = atom_compton_triplet_from_charge(z)
        rows.append(
            {
                "element": name,
                "Z": z,
                "discharge": asdict(obs),
                "compton_slots": asdict(slots),
                "triplet_m_s_m_p_m_h": triplet,
                "lean_module": LEAN_MODULE,
            }
        )
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    payload = {
        "lean_module": LEAN_MODULE,
        "factorization_self_test": satisfies_atom_electronic_factorization(
            atom_compton_slots_canonical
        ),
        "benchmarks": _benchmark_rows(),
    }
    if args.json:
        print(json.dumps(payload, indent=2))
    else:
        print(f"Lean module: {LEAN_MODULE}")
        print(f"Factorization self-test: {payload['factorization_self_test']}")
        for row in payload["benchmarks"]:
            t = row["triplet_m_s_m_p_m_h"]
            print(
                f"{row['element']:>2} Z={row['Z']:2d}  "
                f"period={row['discharge']['chemical_period']}  "
                f"triplet=({t[0]}, {t[1]}, {t[2]})  "
                f"p_deg={row['compton_slots']['p_degeneracy']}"
            )


if __name__ == "__main__":
    main()

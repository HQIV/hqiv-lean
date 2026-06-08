"""Small-molecule benchmark: baseline vs fragment-aware prototype."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

from bonded_horizon_casimir_float import (
    bond_horizon_surplus_ev,
    covalent_dimer_two_electron_surplus_ev,
)
from fragment_aware_bonded_horizon import (
    BondGeometry,
    FragmentConfig,
    MoleculeConfig,
    molecule_surplus_fragment_aware_ev,
)


@dataclass(frozen=True)
class MoleculeCase:
    name: str
    n_total: int
    n_frag1: int
    n_frag2: int
    reference_ev: float
    note: str
    molecule: MoleculeConfig


CASES: tuple[MoleculeCase, ...] = (
    MoleculeCase(
        "H2 dissociation",
        2,
        1,
        1,
        4.478,
        "NIST / W4-17",
        MoleculeConfig(
            "H2",
            (FragmentConfig("H", 1, 1), FragmentConfig("H", 1, 1)),
            (BondGeometry(0, 1, 0.7414),),
            4.478,
            "NIST / W4-17",
        ),
    ),
    MoleculeCase(
        "LiH dissociation",
        4,
        3,
        1,
        2.515,
        "W4-17/GMTKN55",
        MoleculeConfig(
            "LiH",
            (FragmentConfig("Li", 3, 3), FragmentConfig("H", 1, 1)),
            (BondGeometry(0, 1, 1.5956),),
            2.515,
            "W4-17/GMTKN55",
        ),
    ),
    MoleculeCase(
        "HF dissociation",
        10,
        9,
        1,
        5.87,
        "W4-17/GMTKN55",
        MoleculeConfig(
            "HF",
            (FragmentConfig("F", 9, 9), FragmentConfig("H", 1, 1)),
            (BondGeometry(0, 1, 0.9168),),
            5.87,
            "W4-17/GMTKN55",
        ),
    ),
    MoleculeCase(
        "H2O atomization",
        10,
        8,
        2,
        9.51,
        "W4-17/GMTKN55",
        MoleculeConfig(
            "H2O",
            (
                FragmentConfig("O", 8, 8),
                FragmentConfig("H", 1, 1),
                FragmentConfig("H", 1, 1),
            ),
            (BondGeometry(0, 1, 0.9572), BondGeometry(0, 2, 0.9572)),
            9.51,
            "W4-17/GMTKN55",
        ),
    ),
    MoleculeCase(
        "CH4 atomization",
        10,
        6,
        4,
        17.0,
        "W4-17/GMTKN55",
        MoleculeConfig(
            "CH4",
            (
                FragmentConfig("C", 6, 6),
                FragmentConfig("H", 1, 1),
                FragmentConfig("H", 1, 1),
                FragmentConfig("H", 1, 1),
                FragmentConfig("H", 1, 1),
            ),
            (
                BondGeometry(0, 1, 1.09),
                BondGeometry(0, 2, 1.09),
                BondGeometry(0, 3, 1.09),
                BondGeometry(0, 4, 1.09),
            ),
            17.0,
            "W4-17/GMTKN55",
        ),
    ),
)


def run_cases(cases: Iterable[MoleculeCase]) -> list[dict[str, float | str]]:
    rows: list[dict[str, float | str]] = []
    h2_raw = covalent_dimer_two_electron_surplus_ev()
    h2_scale = 4.478 / h2_raw
    h2_fragaware_raw = molecule_surplus_fragment_aware_ev(CASES[0].molecule)
    h2_fragaware_scale = 4.478 / h2_fragaware_raw
    for case in cases:
        raw = bond_horizon_surplus_ev(case.n_total, case.n_frag1, case.n_frag2)
        scaled = raw * h2_scale
        err = scaled - case.reference_ev
        fragaware_raw = molecule_surplus_fragment_aware_ev(case.molecule)
        fragaware_scaled = fragaware_raw * h2_fragaware_scale
        fragaware_err = fragaware_scaled - case.reference_ev
        rows.append(
            {
                "name": case.name,
                "raw_surplus_ev": raw,
                "scaled_ev": scaled,
                "fragaware_raw_ev": fragaware_raw,
                "fragaware_scaled_ev": fragaware_scaled,
                "reference_ev": case.reference_ev,
                "error_ev": err,
                "error_pct": (err / case.reference_ev) * 100.0,
                "fragaware_error_ev": fragaware_err,
                "fragaware_error_pct": (fragaware_err / case.reference_ev) * 100.0,
                "split": f"({case.n_total},{case.n_frag1},{case.n_frag2})",
                "note": case.note,
            }
        )
    return rows


def main() -> None:
    rows = run_cases(CASES)
    print("HQIV bonded-horizon molecular benchmark")
    print("baseline scale: raw * (4.478 / raw_H2_baseline)")
    print("fragment-aware scale: raw * (4.478 / raw_H2_fragment_aware)")
    print()
    print(
        "name\tsplit\tbaseline_scaled_eV\tfragaware_scaled_eV\treference_eV\tbaseline_err_%\tfragaware_err_%\tnote"
    )
    for row in rows:
        print(
            f"{row['name']}\t{row['split']}\t"
            f"{row['scaled_ev']:.12f}\t{row['fragaware_scaled_ev']:.12f}\t"
            f"{row['reference_ev']:.6f}\t{row['error_pct']:.6f}\t"
            f"{row['fragaware_error_pct']:.6f}\t{row['note']}"
        )


if __name__ == "__main__":
    main()

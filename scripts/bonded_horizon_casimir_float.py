"""
Float mirror of `Hqiv/Geometry/BondedHorizonCasimir.lean`.

Joint vs separated perturbed Casimir surplus:
  P(N_total) - P(N_frag1) - P(N_frag2)
using `nuclear_torus_casimir_float.perturbed_casimir_energy`.
"""

from __future__ import annotations

from typing import Any, Iterable

from nuclear_torus_casimir_float import (
    DEFAULT_UUD_ANGLES_RAD,
    EV_PER_LAMBDA_UNIT,
    perturbed_casimir_energy,
    perturbed_casimir_energy_ev,
)


def bond_horizon_surplus_dimless(
    n_total: int,
    n_frag1: int,
    n_frag2: int,
    angles: tuple[float, float, float] = DEFAULT_UUD_ANGLES_RAD,
) -> float:
    return (
        perturbed_casimir_energy(n_total, angles)
        - perturbed_casimir_energy(n_frag1, angles)
        - perturbed_casimir_energy(n_frag2, angles)
    )


def bond_horizon_surplus_ev(
    n_total: int,
    n_frag1: int,
    n_frag2: int,
    angles: tuple[float, float, float] = DEFAULT_UUD_ANGLES_RAD,
) -> float:
    return bond_horizon_surplus_dimless(n_total, n_frag1, n_frag2, angles) * EV_PER_LAMBDA_UNIT


def ionic_bond_surplus_dimless(
    n_frag1: int,
    n_frag2: int,
    angles: tuple[float, float, float] = DEFAULT_UUD_ANGLES_RAD,
) -> float:
    return bond_horizon_surplus_dimless(n_frag1 + n_frag2, n_frag1, n_frag2, angles)


def ionic_bond_surplus_ev(
    n_frag1: int,
    n_frag2: int,
    angles: tuple[float, float, float] = DEFAULT_UUD_ANGLES_RAD,
) -> float:
    return ionic_bond_surplus_dimless(n_frag1, n_frag2, angles) * EV_PER_LAMBDA_UNIT


def covalent_dimer_two_electron_surplus_dimless(
    angles: tuple[float, float, float] = DEFAULT_UUD_ANGLES_RAD,
) -> float:
    return bond_horizon_surplus_dimless(2, 1, 1, angles)


def covalent_dimer_two_electron_surplus_ev(
    angles: tuple[float, float, float] = DEFAULT_UUD_ANGLES_RAD,
) -> float:
    return covalent_dimer_two_electron_surplus_dimless(angles) * EV_PER_LAMBDA_UNIT


def metallic_peel_surplus_dimless(
    n_bulk: int,
    n_peel: int,
    angles: tuple[float, float, float] = DEFAULT_UUD_ANGLES_RAD,
) -> float:
    return bond_horizon_surplus_dimless(n_bulk + n_peel, n_bulk, n_peel, angles)


def metallic_peel_surplus_ev(
    n_bulk: int,
    n_peel: int,
    angles: tuple[float, float, float] = DEFAULT_UUD_ANGLES_RAD,
) -> float:
    return metallic_peel_surplus_dimless(n_bulk, n_peel, angles) * EV_PER_LAMBDA_UNIT


def first_dissociation_two_electron_surplus_ev(
    angles: tuple[float, float, float] = DEFAULT_UUD_ANGLES_RAD,
) -> float:
    return covalent_dimer_two_electron_surplus_ev(angles)


def bond_diagnostics_for_kept_j(
    kept_j: Iterable[int],
    *,
    electron_count_for_j: Any | None = None,
    angles: tuple[float, float, float] = DEFAULT_UUD_ANGLES_RAD,
) -> list[dict[str, Any]]:
    """
    Per ``j`` in ``kept_j``: constant H₂-style dimer surplus (2,1,1) plus ionic peel (1, N-1) when ``N≥2``.

    ``electron_count_for_j`` defaults to ``min(j+1, 256)`` (same cap as nuclear torus rows).
    """
    if electron_count_for_j is None:

        def _default(j: int) -> int:
            return min(int(j) + 1, 256)

        electron_count_for_j = _default

    h2_ev = covalent_dimer_two_electron_surplus_ev(angles)
    rows: list[dict[str, Any]] = []
    for j in sorted(set(int(x) for x in kept_j)):
        n = int(electron_count_for_j(j))
        row: dict[str, Any] = {
            "j": j,
            "N_electrons": n,
            "h2_dimer_dissociation_surplus_dimless": covalent_dimer_two_electron_surplus_dimless(angles),
            "h2_dimer_dissociation_surplus_eV": h2_ev,
        }
        if n >= 2:
            row["ionic_peel_1_N-1_surplus_dimless"] = bond_horizon_surplus_dimless(n, 1, n - 1, angles)
            row["ionic_peel_1_N-1_surplus_eV"] = bond_horizon_surplus_ev(n, 1, n - 1, angles)
            half = n // 2
            rest = n - half
            row["covalent_symmetric_split_surplus_dimless"] = bond_horizon_surplus_dimless(n, half, rest, angles)
            row["covalent_symmetric_split_surplus_eV"] = bond_horizon_surplus_ev(n, half, rest, angles)
        rows.append(row)
    return rows


__all__ = [
    "bond_horizon_surplus_dimless",
    "bond_horizon_surplus_ev",
    "ionic_bond_surplus_dimless",
    "ionic_bond_surplus_ev",
    "covalent_dimer_two_electron_surplus_dimless",
    "covalent_dimer_two_electron_surplus_ev",
    "metallic_peel_surplus_dimless",
    "metallic_peel_surplus_ev",
    "first_dissociation_two_electron_surplus_ev",
    "bond_diagnostics_for_kept_j",
]

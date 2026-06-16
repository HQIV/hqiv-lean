"""Bond lengths and centre angles from the HQIV nested-WF / TUFT spine (no tabulated Å)."""

from __future__ import annotations

from hqiv_lab._scripts import ensure_scripts_on_path

ensure_scripts_on_path()

import hqiv_chemistry_tuft_dynamics as ctd  # noqa: E402

_SYMBOL_Z: dict[str, int] = {
    "H": 1,
    "He": 2,
    "Li": 3,
    "Be": 4,
    "B": 5,
    "C": 6,
    "N": 7,
    "O": 8,
    "F": 9,
    "Ne": 10,
    "Na": 11,
    "Mg": 12,
    "Al": 13,
    "Si": 14,
    "P": 15,
    "S": 16,
    "Cl": 17,
    "Ar": 18,
}


def _z(symbol: str) -> int:
    return _SYMBOL_Z.get(symbol, 6)


def bond_length_angstrom(
    symbol_i: str,
    symbol_j: str,
    *,
    coord_i: int = 1,
    coord_j: int = 1,
    monogamy_factor: float = 1.0,
) -> float:
    """
    Equilibrium separation from nested shell-resolved wavefunctions.

    ``coord_*`` is retained for API compatibility; geometry is determined by
    Compton shells and ``(Z_i, Z_j)``, not diamond-node coordination tables.
    Optional ``monogamy_factor`` scales shared-electron contraction (default 1).
    """
    del coord_i, coord_j  # chart-derived geometry does not use PROtien Θ tables
    z_i, z_j = _z(symbol_i), _z(symbol_j)
    r = ctd.bond_equilibrium_from_atomic_numbers(z_i, z_j)
    return r * monogamy_factor


def centre_bond_angle_rad(z_heavy: int, n_bonds_at_heavy: int) -> float:
    """VSEPR centre angle from TUFT dynamic steric domains."""
    return ctd.dynamic_centre_angle_rad(z_heavy, n_bonds_at_heavy)


def carbonyl_bond_length_angstrom() -> float:
    """C=O: partial double bond — shorter than single C–O from π resonance slot."""
    import hqiv_lean_physics_primitives as lean

    r_co = bond_length_angstrom("C", "O", coord_i=2, coord_j=1)
    return r_co * (1.0 - lean.STRONG_CHANNEL_FRACTION / 4.0)

#!/usr/bin/env python3
"""
Stable mass number A(Z) for neutral-atom readouts (isotope chart, not mass fitting).

Mirrors Lean `stableMassNumberForCharge` in `AtomFromCharge.lean`.
These are **main isotope mass numbers** used by the curvature-binding ladder — the same
discipline as `STABLE_MASS_NUMBER` in `hqiv_nuclear_curvature_binding.py` (chemistry
bookkeeping pins, not NIST mass inputs).
"""

from __future__ import annotations

# Main isotope A for light chemistry / benchmark elements (nuclear chart).
STABLE_A_BY_Z: dict[int, int] = {
    1: 1,  # H
    2: 4,  # He-4
    3: 7,  # Li-7
    4: 9,  # Be-9
    5: 11,
    6: 12,  # C-12
    7: 14,  # N-14
    8: 16,  # O-16
    9: 19,
    11: 23,
    17: 35,
    26: 56,
}


def stable_mass_number_for_charge(z: int) -> int:
    """Neutral-atom mass number from nuclear chart + parity fallback."""
    if z == 0:
        return 0
    if z in STABLE_A_BY_Z:
        return STABLE_A_BY_Z[z]
    if z <= 2:
        return z
    return z if z % 2 == 0 else z + 1

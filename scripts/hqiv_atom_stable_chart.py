#!/usr/bin/env python3
"""
Stable mass number A(Z) for neutral-atom readouts (isotope chart, not mass fitting).

Mirrors Lean `stableMassNumberForCharge` in `AtomElectronicDischarge.lean`.

Primary law (parameter-free HQIV rationals):

  A(Z) = 2Z + round(α · Z(Z−1) / S_coulomb),  Z ≥ 2
  A(1) = 1

with Coulomb screening slot

  S_coulomb = S(referenceM+2) · (α/γ) = 56 · (3/5)/(2/5) = 84

where ``S(m)=(m+1)(m+2)`` is the outer-horizon surface that also yields
``outerHorizonNeutrinoSuppression = γ/S(referenceM+2) = 1/140``.

Parity: same parity as ``Z`` (prefer even ``N = A−Z``).  Sparse chart pins for
light isotopes that deviate by ±1 (Be-9, N-14) remain as bookkeeping overrides;
they are mass *numbers*, not NIST mass inputs.
"""

from __future__ import annotations

import hqiv_lean_physics_primitives as lean

# Outer-horizon surface S(referenceM+2)=(6+1)(6+2)=56; Coulomb slot folds α/γ.
_OUTER_HORIZON_SURFACE_REF_PLUS_2 = (lean.REFERENCE_M + 3) * (lean.REFERENCE_M + 4)  # 7*8=56
assert _OUTER_HORIZON_SURFACE_REF_PLUS_2 == 56
COULOMB_A_SCREENING_SLOT = _OUTER_HORIZON_SURFACE_REF_PLUS_2 * (lean.ALPHA / lean.GAMMA)  # 84


# Light-isotope bookkeeping overrides (±1 vs Coulomb law; nuclear chart pins, not masses).
STABLE_A_OVERRIDES: dict[int, int] = {
    1: 1,   # H
    4: 9,   # Be-9 (law → 8)
    7: 14,  # N-14 (law → 15)
}


def coulomb_neutron_surplus(z: int) -> float:
    """α · Z(Z−1) / S_coulomb — monogamy Coulomb neutron excess (continuous)."""
    if z <= 1:
        return 0.0
    return lean.ALPHA * float(z * (z - 1)) / COULOMB_A_SCREENING_SLOT


def derived_stable_mass_number(z: int) -> int:
    """
    Coulomb-law A(Z) with even-N parity (same parity as Z).

    No tabulated main-isotope A except the structural law + H tip.
    """
    if z <= 0:
        return 0
    if z == 1:
        return 1
    a0 = 2.0 * float(z) + coulomb_neutron_surplus(z)
    a = int(round(a0))
    target_parity = z % 2
    if a % 2 != target_parity:
        a += 1 if a0 >= a else -1
    return max(a, z)


def stable_mass_number_for_charge(z: int) -> int:
    """Neutral-atom mass number: sparse overrides, else Coulomb A(Z) law."""
    if z == 0:
        return 0
    if z in STABLE_A_OVERRIDES:
        return STABLE_A_OVERRIDES[z]
    return derived_stable_mass_number(z)


# Back-compat alias used by nuclear_curvature_binding / derived_chemistry.
STABLE_A_BY_Z: dict[int, int] = {
    z: stable_mass_number_for_charge(z)
    for z in (
        1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 14, 17, 26, 29, 32,
    )
}

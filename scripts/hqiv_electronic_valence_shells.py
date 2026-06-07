#!/usr/bin/env python3
"""
Electronic valence shell indices on the HQIV Compton ladder (s, p, …).

Nuclear drum shells ``m_nuc(A)`` (inside-ratio readout) are **not** the same as
electronic Fresnel indices used in LiH / heavy-hydride chemistry:

  • H 1s  → ``m = 1``
  • Period-2 valence (Li…Ne) 2s / 2p → ``m = 4`` / ``m = 3`` (Lean ``(4,3,1)``)

Python witness for ``Hqiv.QuantumChemistry.DynamicBindingChart`` /
``BondedHorizonCasimirMoleculeBench`` atomization splits.
"""

from __future__ import annotations

import math
from typing import Literal

import hqiv_lean_physics_primitives as lean
from fragment_aware_bonded_horizon import FragmentConfig

# Lean LiH / heavy-hydride Compton slots (`compare_quantum_chem_witnesses.py`).
ELECTRONIC_M_S_PERIOD2 = 4
ELECTRONIC_M_P_PERIOD2 = 3
ELECTRONIC_M_H_1S = 1

ShellLabel = Literal["1s", "2s", "2p", "none"]


def electronic_compton_shells(z: int) -> tuple[int, int | None]:
    """
    Compton ladder indices for valence electrons (not nuclear ``m_nuc``).

    H and He-like use ``(1, None)``; period-2 covalent centres use ``(4, 3)``.
    """
    if z <= 1:
        return ELECTRONIC_M_H_1S, None
    if z <= 10:
        return ELECTRONIC_M_S_PERIOD2, ELECTRONIC_M_P_PERIOD2
    return ELECTRONIC_M_S_PERIOD2, ELECTRONIC_M_P_PERIOD2


def electronic_shell_label(z: int, *, slot: str = "s") -> ShellLabel:
    """Chemist shell label for readout witnesses (``1s``, ``2s``, ``2p``)."""
    if z <= 1:
        return "1s"
    if z <= 2:
        return "1s" if slot == "s" else "none"
    if slot == "p":
        return "2p"
    return "2s"


def compton_slot_s2_weights(triplet: tuple[int, int, int]) -> tuple[float, float, float]:
    """S² degeneracy weights on Compton slots (s, p, light): ``(1, 2ℓ+1, 1)``."""
    if lean.compton_p_shell_active(triplet):
        return (1.0, 3.0, 1.0)
    return (1.0, 1.0, 1.0)


def eta_p_s2_weighted(
    angles_rad: tuple[float, float, float],
    triplet: tuple[int, int, int],
    *,
    phase_theta: float = math.pi / 2.0,
) -> float:
    """
    Phase participation η = θ/θ₀ with S² weights on the (s, p, H) slots.

    Replaces a plain mean-angle η when the p shell is active (``2ℓ+1 = 3``).
    """
    if not angles_rad:
        return 0.0
    weights = compton_slot_s2_weights(triplet)
    etas = [min(max(a, 0.0) / phase_theta, 1.0) for a in angles_rad]
    wsum = sum(weights)
    if wsum <= 0.0:
        return 0.0
    return sum(w * e for w, e in zip(weights, etas)) / wsum


def chemistry_compton_triplet(
    fragments: tuple[FragmentConfig, ...],
) -> tuple[int, int, int]:
    """Lean ``DynamicBindingChart`` electronic triplets."""
    if all(f.z_nuclear == 1 for f in fragments):
        return (ELECTRONIC_M_H_1S, ELECTRONIC_M_H_1S, ELECTRONIC_M_H_1S)
    if len(fragments) == 2 and fragments[0].z_nuclear == fragments[1].z_nuclear:
        if fragments[0].z_nuclear > 1:
            return (
                ELECTRONIC_M_S_PERIOD2,
                ELECTRONIC_M_S_PERIOD2,
                ELECTRONIC_M_S_PERIOD2,
            )
    if any(f.z_nuclear == 1 for f in fragments):
        return (
            ELECTRONIC_M_S_PERIOD2,
            ELECTRONIC_M_P_PERIOD2,
            ELECTRONIC_M_H_1S,
        )
    return (
        ELECTRONIC_M_S_PERIOD2,
        ELECTRONIC_M_S_PERIOD2,
        ELECTRONIC_M_S_PERIOD2,
    )


def lean_atomization_horizon_split(
    name: str,
    fragments: tuple[FragmentConfig, ...],
) -> tuple[int, int, int] | None:
    """
    Lean ``BondedHorizonCasimirMoleculeBench`` electron partitions.

    Returns ``(n_total, n_heavy_fragment, n_light_fragment)`` for
    ``bond_horizon_surplus_dimless`` when defined; otherwise ``None``.
    """
    key = name.upper()
    electrons = tuple(max(f.electrons, 0) for f in fragments)
    total = sum(electrons)
    if key == "H2O":
        heavy = next(f.electrons for f in fragments if f.z_nuclear > 1)
        light = total - heavy
        return total, heavy, light
    if key == "CH4":
        heavy = fragments[0].electrons
        light = total - heavy
        return total, heavy, light
    if key == "NH3":
        heavy = fragments[0].electrons
        light = total - heavy
        return total, heavy, light
    return None


def period2_valence_electron_count(z: int) -> int:
    """Valence electrons outside the He core (O → 6, N → 5, C → 4)."""
    if z <= 2:
        return z
    return min(z, 10) - 2


def centre_vsepr_lone_pair_count(z_heavy: int, n_bonds_at_centre: int) -> int:
    """VSEPR lone-pair count ``(V - X) / 2`` for period-2 hydrides / water / ammonia."""
    if z_heavy < 3 or z_heavy > 10 or n_bonds_at_centre < 1:
        return 0
    valence = period2_valence_electron_count(z_heavy)
    bonding = 2 * n_bonds_at_centre
    return max(0, (valence - bonding) // 2)


def centre_lone_pair_surplus_dress(
    z_heavy: int,
    n_bonds_at_centre: int,
    eta_p_linear: float,
) -> float:
    """
    Dress atomization surplus for nonbonding 2p pairs on the heavy centre.

    Lean ``dynamicLonePairSurplusDress``: ``1 + (4/8) · n_LP · η_p``.
    """
    n_lp = centre_vsepr_lone_pair_count(z_heavy, n_bonds_at_centre)
    if n_lp <= 0:
        return 1.0
    return 1.0 + lean.STRONG_CHANNEL_FRACTION * float(n_lp) * eta_p_linear


def hyperclosure_surplus_dress(n_centre_bonds: int) -> float:
    """
    Bent-centre hyperclosure (H₂O-style two O–H contacts).

    Lean ``dynamicBentHyperclosureDress``.
    """
    if n_centre_bonds == 2:
        return 1.0 + lean.STRONG_CHANNEL_FRACTION * 0.25
    return 1.0

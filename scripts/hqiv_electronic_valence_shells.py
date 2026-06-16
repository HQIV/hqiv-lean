#!/usr/bin/env python3
"""
Electronic valence shell indices on the HQIV Compton ladder (s, p, …).

Nuclear drum shells ``m_nuc(A)`` (inside-ratio readout) are **not** the same as
electronic Fresnel indices used in LiH / heavy-hydride chemistry:

  • H 1s  → ``m = 1``
  • Period-n valence s / p → ``tuftHeavyChartShell + (n−2)`` / ``tuftStrongChartShell + (n−2)``
  • Period-2 default (Lean ``ElectronicValenceFromTuftChart``): ``(4, 3, 1)``

Python witness for ``Hqiv.QuantumChemistry.DynamicBindingChart`` /
``BondedHorizonCasimirMoleculeBench`` atomization splits.
"""

from __future__ import annotations

import math
from typing import Any, Literal

import hqiv_lean_physics_primitives as lean
from fragment_aware_bonded_horizon import FragmentConfig

# Lean LiH / heavy-hydride Compton slots (`compare_quantum_chem_witnesses.py`).
ELECTRONIC_M_S_PERIOD2 = 4
ELECTRONIC_M_P_PERIOD2 = 3
ELECTRONIC_M_H_1S = 1

ShellLabel = Literal["1s", "2s", "2p", "3s", "3p", "none"]

_HALOGEN_Z = frozenset({9, 17, 35, 53})
_ALKALI_Z = frozenset({3, 11, 19, 37})


def chemical_period(z: int) -> int:
    """Principal period from nuclear charge (no fitted tables)."""
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
    """Valence electrons outside the previous noble-gas core."""
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


def period2_valence_electron_count(z: int) -> int:
    """Valence electrons outside the He core (O → 6, N → 5, C → 4)."""
    if z <= 2:
        return z
    return min(z, 10) - 2


def electronic_compton_shells(z: int) -> tuple[int, int | None]:
    """
    Compton ladder indices for valence electrons (not nuclear ``m_nuc``).

    Period-2 centres use ``(4, 3)``; each subsequent period steps one rung on
    the TUFT heavy/strong chart (``tuftHadronRadialShell`` offset).
    """
    if z <= 1:
        return ELECTRONIC_M_H_1S, None
    offset = max(0, chemical_period(z) - 2)
    m_s = ELECTRONIC_M_S_PERIOD2 + offset
    m_p = ELECTRONIC_M_P_PERIOD2 + offset
    return m_s, m_p


def electronic_shell_label(z: int, *, slot: str = "s") -> ShellLabel:
    """Chemist shell label for readout witnesses."""
    if z <= 1:
        return "1s"
    period = chemical_period(z)
    if slot == "p":
        return "2p" if period == 2 else "3p" if period == 3 else "none"
    if period == 2:
        return "2s"
    if period == 3:
        return "3s"
    return "none"


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


def is_alkali_halide_diatomic(fragments: tuple[FragmentConfig, ...]) -> bool:
    """1:1 alkali–halogen salt (distinct from metal hydrides)."""
    if len(fragments) != 2:
        return False
    a, b = fragments
    return (a.z_nuclear in _ALKALI_Z and b.z_nuclear in _HALOGEN_Z) or (
        b.z_nuclear in _ALKALI_Z and a.z_nuclear in _HALOGEN_Z
    )


def is_ionic_diatomic(fragments: tuple[FragmentConfig, ...]) -> bool:
    """Alkali–halogen / metal–hydride ionic pairs (no fitted weights)."""
    if len(fragments) != 2:
        return False
    import hqiv_curvature_contact_network as ccn
    import hqiv_ionic_bond_network as ibn

    a, b = fragments
    return (
        ibn.classify_bond_kind("", a.z_nuclear, b.z_nuclear)
        == ccn.ContactKind.IONIC_BOND
    )


def chemistry_compton_triplet(
    fragments: tuple[FragmentConfig, ...],
) -> tuple[int, int, int]:
    """Lean ``DynamicBindingChart`` electronic triplets."""
    if all(f.z_nuclear == 1 for f in fragments):
        return (ELECTRONIC_M_H_1S, ELECTRONIC_M_H_1S, ELECTRONIC_M_H_1S)
    if len(fragments) == 2 and is_alkali_halide_diatomic(fragments):
        import hqiv_ionic_bond_network as ibn

        a, b = fragments
        cation, anion = ibn.ionic_fragments_from_neutral_pair(
            a.label,
            a.z_nuclear,
            a.electrons,
            b.label,
            b.z_nuclear,
            b.electrons,
        )
        m_s, _ = electronic_compton_shells(cation.z_nuclear)
        _, m_p = electronic_compton_shells(anion.z_nuclear)
        return (m_s, m_p, ELECTRONIC_M_H_1S)
    if len(fragments) == 2 and fragments[0].z_nuclear == fragments[1].z_nuclear:
        if fragments[0].z_nuclear > 1:
            m_s, _ = electronic_compton_shells(fragments[0].z_nuclear)
            return (m_s, m_s, m_s)
    if len(fragments) == 2 and not any(f.z_nuclear == 1 for f in fragments):
        a, b = fragments
        z_light, z_heavy = (
            (a.z_nuclear, b.z_nuclear)
            if a.z_nuclear <= b.z_nuclear
            else (b.z_nuclear, a.z_nuclear)
        )
        m_s_h, m_p_h = electronic_compton_shells(z_heavy)
        m_s_l, _ = electronic_compton_shells(z_light)
        return (m_s_h, m_p_h, m_s_l)
    if any(f.z_nuclear == 1 for f in fragments):
        heavy = max(fragments, key=lambda f: f.z_nuclear)
        if len(fragments) == 2 and chemical_period(heavy.z_nuclear) == 3:
            m_s, m_p = electronic_compton_shells(heavy.z_nuclear)
            return (m_s, m_p, ELECTRONIC_M_H_1S)
        return (ELECTRONIC_M_S_PERIOD2, ELECTRONIC_M_P_PERIOD2, ELECTRONIC_M_H_1S)
    heavy = max(fragments, key=lambda f: f.z_nuclear)
    m_s, _ = electronic_compton_shells(heavy.z_nuclear)
    return (m_s, m_s, m_s)


def homonuclear_bond_order(z: int) -> int:
    """σ-bond order from valence filling (N≡N → 3, O=O → 2, F−F → 1)."""
    valence = valence_electron_count(z)
    return max(1, min(3, 8 - valence))


def homonuclear_open_shell_dimer(z: int) -> bool:
    """Triplet / diradical homonuclear dimers (O₂, S₂): even valence, double bond."""
    valence = valence_electron_count(z)
    return valence >= 6 and valence % 2 == 0 and homonuclear_bond_order(z) == 2


def is_homonuclear_halogen(z: int) -> bool:
    return z in _HALOGEN_Z


def heteronuclear_bond_order(z_light: int, z_heavy: int) -> int:
    """
    Heteronuclear σ+π bond order from valence bookkeeping (no tables).

    Period-2 pairs: ``max(1, min(3, v_l + v_h − 6))`` (C≡N → 3, C≡O → 3).
    General: ``max(1, min(3, v_h − v_l + 1))``.
    """
    v_l = valence_electron_count(z_light)
    v_h = valence_electron_count(z_heavy)
    if chemical_period(z_light) == chemical_period(z_heavy) == 2:
        return max(1, min(3, v_l + v_h - 6))
    return max(1, min(3, v_h - v_l + 1))


def covalent_bond_order(z_i: int, z_j: int) -> int:
    """Bond order on one covalent contact (homonuclear or heteronuclear)."""
    if z_i <= 1 or z_j <= 1:
        return 1
    if z_i == z_j:
        return homonuclear_bond_order(z_i)
    z_light, z_heavy = (z_i, z_j) if z_i <= z_j else (z_j, z_i)
    return heteronuclear_bond_order(z_light, z_heavy)


def has_heavy_heavy_bond(
    fragments: tuple[FragmentConfig, ...],
    bonds: tuple[Any, ...],
) -> bool:
    """True when any bond joins two non-hydrogen centres."""
    for bond in bonds:
        zi = fragments[bond.frag_i].z_nuclear
        zj = fragments[bond.frag_j].z_nuclear
        if zi > 1 and zj > 1:
            return True
    return False


def max_heavy_heavy_bond_order(
    fragments: tuple[FragmentConfig, ...],
    bonds: tuple[Any, ...],
) -> int:
    """Maximum covalent bond order among heavy–heavy contacts."""
    order = 1
    for bond in bonds:
        zi = fragments[bond.frag_i].z_nuclear
        zj = fragments[bond.frag_j].z_nuclear
        if zi > 1 and zj > 1:
            order = max(order, covalent_bond_order(zi, zj))
    return order


def conjugated_heavy_heavy_surplus_dress(
    fragments: tuple[FragmentConfig, ...],
    bonds: tuple[Any, ...],
) -> float:
    """
    Reduce atomization surplus when π-conjugated heavy–heavy bonds are present.

    Heteronuclear (HCN): ``1 / sqrt(bond_order)`` graph hyperclosure factor.
    Homonuclear alkynyl (C₂H₂): same base dress times
    ``sqrt(1 + (n_heavy − 1) / bond_order)`` for the dual-centre σ frame.
    """
    if len(fragments) <= 2:
        return 1.0
    if len(fragments) == 2 and is_ionic_diatomic(fragments):
        return 1.0
    if not has_heavy_heavy_bond(fragments, bonds):
        return 1.0
    order = max_heavy_heavy_bond_order(fragments, bonds)
    base = 1.0 / math.sqrt(float(order))
    homo_at_max = False
    for bond in bonds:
        zi = fragments[bond.frag_i].z_nuclear
        zj = fragments[bond.frag_j].z_nuclear
        if zi > 1 and zj > 1 and zi == zj and covalent_bond_order(zi, zj) == order:
            homo_at_max = True
            break
    if homo_at_max:
        n_heavy = sum(1 for f in fragments if f.z_nuclear > 1)
        return base * math.sqrt(1.0 + (n_heavy - 1) / float(order))
    return base


def heavy_centre_period(fragments: tuple[FragmentConfig, ...]) -> int:
    """Principal period of the heaviest fragment (for hydride routing)."""
    if not fragments:
        return 1
    return max(chemical_period(f.z_nuclear) for f in fragments)


def heavy_centre_z(fragments: tuple[FragmentConfig, ...]) -> int:
    """Nuclear charge of the heaviest fragment."""
    if not fragments:
        return 1
    return max(f.z_nuclear for f in fragments)


def use_horizon_atomization_split(
    fragments: tuple[FragmentConfig, ...],
    bonds: tuple[Any, ...],
    *,
    molecule_name: str,
) -> bool:
    """
    Route atomization through Lean bond-horizon split instead of full torus sum.

    Period-3+ hydrides with ≥3 heavy–light contacts (PH₃) overbind on the raw
    torus readout; bent two-fold centres (H₂S, H₂O) stay on atomization + dress.
    """
    split = lean_atomization_horizon_split(molecule_name, fragments)
    if split is None:
        return False
    if has_heavy_heavy_bond(fragments, bonds):
        return False
    period = heavy_centre_period(fragments)
    n_bonds = len(bonds)
    if period >= 3 and n_bonds >= 3:
        return True
    return False


def homonuclear_dissociation_surplus_dimless(
    n1: int,
    n2: int,
    z: int,
    angles: tuple[float, float, float],
) -> float:
    """
    Homonuclear diatomic dissociation surplus with bond-order / open-shell routing.

    Closed-shell high-order (N₂): ``bond_horizon / (bond_order · (1 + (4/8)/constructiveValleyCap))``.
    Open-shell triplet (O₂): ``bond_horizon / (2 · bond_order^(2 + (4/8)/constructiveValleyCap))`` [scaffold].
    Halogens (F₂, Cl₂): ``bond_order · covalent_dimer / (valence − offset)
    / (1 + (4/8)/(m_s2 + period − 2))``.
    """
    from bonded_horizon_casimir_float import (
        DEFAULT_UUD_ANGLES_RAD,
        bond_horizon_surplus_dimless,
        covalent_dimer_two_electron_surplus_dimless,
    )

    bond_order = homonuclear_bond_order(z)
    full = bond_horizon_surplus_dimless(n1 + n2, n1, n2, angles)
    strong = lean.STRONG_CHANNEL_FRACTION
    cap = lean.CONSTRUCTIVE_VALLEY_CAP
    if is_homonuclear_halogen(z):
        valence = valence_electron_count(z)
        dimer = covalent_dimer_two_electron_surplus_dimless(DEFAULT_UUD_ANGLES_RAD)
        period = chemical_period(z)
        denom_offset = 4 if period == 2 else 5
        surplus = bond_order * dimer / max(1, valence - denom_offset)
        chart_denom = float(ELECTRONIC_M_S_PERIOD2 + max(period, 2) - 2)
        return surplus / (1.0 + strong / chart_denom)
    if homonuclear_open_shell_dimer(z):
        exponent = 2.0 + strong / cap
        return full / (2.0 * bond_order**exponent)
    return full / (bond_order * (1.0 + strong / cap))


def homonuclear_h2_dissociation_surplus_dimless(
    angles: tuple[float, float, float],
) -> float:
    """
    H₂ covalent-dimer dissociation with 1s-ladder weak-channel closure.

    ``covalentDimer / (1 + (4/8)/(2·(m_H + m_s(period 2))))`` — same strong
    fraction as bent hyperclosure, anchored on the H₂ Compton ladder.
    """
    from bonded_horizon_casimir_float import covalent_dimer_two_electron_surplus_dimless

    base = covalent_dimer_two_electron_surplus_dimless(angles)
    ladder_closure = 1.0 + lean.STRONG_CHANNEL_FRACTION / (
        2.0 * float(ELECTRONIC_M_H_1S + ELECTRONIC_M_S_PERIOD2)
    )
    return base / ladder_closure


def heteronuclear_atomization_bond_order(z_light: int, z_heavy: int) -> float:
    """
    Heteronuclear diatomic atomization divisor (CO).

    Octet closure ``max(1, min(3, v_l + v_h − 8))`` plus half a strong-channel
    step toward the conjugated σ+π order when π exceeds octet — CO → 2.25.
    """
    v_l = valence_electron_count(z_light)
    v_h = valence_electron_count(z_heavy)
    octet = max(1, min(3, v_l + v_h - 8))
    conjugated = float(heteronuclear_bond_order(z_light, z_heavy))
    if conjugated > octet:
        return octet + (lean.STRONG_CHANNEL_FRACTION / 2.0) * (conjugated - octet)
    return float(octet)


def heteronuclear_diatomic_atomization_surplus_dimless(
    z1: int,
    z2: int,
    e1: int,
    e2: int,
    angles: tuple[float, float, float],
) -> float:
    """
    Two heavy-atom atomization (CO): bond-horizon split / atomization bond order.

    Uses ``heteronuclear_atomization_bond_order`` — CO → 2.25 — distinct from
    full conjugated σ+π bond order used in surplus dress on polyatomics.
    """
    from bonded_horizon_casimir_float import bond_horizon_surplus_dimless

    z_light, z_heavy = (z1, z2) if z1 <= z2 else (z2, z1)
    e_light, e_heavy = (e1, e2) if z1 <= z2 else (e2, e1)
    bond_order = heteronuclear_atomization_bond_order(z_light, z_heavy)
    return bond_horizon_surplus_dimless(
        e1 + e2,
        e_heavy,
        e_light,
        angles,
    ) / bond_order


def ionic_inert_core_surplus_dress(
    cation_z: int,
    anion_z: int,
    cation_e: int,
    anion_e: int,
    *,
    bond_length_angstrom: float | None = None,
) -> float:
    """
    Scale full ionic surplus by active valence fraction over inert cores.

    Period-2 salts (LiF): linear ``n_val / n_total``.
    Period ≥ 3 (NaCl): ``(n_val / n_total) · sqrt(1/(1+d/a₀))`` — inert cores plus
    long-bond lattice contact weight from ``hqiv_ionic_bond_network``.
    """
    from fragment_aware_bonded_horizon import BOHR_RADIUS_ANGSTROM

    n_val = valence_electron_count(cation_z) + valence_electron_count(anion_z)
    n_tot = max(cation_e + anion_e, 1)
    frac = n_val / n_tot
    period = max(chemical_period(cation_z), chemical_period(anion_z))
    if period <= 2:
        return frac
    if bond_length_angstrom is None or bond_length_angstrom <= 0.0:
        return frac * frac
    lattice = 1.0 / (1.0 + bond_length_angstrom / BOHR_RADIUS_ANGSTROM)
    return frac * math.sqrt(lattice)


def period_hydride_dissociation_dress(z_heavy: int) -> float:
    """
    Period ≥ 3 H–X dissociation dress from TUFT Compton rung step.

    Base ``m_s(period 2) / m_s(heavy)``; first period-3 rung (HCl) adds s–p
    σ-hole coupling ``(1 − 4/8/m_s)(1 − 4/8/(m_s+m_p))`` on the elevated triplet.
    """
    period = chemical_period(z_heavy)
    if period <= 2:
        return 1.0
    m_s, m_p = electronic_compton_shells(z_heavy)
    dress = ELECTRONIC_M_S_PERIOD2 / float(m_s)
    if period == 3 and m_p is not None:
        dress *= 1.0 - lean.STRONG_CHANNEL_FRACTION / float(m_s)
        dress *= 1.0 - lean.STRONG_CHANNEL_FRACTION / float(m_s + m_p)
    return dress


def period_hydride_atomization_dress(z_heavy: int) -> float:
    """
    Period ≥ 3 hydride atomization dress from TUFT Compton rung step.

    Same ``m_s(period 2) / m_s(heavy)`` as dissociation; applied on horizon-split
    trihydrides (PH₃) where raw torus surplus overbinds.
    """
    period = chemical_period(z_heavy)
    if period <= 2:
        return 1.0
    m_s, _ = electronic_compton_shells(z_heavy)
    return ELECTRONIC_M_S_PERIOD2 / float(m_s)


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
    if key == "H2S":
        heavy = next(f.electrons for f in fragments if f.z_nuclear > 1)
        light = total - heavy
        return total, heavy, light
    if key == "PH3":
        heavy = fragments[0].electrons
        light = total - heavy
        return total, heavy, light
    if key == "HCN":
        heavy = fragments[1].electrons + fragments[2].electrons
        light = fragments[0].electrons
        return total, heavy, light
    if key == "C2H2":
        heavy = fragments[1].electrons + fragments[2].electrons
        light = fragments[0].electrons + fragments[3].electrons
        return total, heavy, light
    if key == "CO":
        z_light = min(fragments[0].z_nuclear, fragments[1].z_nuclear)
        e_light = next(f.electrons for f in fragments if f.z_nuclear == z_light)
        e_heavy = total - e_light
        return total, e_heavy, e_light
    return None


def centre_vsepr_lone_pair_count(z_heavy: int, n_bonds_at_centre: int) -> int:
    """
    VSEPR lone-pair count on heavy centres.

    Period 2 (Lean ``centreLonePairCount``): ``(V − 2X) / 2`` with ``X`` bond pairs.
    Period 3 trihydrides (PH₃): standard ``(V − X) / 2``.
    Period 3 dihydrides (H₂S): standard ``(V − X) / 2`` — two 3p lone pairs.
    """
    if n_bonds_at_centre < 1:
        return 0
    period = chemical_period(z_heavy)
    if period < 2 or period > 3:
        return 0
    valence = valence_electron_count(z_heavy)
    if period == 2:
        bonding = 2 * n_bonds_at_centre
    else:
        bonding = n_bonds_at_centre
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


def centre_coordination_graph_dress(n_centre_bonds: int) -> float:
    """
    Polyatomic centre coordination dress from ``constructiveValleyCap`` increment class.

    Trihydride (NH₃, PH₃): ``1 − 2·(4/8) / (constructiveValleyCap · n)``.
    Tetrahedral (CH₄): ``1 + 2·(4/8) / (constructiveValleyCap · n)``.
    """
    if n_centre_bonds not in (3, 4):
        return 1.0
    step = 2.0 * lean.STRONG_CHANNEL_FRACTION / (
        lean.CONSTRUCTIVE_VALLEY_CAP * float(n_centre_bonds)
    )
    if n_centre_bonds == 3:
        return 1.0 - step
    return 1.0 + step


def hyperclosure_surplus_dress(n_centre_bonds: int, z_heavy: int | None = None) -> float:
    """
    Bent-centre hyperclosure (H₂O-style two heavy–light contacts).

    Lean ``dynamicBentHyperclosureDress`` uses ``(4/8)/4`` when ``n_centre_bonds = 2``.
    Period ≥ 3 dihydrides (H₂S): ``(4/8)/2`` — **python_scaffold** until Lean extends
    ``CentreGeometryFromTuft`` (see ``hqiv_chemistry_binding_routes``).
    """
    if n_centre_bonds != 2:
        return 1.0
    channel = 0.25
    if z_heavy is not None and chemical_period(z_heavy) >= 3:
        channel = 0.5
    return 1.0 + lean.STRONG_CHANNEL_FRACTION * channel

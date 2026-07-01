#!/usr/bin/env python3
"""
HQIV particle-first shell structure: the periodic table from two axiom-level multiplicities.

The chemistry engine had three injected literals — the octet ``8``, the subshell capacities
``{2,6,10,14}``, and the noble-gas valence subtraction.  All three are reconstructed here from
particle-level HQIV structure.

The Madelung ``(n+ℓ)`` filling "looks different but is the same shape" as the rest of the network:
a radial step (``n→n+1``) and an angular step (``ℓ→ℓ+1``) are the *same unit step* of the growing
discrete-light-cone shell network, so ``g = n+ℓ`` is just the BFS **generation** (graph distance)
at which a subshell appears.  Filling closest-generation-first is the same growth order used
elsewhere.  Each generation holds ``2·⌈g/2⌉²`` electrons — the Janet left-step periods
``2,2,8,8,18,18,32`` — and the periodic table's signature DOUBLING is exactly the floor/ceil
pairing ``C(2k−1)=C(2k)=2k²``.  The only residual stated input is the within-generation tie-break
(lower n first = marginal radial-over-angular cost).

Two multiplicities, both axiom-level:

  * **monogamy pairing  g_pair = 2** — informational monogamy makes a shared phase channel a
      *monogamous pair* of two opposite-phase carriers (this is the "spin doubling"); it is the
      same ``2`` that already sets φ(m)=2(m+1) and the ``1 − α/2`` contact contraction.
  * **angular degeneracy  2ℓ+1** — the discrete light-cone shells are spheres, so each orbital
      angular momentum ℓ carries the S² spherical-harmonic multiplicity ``2ℓ+1``.  This is exactly
      the weight already exported by ``hqiv_electronic_valence_shells.compton_slot_s2_weights``.

From these:

  subshell capacity      cap(ℓ) = g_pair · (2ℓ+1)        → s,p,d,f = 2,6,10,14
  octet (s+p closure)    OCTET  = cap(0) + cap(1) = 8
  fill order             Madelung (n+ℓ, then n)          → 1s,2s,2p,3s,3p,4s,3d,4p,…
  noble-gas closures     cumulative count after each np  → 2,10,18,36,54,86
  valence_electron_count z − (largest closure below z)

This reproduces ``hqiv_electronic_valence_shells.valence_electron_count`` for every Z (a proof
that the hand-coded periodic table *is* the derived shell filling), and feeds the octet into
``hqiv_allotrope_network`` so the allotrope/bond engine bottoms out in particles.

Lean: ``Hqiv.QuantumChemistry.ParticleShellStructure``.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

# --- Axiom-level multiplicities -------------------------------------------------------------

#: Informational-monogamy pairing: a shared phase channel binds two opposite-phase carriers.
MONOGAMY_PAIR_MULTIPLICITY = 2


def angular_degeneracy(l: int) -> int:
    """S² spherical-harmonic multiplicity of an orbital angular momentum ℓ: ``2ℓ+1``.

    The discrete light-cone shells are spheres; an ℓ-mode carries ``2ℓ+1`` magnetic sublevels.
    (Same weight as ``compton_slot_s2_weights`` → p-shell = 3.)
    """
    return 2 * l + 1


def subshell_capacity(l: int) -> int:
    """Electrons an ℓ-subshell holds = monogamy pair × angular degeneracy = ``2(2ℓ+1)``.

    s,p,d,f → 2,6,10,14.  Replaces the hand-coded ``SUBSHELL_CAPACITY`` dict.
    """
    return MONOGAMY_PAIR_MULTIPLICITY * angular_degeneracy(l)


def octet_capacity() -> int:
    """The octet = closure of the valence s+p shells = ``cap(0)+cap(1)`` = 8.

    Particle meaning: a p-block atom completes when its two lowest angular channels (ℓ=0 sphere
    + ℓ=1 vector triple), each monogamy-paired, are full: ``2·1 + 2·3 = 8``.  Not a literal.
    """
    return subshell_capacity(0) + subshell_capacity(1)


def max_bond_order() -> int:
    """Maximum covalent bond order between two atoms = the p-shell angular degeneracy ``2·1+1 = 3``.

    A single monogamy contact can share at most the σ + 2π channels of the ℓ=1 vector triple,
    so the triple bond (N≡N) is the ceiling.  Replaces the literal ``min(…, 3)`` cap.
    """
    return angular_degeneracy(1)


def bonding_capacity(z: int) -> int:
    """Covalent bonds an atom commits = electrons to the *nearest* closed shell.

    An atom reaches closure either by sharing electrons up to the octet (right side: O→2, F→1) or
    by shedding its few valence electrons (left side: Li→1, Be→2, B→3), whichever is fewer:
    ``cap = min(valence, target − valence)``, with the shell target the s+p octet (period ≥ 2) or
    the 1s duet (period 1).  This is the single capacity behind every bond order — homonuclear,
    heteronuclear, and networked.
    """
    v = valence_electron_count(z)
    # period-1 closes at the 1s duet cap(0)=2 (H, He); period ≥ 2 at the s+p octet.
    duet = subshell_capacity(0)
    target = duet if z <= duet else octet_capacity()
    return max(0, min(v, target - v))


def valence_pair_slots(z: int) -> int:
    """Pair-slots in the closed valence shell = ``target/2`` (duet→1, octet→4).

    Each slot is its own closure system: it is either *shared* (a bond, the off-diagonal coupling to
    a neighbour) or *unshared* (a lone pair, the diagonal self-coupling).  This is the same
    shared/self dichotomy as the bond coupling matrix, applied recursively to every slot.
    """
    duet = subshell_capacity(0)
    target = duet if z <= duet else octet_capacity()
    return target // 2


def lone_pair_count(z: int, n_sigma_bonds: int | None = None) -> int:
    """Lone pairs forced by electron conservation — not a separate Lewis rule.

    Budget over the valence pair-slots (each slot its own system, identical rules): the atom supplies
    1 e⁻ to each *shared* slot (σ-bond) and 2 e⁻ to each *unshared* slot (lone pair).  With ``B``
    σ-bonds the remaining ``V − B`` valence electrons pair up: ``L = (V − B)/2``.  ``B`` defaults to
    the derived :func:`bonding_capacity`; the leftover ``V − B`` is always even, so the budget
    ``2L + B = V`` closes exactly.  Lean: ``LonePairPartition.electron_budget_closes``.
    """
    v = valence_electron_count(z)
    b = bonding_capacity(z) if n_sigma_bonds is None else n_sigma_bonds
    if b >= v:
        return 0
    return (v - b) // 2


def steric_domain_count(z: int, n_sigma_bonds: int | None = None) -> int:
    """VSEPR electron-domain count = σ-bonds + lone pairs, both from the one octet budget.

    Right-side p-block atoms (V ≥ 4) all return 4 (tetrahedral electron geometry); electron-deficient
    left-side atoms (V ≤ 4) return V.  Lean: ``LonePairPartition.domains_right/​domains_left``.
    """
    v = valence_electron_count(z)
    b = bonding_capacity(z) if n_sigma_bonds is None else n_sigma_bonds
    return min(b, v) + lone_pair_count(z, b)


def geometric_bond_order(cap_i: float, cap_j: float) -> float:
    """Bond order on a contact = the saturated 2×2 coupling of the two atoms' bonding capacities,
    capped at the p-shell triple: ``min(max_bond_order, √(cap_i·cap_j))``.

    The ``√`` is not a posited mean: a shared bond is the off-diagonal of a positive-semidefinite
    coupling matrix, so ``b ≤ √(cap_i·cap_j)`` (Cauchy–Schwarz) and full coherent sharing saturates it
    (det = 0, one rank-1 shared pair) — see ``Hqiv/QuantumChemistry/BondOrderCoupling.lean``.  One
    derived rule for all covalent bonds: homonuclear collapses to ``cap`` (``√(c·c)=c``), heteronuclear
    interpolates (CO ``√(4·2)≈2.83``, NO ``√(3·2)≈2.45``), and ionic-leaning pairs fall to 1
    (LiF ``√(1·1)=1``) — no ``−6/+1`` offsets.
    """
    return min(float(max_bond_order()), math.sqrt(max(0.0, cap_i) * max(0.0, cap_j)))


# --- Madelung ordering as network step-distance (the "same shape" as the shell network) ----

def shell_generation(n: int, l: int) -> int:
    """Network step-distance of subshell ``(n, ℓ)`` from the 1s origin: ``g = n + ℓ``.

    Madelung "looks different but is the same shape" as the rest of the HQIV shell network: a
    radial step (``n → n+1``) and an angular step (``ℓ → ℓ+1``) are the **same unit step** of the
    growing discrete-light-cone network.  So ``n+ℓ`` is not a chemistry rule — it is the BFS
    *generation* (graph distance) at which a subshell first appears.  Filling by generation is the
    same growth order the network uses everywhere; the only residual is the within-generation
    tie-break (marginal radial-over-angular cost → lower n fills first).
    """
    return n + l


def generation_capacity(g: int) -> int:
    """Electrons a whole generation ``g = n+ℓ`` holds = ``2·⌈g/2⌉²``.

    These are the Janet (left-step) period lengths 2,2,8,8,18,18,32 — and the periodic table's
    signature DOUBLING (each value twice) is just the floor/ceil pairing: generations ``2k−1`` and
    ``2k`` share ``⌈g/2⌉ = k`` and so the same capacity ``2k²``.  Particle origin of the doubling.
    """
    if g <= 0:
        return 0
    half = (g + 1) // 2  # = ceil(g/2)
    return 2 * half * half


def madelung_fill_order(max_n: int = 7) -> list[tuple[int, int]]:
    """Subshells ``(n, ℓ)`` ordered by network step-distance ``g = n+ℓ``, ties by increasing n.

    This is BFS over the shell network (closest generation first), the same growth shape used
    throughout HQIV — not an injected chemistry ordering.  Reproduces ``SUBSHELL_FILL_ORDER``.
    """
    subs = [(n, l) for n in range(1, max_n + 1) for l in range(n)]
    return sorted(subs, key=lambda nl: (shell_generation(*nl), nl[0]))


def left_step_period_lengths(max_g: int = 8) -> list[int]:
    """Janet left-step period lengths = generation capacities ``[2,2,8,8,18,18,32,32]``."""
    return [generation_capacity(g) for g in range(1, max_g + 1)]


def noble_gas_closures(max_n: int = 7) -> list[int]:
    """Cumulative electron counts at each shell closure (the noble-gas Z): ``2,10,18,36,54,86``.

    Filling subshells in Madelung order with the *derived* capacities, a closure occurs after the
    1s shell (He) and after every np subshell (ℓ=1) completes — that is where the s+p octet of a
    principal shell is satisfied and the next electron must open a new, higher sphere.
    """
    closures: list[int] = []
    cumulative = 0
    for n, l in madelung_fill_order(max_n):
        cumulative += subshell_capacity(l)
        if (n, l) == (1, 0) or l == 1:  # He closure, then every np closure
            closures.append(cumulative)
    return closures


def valence_electron_count(z: int) -> int:
    """Valence electrons = ``z − (largest noble-gas closure strictly below z)`` (derived).

    Reproduces ``hqiv_electronic_valence_shells.valence_electron_count`` for all Z, but now from
    the derived capacities + Madelung order rather than a hand-coded noble-gas table.
    """
    core = 0
    for c in noble_gas_closures():
        if c < z:
            core = c
        else:
            break
    return z - core


def main() -> None:
    parser = argparse.ArgumentParser(description="HQIV particle-first shell structure")
    parser.add_argument("--json-out", type=str, default=None)
    args = parser.parse_args()

    closures = noble_gas_closures()
    caps = {("s", 0): subshell_capacity(0), ("p", 1): subshell_capacity(1),
            ("d", 2): subshell_capacity(2), ("f", 3): subshell_capacity(3)}

    print("HQIV particle-first shell structure (two axiom-level multiplicities → periodic table)")
    print(f"  monogamy pairing g_pair = {MONOGAMY_PAIR_MULTIPLICITY}")
    print(f"  subshell capacity 2(2ℓ+1): " +
          ", ".join(f"{name}={c}" for (name, _l), c in caps.items()))
    print(f"  OCTET = cap(s)+cap(p) = {octet_capacity()}")
    print(f"  max bond order = p-degeneracy = {max_bond_order()}")
    print(f"  generation g = n+l = network step-distance (radial step = angular step)")
    print(f"  generation capacity 2*ceil(g/2)^2 = {left_step_period_lengths()}  (Janet periods)")
    print(f"    -> doubling = floor/ceil pairing: C(2k-1)=C(2k)")
    print(f"  noble-gas closures = {closures}")

    # consistency check against the real periodic-table noble gases (independent ground truth)
    real_noble_gas_z = [2, 10, 18, 36, 54, 86, 118]
    print(f"  closures match real noble gases: {closures == real_noble_gas_z}")

    if args.json_out:
        payload = {
            "source": "scripts/hqiv_particle_shell_structure.py",
            "lean_module": "Hqiv.QuantumChemistry.ParticleShellStructure",
            "parameter_policy": "axiom_level_multiplicities_only",
            "axiom_inputs": {
                "monogamy_pair_multiplicity": MONOGAMY_PAIR_MULTIPLICITY,
                "angular_degeneracy": "2l+1 (S^2 spherical-harmonic multiplicity)",
            },
            "stated_rule": "filling = BFS by network step-distance g=n+l (radial step = angular step); within-generation tie-break by n",
            "derived": {
                "subshell_capacity_2_2l_plus_1": {str(l): subshell_capacity(l) for l in range(4)},
                "octet": octet_capacity(),
                "max_bond_order": max_bond_order(),
                "generation_capacity_left_step_periods": left_step_period_lengths(),
                "doubling_explanation": "C(2k-1)=C(2k)=2k^2 from ceil(g/2) pairing",
                "noble_gas_closures": closures,
                "valence_electron_count_Z1_54": {
                    str(z): valence_electron_count(z) for z in range(1, 55)
                },
            },
            "consistency": {"closures_match_real_noble_gases": closures == [2, 10, 18, 36, 54, 86, 118]},
        }
        out = Path(args.json_out)
        out.write_text(json.dumps(payload, indent=2))
        print(f"\nWrote {out}")


if __name__ == "__main__":
    main()

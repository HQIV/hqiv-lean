#!/usr/bin/env python3
"""
Post-α nuclear geometry: sphere touching on the ⁴He compound surface.

Physical caveats addressed in this version (per review):
- Protons and neutrons have different effective strong-interaction "diameters"
  → different contact capacities and strengths per facet.
- "Three neutrons can't touch" on the same triangular facet geometry used by protons
  (Pauli + geometry). Neutrons use inter-facet or far positions with reduced multiplicity.
- Avoid double-counting well depths: the base cluster binding comes from the
  composite-trace / inside curvature. Extra contacts only modulate an *incremental*
  surface term. Non-touching nucleons (higher shells) get a decaying participation
  factor (open question: how much they still deepen the collective well via mean-field
  or extended Casimir surfaces).
- Non-touching nucleons: fractional participation that falls with "shell distance"
  from the α core.

This is still a diagnostic / exploration model. The Lean version in HQIVNuclei should
eventually reflect the same physical distinctions once the open questions are closed.

Lean target: generalize `bbnProtonFacetTouches` / `postAlphaOutsideValleyCountEffective`
beyond the previous A=7 special cases, with separate p/n contact rules.
"""

from __future__ import annotations

from dataclasses import dataclass

import hqiv_bbn_abundances as bbn

ALPHA_CORE_N = 2
ALPHA_TETRAHEDRAL_FACETS = 4

# Different effective contact geometry for p vs n (different strong diameters)
PROTON_FACET_VERTEX_CONTACTS = 3          # full triangular facet for a proton
NEUTRON_MAX_PER_FACET = 1                 # "three neutrons can't touch" on same triangle
NEUTRON_FACET_CONTACTS = 1                # reduced multiplicity
FAR_NEUTRON_POINT_CONTACTS = 1
FAR_NEUTRON_TOUCH_WEIGHT = bbn.STRONG_CHANNEL_FRACTION  # 4/8

CONSTRUCTIVE_VALLEY_CAP = 6
VALLEY_HE4 = 6

# Participation of non-touching nucleons in the collective well depth
# (open question — this is a tunable diagnostic decay)
def non_touching_participation(shell_distance: int) -> float:
    """Fractional contribution of a nucleon that does not directly touch the α core.
    shell_distance = 0 for direct facet/far contacts, 1 for next shell, etc.
    """
    if shell_distance <= 0:
        return 1.0
    return 1.0 / (1.0 + 0.5 * shell_distance)   # example decay; can be derived from Casimir later


@dataclass(frozen=True)
class ProtonFacetTouch:
    facet_idx: int
    contact_count: int = PROTON_FACET_VERTEX_CONTACTS


@dataclass(frozen=True)
class FarNeutronTouch:
    neutron_idx: int
    contact_count: int = FAR_NEUTRON_POINT_CONTACTS


def post_alpha_extra_neutrons(A: int, Z: int) -> int:
    n = A - Z
    return max(0, n - ALPHA_CORE_N)


def bbn_proton_facet_touches(A: int, Z: int) -> tuple[ProtonFacetTouch, ...]:
    """
    Staged / generalized proton assignment to α facets (for generalization from ⁵Li/⁵Be).

    Key physical refinement for the 5-body case and beyond:
    - The very first proton added to a new face does NOT instantly get the full 3 vertex contacts.
    - It starts with partial occupation (1 contact for the 5th nucleon on the tetrahedron).
    - As more protons are assigned to faces (higher A), occupation per face builds toward 3.
    - This avoids the discontinuous jump that the previous "full face immediately" model had for ⁵Li.

    Current staged rule (simple linear ramp for diagnostic purposes):
      contacts_per_occupied_face = min(3, 1 + extra_protons_on_that_face)
    For the absolute first extra proton overall (⁵Li), it gets 1 contact.
    """
    if A <= 4:
        return ()

    extra_protons = max(0, Z - 2)
    n_faces = min(extra_protons, ALPHA_TETRAHEDRAL_FACETS)

    # Staged contacts: first proton on a face gets 1, subsequent build toward 3.
    # For the minimal 5-body case this gives 1 contact for ⁵Li.
    contacts_this_face = min(3, 1 + max(0, (extra_protons - 1) // n_faces)) if n_faces > 0 else 0

    return tuple(ProtonFacetTouch(i, contact_count=contacts_this_face) for i in range(n_faces))


def bbn_far_neutron_touches(A: int, Z: int) -> tuple[FarNeutronTouch, ...]:
    """Neutrons do not get full triangular facets.
    They use far or limited inter-facet positions with reduced strength.
    """
    if A <= 4:
        return ()
    extra_neutrons = post_alpha_extra_neutrons(A, Z)
    # For now all extra neutrons treated as "far" (open: some could be inter-facet)
    return tuple(FarNeutronTouch(i) for i in range(extra_neutrons))


def proton_facet_touches_feasible(touches: tuple[ProtonFacetTouch, ...]) -> bool:
    facets = [t.facet_idx for t in touches]
    return len(facets) == len(set(facets))


def proton_facet_touch_contact_sum(touches: tuple[ProtonFacetTouch, ...]) -> int:
    return sum(t.contact_count for t in touches)


def far_neutron_touch_contact_sum(touches: tuple[FarNeutronTouch, ...]) -> int:
    return sum(t.contact_count for t in touches)


def far_neutron_weighted_contact_sum(A: int, Z: int) -> float:
    raw = far_neutron_touch_contact_sum(bbn_far_neutron_touches(A, Z))
    return raw * FAR_NEUTRON_TOUCH_WEIGHT


def post_alpha_outside_valley_count(A: int, Z: int) -> int:
    if A <= 4:
        return 0
    return CONSTRUCTIVE_VALLEY_CAP + proton_facet_touch_contact_sum(
        bbn_proton_facet_touches(A, Z)
    )


def post_alpha_outside_valley_count_effective(A: int, Z: int) -> float:
    """Effective outside contacts with p/n asymmetry and non-touching participation.

    - Protons on facets: full strength (3 contacts).
    - Neutrons: reduced far weight + no triple-contact facets.
    - Non-direct nucleons: decaying participation factor (addresses open question
      of how much they still deepen the collective well).
    """
    if A <= 4:
        return 0.0

    core = float(CONSTRUCTIVE_VALLEY_CAP)

    # Proton facet contribution (full strength)
    p_contacts = proton_facet_touch_contact_sum(bbn_proton_facet_touches(A, Z))

    # Neutron contribution (far only in current model, already weighted)
    n_weighted = far_neutron_weighted_contact_sum(A, Z)

    # For nucleons beyond the first post-α layer, apply participation decay.
    # shell_distance ≈ max(0, extra_p + extra_n - (facets + some far slots))
    extra = max(0, (A - 4) - 4)   # rough outer shell count after filling 4 facets + some far
    participation = non_touching_participation(1 if extra > 0 else 0)

    # Only the *incremental* surface term gets the participation factor
    # (helps avoid double-counting the base well depth from composite trace).
    incremental = (p_contacts + n_weighted) * participation

    return core + incremental


def spin_stability_participation(A: int, Z: int) -> float:
    """Feasibility of proton facet assignment (distinct facets) + neutron packing constraints."""
    if A <= 4:
        return 1.0
    p_touches = bbn_proton_facet_touches(A, Z)
    if not p_touches:
        # All extra are neutrons → still feasible via far positions, but reduced strength
        return 0.6   # heuristic; can be refined
    return 1.0 if proton_facet_touches_feasible(p_touches) else 0.0


# =============================================================================
# 5-body microscope: how ⁵Li and ⁵Be sit on the α tetrahedron
# =============================================================================

def analyze_5_body_addition():
    """
    "Find out how Be5 and Li5 look when added to the tetrahedron"
    (as requested for generalization).

    ⁴He base: regular tetrahedron, 4 faces, 6 edges, 4 vertices.
    Each face is an equilateral triangle → natural 3-contact site for a proton.

    Adding the 5th nucleon:
    - ⁵Li (Z=3, A=5): α + 1p. The proton must occupy one of the 4 faces.
    - ⁵Be (Z=4, A=5): α + 2p (extremely proton-rich, 1 neutron total).
      Two protons on two different faces (they cannot share a face comfortably
      at this stage without major distortion).

    Current (naive) model gives the first extra proton full 3 contacts immediately.
    This creates a discontinuous jump in binding when going from ⁴He to ⁵Li.

    Physical picture for generalization:
    - The first proton on a new face does not instantly get all three vertices.
    - It can start at a vertex (1 contact) or sit above the face center with partial overlap.
    - As the system relaxes or more nucleons are added to that face, contacts build 1 → 2 → 3.
    - This staged filling makes the model continuous and generalizable to higher shells.
    """
    print("=== 5-Body Geometry on the α Tetrahedron ===")
    print("Base ⁴He: 4 triangular faces, 6 edges, 4 vertices.")
    print("Each face offers a natural 3-vertex contact site for a proton.\n")

    for A, Z, label in [(5, 3, "⁵Li (α + p)"), (5, 4, "⁵Be (α + 2p, neutron-poor)")]:
        extra_p = max(0, Z - 2)
        extra_n = max(0, (A - Z) - 2)
        p_touches = bbn_proton_facet_touches(A, Z)
        n_touches = bbn_far_neutron_touches(A, Z)
        eff = post_alpha_outside_valley_count_effective(A, Z)

        print(f"{label}:")
        print(f"  extra protons on α: {extra_p}")
        print(f"  faces occupied (current model): {len(p_touches)}")
        print(f"  contacts from protons (current model): {sum(t.contact_count for t in p_touches)}")
        print(f"  extra neutrons: {extra_n} (treated as far, weight 4/8)")
        print(f"  effective post-α valley contribution (current): {eff - 6:.1f}")
        print(f"  total effective outside valleys: {eff:.1f}")
        print()

    print("Observation for generalization:")
    print("  Current model gives ⁵Li sudden +3 contacts (full face).")
    print("  This may over-estimate the incremental binding for the very first extra nucleon.")
    print("  Better: staged occupation per face (1 → 2 → 3 contacts as the face fills).")
    print("  This makes adding the 5th nucleon smoother and provides a template for")
    print("  how faces get occupied when building larger compound surfaces (A=6,7,8+).")
    print()


if __name__ == "__main__":
    analyze_5_body_addition()

# =============================================================================
# Open questions explicitly noted for future refinement
# =============================================================================
"""
Open physics questions for the generalized packing model:

1. Non-touching nucleons' contribution to well depth:
   - Current: decaying participation factor (diagnostic).
   - Better: derive from extended Casimir surfaces or mean-field overlap with the
     collective φ field of the whole compound object.

2. p vs n contact geometry:
   - Different radii → different maximum multiplicity per facet and different
     overlap energy per contact. The current 3-for-p vs 1-for-n is a first cut.

3. Double-counting:
   - Base binding (composite trace / inside curvature) already contains a lot of
     the vacuum-mode / Casimir energy. Extra contacts should only add the *differential*
     surface overlap, not re-scale the entire well.

4. Higher geometries:
   - For A >> 8–12 the α core + first shell saturates. Additional nucleons live on
     a new compound surface (perhaps octahedral or spherical harmonics at higher m).
     The simple "facet on α" picture must be nested or replaced.

These should be explored in the self-contained diagnostic script and then
formalized in HQIVNuclei.lean before being used for precision BBN predictions.
"""


def sphere_touch_separation_m(m: int) -> float:
    r = float(m + 1)
    return r + r


def be7_to_li7_capture_q(
    Q_be: float,
    Q_li: float,
) -> float:
    """Lean `bbnBe7ToLi7CaptureQ`: γ·(4/8)·max(0, Q_Be − Q_Li)."""
    return bbn.GAMMA_HQIV * bbn.STRONG_CHANNEL_FRACTION * max(0.0, Q_be - Q_li)

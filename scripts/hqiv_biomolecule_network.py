#!/usr/bin/env python3
"""
Biomolecular network readouts from the HQIV bond-order / monogamy spine.

Two scales, one engine:

* **Covalent skeleton** — the peptide unit ``O=C–N`` and nucleobase fragments are resolved
  bond-by-bond with the same geometric-mean ``cap/k`` combiner used for O₃/CO₂ allotropes
  (`hqiv_allotrope_network.analyze_network`).  The peptide C–N inherits partial double-bond
  character from the carbonyl's shared π channel — the origin of backbone planarity.

* **Hydrogen-bond interface** — a hydrogen bond is a *half-monogamy spectator contact*: an
  electronegative atom (N/O) shares its proton (donor) into a partner's open lone pair
  (acceptor).  Donor/acceptor roles are DERIVED from whether the Watson–Crick edge atom carries
  a proton in its neutral tautomer; the canonical pair counts (A·T → 2, G·C → 3) then fall out
  of edge complementarity — no pairing table is assumed, only the base-edge topology (the same
  status as handing O₃ its bent connectivity).

Nothing here imports H-bond counts, pairing rules, or bond orders: they are computed.

Usage:
  PYTHONPATH=scripts python3 scripts/hqiv_biomolecule_network.py
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass

import hqiv_allotrope_network as aln
import hqiv_lean_physics_primitives as lean
import hqiv_spine_chemistry as sc

# --------------------------------------------------------------------------------------------------
# Hydrogen bond = half-monogamy spectator contact
# --------------------------------------------------------------------------------------------------

HBOND_DONOR = "donor"
HBOND_ACCEPTOR = "acceptor"

# A hydrogen bond is a *spectator* half-monogamy contact (Biomolecule + Spectroscopy.lean).
SPECTATOR_HALF_MONOGAMY_CONTACT = sc.MONOGAMY_SPECTATOR_CONTACT


@dataclass(frozen=True)
class EdgeSite:
    """One atom on a base's Watson–Crick pairing face.

    ``element`` is N or O (the only electronegative H-bonding atoms in the canonical bases) and
    ``has_proton`` records whether it carries an H in the neutral tautomer.  This pair of facts is
    pure base-edge topology — the structural input — exactly like the connectivity handed to an
    allotrope network; the H-bond role and pair counts below are derived from it.
    """

    label: str
    element: str
    has_proton: bool


def hbond_role(site: EdgeSite) -> str:
    """Donor if the atom carries the bridging proton, acceptor if it offers an open lone pair.

    The shared proton *defines* the donor (it is the half-monogamy carrier); an N/O without a
    proton presents a lone pair and accepts.  Derived from ``has_proton`` alone.
    """
    return HBOND_DONOR if site.has_proton else HBOND_ACCEPTOR


def _complementary(role_a: str, role_b: str) -> bool:
    return {role_a, role_b} == {HBOND_DONOR, HBOND_ACCEPTOR}


# Watson–Crick edges read in the paired (aligned) order, major→minor groove.  Atoms only; the
# donor/acceptor pattern is NOT stored — it is derived from ``has_proton`` at read time.
WATSON_CRICK_EDGES: dict[str, tuple[EdgeSite, ...]] = {
    # Adenine: N1 (ring, no H) acceptor; N6–H (exocyclic amine) donor.
    "A": (EdgeSite("N1", "N", False), EdgeSite("N6", "N", True)),
    # Thymine / Uracil: N3–H donor; O4 (carbonyl) acceptor.
    "T": (EdgeSite("N3", "N", True), EdgeSite("O4", "O", False)),
    "U": (EdgeSite("N3", "N", True), EdgeSite("O4", "O", False)),
    # Guanine: O6 (carbonyl) acceptor; N1–H donor; N2–H (exocyclic amine) donor.
    "G": (EdgeSite("O6", "O", False), EdgeSite("N1", "N", True), EdgeSite("N2", "N", True)),
    # Cytosine: N4–H (exocyclic amine) donor; N3 (ring) acceptor; O2 (carbonyl) acceptor.
    "C": (EdgeSite("N4", "N", True), EdgeSite("N3", "N", False), EdgeSite("O2", "O", False)),
}

# Conventional names for output only.
_BASE_NAMES = {"A": "adenine", "T": "thymine", "U": "uracil", "G": "guanine", "C": "cytosine"}


@dataclass(frozen=True)
class BasePairReadout:
    pair: str
    edge_x_roles: tuple[str, ...]
    edge_y_roles: tuple[str, ...]
    hydrogen_bonds: int
    is_canonical_watson_crick: bool
    note: str


def watson_crick_pair(base_x: str, base_y: str) -> BasePairReadout:
    """Resolve the hydrogen-bond interface between two bases from edge complementarity.

    A canonical Watson–Crick pair requires equal-length edges with *every* aligned site
    complementary (donor opposite acceptor); the H-bond count is then the edge length.
    Unequal or partially complementary edges (G·U wobble, mismatches) give fewer/non-canonical
    contacts.  A·T → 2 and G·C → 3 emerge with no pairing rule supplied.
    """
    ex = WATSON_CRICK_EDGES[base_x]
    ey = WATSON_CRICK_EDGES[base_y]
    roles_x = tuple(hbond_role(s) for s in ex)
    roles_y = tuple(hbond_role(s) for s in ey)
    matches = sum(1 for a, b in zip(roles_x, roles_y) if _complementary(a, b))
    canonical = len(ex) == len(ey) and matches == len(ex)
    if canonical:
        note = f"canonical Watson–Crick: {matches} complementary donor/acceptor contacts"
    elif len(ex) != len(ey):
        note = "edge-length mismatch → non-canonical (wobble/mispair)"
    else:
        note = "incomplete complementarity → non-canonical mispair"
    return BasePairReadout(
        pair=f"{base_x}·{base_y}",
        edge_x_roles=roles_x,
        edge_y_roles=roles_y,
        hydrogen_bonds=matches,
        is_canonical_watson_crick=canonical,
        note=note,
    )


def canonical_pairing_partner(base: str) -> str | None:
    """The unique base whose edge is fully complementary — derived, not tabulated."""
    partners = [
        other
        for other in WATSON_CRICK_EDGES
        if other != base and watson_crick_pair(base, other).is_canonical_watson_crick
    ]
    # collapse T/U degeneracy (identical WC face) to a single representative
    uniq = sorted(set(partners))
    if not uniq:
        return None
    return "/".join(uniq)


# --------------------------------------------------------------------------------------------------
# Covalent skeleton (reuses the allotrope bond-resolved engine)
# --------------------------------------------------------------------------------------------------

# Peptide unit O=C–N: carbonyl C (degree counts its O, N and Cα), amide N (its C, H and Cα).
# The Cα/H stubs are included so the central-atom degrees match the real sp² coordination.
_PEPTIDE_FRAGMENT = {
    "z_list": [8, 6, 7, 6, 1, 6],  # O, C(=O), N, Cα(C-side), H(on N), Cα(N-side)
    "edges": [(0, 1), (1, 2), (1, 3), (2, 4), (2, 5)],
    "label": "peptide unit O=C(–Cα)–N(–H)(–Cα')",
}


@dataclass(frozen=True)
class PeptideBondReadout:
    label: str
    c_o_bond_order: float
    c_n_bond_order: float
    c_n_has_partial_double: bool
    carbonyl_c_coordination: int
    amide_n_coordination: int
    note: str


# Aromatic ring skeletons (the nucleobase building blocks) as explicit networks: ring atoms first,
# then one H stub per CH/NH site so the coordination — and thus the capacity split — is physical.
# Topology only; bond orders and planarity are derived by the capacity-conserving engine.
def _ring(z_ring: list[int], h_on: list[bool]) -> tuple[list[int], list[tuple[int, int]]]:
    n = len(z_ring)
    z = list(z_ring)
    edges = [(i, (i + 1) % n) for i in range(n)]
    for i, has_h in enumerate(h_on):
        if has_h:
            edges.append((i, len(z)))
            z.append(1)
    return z, edges


AROMATIC_RINGS: dict[str, tuple[list[int], list[tuple[int, int]]]] = {
    # benzene C6H6 — the aromatic reference (Kekulé-average 1.5)
    "benzene": _ring([6, 6, 6, 6, 6, 6], [True] * 6),
    # pyridine C5N — one ring N with a lone pair (no H)
    "pyridine": _ring([7, 6, 6, 6, 6, 6], [False, True, True, True, True, True]),
    # pyrimidine C4N2 — the cytosine/thymine/uracil six-ring (N at 1,3)
    "pyrimidine": _ring([7, 6, 7, 6, 6, 6], [False, True, False, True, True, True]),
    # imidazole C3N2 — the purine five-ring (one pyrrole N–H, one pyridine N:)
    "imidazole": _ring([7, 6, 7, 6, 6], [True, True, False, True, True]),
}


@dataclass(frozen=True)
class AromaticRingReadout:
    name: str
    ring_size: int
    ring_bond_orders: tuple[float, ...]
    min_ring_order: float
    max_ring_order: float
    all_delocalised: bool
    centre_angles_deg: tuple[float, ...]
    planar: bool


def aromatic_ring_readout(name: str) -> AromaticRingReadout:
    """Resolve an aromatic heterocycle's ring bonds and planarity from the network engine.

    Every ring atom keeps a leftover π pair after its σ bonds, so its heavy bonds carry order > 1
    (benzene exactly 1.5 — the Kekulé average); the σ-domain centre angles are all trigonal/linear
    (120°/180°), never tetrahedral, so the ring is planar and base-stacking — derived, with only the
    ring topology supplied.  (Ring N reads 180° because the shared VSEPR count undercounts the
    in-plane lone pair of an aromatic, odd-valence nitrogen; planarity is unaffected.)
    """
    z_list, edges = AROMATIC_RINGS[name]
    ring_n = sum(1 for z in z_list if z > 1)
    net = aln.analyze_network(name, z_list, edges)
    ring_orders = tuple(
        b.bond_order for b in net.bonds if b.z_i > 1 and b.z_j > 1
    )
    angles = net.central_angles_deg
    # planar ⇔ no sp³ centre: every σ-domain angle is at least the trigonal (sp²) angle
    # arccos(−1/2)=120°; sp (180°) also passes, only tetrahedral arccos(−1/3)=109.47° fails.
    # The boundary is derived from the VSEPR cosine, not a hand-set degree.
    trigonal_deg = math.degrees(math.acos(-1.0 / 2.0))
    return AromaticRingReadout(
        name=name,
        ring_size=ring_n,
        ring_bond_orders=ring_orders,
        min_ring_order=min(ring_orders),
        max_ring_order=max(ring_orders),
        all_delocalised=all(o > 1.0 for o in ring_orders),
        centre_angles_deg=angles,
        planar=all(a >= trigonal_deg - 1e-6 for a in angles) if angles else False,
    )


# Full nucleobase covalent skeletons (heavy atoms + one H stub per N–H/C–H, two per NH₂) as
# explicit networks.  Only connectivity is supplied (topology, the same status as O₃); every bond
# order and the planarity are derived by the capacity-conserving engine.  Index legend appears in
# each comment; trailing 1's are hydrogen stubs.
NUCLEOBASES: dict[str, tuple[list[int], list[tuple[int, int]], str]] = {
    # Uracil C4N2O2: ring N1 C2 N3 C4 C5 C6, carbonyls O2 O4; H on N1,N3,C5,C6.
    "uracil": (
        [7, 6, 7, 6, 6, 6, 8, 8] + [1, 1, 1, 1],
        [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0), (1, 6), (3, 7),
         (0, 8), (2, 9), (4, 10), (5, 11)],
        "uracil (pyrimidine-2,4-dione)",
    ),
    # Thymine = uracil + 5-methyl: C7 on C5 (no H on C5); H on N1,N3,C6 and 3 on C7.
    "thymine": (
        [7, 6, 7, 6, 6, 6, 8, 8, 6] + [1, 1, 1, 1, 1, 1],
        [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0), (1, 6), (3, 7), (4, 8),
         (0, 9), (2, 10), (5, 11), (8, 12), (8, 13), (8, 14)],
        "thymine (5-methyluracil)",
    ),
    # Cytosine C4N3O: ring N1 C2 N3 C4 C5 C6, carbonyl O2, exocyclic amine N4 on C4;
    # H on N1,C5,C6 and 2 on N4 (N3 is a pyridine-type ring N, no H).
    "cytosine": (
        [7, 6, 7, 6, 6, 6, 8, 7] + [1, 1, 1, 1, 1],
        [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0), (1, 6), (3, 7),
         (0, 8), (4, 9), (5, 10), (7, 11), (7, 12)],
        "cytosine (4-aminopyrimidin-2-one)",
    ),
    # Adenine C5N5: fused 6-ring (N1 C2 N3 C4 C5 C6) + 5-ring (C4 C5 N7 C8 N9), exocyclic amine
    # N6 on C6; H on C2,C8,N9 and 2 on N6.
    "adenine": (
        [7, 6, 7, 6, 6, 6, 7, 6, 7, 7] + [1, 1, 1, 1, 1],
        [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0),
         (4, 6), (6, 7), (7, 8), (8, 3), (5, 9),
         (1, 10), (7, 11), (8, 12), (9, 13), (9, 14)],
        "adenine (6-aminopurine)",
    ),
    # Guanine C5N5O: fused 6-ring + 5-ring; carbonyl O6 on C6, exocyclic amine N2 on C2;
    # H on N1,C8,N9 and 2 on N2 (N3,N7 pyridine-type).
    "guanine": (
        [7, 6, 7, 6, 6, 6, 7, 6, 7, 8, 7] + [1, 1, 1, 1, 1],
        [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0),
         (4, 6), (6, 7), (7, 8), (8, 3), (5, 9), (1, 10),
         (0, 11), (7, 12), (8, 13), (10, 14), (10, 15)],
        "guanine (2-amino-6-oxopurine)",
    ),
}


@dataclass(frozen=True)
class NucleobaseReadout:
    name: str
    label: str
    heavy_atoms: int
    min_ring_order: float
    max_ring_order: float
    all_skeleton_delocalised: bool
    planar: bool
    carbonyl_orders: tuple[float, ...]
    exocyclic_amine_orders: tuple[float, ...]


def nucleobase_readout(name: str) -> NucleobaseReadout:
    """Resolve a whole nucleobase covalent skeleton with the capacity-conserving engine.

    Carbonyls (C=O) come out as strong double-leaning contacts, exocyclic amines (C–NH₂) as
    partial doubles (conjugation into the ring), and every heavy–heavy bond carries order > 1 on a
    planar (no-sp³) frame — the aromatic/amide delocalisation that makes bases flat and stacking.
    Only the connectivity is given.
    """
    z_list, edges, label = NUCLEOBASES[name]
    n = len(z_list)
    heavy_degree = [0] * n
    total_degree = [0] * n
    for i, j in edges:
        total_degree[i] += 1
        total_degree[j] += 1
        if z_list[j] > 1:
            heavy_degree[i] += 1
        if z_list[i] > 1:
            heavy_degree[j] += 1
    net = aln.analyze_network(name, z_list, edges)
    heavy_heavy = [b for b in net.bonds if b.z_i > 1 and b.z_j > 1]
    carbonyls = tuple(b.bond_order for b in heavy_heavy if {b.z_i, b.z_j} == {6, 8})
    # exocyclic amine = C–N where the N has a single heavy neighbour (terminal NH₂)
    amines = tuple(
        b.bond_order
        for b in heavy_heavy
        if {b.z_i, b.z_j} == {6, 7}
        and (
            (b.z_i == 7 and heavy_degree[b.i] == 1) or (b.z_j == 7 and heavy_degree[b.j] == 1)
        )
    )
    orders = [b.bond_order for b in heavy_heavy]
    trigonal_deg = math.degrees(math.acos(-1.0 / 2.0))
    # planarity assesses the *conjugated framework* (atoms with ≥2 heavy neighbours); pendant sp³
    # substituents (e.g. thymine's 5-methyl) sit off the ring and do not pucker it.
    framework_angles = [
        aln.network_bond_angle_deg(z_list[a], total_degree[a])
        for a in range(n)
        if heavy_degree[a] >= 2
    ]
    framework_angles = [a for a in framework_angles if a is not None]
    return NucleobaseReadout(
        name=name,
        label=label,
        heavy_atoms=sum(1 for z in z_list if z > 1),
        min_ring_order=min(orders),
        max_ring_order=max(orders),
        all_skeleton_delocalised=all(o > 1.0 for o in orders),
        planar=all(a >= trigonal_deg - 1e-6 for a in framework_angles),
        carbonyl_orders=carbonyls,
        exocyclic_amine_orders=amines,
    )


# Single-letter code → skeleton name (the codes used in the pairing rules).
_LETTER_TO_BASE = {"A": "adenine", "T": "thymine", "U": "uracil", "G": "guanine", "C": "cytosine"}


@dataclass(frozen=True)
class RingStrainReadout:
    hybridization: str
    steric_domains: int
    strain_by_size_deg: dict[int, float]
    minimal_ring_size: int
    biological_ring: str


def ring_strain_readout(hybridization: str) -> RingStrainReadout:
    """Which planar ring size a hybridization prefers, from VSEPR-vs-polygon angle alone.

    sp² (3 σ-domains) closes strain-free at the six-ring (aromatic nucleobases); sp³ (4 domains)
    is most relaxed at the five-ring (the furanose sugar of the backbone).  This is the angular
    reason the two rings of every nucleotide are exactly those sizes — derived, no ring table.
    """
    domains = 3 if hybridization == "sp2" else 4
    sizes = (3, 4, 5, 6, 7, 8)
    strain = {n: aln.ring_angular_strain_deg(n, domains) for n in sizes}
    bio = {"sp2": "aromatic nucleobase six-ring", "sp3": "furanose sugar five-ring"}[hybridization]
    return RingStrainReadout(
        hybridization=hybridization,
        steric_domains=domains,
        strain_by_size_deg=strain,
        minimal_ring_size=aln.minimal_strain_ring_size(domains, sizes),
        biological_ring=bio,
    )


def nucleobase_ring_count(name: str) -> int:
    """Number of fused rings = cyclomatic number of the heavy-atom graph, ``E − V + 1``.

    No ring table: the connected covalent skeleton's independent cycles count themselves —
    pyrimidines (uracil/thymine/cytosine) → 1, purines (adenine/guanine) → 2.
    """
    name = _LETTER_TO_BASE.get(name, name)
    z_list, edges, _ = NUCLEOBASES[name]
    heavy = {i for i, z in enumerate(z_list) if z > 1}
    heavy_edges = sum(1 for i, j in edges if z_list[i] > 1 and z_list[j] > 1)
    return heavy_edges - len(heavy) + 1


def nucleobase_class(name: str) -> str:
    """Purine (two fused rings) vs pyrimidine (one ring) — derived from the ring count alone."""
    return "purine" if nucleobase_ring_count(name) == 2 else "pyrimidine"


@dataclass(frozen=True)
class BasePairWidthReadout:
    pair: str
    classes: tuple[str, str]
    total_ring_count: int
    is_purine_pyrimidine: bool


def base_pair_width_readout(base_x: str, base_y: str) -> BasePairWidthReadout:
    """A canonical rung's size: total fused-ring count across the pair.

    Because the donor/acceptor complementarity rule pairs a (large) purine with a (small)
    pyrimidine, every canonical rung carries the *same* total ring count (2 + 1 = 3) — the
    isostericity that gives the double helix a uniform width.  One rule (complementarity) yields
    both the H-bond counts and the constant width; no separate size rule is imposed.
    """
    cx, cy = nucleobase_class(base_x), nucleobase_class(base_y)
    return BasePairWidthReadout(
        pair=f"{base_x}·{base_y}",
        classes=(cx, cy),
        total_ring_count=nucleobase_ring_count(base_x) + nucleobase_ring_count(base_y),
        is_purine_pyrimidine={cx, cy} == {"purine", "pyrimidine"},
    )


def peptide_bond_readout() -> PeptideBondReadout:
    """Resolve the amide ``C–N`` bond order with the unified geometric-mean engine.

    With the carbonyl C and amide N both three-coordinate, the C–N contact carries
    ``√((cap_C/3)·(cap_N/3))`` > 1: partial double-bond character delocalised from the carbonyl
    π channel.  That surplus over a pure single bond is what planarises (sp²) the peptide group.
    """
    net = aln.analyze_network(
        _PEPTIDE_FRAGMENT["label"], _PEPTIDE_FRAGMENT["z_list"], _PEPTIDE_FRAGMENT["edges"]
    )
    c_o = next(b for b in net.bonds if {b.z_i, b.z_j} == {8, 6})
    c_n = next(b for b in net.bonds if {b.z_i, b.z_j} == {6, 7})
    return PeptideBondReadout(
        label=_PEPTIDE_FRAGMENT["label"],
        c_o_bond_order=c_o.bond_order,
        c_n_bond_order=c_n.bond_order,
        c_n_has_partial_double=c_n.bond_order > 1.0,
        carbonyl_c_coordination=c_n.coordination_i if c_n.z_i == 6 else c_n.coordination_j,
        amide_n_coordination=c_n.coordination_j if c_n.z_j == 7 else c_n.coordination_i,
        note="C–N > 1 ⇒ partial double bond ⇒ planar (sp²) amide group",
    )


# --------------------------------------------------------------------------------------------------
# Payload + CLI
# --------------------------------------------------------------------------------------------------

CANONICAL_PAIRS = (("A", "T"), ("G", "C"))
WOBBLE_AND_MISMATCH = (("G", "U"), ("A", "C"), ("A", "G"))


def build_payload() -> dict:
    canonical = [asdict(watson_crick_pair(x, y)) for x, y in CANONICAL_PAIRS]
    other = [asdict(watson_crick_pair(x, y)) for x, y in WOBBLE_AND_MISMATCH]
    partners = {b: canonical_pairing_partner(b) for b in ("A", "T", "G", "C")}
    return {
        "spectator_half_monogamy_contact": SPECTATOR_HALF_MONOGAMY_CONTACT,
        "base_names": _BASE_NAMES,
        "canonical_base_pairs": canonical,
        "wobble_and_mismatch": other,
        "derived_pairing_partners": partners,
        "peptide_bond": asdict(peptide_bond_readout()),
        "aromatic_rings": {name: asdict(aromatic_ring_readout(name)) for name in AROMATIC_RINGS},
        "nucleobases": {name: asdict(nucleobase_readout(name)) for name in NUCLEOBASES},
        "base_classes": {name: nucleobase_class(name) for name in NUCLEOBASES},
        "canonical_pair_widths": [asdict(base_pair_width_readout(x, y)) for x, y in CANONICAL_PAIRS],
        "ring_strain": {hyb: asdict(ring_strain_readout(hyb)) for hyb in ("sp2", "sp3")},
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="emit JSON payload")
    args = parser.parse_args()
    payload = build_payload()
    if args.json:
        print(json.dumps(payload, indent=2))
        return

    print("HQIV biomolecular network readouts")
    print("=" * 64)
    print(f"hydrogen bond = spectator half-monogamy contact (1 + γ/2 = "
          f"{SPECTATOR_HALF_MONOGAMY_CONTACT:.3f})")
    print()
    print("Watson–Crick base pairs (donor/acceptor complementarity → H-bond count):")
    for row in payload["canonical_base_pairs"]:
        flag = "canonical" if row["is_canonical_watson_crick"] else "non-canonical"
        print(f"  {row['pair']:>5}  H-bonds = {row['hydrogen_bonds']}  [{flag}]")
        print(f"         edge X {row['edge_x_roles']}")
        print(f"         edge Y {row['edge_y_roles']}")
    print()
    print("Non-canonical (wobble / mismatch):")
    for row in payload["wobble_and_mismatch"]:
        print(f"  {row['pair']:>5}  contacts = {row['hydrogen_bonds']}  → {row['note']}")
    print()
    print("Derived canonical partners:")
    for base, partner in payload["derived_pairing_partners"].items():
        print(f"  {base} ({_BASE_NAMES[base]:>8}) ↔ {partner}")
    print()
    pep = payload["peptide_bond"]
    print("Peptide bond (unified geometric-mean skeleton):")
    print(f"  {pep['label']}")
    print(f"  C=O order = {pep['c_o_bond_order']:.3f}   C–N order = {pep['c_n_bond_order']:.3f}")
    print(f"  → {pep['note']}")
    print()
    print("Aromatic ring skeletons (capacity-conserving, H-pinned):")
    for name, ring in payload["aromatic_rings"].items():
        lo, hi = ring["min_ring_order"], ring["max_ring_order"]
        order = f"{lo:.3f}" if abs(lo - hi) < 1e-9 else f"{lo:.3f}–{hi:.3f}"
        flag = "delocalised" if ring["all_delocalised"] else "localised"
        planar = "planar" if ring["planar"] else "puckered"
        print(f"  {name:>10} ({ring['ring_size']}-ring)  order = {order}  [{flag}, {planar}]")
    print()
    print("Full nucleobase skeletons (capacity-conserving, H-pinned):")
    for name, base in payload["nucleobases"].items():
        co = ",".join(f"{o:.2f}" for o in base["carbonyl_orders"]) or "—"
        nh2 = ",".join(f"{o:.2f}" for o in base["exocyclic_amine_orders"]) or "—"
        planar = "planar" if base["planar"] else "puckered"
        cls = payload["base_classes"][name]
        print(f"  {name:>9} ({base['heavy_atoms']:>2} heavy, {cls:>10})  ring {base['min_ring_order']:.2f}"
              f"–{base['max_ring_order']:.2f}  C=O [{co}]  C–NH₂ [{nh2}]  [{planar}]")
    print()
    print("Uniform helix width (one complementarity rule → purine+pyrimidine rungs):")
    for w in payload["canonical_pair_widths"]:
        tag = "purine+pyrimidine" if w["is_purine_pyrimidine"] else "size-mismatched"
        print(f"  {w['pair']:>5}  {w['classes'][0]}+{w['classes'][1]} → {w['total_ring_count']} rings  [{tag}]")
    print()
    print("Ring strain from first principles (VSEPR angle − polygon interior angle):")
    for hyb, rs in payload["ring_strain"].items():
        sizes = "  ".join(f"{n}:{rs['strain_by_size_deg'][n]:+.1f}°"
                          for n in (3, 4, 5, 6, 7))
        print(f"  {hyb}: {sizes}")
        print(f"       → min strain at {rs['minimal_ring_size']}-ring ({rs['biological_ring']})")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
HQIV intramolecular network allotropes from first principles.

Same atoms, different bond graph (diamond vs graphite vs carbyne; O₂ vs O₃; S₈ ring)
are *not* new chemistry — they are one geometric law applied to different coordinations.

Foundational law (no fitted coefficients, no Pauling/CRC tables):

  1. Octet shared-pair capacity     cap(Z) = 8 − valence_electron_count(Z)
       the number of shared electron pairs the atom commits to complete its octet.
  2. Each atom commits cap(Z)/k to *each* of its `k` bonds (its per-bond offer).  A bond is a
       single shared contact between two atoms, so its order is the **geometric mean** of the two
       endpoints' offers — the same √(·) combiner the heteronuclear bond geometry and the nuclear
       binding use.  Treating bonds individually is what O₃ forces: its terminal end (k=1, offer 2)
       and central end (k=2, offer 1) give √2 ≈ 1.41, strictly between single and double:
         bond order   p = √( cap(Zᵢ)/kᵢ · cap(Zⱼ)/kⱼ ).
       For a symmetric homonuclear, uniform-coordination network this reduces to cap/k, so the
       diamond/graphite/O₂ readouts are unchanged.
  3. The σ-framework sets the bond angle from VSEPR steric domains
       (k σ-neighbours + lone pairs), exactly as a single centre:
         θ(Z, k) = arccos(−1 / (domains − 1)),   domains = k + lone_pairs(Z, k).
  4. The bond length contracts with the fractional order on the single-bond carrier
       contact (the same `1/(1+(p−1)·strong/4)` law the diatomic engine uses):
         r(Z, k) = r_single(Z) · length_scale(p).
  5. The *allowed coordination spectrum* — i.e. which allotropes exist — is forced by
       the bond-order window 1 ≤ p ≤ 3 (a bond is at least single, at most triple):
         ⌈cap/3⌉ ≤ k ≤ cap.

This reproduces, with no fit:
  * carbon: k=4 diamond (sp³, 109.47°, p=1), k=3 graphite (sp², 120°, p=4/3),
            k=2 carbyne (sp, 180°, p=2) — the angles are exact;
  * S₈ ring: k=2 with 2 lone pairs → 108-ish (arccos(−1/3)=109.47°), p=1;
  * the coordination spectrum itself (which k are allowed) per element;
  * bond-resolved finite molecules: O₂ (p=2), O₃ (p=√2≈1.41, bent), CO₂ (p=2, linear O=C=O),
            azide (p≈2, linear) — each bond's order from the geometric mean of its two ends.

Comparison constants (diamond/graphite/… bond lengths and angles) are guardrails only;
they never enter the derivation.

Lean: `Hqiv.QuantumChemistry.AllotropeNetwork`.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path

import hqiv_chemistry_tuft_dynamics as ctd
import hqiv_electronic_valence_shells as evs
import hqiv_lean_physics_primitives as lean
import hqiv_particle_shell_structure as pss

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_JSON = ROOT / "data" / "allotrope_network_witnesses.json"

# Octet closure target for p-block shared-pair counting — DERIVED, not a literal: the s+p shell
# closure ``2(2·0+1) + 2(2·1+1) = 8`` (monogamy pairing × angular degeneracy), via the
# particle-first shell-structure layer.
OCTET = pss.octet_capacity()


def octet_shared_pair_capacity(z: int) -> int:
    """Shared electron pairs the atom commits to reach its nearest closed shell.

    ``cap = min(valence, octet − valence)`` so it is correct on both sides of the table:
    carbon (V=4)→4, nitrogen→3, oxygen→2, sulfur→2, and equally Li→1, B→3.  This is the total
    bond order summed over *all* of the atom's bonds, the budget a network partitions — the same
    ``bonding_capacity`` the diatomic bond-order rule uses (single source of truth).
    """
    return pss.bonding_capacity(z)


def atom_per_bond_capacity_offer(z: int, coordination: int) -> float:
    """What one atom commits to *each* of its bonds: `cap(Z) / k` on its own coordination.

    Terminal O in O₃ (k=1) offers 2; central O (k=2) offers 1; sp² C (k=3) offers 4/3.
    Symmetric special case of :func:`heavy_bond_capacity_offer` with no hydrogen neighbours.
    """
    if coordination <= 0:
        return 0.0
    return octet_shared_pair_capacity(z) / float(coordination)


def heavy_bond_capacity_offer(z: int, heavy_coordination: int, hydrogen_bonds: int = 0) -> float:
    """Capacity an atom offers to each *heavy* bond, after hydrogen bonds claim their share.

    Hydrogen has one electron, so every X–H contact pins exactly one shared pair (bond order 1).
    Those pinned pairs are removed from the atom's budget first, and the **residual** capacity is
    split over the remaining heavy neighbours: `offer = (cap − n_H) / k_heavy`.  This conserves the
    octet budget and is what makes aromatic rings come out right: benzene's ring C (cap 4, one C–H,
    two ring bonds) offers `(4−1)/2 = 3/2`, so each ring bond is `√(3/2·3/2) = 1.5` — the
    Kekulé-average aromatic order — not the `4/3` a naïve `cap/3` would give.
    """
    if heavy_coordination <= 0:
        return 0.0
    residual = octet_shared_pair_capacity(z) - hydrogen_bonds
    return max(0.0, residual) / float(heavy_coordination)


def bond_coupling_matrix(offer_i: float, offer_j: float, coherence: float = 1.0) -> list[list[float]]:
    """2×2 coupling (Gram) matrix of a bond: diagonal = each atom's own per-bond offer, off-diagonal
    = the shared bond order.

    Treating each atom as its own system, the shared channel is the off-diagonal `b`.  A real shared
    channel is positive-semidefinite, so (with nonnegative offers) `det = oᵢ·oⱼ − b² ≥ 0`
    (Cauchy–Schwarz).  ``coherence`` ∈ [0,1] is the fraction of full coherent sharing; `1` saturates
    the bound.  See ``Hqiv/QuantumChemistry/BondOrderCoupling.lean``.
    """
    b = coherent_bond_order(offer_i, offer_j) * coherence
    return [[offer_i, b], [b, offer_j]]


def bond_channel_determinant(offer_i: float, offer_j: float, order: float) -> float:
    """`det = oᵢ·oⱼ − b²` of the coupling matrix; `0` is the fully-shared (rank-1) saturated bond."""
    return offer_i * offer_j - order * order


def coherent_bond_order(offer_i: float, offer_j: float) -> float:
    """Bond order = the **maximal coherent** off-diagonal of the 2×2 coupling matrix.

    DERIVED, not posited as a geometric mean: positive-semidefiniteness of the shared channel forces
    `b ≤ √(oᵢ·oⱼ)`, and full coherent sharing saturates that (det = 0, a single rank-1 shared pair),
    giving `b = √(oᵢ·oⱼ)`.  The geometric mean is therefore the Cauchy–Schwarz-saturating bond order;
    sub-saturated (ionic/dative) sharing leaves the pair *count* unchanged and is carried as the
    force-constant resonance correction.  Lean: ``BondOrderCoupling.bond_order_le_geometric_mean`` and
    ``geometric_mean_zero_det``.
    """
    return math.sqrt(max(0.0, offer_i) * max(0.0, offer_j))


def resolved_bond_order(z_i: int, k_i: int, z_j: int, k_j: int) -> float:
    """Per-bond order = saturated coupling of the two endpoints' per-bond capacity offers.

    A bond is a single shared contact, so its order is the coherent saturation
    (:func:`coherent_bond_order`) of what each end commits — not a uniform centre average.  This is
    what lets the *two ends* of an asymmetric network bond differ: O₃'s terminal (offer 2) and
    central (offer 1) ends give `√2 ≈ 1.41` (between single and double), while symmetric bonds reduce
    to the common `cap/k`.
    """
    return coherent_bond_order(
        atom_per_bond_capacity_offer(z_i, k_i), atom_per_bond_capacity_offer(z_j, k_j)
    )


def network_bond_order(z: int, coordination: int) -> float:
    """Symmetric (homonuclear, uniform-coordination) bond order — the `cap/k` special case
    of :func:`resolved_bond_order` with both endpoints identical."""
    return resolved_bond_order(z, coordination, z, coordination)


def allowed_coordinations(z: int) -> tuple[int, ...]:
    """Coordination numbers `k` admitting a physical bond order 1 ≤ cap/k ≤ 3.

    The lower edge `k = ⌈cap/3⌉` is the maximally multiple-bonded network (triple), the
    upper edge `k = cap` is the all-single network.  This *is* the derived allotrope family.
    """
    cap = octet_shared_pair_capacity(z)
    if cap <= 0:
        return ()
    # 1 ≤ cap/k ≤ max_bond_order (the p-shell triple) — ceiling is DERIVED, not a literal 3.
    k_min = max(1, math.ceil(cap / pss.max_bond_order()))
    k_max = cap
    return tuple(range(k_min, k_max + 1))


def network_lone_pair_count(z: int, coordination: int) -> int:
    """VSEPR lone pairs on the centre at coordination `k` (existing valence-shell readout)."""
    return evs.centre_vsepr_lone_pair_count(z, coordination)


def steric_domain_count(z: int, coordination: int) -> int:
    """σ-framework steric domains = bonded neighbours + lone pairs."""
    return coordination + network_lone_pair_count(z, coordination)


def network_bond_angle_rad(z: int, coordination: int) -> float | None:
    """Bond angle from VSEPR domain count: θ = arccos(−1/(domains−1)).

    domains 2→180° (linear), 3→120° (trigonal/sp²), 4→109.47° (tetrahedral/sp³).
    Returns ``None`` for a diatomic (`k < 2`): a single bond has no angle.
    """
    if coordination < 2:
        return None
    domains = steric_domain_count(z, coordination)
    return ctd.centre_angle_rad_from_domains(domains)


def network_bond_angle_deg(z: int, coordination: int) -> float | None:
    rad = network_bond_angle_rad(z, coordination)
    return None if rad is None else math.degrees(rad)


def polygon_interior_angle_deg(n: int) -> float:
    """Interior angle of a regular planar `n`-gon: `(n−2)·180/n` (pure geometry, no chemistry)."""
    return (n - 2) * 180.0 / n


def balanced_unit_contact_cos(d: int) -> float:
    """Pairwise cosine of `d` balanced unit contact directions — DERIVED, not the VSEPR input.

    The σ-domains are unit informational-monogamy contacts.  If the centre is in equilibrium their
    directions carry no net flux (Kirchhoff's node law / momentum balance), so `∑ᵢ vᵢ = 0`; with
    equivalent (symmetric) contacts sharing one pairwise cosine `c`,
    `0 = ‖∑ vᵢ‖² = d·(1 + (d−1)c)`, hence `c = −1/(d−1)`.  The VSEPR angle `arccos(c)` is therefore
    forced by balance + symmetry — see ``Hqiv/QuantumChemistry/VSEPRFromBalance.lean``.
    """
    return -1.0 / (d - 1)


def _balanced_unit_vectors(d: int) -> list[list[float]]:
    """A concrete zero-sum symmetric frame of `d` unit vectors (regular-simplex vertices)."""
    mean = 1.0 / d
    norm = math.sqrt((d - 1) / d)
    return [[((1.0 if i == j else 0.0) - mean) / norm for j in range(d)] for i in range(d)]


def balance_residual_norm(d: int) -> float:
    """`‖∑ᵢ vᵢ‖` for the constructed frame — ~0 confirms the contacts are in equilibrium."""
    vs = _balanced_unit_vectors(d)
    resultant = [sum(v[k] for v in vs) for k in range(d)]
    return math.sqrt(sum(x * x for x in resultant))


def measured_contact_cos(d: int) -> float:
    """Pairwise cosine *measured* from the constructed zero-sum frame (should equal −1/(d−1))."""
    vs = _balanced_unit_vectors(d)
    return sum(vs[0][k] * vs[1][k] for k in range(d))


def ideal_hybridization_angle_deg(steric_domains: int) -> float:
    """Strain-free VSEPR angle = `arccos` of the *derived* balance cosine `−1/(d−1)`.

    Not a tabulated rule: the cosine comes from :func:`balanced_unit_contact_cos` (equilibrium of
    unit contacts), so sp→180°, sp²→120°, sp³→109.47° are consequences of balance.
    """
    if steric_domains <= 2:
        return 180.0
    return math.degrees(math.acos(balanced_unit_contact_cos(steric_domains)))


def ring_angular_strain_deg(n: int, steric_domains: int) -> float:
    """Planar-ring angular strain = ideal VSEPR angle − regular-polygon interior angle.

    Two angles, one comparison: a flat ring is unstrained exactly when its atoms' preferred VSEPR
    angle equals the polygon's interior angle.  sp² closes perfectly at `n=6` (benzene → 0°); sp³
    is nearly perfect at `n=5` (furanose → +1.47°) and is compressed at `n=3,4` — the angular origin
    of why five- and six-membered rings dominate (sugars, nucleobases).  No ring table.
    """
    return ideal_hybridization_angle_deg(steric_domains) - polygon_interior_angle_deg(n)


def minimal_strain_ring_size(steric_domains: int, candidates: tuple[int, ...] = (3, 4, 5, 6, 7, 8)) -> int:
    """The planar ring size that minimises |angular strain| for a given hybridization.

    Falls out as `n=6` for sp² and `n=5` for sp³ — derived, not asserted."""
    return min(candidates, key=lambda n: abs(ring_angular_strain_deg(n, steric_domains)))


def length_is_reliable(z: int) -> bool:
    """Absolute bond length is trustworthy only where the nested-WF covalent radius is
    (period ≤ 2).  Period 3+ absolute lengths inherit the known carrier-radius gap; the
    bond-order contraction *trend* and the angle remain valid everywhere."""
    return z <= 10


def single_bond_carrier_length_angstrom(z: int) -> float:
    """The HQIV single-bond carrier contact `2 r_i / (1−α/2)` (bond order 1 reference)."""
    m = ctd.bond_contact_compton_shell(z, z)
    r_i = ctd.nested_wf_covalent_radius_bohr(m, z)
    mono = ctd.INFORMATIONAL_MONOGAMY_LENGTH_FACTOR
    return 2.0 * r_i / mono * ctd.BOHR_RADIUS_ANGSTROM


def fractional_length_scale(bond_order: float) -> float:
    """Bond-order contraction `1/(1+(p−1)·strong/n_rep)` extended to fractional `p` (≥1).

    The contraction coefficient is the strong-channel fraction over the monogamy-core power
    `n_rep = referenceM = 4` (the same core power in the Mie/Born–Landé bond curvature), so no new
    constant enters; it reproduces the double/triple-bond contractions to a few percent.
    """
    if bond_order <= 1.0:
        return 1.0
    return 1.0 / (1.0 + (bond_order - 1.0) * lean.STRONG_CHANNEL_FRACTION / float(lean.REFERENCE_M))


def pair_single_bond_carrier_angstrom(z_i: int, z_j: int) -> float:
    """Single-bond carrier contact for a (possibly heteronuclear) pair = geometric mean of
    the two atomic single-bond carriers (same `√(rᵢ rⱼ)` rule the diatomic engine uses)."""
    r_i = single_bond_carrier_length_angstrom(z_i)
    if z_i == z_j:
        return r_i
    r_j = single_bond_carrier_length_angstrom(z_j)
    return math.sqrt(r_i * r_j)


def network_bond_length_angstrom(z: int, coordination: int) -> float:
    """Per-bond equilibrium length: single-bond carrier × fractional-order contraction."""
    p = network_bond_order(z, coordination)
    return single_bond_carrier_length_angstrom(z) * fractional_length_scale(p)


def resolved_bond_length_angstrom(z_i: int, k_i: int, z_j: int, k_j: int) -> float:
    """Per-bond length from the resolved (geometric-mean) order on the pair carrier contact."""
    p = resolved_bond_order(z_i, k_i, z_j, k_j)
    return pair_single_bond_carrier_angstrom(z_i, z_j) * fractional_length_scale(p)


def resolved_bond_length_from_order(z_i: int, z_j: int, bond_order: float) -> float:
    """Per-bond length from a precomputed (capacity-conserving) order on the pair carrier."""
    return pair_single_bond_carrier_angstrom(z_i, z_j) * fractional_length_scale(bond_order)


@dataclass(frozen=True)
class NetworkBond:
    i: int
    j: int
    z_i: int
    z_j: int
    coordination_i: int
    coordination_j: int
    offer_i: float
    offer_j: float
    bond_order: float
    bond_length_angstrom: float
    length_reliable: bool


@dataclass(frozen=True)
class NetworkReadout:
    name: str
    z_list: tuple[int, ...]
    coordinations: tuple[int, ...]
    bonds: tuple[NetworkBond, ...]
    central_angles_deg: tuple[float, ...]


def analyze_network(name: str, z_list: list[int], edges: list[tuple[int, int]]) -> NetworkReadout:
    """Resolve every bond of an explicit network individually.

    The coordination of each site is its graph *degree*; each bond order is the geometric mean
    of its two endpoints' `cap/k` offers, and angles are the VSEPR domain angles at each
    multi-coordinate centre.  This is the bond-by-bond treatment O₃/CO₂ require.
    """
    n = len(z_list)
    degree = [0] * n
    heavy_degree = [0] * n
    hydrogen_bonds = [0] * n
    for i, j in edges:
        degree[i] += 1
        degree[j] += 1
        if z_list[j] <= 1:
            hydrogen_bonds[i] += 1
        else:
            heavy_degree[i] += 1
        if z_list[i] <= 1:
            hydrogen_bonds[j] += 1
        else:
            heavy_degree[j] += 1

    bonds: list[NetworkBond] = []
    for i, j in edges:
        zi, zj = z_list[i], z_list[j]
        ki, kj = degree[i], degree[j]
        if zi <= 1 or zj <= 1:
            # X–H pins exactly one shared pair (hydrogen has one electron).
            offer_i = offer_j = 1.0
            order = 1.0
        else:
            offer_i = heavy_bond_capacity_offer(zi, heavy_degree[i], hydrogen_bonds[i])
            offer_j = heavy_bond_capacity_offer(zj, heavy_degree[j], hydrogen_bonds[j])
            order = coherent_bond_order(offer_i, offer_j)
        bonds.append(
            NetworkBond(
                i=i,
                j=j,
                z_i=zi,
                z_j=zj,
                coordination_i=ki,
                coordination_j=kj,
                offer_i=offer_i,
                offer_j=offer_j,
                bond_order=order,
                bond_length_angstrom=resolved_bond_length_from_order(zi, zj, order),
                length_reliable=length_is_reliable(zi) and length_is_reliable(zj),
            )
        )

    angles: list[float] = []
    for i in range(n):
        if degree[i] >= 2:
            a = network_bond_angle_deg(z_list[i], degree[i])
            if a is not None:
                angles.append(a)
    return NetworkReadout(
        name=name,
        z_list=tuple(z_list),
        coordinations=tuple(degree),
        bonds=tuple(bonds),
        central_angles_deg=tuple(angles),
    )


# Explicit *finite/asymmetric* networks (z list + bond edges) — topology only, no geometry
# inputs.  Extended uniform solids (diamond, graphite) instead use the symmetric centre model
# `element_allotropes`, where every atom shares the lattice coordination; a finite cluster would
# mis-coordinate the boundary atoms.  The bond-resolved graph below is for molecules whose ends
# genuinely differ in coordination (the O₃ insight).
NAMED_NETWORKS: dict[str, tuple[list[int], list[tuple[int, int]]]] = {
    "O2 (O=O)": ([8, 8], [(0, 1)]),
    "O3 ozone (bent)": ([8, 8, 8], [(0, 1), (1, 2)]),
    "CO2 (O=C=O)": ([8, 6, 8], [(0, 1), (1, 2)]),
    "N3- azide (linear)": ([7, 7, 7], [(0, 1), (1, 2)]),
}

# Per-bond comparison guardrails: bond order and length [Å] (never inputs).
NETWORK_COMPARISON: dict[str, dict[str, float]] = {
    "O2 (O=O)": {"bond_order": 2.0, "r": 1.208},
    "O3 ozone (bent)": {"bond_order": 1.5, "r": 1.278, "angle": 116.8},
    "CO2 (O=C=O)": {"bond_order": 2.0, "r": 1.163, "angle": 180.0},
    "N3- azide (linear)": {"bond_order": 2.0, "angle": 180.0},
}


@dataclass(frozen=True)
class AllotropeReadout:
    element_z: int
    name: str
    coordination: int
    octet_capacity: int
    bond_order: float
    lone_pairs: int
    steric_domains: int
    bond_angle_deg: float | None
    bond_length_angstrom: float
    length_reliable: bool
    hybridization: str


def _hybridization(domains: int) -> str:
    return {2: "sp", 3: "sp2", 4: "sp3", 5: "sp3d", 6: "sp3d2"}.get(domains, f"{domains}-domain")


# Conventional allotrope names per (element_Z, coordination) — labels only, not inputs.
_ALLOTROPE_NAMES: dict[tuple[int, int], str] = {
    (6, 4): "diamond (sp3)",
    (6, 3): "graphite/graphene (sp2)",
    (6, 2): "carbyne (sp)",
    (14, 4): "silicon (diamond-cubic)",
    (14, 3): "silicene (sp2)",
    (32, 4): "germanium (diamond-cubic)",
    (8, 1): "dioxygen O2",
    (8, 2): "ozone-like O3 (single-bond limit)",
    (7, 1): "dinitrogen N2",
    (7, 2): "azo-like (bo 1.5)",
    (7, 3): "trivalent N network",
    (16, 2): "sulfur S8 ring",
    (15, 3): "phosphorus network (sp3)",
}


def allotrope_readout(z: int, coordination: int) -> AllotropeReadout:
    domains = steric_domain_count(z, coordination)
    name = _ALLOTROPE_NAMES.get((z, coordination), f"Z{z} k={coordination}")
    return AllotropeReadout(
        element_z=z,
        name=name,
        coordination=coordination,
        octet_capacity=octet_shared_pair_capacity(z),
        bond_order=network_bond_order(z, coordination),
        lone_pairs=network_lone_pair_count(z, coordination),
        steric_domains=domains,
        bond_angle_deg=network_bond_angle_deg(z, coordination),
        bond_length_angstrom=network_bond_length_angstrom(z, coordination),
        length_reliable=length_is_reliable(z),
        hybridization=_hybridization(domains),
    )


def element_allotropes(z: int) -> tuple[AllotropeReadout, ...]:
    """The derived allotrope family for an element (one readout per allowed coordination)."""
    return tuple(allotrope_readout(z, k) for k in allowed_coordinations(z))


# Comparison guardrails (NIST/CRC) — bond length [Å], bond angle [deg]; never inputs.
COMPARISON: dict[tuple[int, int], dict[str, float]] = {
    (6, 4): {"r": 1.544, "angle": 109.5},   # diamond
    (6, 3): {"r": 1.421, "angle": 120.0},   # graphite
    (6, 2): {"r": 1.280, "angle": 180.0},   # carbyne (cumulene/polyyne avg)
    (14, 4): {"angle": 109.5},              # silicon (length period-3 unreliable)
    (8, 1): {"r": 1.208},                   # O2 (diatomic, no angle)
    (16, 2): {"angle": 108.0},              # S8 ring (length period-3 unreliable)
}


def build_payload() -> dict:
    elements = [6, 14, 8, 7, 16]
    rows = []
    for z in elements:
        for ro in element_allotropes(z):
            d = asdict(ro)
            comp = COMPARISON.get((z, ro.coordination))
            if comp is not None:
                d["comparison"] = comp
                if ro.bond_angle_deg is not None and "angle" in comp:
                    d["angle_error_deg"] = ro.bond_angle_deg - comp["angle"]
                if ro.length_reliable and "r" in comp:
                    d["length_error_pct"] = (
                        100.0 * (ro.bond_length_angstrom - comp["r"]) / comp["r"]
                    )
            rows.append(d)
    networks = []
    for name, (z_list, edges) in NAMED_NETWORKS.items():
        ro = analyze_network(name, z_list, edges)
        # one representative bond order/length per network (the resolved bonds are equivalent)
        bo = ro.bonds[0].bond_order
        d = {
            "name": name,
            "coordinations": list(ro.coordinations),
            "bond_order": bo,
            "bond_length_angstrom": ro.bonds[0].bond_length_angstrom,
            "length_reliable": ro.bonds[0].length_reliable,
            "central_angles_deg": list(ro.central_angles_deg),
            "bonds": [asdict(b) for b in ro.bonds],
        }
        comp = NETWORK_COMPARISON.get(name)
        if comp is not None:
            d["comparison"] = comp
            if "bond_order" in comp:
                d["bond_order_error"] = bo - comp["bond_order"]
            if "angle" in comp and ro.central_angles_deg:
                d["angle_error_deg"] = ro.central_angles_deg[0] - comp["angle"]
        networks.append(d)

    return {
        "source": "scripts/hqiv_allotrope_network.py",
        "lean_module": "Hqiv.QuantumChemistry.AllotropeNetwork",
        "parameter_policy": "no_fitted_coefficients",
        "input_policy": "NIST/CRC bond lengths & angles are comparison-only; never in the solve",
        "law": {
            "capacity": "cap(Z) = 8 - valence_electron_count(Z)  (octet shared-pair budget)",
            "offer": "each atom commits cap(Z)/k to each of its k bonds",
            "bond_order": "per bond = geometric mean of the two endpoints' offers (sqrt)",
            "symmetric_order": "homonuclear uniform-k reduces to cap/k",
            "angle": "theta = arccos(-1/(domains-1)), domains = k + VSEPR lone pairs",
            "length": "r = pair_single_bond_carrier * 1/(1+(p-1)*strong/4)",
            "spectrum": "allowed k in [ceil(cap/3), cap]  (1 <= p <= 3)",
        },
        "rows": rows,
        "networks": networks,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="HQIV intramolecular allotrope networks")
    parser.add_argument("--json-out", type=str, default=None)
    args = parser.parse_args()

    payload = build_payload()
    print("HQIV allotrope networks from first principles (capacity → coordination → readout)")
    print(f"  law: cap=8-valence ; bond_order=cap/k ; angle=arccos(-1/(domains-1))\n")
    hdr = f"{'allotrope':28s} {'k':>2s} {'cap':>3s} {'bo':>5s} {'dom':>3s} {'angle°':>7s} {'r Å':>6s}"
    print(hdr)
    print("-" * len(hdr))
    for row in payload["rows"]:
        ang = f"{row['bond_angle_deg']:7.1f}" if row["bond_angle_deg"] is not None else "    n/a"
        r_str = f"{row['bond_length_angstrom']:6.2f}" if row["length_reliable"] else "  (p3)"
        line = (
            f"{row['name']:28s} {row['coordination']:2d} {row['octet_capacity']:3d} "
            f"{row['bond_order']:5.2f} {row['steric_domains']:3d} {ang} {r_str}"
        )
        bits = []
        if "angle_error_deg" in row:
            bits.append(f"angle={row['comparison']['angle']:.1f} Δ={row['angle_error_deg']:+.1f}°")
        if "length_error_pct" in row:
            bits.append(f"r={row['comparison']['r']:.3f} Δr={row['length_error_pct']:+.1f}%")
        if bits:
            line += "   [vs " + ", ".join(bits) + "]"
        print(line)

    print("\nBond-resolved networks (each bond = geometric mean of endpoint cap/k offers):")
    nhdr = f"{'network':20s} {'coord':>10s} {'bo':>5s} {'r Å':>6s} {'angle°':>7s}"
    print(nhdr)
    print("-" * len(nhdr))
    for net in payload["networks"]:
        coord = ",".join(str(c) for c in net["coordinations"])
        ang = (
            f"{net['central_angles_deg'][0]:7.1f}"
            if net["central_angles_deg"]
            else "    n/a"
        )
        r_str = f"{net['bond_length_angstrom']:6.2f}" if net["length_reliable"] else "  (p3)"
        line = f"{net['name']:20s} {coord:>10s} {net['bond_order']:5.2f} {r_str} {ang}"
        bits = []
        if "bond_order_error" in net:
            bits.append(f"bo {net['comparison']['bond_order']} Δ={net['bond_order_error']:+.2f}")
        if "angle_error_deg" in net:
            bits.append(f"angle {net['comparison']['angle']} Δ={net['angle_error_deg']:+.1f}°")
        if bits:
            line += "   [vs " + ", ".join(bits) + "]"
        print(line)

    if args.json_out:
        out = Path(args.json_out)
        out.write_text(json.dumps(payload, indent=2))
        print(f"\nWrote {out}")


if __name__ == "__main__":
    main()

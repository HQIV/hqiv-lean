"""Pyranose ring contact graph — derived chair span (no tabulated Å)."""

from __future__ import annotations

import math

from hqiv_lab._scripts import ensure_scripts_on_path
from hqiv_lab.spec import MoleculeSpec

ensure_scripts_on_path()
import hqiv_lean_physics_primitives as lean  # noqa: E402

from fragment_aware_bonded_horizon import BondGeometry, FragmentConfig  # noqa: E402

PYRANOSE_RING_BOND_COUNT = 6


def _is_pyranose_ring_nodes(fragments: tuple[FragmentConfig, ...], nodes: tuple[int, ...]) -> bool:
    if len(nodes) != PYRANOSE_RING_BOND_COUNT:
        return False
    zs = [fragments[i].z_nuclear for i in nodes]
    n_c = sum(1 for z in zs if z == 6)
    n_o = sum(1 for z in zs if z == 8)
    return n_c >= 4 and 1 <= n_o <= 2


def _heavy_only_adjacency(
    fragments: tuple[FragmentConfig, ...],
    bonds: tuple[BondGeometry, ...],
) -> tuple[list[list[int]], dict[tuple[int, int], BondGeometry]]:
    n = len(fragments)
    adj: list[list[int]] = [[] for _ in range(n)]
    bond_map: dict[tuple[int, int], BondGeometry] = {}
    for b in bonds:
        zi = fragments[b.frag_i].z_nuclear
        zj = fragments[b.frag_j].z_nuclear
        if zi <= 1 or zj <= 1:
            continue
        adj[b.frag_i].append(b.frag_j)
        adj[b.frag_j].append(b.frag_i)
        key = (min(b.frag_i, b.frag_j), max(b.frag_i, b.frag_j))
        bond_map[key] = b
    return adj, bond_map


def pyranose_ring_bond_lengths(
    fragments: tuple[FragmentConfig, ...],
    bonds: tuple[BondGeometry, ...],
) -> tuple[float, ...] | None:
    """
    Bond lengths along a 6-member O/C ring closure, if present.

    Walks simple 6-cycles in the heavy-atom graph (excludes O–H legs).
    """
    adj, bond_map = _heavy_only_adjacency(fragments, bonds)

    best: tuple[float, ...] | None = None

    heavy_bonds = tuple(
        b
        for b in bonds
        if fragments[b.frag_i].z_nuclear > 1 and fragments[b.frag_j].z_nuclear > 1
    )

    def walk(
        start: int,
        current: int,
        prev: int,
        depth: int,
        lengths: list[float],
        nodes: list[int],
    ) -> None:
        nonlocal best
        if depth == PYRANOSE_RING_BOND_COUNT:
            if current == start and len(lengths) == PYRANOSE_RING_BOND_COUNT:
                ring_nodes = tuple(nodes[:PYRANOSE_RING_BOND_COUNT])
                if len(set(ring_nodes)) == PYRANOSE_RING_BOND_COUNT and _is_pyranose_ring_nodes(
                    fragments, ring_nodes
                ):
                    cycle = tuple(lengths)
                    if best is None or sum(cycle) > sum(best):
                        best = cycle
            return
        if depth >= PYRANOSE_RING_BOND_COUNT:
            return
        for nb in adj[current]:
            if nb == prev:
                continue
            if depth > 0 and nb == start and depth < PYRANOSE_RING_BOND_COUNT - 1:
                continue
            if depth == PYRANOSE_RING_BOND_COUNT - 1 and nb != start:
                continue
            key = (min(current, nb), max(current, nb))
            bond = bond_map.get(key)
            if bond is None:
                continue
            walk(start, nb, current, depth + 1, lengths + [bond.distance_angstrom], nodes + [nb])

    for b in heavy_bonds:
        walk(b.frag_i, b.frag_j, b.frag_i, 1, [b.distance_angstrom], [b.frag_i, b.frag_j])

    return best


def pyranose_ring_node_sets(
    fragments: tuple[FragmentConfig, ...],
    bonds: tuple[BondGeometry, ...],
) -> tuple[frozenset[int], ...]:
    """Distinct 6-member pyranose ring node sets in the heavy-atom graph."""
    adj, bond_map = _heavy_only_adjacency(fragments, bonds)
    found: set[frozenset[int]] = set()

    heavy_bonds = tuple(
        b
        for b in bonds
        if fragments[b.frag_i].z_nuclear > 1 and fragments[b.frag_j].z_nuclear > 1
    )

    def walk(
        start: int,
        current: int,
        prev: int,
        depth: int,
        nodes: list[int],
    ) -> None:
        if depth == PYRANOSE_RING_BOND_COUNT:
            if current == start and len(nodes) >= PYRANOSE_RING_BOND_COUNT:
                ring_nodes = tuple(nodes[:PYRANOSE_RING_BOND_COUNT])
                if len(set(ring_nodes)) == PYRANOSE_RING_BOND_COUNT and _is_pyranose_ring_nodes(
                    fragments, ring_nodes
                ):
                    found.add(frozenset(ring_nodes))
            return
        if depth >= PYRANOSE_RING_BOND_COUNT:
            return
        for nb in adj[current]:
            if nb == prev:
                continue
            if depth > 0 and nb == start and depth < PYRANOSE_RING_BOND_COUNT - 1:
                continue
            if depth == PYRANOSE_RING_BOND_COUNT - 1 and nb != start:
                continue
            key = (min(current, nb), max(current, nb))
            if bond_map.get(key) is None:
                continue
            walk(start, nb, current, depth + 1, nodes + [nb])

    for b in heavy_bonds:
        walk(b.frag_i, b.frag_j, b.frag_i, 1, [b.frag_i, b.frag_j])

    return tuple(sorted(found, key=lambda s: min(s)))


def pyranose_ring_count(spec: MoleculeSpec) -> int:
    """Number of disjoint pyranose rings (disaccharide → 2)."""
    return len(pyranose_ring_node_sets(spec.fragments, spec.bonds))


def pyranose_disaccharide_cell_scale(n_rings: int) -> float:
    """
    Expand Bravais edges when Z·MW counts multiple rings per molecule.

    ``n_rings^(1/3)`` — Lean ``pyranoseDisaccharideCellScale``.
    """
    if n_rings <= 1:
        return 1.0
    return float(n_rings) ** (1.0 / 3.0)


def pyranose_ring_mean_bond_angstrom(spec: MoleculeSpec) -> float | None:
    """Mean ring bond length from spec graph, or None if no pyranose ring."""
    lengths = pyranose_ring_bond_lengths(spec.fragments, spec.bonds)
    if lengths is None:
        return None
    return sum(lengths) / len(lengths)


def pyranose_chair_inplane_axis_factor() -> float:
    """Orthorhombic in-plane ring tile (Lean ``pyranoseChairInPlaneAxisFactor``)."""
    return math.sqrt(2.0) * (1.0 + lean.ALPHA / 2.0)


def pyranose_chair_stack_axis_factor() -> float:
    """Long H-bond stack axis between chair layers (Lean ``pyranoseChairStackAxisFactor``)."""
    sc = lean.STRONG_CHANNEL_FRACTION
    return (1.0 + lean.ALPHA + lean.GAMMA / 4.0) * math.sqrt(2.0) * math.sqrt(1.0 + sc / 4.0)


def pyranose_chair_short_axis_factor() -> float:
    """
    Compressed chair projection axis (Lean ``pyranoseChairShortAxisFactor``).

    Ring² closure + diatomic glide compress: ``1 + γ/(n_ring² + 2)``.
    """
    base = (1.0 + lean.GAMMA / 4.0) / (1.0 + lean.ALPHA / 4.0)
    ring_closure = 1.0 + lean.GAMMA / (float(PYRANOSE_RING_BOND_COUNT**2 + 2))
    return base / ring_closure


def pyranose_molecules_per_cell() -> int:
    """Z from crystalline coordination reference (polyol motif = 4)."""
    return 4


def pyranose_chair_diameter_factor() -> float:
    """Across-ring span / mean ring bond (Lean ``pyranoseChairDiameterFactor``)."""
    return 2.0 * (1.0 + lean.ALPHA + lean.GAMMA / 4.0)


def pyranose_chair_open_factor() -> float:
    """Chair puckering open cell (Lean ``pyranoseChairOpenCell``)."""
    return 1.0 + lean.GAMMA / 4.0


def pyranose_exocyclic_oh_dress_factor(n_inter: int) -> float:
    """
    Axial/equatorial OH reach beyond ring span (Lean ``pyranoseExocyclicOhDressFactor``).

    ``sqrt(1 + (4/8)·n_inter / 6)`` on nn contact — no fitted Å.
    """
    sc = lean.STRONG_CHANNEL_FRACTION
    n = max(n_inter, 1)
    return math.sqrt(1.0 + sc * float(n) / float(PYRANOSE_RING_BOND_COUNT))


def pyranose_ring_contact_distance_angstrom(
    ring_mean_bond: float,
    *,
    n_inter: int = 4,
) -> float:
    """
    Nearest-neighbour centre separation from ring contact graph.

    ``r_nn = r_ring · 2(1+α+γ/4) · (1+γ/4) · sqrt(1 + sc·n_inter/6)``.
    """
    return (
        ring_mean_bond
        * pyranose_chair_diameter_factor()
        * pyranose_chair_open_factor()
        * pyranose_exocyclic_oh_dress_factor(n_inter)
    )


def has_pyranose_ring(spec: MoleculeSpec) -> bool:
    return pyranose_ring_mean_bond_angstrom(spec) is not None

"""Extended polyol contact graph (triol backbone, no tabulated Å)."""

from __future__ import annotations

import math

from hqiv_lab._scripts import ensure_scripts_on_path
from hqiv_lab.coordination import MonomerGeometry
from hqiv_lab.spec import MoleculeSpec

ensure_scripts_on_path()
import hqiv_lean_physics_primitives as lean  # noqa: E402

from fragment_aware_bonded_horizon import BondGeometry, FragmentConfig  # noqa: E402


def _count_oh_groups(
    fragments: tuple[FragmentConfig, ...],
    bonds: tuple[BondGeometry, ...],
) -> int:
    o_indices = {i for i, f in enumerate(fragments) if f.z_nuclear == 8}
    h_indices = {i for i, f in enumerate(fragments) if f.z_nuclear == 1}
    oh = 0
    for o in o_indices:
        has_h = any(
            (b.frag_i == o and b.frag_j in h_indices) or (b.frag_j == o and b.frag_i in h_indices)
            for b in bonds
        )
        has_heavy = any(
            (b.frag_i == o and b.frag_j not in h_indices)
            or (b.frag_j == o and b.frag_i not in h_indices)
            for b in bonds
        )
        if has_h and has_heavy:
            oh += 1
    return oh


def triol_backbone_bond_lengths(
    fragments: tuple[FragmentConfig, ...],
    bonds: tuple[BondGeometry, ...],
) -> tuple[float, ...] | None:
    """
    Longest carbon-only chain bonds (glycerol HO–CH₂–CH(OH)–CH₂–OH spine).
    """
    c_indices = [i for i, f in enumerate(fragments) if f.z_nuclear == 6]
    if len(c_indices) < 2:
        return None
    adj: dict[int, list[int]] = {i: [] for i in c_indices}
    bond_map: dict[tuple[int, int], BondGeometry] = {}
    for b in bonds:
        if fragments[b.frag_i].z_nuclear == 6 and fragments[b.frag_j].z_nuclear == 6:
            adj[b.frag_i].append(b.frag_j)
            adj[b.frag_j].append(b.frag_i)
            key = (min(b.frag_i, b.frag_j), max(b.frag_i, b.frag_j))
            bond_map[key] = b

    best: list[float] = []

    def walk(current: int, prev: int, lengths: list[float]) -> None:
        nonlocal best
        if len(lengths) > len(best):
            best = lengths[:]
        for nb in adj.get(current, []):
            if nb == prev:
                continue
            key = (min(current, nb), max(current, nb))
            bond = bond_map.get(key)
            if bond is None:
                continue
            walk(nb, current, lengths + [bond.distance_angstrom])

    for c in c_indices:
        walk(c, -1, [])

    if len(best) < 2:
        return None
    return tuple(best)


def triol_backbone_mean_bond_angstrom(spec: MoleculeSpec) -> float | None:
    lengths = triol_backbone_bond_lengths(spec.fragments, spec.bonds)
    if lengths is None:
        return None
    return sum(lengths) / len(lengths)


def triol_backbone_diameter_factor() -> float:
    """Span / mean backbone bond (Lean ``triolBackboneDiameterFactor``)."""
    return 2.0 * (1.0 + lean.ALPHA / 2.0 + lean.GAMMA / 8.0)


def triol_backbone_open_factor() -> float:
    return 1.0 + lean.GAMMA / 8.0


def triol_exocyclic_oh_dress_factor(n_inter: int) -> float:
    sc = lean.STRONG_CHANNEL_FRACTION
    n = max(n_inter, 1)
    return math.sqrt(1.0 + sc * float(n) / 4.0)


def triol_backbone_contact_distance_angstrom(
    backbone_mean: float,
    *,
    n_inter: int,
) -> float:
    """Triol nn contact from backbone graph (mirrors pyranose ring contact spine)."""
    return (
        backbone_mean
        * triol_backbone_diameter_factor()
        * triol_backbone_open_factor()
        * triol_exocyclic_oh_dress_factor(n_inter)
    )


def is_triol_polyol(spec: MoleculeSpec) -> bool:
    from hqiv_lab.pyranose_geometry import has_pyranose_ring

    if has_pyranose_ring(spec):
        return False
    return _count_oh_groups(spec.fragments, spec.bonds) >= 3


def triol_bravais_axis_factors() -> tuple[float, float, float]:
    """Orthorhombic triol layer (peptide-layer γ/8 stack slot)."""
    sc = lean.STRONG_CHANNEL_FRACTION
    a = math.sqrt(2.0) * (1.0 + lean.ALPHA / 2.0)
    b = (1.0 + lean.ALPHA + lean.GAMMA / 8.0) * math.sqrt(2.0) * math.sqrt(1.0 + sc / 4.0)
    c = (1.0 + lean.GAMMA / 8.0) / (1.0 + lean.ALPHA / 4.0)
    return a, b, c


def is_monomer_polyol_alcohol(spec: MoleculeSpec) -> bool:
    """Single-unit alcohol (CH₃OH-type): not pyranose, not triol, MW < 50."""
    from hqiv_lab.pyranose_geometry import has_pyranose_ring

    if has_pyranose_ring(spec) or is_triol_polyol(spec):
        return False
    if spec.molecular_weight_amu >= 50.0:
        return False
    return _count_oh_groups(spec.fragments, spec.bonds) >= 1


def monomer_polyol_liquid_density_factor() -> float:
    """Liquid ρ correction above monomer alcohol T_melt (Lean ``monomerPolyolLiquidDensityFactor``)."""
    return 1.0 + lean.GAMMA / 4.0


def polyol_triol_liquid_density_factor() -> float:
    """Liquid ρ scale above triol T_melt (Lean ``polyolTriolLiquidDensityFactor``)."""
    return 1.0 + lean.GAMMA / 6.0

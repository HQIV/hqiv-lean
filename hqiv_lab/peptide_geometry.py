"""Peptide backbone contact graph for layer Bravais (no tabulated Å)."""

from __future__ import annotations

import math

from functools import lru_cache

from hqiv_lab._scripts import ensure_scripts_on_path
from hqiv_lab.spec import MoleculeSpec

ensure_scripts_on_path()
import hqiv_lean_physics_primitives as lean  # noqa: E402

from fragment_aware_bonded_horizon import BondGeometry, FragmentConfig  # noqa: E402


def _is_backbone_label(label: str) -> bool:
    u = label.upper()
    return u.startswith("N") or u.startswith("CA") or u in ("C", "C1", "C2")


def peptide_backbone_bond_lengths(
    fragments: tuple[FragmentConfig, ...],
    bonds: tuple[BondGeometry, ...],
) -> tuple[float, ...]:
    """Bond lengths along labelled backbone path (N–CA–C–N–…)."""
    idx = {f.label.upper(): i for i, f in enumerate(fragments)}
    # gly-gly order: N1-CA1-C1-N2-CA2-C2
    path_labels = ("N1", "CA1", "C1", "N2", "CA2", "C2")
    if not all(l in idx for l in path_labels):
        # generic: heavy bonds in bond list order among backbone atoms
        backbone = {i for i, f in enumerate(fragments) if _is_backbone_label(f.label)}
        out: list[float] = []
        for b in bonds:
            if b.frag_i in backbone and b.frag_j in backbone:
                out.append(b.distance_angstrom)
        return tuple(out)
    lengths: list[float] = []
    for a, b_label in zip(path_labels, path_labels[1:]):
        ia, ib = idx[a], idx[b_label]
        for bond in bonds:
            if (bond.frag_i, bond.frag_j) == (ia, ib) or (bond.frag_j, bond.frag_i) == (ia, ib):
                lengths.append(bond.distance_angstrom)
                break
    return tuple(lengths)


def peptide_backbone_mean_bond_angstrom(spec: MoleculeSpec) -> float:
    lengths = peptide_backbone_bond_lengths(spec.fragments, spec.bonds)
    if not lengths:
        return 1.0
    return sum(lengths) / len(lengths)


def peptide_backbone_bond_count(spec: MoleculeSpec) -> int:
    return max(len(peptide_backbone_bond_lengths(spec.fragments, spec.bonds)), 1)


def peptide_backbone_diameter_factor() -> float:
    return 2.0 * (1.0 + lean.ALPHA + lean.GAMMA / 8.0)


def peptide_backbone_open_factor() -> float:
    return 1.0 + lean.GAMMA / 8.0


def peptide_sheet_short_axis_factor(n_backbone: int) -> float:
    base = (1.0 + lean.GAMMA / 8.0) / (1.0 + lean.ALPHA / 4.0)
    closure = 1.0 + lean.GAMMA / (float(n_backbone**2 + 2))
    return base / closure


def peptide_backbone_contact_distance_angstrom(spec: MoleculeSpec, *, n_inter: int) -> float:
    mean = peptide_backbone_mean_bond_angstrom(spec)
    sc = lean.STRONG_CHANNEL_FRACTION
    dress = math.sqrt(1.0 + sc * float(max(n_inter, 1)) / 4.0)
    return mean * peptide_backbone_diameter_factor() * peptide_backbone_open_factor() * dress


def peptide_sheet_axis_factors(spec: MoleculeSpec) -> tuple[float, float, float]:
    n_bb = peptide_backbone_bond_count(spec)
    sc = lean.STRONG_CHANNEL_FRACTION
    a = math.sqrt(2.0) * (1.0 + lean.ALPHA / 2.0)
    b = (1.0 + lean.ALPHA + lean.GAMMA / 8.0) * math.sqrt(2.0) * math.sqrt(1.0 + sc / 4.0)
    c = peptide_sheet_short_axis_factor(n_bb)
    return a, b, c


@lru_cache(maxsize=1)
def ca_ca_step_angstrom() -> float:
    """Adjacent Cα–Cα spacing from derived backbone placement (extended control)."""
    from hqiv_lab.miniprotein_backbone import place_ca_trace, ramachandran_extended_rad

    ca = place_ca_trace("GG", (ramachandran_extended_rad(), ramachandran_extended_rad()))
    dx = ca[1][0] - ca[0][0]
    dy = ca[1][1] - ca[0][1]
    dz = ca[1][2] - ca[0][2]
    return math.sqrt(dx * dx + dy * dy + dz * dz)


@lru_cache(maxsize=1)
def helix_ca_i_i3_distance_angstrom() -> float:
    """Helix Cα_i–Cα_{i+3} from α-Ramachandran NeRF spine (self-consistent with fold)."""
    from hqiv_lab.miniprotein_backbone import place_ca_trace, ramachandran_alpha_rad

    ca = place_ca_trace("AAAA", (ramachandran_alpha_rad(),) * 4)
    dx = ca[0][0] - ca[3][0]
    dy = ca[0][1] - ca[3][1]
    dz = ca[0][2] - ca[3][2]
    return math.sqrt(dx * dx + dy * dy + dz * dz)


@lru_cache(maxsize=1)
def helix_ca_i_i4_distance_angstrom() -> float:
    """Helix Cα_i–Cα_{i+4} from α-Ramachandran NeRF spine."""
    from hqiv_lab.miniprotein_backbone import place_ca_trace, ramachandran_alpha_rad

    ca = place_ca_trace("AAAAA", (ramachandran_alpha_rad(),) * 5)
    dx = ca[0][0] - ca[4][0]
    dy = ca[0][1] - ca[4][1]
    dz = ca[0][2] - ca[4][2]
    return math.sqrt(dx * dx + dy * dy + dz * dz)


@lru_cache(maxsize=1)
def sheet_ca_i_i2_distance_angstrom() -> float:
    """In-strand β Cα_i–Cα_{i+2} from β-Ramachandran NeRF spine."""
    from hqiv_lab.miniprotein_backbone import place_ca_trace, ramachandran_beta_rad

    ca = place_ca_trace("AAA", (ramachandran_beta_rad(),) * 3)
    dx = ca[0][0] - ca[2][0]
    dy = ca[0][1] - ca[2][1]
    dz = ca[0][2] - ca[2][2]
    return math.sqrt(dx * dx + dy * dy + dz * dz)


@lru_cache(maxsize=1)
def helix_ca_i_i3_nominal_scale() -> float:
    """Nominal pitch slot ``1 + α + γ/4`` (Lean ``helixCaIi3DistanceScale``)."""
    return 1.0 + lean.ALPHA + lean.GAMMA / 4.0


@lru_cache(maxsize=1)
def helix_ca_i_i3_distance_nominal_angstrom() -> float:
    """Nominal helix i+3 target: adjacent Cα step · ``(1 + α + γ/4)``."""
    return ca_ca_step_angstrom() * helix_ca_i_i3_nominal_scale()


def compact_terminus_ca_distance_angstrom(n_residues: int, *, contact_angstrom: float) -> float:
    """Compact miniprotein end-to-end Cα target: contact · √(n/6)."""
    n = max(n_residues, 2)
    return contact_angstrom * math.sqrt(n / 6.0)


@lru_cache(maxsize=1)
def helix_sheet_ca_packing_distance_angstrom() -> float:
    """
    Cross-register Cα distance between adjacent β-strand and α-helix segments.

    Mean of spine-measured helix i+3 and sheet i+2 slots, dressed by the 3.6-turn
    ψ channel ``(1 + γ/6)`` (same factor as Ramachandran α ψ dress).
    """
    h3 = helix_ca_i_i3_distance_angstrom()
    s2 = sheet_ca_i_i2_distance_angstrom()
    return (h3 + s2) / 2.0 * (1.0 + lean.GAMMA / 6.0)

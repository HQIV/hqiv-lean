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
def helix_ca_i_i3_distorted_distance_angstrom() -> float:
    """Helix Cα_i–Cα_{i+3} from distorted-helix basin (compact miniprotein)."""
    from hqiv_lab.miniprotein_backbone import place_ca_trace, ramachandran_distorted_helix_rad

    d = ramachandran_distorted_helix_rad()
    ca = place_ca_trace("AAAA", (d,) * 4)
    return math.dist(ca[0], ca[3])


@lru_cache(maxsize=1)
def helix_ca_i_i4_distorted_distance_angstrom() -> float:
    """Helix Cα_i–Cα_{i+4} from distorted-helix basin."""
    from hqiv_lab.miniprotein_backbone import place_ca_trace, ramachandran_distorted_helix_rad

    d = ramachandran_distorted_helix_rad()
    ca = place_ca_trace("AAAAA", (d,) * 5)
    return math.dist(ca[0], ca[4])


@lru_cache(maxsize=1)
def helix_sheet_hairpin_compact_distance_angstrom() -> float:
    """Sheet–helix register from compact spine (strap₃–turn–distorted-helix₁)."""
    from hqiv_lab.miniprotein_backbone import (
        place_ca_trace,
        ramachandran_distorted_helix_rad,
        ramachandran_strap_helix_turn_rad,
        ramachandran_strap_rad,
    )

    ca = place_ca_trace(
        "LYIQWL",
        (
            ramachandran_strap_rad(),
            ramachandran_strap_rad(),
            ramachandran_strap_rad(),
            ramachandran_strap_helix_turn_rad(),
            ramachandran_strap_helix_turn_rad(),
            ramachandran_distorted_helix_rad(),
        ),
    )
    return math.dist(ca[2], ca[5])


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
def sheet_ca_i_i2_strap_distance_angstrom() -> float:
    """Hairpin strap Cα_i–Cα_{i+2} (φ = γπ, ψ = (α/2)π)."""
    from hqiv_lab.miniprotein_backbone import place_ca_trace, ramachandran_strap_rad

    ca = place_ca_trace("AAA", (ramachandran_strap_rad(),) * 3)
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
    """Cross-register Cα distance (canonical β + α basins, dressed by ``1 + γ/6``)."""
    h3 = helix_ca_i_i3_distance_angstrom()
    s2 = sheet_ca_i_i2_distance_angstrom()
    return (h3 + s2) / 2.0 * (1.0 + lean.GAMMA / 6.0)


def covalent_backbone_curvature_at_site(
    theta_rad: float,
    *,
    medium_density_fraction: float,
) -> dict[str, float]:
    """
    Covalent bond curvature witness at a protein site with bulk ρ from solvent phase.

    Bridges ``bond_curvature_quant_witness`` (small-molecule Compton θ) to
    ``contact_curvature_weight`` tertiary dress on the same spine constants.
    """
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_curvature_bond_state as cbs

    return cbs.bond_curvature_quant_witness(
        theta_rad,
        medium_density_fraction=medium_density_fraction,
    )


def stacked_line_outside_curvature_scale(theta_rad: float) -> float:
    """
    Lean ``outsideContactCoupling`` / ``stackedLineOutsideCurvatureScale``.

    Stacked in-register Cα contacts shorten by ``(θ/θ₀)^α`` with α = 3/5
  (``G_eff`` on the Compton IR-window contact angle).
    """
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_curvature_bond_state as cbs

    theta0 = cbs.phase_theta()
    theta = min(max(theta_rad, 1e-12), theta0)
    return cbs.outside_contact_coupling(theta)


def backbone_stacking_angle_rad(
    ca: list[tuple[float, float, float]],
    i: int,
    j: int,
) -> float:
    """
    Backbone flow angle at site ``i`` toward partner ``j``.

    For in-register sheet i+2 slots prefer ``strand_register_stacking_angle_rad``.
    """
    n = len(ca)
    if n < 2 or i < 0 or j < 0 or i >= n or j >= n or i == j:
        return math.pi / 2.0
    if i > 0:
        vin = (ca[i][0] - ca[i - 1][0], ca[i][1] - ca[i - 1][1], ca[i][2] - ca[i - 1][2])
    elif i + 1 < n:
        vin = (ca[i + 1][0] - ca[i][0], ca[i + 1][1] - ca[i][1], ca[i + 1][2] - ca[i][2])
    else:
        return math.pi / 2.0
    vout = (ca[j][0] - ca[i][0], ca[j][1] - ca[i][1], ca[j][2] - ca[i][2])
    mag_in = math.sqrt(vin[0] ** 2 + vin[1] ** 2 + vin[2] ** 2)
    mag_out = math.sqrt(vout[0] ** 2 + vout[1] ** 2 + vout[2] ** 2)
    if mag_in < 1e-12 or mag_out < 1e-12:
        return math.pi / 2.0
    cosang = max(-1.0, min(1.0, (vin[0] * vout[0] + vin[1] * vout[1] + vin[2] * vout[2]) / (mag_in * mag_out)))
    return math.acos(cosang)


def strand_register_stacking_angle_rad(
    ca: list[tuple[float, float, float]],
    i: int,
    j: int,
) -> float:
    """Interior strand bend at ``i+1`` for in-register sheet i+2 (stacked-line θ)."""
    if j != i + 2 or i + 2 >= len(ca):
        return math.pi / 2.0
    v1 = (ca[i + 1][0] - ca[i][0], ca[i + 1][1] - ca[i][1], ca[i + 1][2] - ca[i][2])
    v2 = (ca[j][0] - ca[i + 1][0], ca[j][1] - ca[i + 1][1], ca[j][2] - ca[i + 1][2])
    mag1 = math.sqrt(v1[0] ** 2 + v1[1] ** 2 + v1[2] ** 2)
    mag2 = math.sqrt(v2[0] ** 2 + v2[1] ** 2 + v2[2] ** 2)
    if mag1 < 1e-12 or mag2 < 1e-12:
        return math.pi / 2.0
    cosang = max(-1.0, min(1.0, (v1[0] * v2[0] + v1[1] * v2[1] + v1[2] * v2[2]) / (mag1 * mag2)))
    return math.acos(cosang)


@lru_cache(maxsize=1)
def beta_strand_stacking_angle_rad() -> float:
    """Open β-basin strand bend on the proved i+2 NeRF prototype (dress θ source)."""
    from hqiv_lab.miniprotein_backbone import place_ca_trace, ramachandran_beta_rad

    ca = place_ca_trace("AAA", (ramachandran_beta_rad(),) * 3)
    return strand_register_stacking_angle_rad(ca, 0, 2)


def dress_stacked_line_contact_distance(
    base_angstrom: float,
    ca: list[tuple[float, float, float]],
    i: int,
    j: int,
    *,
    open_beta_spine: bool = False,
) -> float:
    """
    Apply outside ``G_eff(θ)`` shortening to an open-register stacked Cα target.

    Open canonical β i+2 uses the β-spine bend (not the fold register trace) so the
    contraction factor matches ``outsideContactCoupling`` on the proved β prototype.
    Only the γ lattice channel participates in contact breathing (sheet i+2 scale uses
    ``1 + γ/4``): ``1 + (γ/2)·(G_eff − 1)`` rather than full ``G_eff``.
    """
    if open_beta_spine:
        theta = beta_strand_stacking_angle_rad()
    else:
        theta = strand_register_stacking_angle_rad(ca, i, j)
    geff = stacked_line_outside_curvature_scale(theta)
    channel = lean.GAMMA / 2.0
    partial = 1.0 + channel * (geff - 1.0)
    return base_angstrom * partial


@lru_cache(maxsize=1)
def helix_sheet_hairpin_distance_angstrom() -> float:
    """Sheet–helix register from strap hairpin prototype (E₃–βα-turn–strap cap)."""
    from hqiv_lab.miniprotein_backbone import (
        place_ca_trace,
        ramachandran_sheet_helix_turn_rad,
        ramachandran_strap_rad,
    )

    ca = place_ca_trace(
        "LYIQWL",
        (
            ramachandran_strap_rad(),
            ramachandran_strap_rad(),
            ramachandran_strap_rad(),
            ramachandran_sheet_helix_turn_rad(),
            ramachandran_sheet_helix_turn_rad(),
            ramachandran_strap_rad(),
        ),
    )
    return math.dist(ca[2], ca[5])

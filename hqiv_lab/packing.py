"""Crystal packing templates — unit-cell geometry from monomer + motif."""

from __future__ import annotations

import math
from dataclasses import dataclass
from enum import Enum

from hqiv_lab.coordination import IntermolecularMotif, MonomerGeometry

from hqiv_lab._scripts import ensure_scripts_on_path

ensure_scripts_on_path()
import hqiv_lean_physics_primitives as lean  # noqa: E402

# Ice Ih hexagonal c/a from tetrahedral O···O network (2√6/3).
HEX_ICE_CA_RATIO = 2.0 * math.sqrt(6.0) / 3.0
# Basal O···O spacing / nn distance in ice Ih.
HEX_ICE_A_OVER_R = math.sqrt(8.0 / 3.0)
# FCC molecular solid: cell edge / centre–centre contact.
FCC_A_OVER_R = math.sqrt(2.0)
# Orthorhombic Z=4 molecular: edge / nn (pyramidal / layered H-bond).
ORTHO_Z4_EDGE_OVER_R = (1.0 + lean.ALPHA) * math.sqrt(3.0 / 2.0)


class CrystalSystem(str, Enum):
    HEXAGONAL = "hexagonal"
    CUBIC = "cubic"
    ORTHORHOMBIC = "orthorhombic"


class BravaisTopology(str, Enum):
    """How nearest-neighbour contact maps to unit-cell edges (no fitted Å)."""

    HEX_ICE_IH = "hex_ice_ih"
    FCC_Z4 = "fcc_z4"
    CUBIC_Z2 = "cubic_z2"
    ORTHO_Z4 = "ortho_z4"
    CHAIN_Z4 = "chain_z4"
    DIATOMIC_ORTHO = "diatomic_ortho"
    GENERIC_CUBIC = "generic_cubic"


@dataclass(frozen=True)
class PackingTemplate:
    """Named allotrope family + Bravais topology for lattice build."""

    label: str
    crystal: CrystalSystem
    molecules_per_cell: int
    topology: BravaisTopology
    description: str = ""
    # Legacy multipliers retained only for disordered / cubic-ice branches.
    a_factor: float = 1.0
    c_factor: float | None = None
    b_factor: float | None = None


def _bend_dress(mono: MonomerGeometry) -> float:
    """Bent-centre lift from H–X–H opening (γ/2 slot, same as prior packing)."""
    return 0.5 * (1.0 - math.cos(0.5 * mono.bond_angle_rad))


def _steric_domain_count(mono: MonomerGeometry) -> int:
    return mono.n_bonds_at_heavy + mono.lone_pair_count


def intermolecular_contact_distance_angstrom(mono: MonomerGeometry) -> float:
    """
    Nearest-neighbour centre–centre separation r_nn [Å] — distinct from covalent r.

    H-bond networks: O–H···O path = 2 r_cov + r_cov·α·(1 + strongChannelFraction)·dress.
    Apolar tetrahedral: 2 r_cov·(1+α)·√(1 + n_domains·strongChannelFraction/4).
    Diatomic: 2 r_cov·(1+α).
    """
    r = mono.mean_bond_length_angstrom
    sc = lean.STRONG_CHANNEL_FRACTION
    n_dom = _steric_domain_count(mono)
    if mono.motif in (
        IntermolecularMotif.TETRAHEDRAL_HBOND,
        IntermolecularMotif.PYRAMIDAL_HBOND,
        IntermolecularMotif.LINEAR_CHAIN,
    ):
        r_hbond = r * lean.ALPHA * (1.0 + sc) * (1.0 + lean.C_RINDLER_SHARED * _bend_dress(mono))
        if mono.motif == IntermolecularMotif.PYRAMIDAL_HBOND:
            # Acceptor lone-pair + 3-fold donor network (NH₃-type).
            r_hbond *= 1.0 + n_dom / 8.0
        return 2.0 * r + r_hbond
    if mono.motif == IntermolecularMotif.APOLAR_CLOSE_PACK:
        n_dom = _steric_domain_count(mono)
        return 2.0 * r * (1.0 + lean.ALPHA) * math.sqrt(1.0 + n_dom * sc / 4.0)
    if mono.motif == IntermolecularMotif.DIATOMIC:
        return 2.0 * r * (1.0 + lean.ALPHA)
    return 2.0 * r * (1.0 + lean.ALPHA)


def contact_distance_angstrom(mono: MonomerGeometry) -> float:
    """Alias: lattice builders use intermolecular nn distance."""
    return intermolecular_contact_distance_angstrom(mono)


def thermal_contact_scale(temperature_k: float, *, exponent: float | None = None) -> float:
    """
    Thermal breathing of nn contact distance.

    Low T → tighter pack: ``(T/T_ref)^exponent`` with ``T_ref = 273.15 K``.
    Apolar solids use ``exponent = γ/16`` (weak zero-point contraction slot).
    """
    t_ref = 273.15
    if temperature_k <= 0.0:
        return 1.0
    exp = lean.GAMMA / 4.0 if exponent is None else exponent
    return (temperature_k / t_ref) ** exp


def lattice_constants_from_topology(
    mono: MonomerGeometry,
    template: PackingTemplate,
    *,
    temperature_k: float = 273.15,
) -> tuple[float, float, float]:
    """Bravais (a,b,c) from r_nn and topology — lattice constant ≠ r_nn when Z>1."""
    r = intermolecular_contact_distance_angstrom(mono)
    if mono.motif == IntermolecularMotif.APOLAR_CLOSE_PACK:
        r *= thermal_contact_scale(temperature_k, exponent=lean.GAMMA / 16.0)
    n_dom = _steric_domain_count(mono)
    topo = template.topology

    if topo == BravaisTopology.HEX_ICE_IH:
        a = r * HEX_ICE_A_OVER_R
        c = a * HEX_ICE_CA_RATIO
        return a, a, c

    if topo == BravaisTopology.FCC_Z4:
        open_cell = 1.0
        if mono.motif == IntermolecularMotif.PYRAMIDAL_HBOND:
            # 3-fold H-bond network: γ/4 cell breathing vs 4-fold tetrahedral ice.
            open_cell = 1.0 + lean.GAMMA / 4.0
        a = r * FCC_A_OVER_R * open_cell
        return a, a, a

    if topo == BravaisTopology.CUBIC_Z2:
        a = r * template.a_factor
        return a, a, a

    if topo in (BravaisTopology.ORTHO_Z4, BravaisTopology.CHAIN_Z4):
        sc = lean.STRONG_CHANNEL_FRACTION
        if topo == BravaisTopology.ORTHO_Z4:
            # Pyramidal molecular orthorhombic: √2 nn spacing + lone-pair shear.
            edge = r * math.sqrt(2.0) * (1.0 + lean.ALPHA / 2.0)
            shear = 1.0 + sc * mono.lone_pair_count / max(n_dom, 1)
            return edge, edge * shear, edge / shear
        # Zigzag chain layer (HF-type).
        edge = r * ORTHO_Z4_EDGE_OVER_R
        a = r * (1.0 + lean.ALPHA)
        b = r * (1.0 + sc)
        c = edge * (1.0 + lean.GAMMA / 2.0)
        return a, b, c

    if topo == BravaisTopology.DIATOMIC_ORTHO:
        a = r * (1.0 + lean.ALPHA)
        b = r * (1.0 + lean.GAMMA)
        c = r * (1.0 + lean.ALPHA + lean.GAMMA)
        return a, b, c

    # Generic / disordered: legacy factor path.
    a = r * template.a_factor
    b = r * (template.b_factor if template.b_factor is not None else template.a_factor)
    c = r * (template.c_factor if template.c_factor is not None else a)
    if template.crystal == CrystalSystem.CUBIC:
        return a, a, a
    if template.crystal == CrystalSystem.HEXAGONAL:
        return a, a, c
    return a, b, c


def templates_for_motif(motif: IntermolecularMotif) -> tuple[PackingTemplate, ...]:
    """Candidate packing families implied by the monomer motif."""
    if motif == IntermolecularMotif.TETRAHEDRAL_HBOND:
        return (
            PackingTemplate(
                "Ih",
                CrystalSystem.HEXAGONAL,
                4,
                BravaisTopology.HEX_ICE_IH,
                description="Hexagonal ice (tetrahedral H-bond, c/a=2√6/3)",
            ),
            PackingTemplate(
                "Ic",
                CrystalSystem.CUBIC,
                2,
                BravaisTopology.CUBIC_Z2,
                a_factor=math.sqrt(2.0),
                description="Cubic ice (diamond-related H-bond)",
            ),
            PackingTemplate(
                "amorphous",
                CrystalSystem.CUBIC,
                1,
                BravaisTopology.GENERIC_CUBIC,
                a_factor=1.0 + lean.ALPHA + lean.GAMMA,
                description="Low-density amorphous solid (disordered tetrahedral)",
            ),
        )
    if motif == IntermolecularMotif.PYRAMIDAL_HBOND:
        return (
            PackingTemplate(
                "solid",
                CrystalSystem.CUBIC,
                4,
                BravaisTopology.FCC_Z4,
                description="Molecular fcc (NH3-type, Z=4, 3-fold H-bond)",
            ),
        )
    if motif == IntermolecularMotif.APOLAR_CLOSE_PACK:
        return (
            PackingTemplate(
                "solid_I",
                CrystalSystem.CUBIC,
                4,
                BravaisTopology.FCC_Z4,
                description="Molecular fcc (CH4-type, Z=4)",
            ),
        )
    if motif == IntermolecularMotif.LINEAR_CHAIN:
        return (
            PackingTemplate(
                "chain",
                CrystalSystem.ORTHORHOMBIC,
                4,
                BravaisTopology.CHAIN_Z4,
                description="Zigzag H-bond chain layers (HF-type, Z=4)",
            ),
        )
    if motif == IntermolecularMotif.DIATOMIC:
        return (
            PackingTemplate(
                "solid",
                CrystalSystem.ORTHORHOMBIC,
                2,
                BravaisTopology.DIATOMIC_ORTHO,
                description="Diatomic orthorhombic",
            ),
        )
    return (
        PackingTemplate(
            "solid",
            CrystalSystem.CUBIC,
            1,
            BravaisTopology.GENERIC_CUBIC,
            a_factor=1.0 + lean.ALPHA,
            description="Generic cubic molecular cell",
        ),
    )


def lattice_constants_from_template(
    mono: MonomerGeometry,
    template: PackingTemplate,
    *,
    temperature_k: float = 273.15,
) -> tuple[float, float, float]:
    """Return (a, b, c) in ångström from monomer nn contact + Bravais topology."""
    return lattice_constants_from_topology(mono, template, temperature_k=temperature_k)

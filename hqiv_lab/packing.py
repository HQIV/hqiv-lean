"""Crystal packing templates — unit-cell geometry from monomer + motif."""

from __future__ import annotations

import math
from dataclasses import dataclass
from enum import Enum

from hqiv_lab.coordination import IntermolecularMotif, MonomerGeometry
from hqiv_lab.spec import MoleculeSpec

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
    PYRANOSE_CHAIR_Z4 = "pyranose_chair_z4"
    TRIOL_LAYER_Z4 = "triol_layer_z4"
    PEPTIDE_SHEET_Z4 = "peptide_sheet_z4"
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
    """Bent-centre lift from H–X–H opening (γ/2 slot); zero for linear monomers."""
    if mono.n_bonds_at_heavy <= 1:
        return 0.0
    return 0.5 * (1.0 - math.cos(0.5 * mono.bond_angle_rad))


def halogen_strong_hbond_leg_factor(mono: MonomerGeometry) -> float:
    """
    Short strong H···X H-bonds on halogen zigzag chains (HF-type, Z ≥ 9).

    ``1 − γ·(4/8)·max(Z−8,0)/Z`` compresses the intermolecular leg vs the
    generic α-slot (mirrors optical halogen dress, inverted on contact).
    """
    if mono.motif != IntermolecularMotif.LINEAR_CHAIN or mono.z_heavy < 9:
        return 1.0
    z_slot = max(float(mono.z_heavy - 8), 0.0) / float(mono.z_heavy)
    return max(0.5, 1.0 - lean.GAMMA * lean.STRONG_CHANNEL_FRACTION * z_slot)


def linear_chain_zigzag_lattice_open_factor(mono: MonomerGeometry) -> float:
    """
    Bm21b zigzag chains need more orthorhombic cell breathing than collinear r_nn.

    ``1 + γ/(6·n_inter)`` on CHAIN_Z4 edges (HQIV rationals; n_inter = 2 for HF).
    """
    if mono.motif != IntermolecularMotif.LINEAR_CHAIN or mono.z_heavy < 9:
        return 1.0
    n_inter = max(mono.intermolecular_contacts, 1)
    return 1.0 + lean.GAMMA / (6.0 * float(n_inter))


def neighbor_covalent_lapse_overlap_factor(mono: MonomerGeometry) -> float:
    """
    Bulk H-bond network: overlapping covalent O–H lapses from tetrahedral neighbors
    shrink the shared intermolecular well.

    ``1 − γ·(4/8) / n_inter`` for tetrahedral bulk ice (4-valent O···O network).
    Pyramidal / chain motifs use separate open-cell slots instead.
    """
    if mono.motif != IntermolecularMotif.TETRAHEDRAL_HBOND:
        return 1.0
    n_coord = max(mono.intermolecular_contacts, 1)
    shrink = lean.GAMMA * lean.STRONG_CHANNEL_FRACTION / float(n_coord)
    return max(0.5, 1.0 - shrink)


def molecular_melt_density_ratio(
    mono: MonomerGeometry,
    template: PackingTemplate | None = None,
) -> tuple[float, bool]:
    """
    min(ρ_s, ρ_m)/max(ρ_s, ρ_m) from lattice geometry (packing spine, not a table).

    Returns (ratio, solid_denser).  Tetrahedral ice uses neighbor lapse overlap;
    pyramidal / chain / apolar use the same open-cell factors as ``lattice_constants_from_topology``.
    """
    _ = template
    g = lean.GAMMA
    a = lean.ALPHA

    if mono.motif == IntermolecularMotif.TETRAHEDRAL_HBOND:
        overlap = neighbor_covalent_lapse_overlap_factor(mono)
        ratio = overlap * lean.PHASE_LIFT_3 / (1.0 + a)
        return min(1.0, max(0.0, ratio)), False

    if mono.motif == IntermolecularMotif.PYRAMIDAL_HBOND:
        open_cell = 1.0 + g / 4.0
        return min(1.0, 1.0 / open_cell), False

    if mono.motif == IntermolecularMotif.APOLAR_CLOSE_PACK:
        ratio = 1.0 - g / 4.0
        return min(1.0, max(0.0, ratio)), True

    if mono.motif == IntermolecularMotif.LINEAR_CHAIN:
        open_chain = linear_chain_zigzag_lattice_open_factor(mono)
        ratio = 1.0 / max(open_chain, 1.0)
        return min(1.0, max(0.0, ratio)), False

    if mono.motif == IntermolecularMotif.POLYOL_HBOND:
        import hqiv_phase_geometry_density as pgd

        ratio = pgd.tetrahedral_melt_density_ratio(mono.intermolecular_contacts)
        return min(1.0, max(0.0, ratio)), True

    if mono.motif == IntermolecularMotif.PEPTIDE_LAYER:
        open_cell = 1.0 + g / 8.0
        return min(1.0, 1.0 / open_cell), True

    return 1.0, False


def melt_density_g_cm3_from_solid(
    rho_solid_g_cm3: float,
    melt_ratio: float,
    *,
    solid_denser: bool,
) -> float:
    """ρ at melt comparison from solid ρ and dynamic min/max ratio."""
    if rho_solid_g_cm3 <= 0.0 or melt_ratio <= 0.0:
        return 0.0
    if solid_denser:
        return rho_solid_g_cm3 * melt_ratio
    return rho_solid_g_cm3 / max(melt_ratio, 1e-30)


def _steric_domain_count(mono: MonomerGeometry) -> int:
    return mono.n_bonds_at_heavy + mono.lone_pair_count


def intermolecular_contact_distance_angstrom(
    mono: MonomerGeometry,
    *,
    spec: MoleculeSpec | None = None,
) -> float:
    """
    Nearest-neighbour centre–centre separation r_nn [Å] — distinct from covalent r.

    H-bond networks: O–H···O path = 2 r_cov + r_hbond, with r_hbond dressed by
    neighbor covalent lapse overlap in bulk tetrahedral / pyramidal networks.
    Pyranose polyols: ring contact graph chair span (``pyranose_ring_contact_distance``).
    Apolar tetrahedral: 2 r_cov·(1+α)·√(1 + n_domains·strongChannelFraction/4).
    Diatomic: 2 r_cov·(1+α).
    """
    if spec is not None and mono.motif == IntermolecularMotif.POLYOL_HBOND:
        from hqiv_lab.pyranose_geometry import (
            pyranose_ring_contact_distance_angstrom,
            pyranose_ring_mean_bond_angstrom,
        )

        ring_mean = pyranose_ring_mean_bond_angstrom(spec)
        if ring_mean is not None:
            return pyranose_ring_contact_distance_angstrom(
                ring_mean, n_inter=mono.intermolecular_contacts
            )

    r = mono.mean_bond_length_angstrom
    sc = lean.STRONG_CHANNEL_FRACTION
    n_dom = _steric_domain_count(mono)
    if mono.motif in (
        IntermolecularMotif.TETRAHEDRAL_HBOND,
        IntermolecularMotif.PYRAMIDAL_HBOND,
        IntermolecularMotif.LINEAR_CHAIN,
        IntermolecularMotif.POLYOL_HBOND,
        IntermolecularMotif.PEPTIDE_LAYER,
    ):
        r_hbond = r * lean.ALPHA * (1.0 + sc) * (1.0 + lean.C_RINDLER_SHARED * _bend_dress(mono))
        if mono.motif == IntermolecularMotif.PYRAMIDAL_HBOND:
            # Acceptor lone-pair + 3-fold donor network (NH₃-type).
            r_hbond *= 1.0 + n_dom / 8.0
        r_hbond *= neighbor_covalent_lapse_overlap_factor(mono)
        if mono.motif == IntermolecularMotif.LINEAR_CHAIN:
            r_hbond *= halogen_strong_hbond_leg_factor(mono)
        return 2.0 * r + r_hbond
    if mono.motif == IntermolecularMotif.APOLAR_CLOSE_PACK:
        n_dom = _steric_domain_count(mono)
        return 2.0 * r * (1.0 + lean.ALPHA) * math.sqrt(1.0 + n_dom * sc / 4.0)
    if mono.motif == IntermolecularMotif.DIATOMIC:
        return 2.0 * r * (1.0 + lean.ALPHA)
    return 2.0 * r * (1.0 + lean.ALPHA)


def contact_distance_angstrom(
    mono: MonomerGeometry,
    *,
    spec: MoleculeSpec | None = None,
) -> float:
    """Alias: lattice builders use intermolecular nn distance."""
    return intermolecular_contact_distance_angstrom(mono, spec=spec)


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
    spec: MoleculeSpec | None = None,
) -> tuple[float, float, float]:
    """Bravais (a,b,c) from r_nn and topology — lattice constant ≠ r_nn when Z>1."""
    r = intermolecular_contact_distance_angstrom(mono, spec=spec)
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
        open_chain = linear_chain_zigzag_lattice_open_factor(mono)
        a = r * (1.0 + lean.ALPHA) * open_chain
        b = r * (1.0 + sc) * open_chain
        c = edge * (1.0 + lean.GAMMA / 2.0) * open_chain
        return a, b, c

    if topo == BravaisTopology.DIATOMIC_ORTHO:
        a = r * (1.0 + lean.ALPHA)
        b = r * (1.0 + lean.GAMMA)
        c = r * (1.0 + lean.ALPHA + lean.GAMMA)
        return a, b, c

    if topo == BravaisTopology.PYRANOSE_CHAIR_Z4:
        from hqiv_lab.pyranose_geometry import (
            pyranose_chair_inplane_axis_factor,
            pyranose_chair_short_axis_factor,
            pyranose_chair_stack_axis_factor,
            pyranose_disaccharide_cell_scale,
            pyranose_ring_count,
        )

        a = r * pyranose_chair_inplane_axis_factor()
        b = r * pyranose_chair_stack_axis_factor()
        c = r * pyranose_chair_short_axis_factor()
        if spec is not None:
            scale = pyranose_disaccharide_cell_scale(pyranose_ring_count(spec))
            a *= scale
            b *= scale
            c *= scale
        return a, b, c

    if topo == BravaisTopology.TRIOL_LAYER_Z4:
        from hqiv_lab.polyol_geometry import triol_bravais_axis_factors

        fa, fb, fc = triol_bravais_axis_factors()
        return r * fa, r * fb, r * fc

    if topo == BravaisTopology.PEPTIDE_SHEET_Z4:
        sc = lean.STRONG_CHANNEL_FRACTION
        edge = r * math.sqrt(2.0) * (1.0 + lean.ALPHA / 2.0)
        shear = 1.0 + sc * mono.lone_pair_count / max(n_dom, 1)
        open_scale = 1.0 + lean.ALPHA / 8.0
        return edge * open_scale, edge * shear * open_scale, edge / shear * open_scale

    # Generic / disordered: legacy factor path.
    a = r * template.a_factor
    b = r * (template.b_factor if template.b_factor is not None else template.a_factor)
    c = r * (template.c_factor if template.c_factor is not None else a)
    if template.crystal == CrystalSystem.CUBIC:
        return a, a, a
    if template.crystal == CrystalSystem.HEXAGONAL:
        return a, a, c
    return a, b, c


def templates_for_motif(
    motif: IntermolecularMotif,
    *,
    spec: MoleculeSpec | None = None,
) -> tuple[PackingTemplate, ...]:
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
    if motif == IntermolecularMotif.POLYOL_HBOND:
        from hqiv_lab.pyranose_geometry import has_pyranose_ring

        if spec is not None and has_pyranose_ring(spec):
            from hqiv_lab.pyranose_geometry import pyranose_molecules_per_cell

            z_cell = pyranose_molecules_per_cell()
            return (
                PackingTemplate(
                    "chair",
                    CrystalSystem.ORTHORHOMBIC,
                    z_cell,
                    BravaisTopology.PYRANOSE_CHAIR_Z4,
                    description="Pyranose chair layer (ring contact graph, Z=4)",
                ),
            )
        if spec is not None and spec.molecular_weight_amu < 50.0:
            return (
                PackingTemplate(
                    "solid",
                    CrystalSystem.CUBIC,
                    4,
                    BravaisTopology.FCC_Z4,
                    description="Compact monomer alcohol fcc (CH3OH-type, Z=4)",
                ),
                PackingTemplate(
                    "layered",
                    CrystalSystem.ORTHORHOMBIC,
                    4,
                    BravaisTopology.ORTHO_Z4,
                    description="Layered OH alcohol H-bond network (Z=4)",
                ),
            )
        from hqiv_lab.polyol_geometry import is_triol_polyol

        if spec is not None and is_triol_polyol(spec):
            return (
                PackingTemplate(
                    "layered",
                    CrystalSystem.ORTHORHOMBIC,
                    4,
                    BravaisTopology.ORTHO_Z4,
                    description="Layered triol OH network (glycerol-type, Z=4)",
                ),
            )
        return (
            PackingTemplate(
                "layered",
                CrystalSystem.ORTHORHOMBIC,
                4,
                BravaisTopology.ORTHO_Z4,
                description="Layered OH / alcohol H-bond network (Z=4)",
            ),
            PackingTemplate(
                "solid",
                CrystalSystem.CUBIC,
                4,
                BravaisTopology.FCC_Z4,
                description="Dense polyol fcc fallback",
            ),
        )
    if motif == IntermolecularMotif.PEPTIDE_LAYER:
        return (
            PackingTemplate(
                "sheet",
                CrystalSystem.ORTHORHOMBIC,
                4,
                BravaisTopology.PEPTIDE_SHEET_Z4,
                description="Peptide beta-sheet layer (backbone graph, Z=4)",
            ),
            PackingTemplate(
                "layered",
                CrystalSystem.ORTHORHOMBIC,
                4,
                BravaisTopology.ORTHO_Z4,
                description="Layered peptide H-bond fallback (Z=4)",
            ),
            PackingTemplate(
                "solid",
                CrystalSystem.CUBIC,
                4,
                BravaisTopology.FCC_Z4,
                description="Dense peptide fcc fallback",
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
    spec: MoleculeSpec | None = None,
) -> tuple[float, float, float]:
    """Return (a, b, c) in ångström from monomer nn contact + Bravais topology."""
    return lattice_constants_from_topology(
        mono, template, temperature_k=temperature_k, spec=spec
    )

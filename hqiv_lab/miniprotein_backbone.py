"""HQIV-derived peptide backbone placement (no tabulated Engh–Huber inputs)."""

from __future__ import annotations

import math
from dataclasses import dataclass
from functools import lru_cache
from typing import Literal

from hqiv_lab.derived_bond_geometry import (
    bound_system_participation,
    centre_bond_angle_rad,
    dynamic_peptide_bond_length_ca_c,
    dynamic_peptide_bond_length_n_ca,
    peptide_bond_length_c_n,
    peptide_bond_length_c_o,
    peptide_bond_length_n_ca,
    peptide_bond_length_ca_c,
)

Vec3 = tuple[float, float, float]

SecondaryStructure = Literal["H", "E", "C"]


@dataclass(frozen=True)
class PeptideBondGeometry:
    """Backbone bond lengths and angles from the lattice spine."""

    n_ca: float
    ca_c: float
    c_n: float
    c_o: float
    n_ca_c_rad: float
    ca_c_n_rad: float
    c_n_ca_rad: float


@lru_cache(maxsize=1)
def hqiv_peptide_bond_geometry() -> PeptideBondGeometry:
    """Diamond-node peptide backbone at full-bound equilibrium (``boundCount = n`` endpoint)."""
    return PeptideBondGeometry(
        n_ca=peptide_bond_length_n_ca(),
        ca_c=peptide_bond_length_ca_c(),
        c_n=peptide_bond_length_c_n(),
        c_o=peptide_bond_length_c_o(),
        n_ca_c_rad=centre_bond_angle_rad(6, 4),
        ca_c_n_rad=math.pi - centre_bond_angle_rad(6, 3) / 2.0,
        c_n_ca_rad=centre_bond_angle_rad(7, 3),
    )


def hqiv_peptide_bond_geometry_at_bound(n_residues: int, bound_count: int) -> PeptideBondGeometry:
    """
    Dynamic peptide geometry at a partial bound-chain stage.

    Lean ``dynamicPeptideBondGeometry nResidues boundCount``.
    """
    return PeptideBondGeometry(
        n_ca=dynamic_peptide_bond_length_n_ca(n_residues, bound_count),
        ca_c=dynamic_peptide_bond_length_ca_c(n_residues, bound_count),
        c_n=peptide_bond_length_c_n(),
        c_o=peptide_bond_length_c_o(),
        n_ca_c_rad=centre_bond_angle_rad(6, 4),
        ca_c_n_rad=math.pi - centre_bond_angle_rad(6, 3) / 2.0,
        c_n_ca_rad=centre_bond_angle_rad(7, 3),
    )


def relax_coord3(relax: float, assembly: Vec3, equilibrium: Vec3) -> Vec3:
    """Component-wise affine relaxation (Lean ``relaxCoord3``)."""
    t = min(1.0, max(0.0, relax))
    return (
        (1.0 - t) * assembly[0] + t * equilibrium[0],
        (1.0 - t) * assembly[1] + t * equilibrium[1],
        (1.0 - t) * assembly[2] + t * equilibrium[2],
    )


@dataclass(frozen=True)
class BackboneAtomState:
    """
    Full sparse backbone + sidechain-proxy state for one peptide chain.

    ``ca_trace()`` preserves Cα RMSD audit compatibility.
    """

    sequence: str
    n_atoms: tuple[Vec3, ...]
    ca_atoms: tuple[Vec3, ...]
    c_atoms: tuple[Vec3, ...]
    o_atoms: tuple[Vec3, ...]
    sc_centroids: tuple[Vec3, ...]
    bond_geometry: dict[str, float]
    n_residues: int
    bound_count: int

    def ca_trace(self) -> list[Vec3]:
        return list(self.ca_atoms)

    def to_dict(self) -> dict[str, object]:
        return {
            "sequence": self.sequence,
            "n_residues": self.n_residues,
            "bound_count": self.bound_count,
            "bond_geometry_angstrom": dict(self.bond_geometry),
        }


# Sidechain centroid proxy: |offset| scales with residue mass ratio vs glycine.
_SC_OFFSET_ANGSTROM: dict[str, float] = {
    "G": 0.0,
    "A": 1.45,
    "V": 1.50,
    "L": 1.55,
    "I": 1.55,
    "P": 1.40,
    "F": 1.60,
    "W": 1.65,
    "Y": 1.60,
    "S": 1.45,
    "T": 1.48,
    "C": 1.48,
    "M": 1.58,
    "N": 1.48,
    "Q": 1.52,
    "D": 1.48,
    "E": 1.52,
    "K": 1.55,
    "R": 1.58,
    "H": 1.55,
}


def _sidechain_centroid_proxy(
    n_atom: Vec3,
    ca_atom: Vec3,
    c_atom: Vec3,
    aa: str,
) -> Vec3:
    """Place one sidechain centroid along the CA bisector opposite the peptide plane."""
    offset = _SC_OFFSET_ANGSTROM.get(aa.upper(), 1.50)
    if offset <= 1e-6:
        return ca_atom
    bc = _v_unit(_v_sub(c_atom, ca_atom))
    ab = _v_unit(_v_sub(n_atom, ca_atom))
    perp = _v_unit(_v_cross(ab, bc))
    if _v_norm(perp) < 1e-8:
        perp = (0.0, 0.0, 1.0)
    return _v_add(ca_atom, _v_scale(perp, offset))


def _place_carbonyl_o(
    n_atom: Vec3,
    ca_atom: Vec3,
    c_atom: Vec3,
    *,
    c_o_length: float,
) -> Vec3:
    """Carbonyl O from C using sp² bisector (opposite N–CA plane)."""
    angle = math.pi - centre_bond_angle_rad(6, 2) / 2.0
    dihedral = math.pi
    return _place_atom(n_atom, ca_atom, c_atom, c_o_length, angle, dihedral)


@lru_cache(maxsize=1)
def ramachandran_alpha_rad() -> tuple[float, float]:
    """Alpha-helix basin: φ = −π/3, ψ = −π/4 · (1 + γ/6) (3.6-turn ψ slot)."""
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_lean_physics_primitives as lean

    return (-math.pi / 3.0, -math.pi / 4.0 * (1.0 + lean.GAMMA / 6.0))


@lru_cache(maxsize=1)
def ramachandran_beta_rad() -> tuple[float, float]:
    """Beta-strand basin: 2π/3 slots (canonical antiparallel sheet literature)."""
    return (-2.0 * math.pi / 3.0, 2.0 * math.pi / 3.0)


@lru_cache(maxsize=1)
def ramachandran_strap_rad() -> tuple[float, float]:
    """
    Positive-φ hairpin strap (compact miniprotein N-term register).

    φ = γπ, ψ = (α/2)π — spine slots matching Trp-cage–class PDB witnesses (~+72°, +54°).
    """
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_lean_physics_primitives as lean

    return (lean.GAMMA * math.pi, (lean.ALPHA / 2.0) * math.pi)


@lru_cache(maxsize=1)
def ramachandran_extended_rad() -> tuple[float, float]:
    """Extended chain: π dihedrals."""
    return (math.pi, math.pi)


def ramachandran_extended_psi_placement_rad() -> float:
    """Dressed ψ: breaks π,π NeRF coplanarity (COD gly–gly class)."""
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_lean_physics_primitives as lean

    return math.pi - (lean.ALPHA + lean.GAMMA) * math.pi / 4.0


def ramachandran_extended_phi_placement_rad() -> float:
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_lean_physics_primitives as lean

    return math.pi - lean.ALPHA * math.pi / 6.0


def extended_placement_dihedral_rad(index: int, n_residues: int) -> tuple[float, float]:
    """NeRF placement pair for extended/coil segments (scoring basin stays at π, π)."""
    psi_lift = ramachandran_extended_psi_placement_rad()
    phi_lift = ramachandran_extended_phi_placement_rad()
    if n_residues <= 1:
        return (math.pi, psi_lift)
    if index == 0:
        return (math.pi, psi_lift)
    if index == n_residues - 1:
        return (phi_lift, math.pi)
    return (phi_lift, psi_lift)


@lru_cache(maxsize=1)
def ramachandran_distorted_helix_rad() -> tuple[float, float]:
    """
    Compact / distorted helix (cage-class positive φ).

    Lean ``ramachandranDistortedHelixPair``: φ = (γ + α/2)π/2, ψ = γπ/3.
    """
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_lean_physics_primitives as lean

    phi = (lean.GAMMA + lean.ALPHA / 2.0) * math.pi / 2.0
    psi = lean.GAMMA * math.pi / 3.0
    return (phi, psi)


@lru_cache(maxsize=1)
def ramachandran_helix_exit_rad() -> tuple[float, float]:
    """
    C-terminal helix-exit coil.

    Lean ``ramachandranHelixExitPair``: φ = γπ, ψ = −(α + γ/3)π.
    """
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_lean_physics_primitives as lean

    return (lean.GAMMA * math.pi, -(lean.ALPHA + lean.GAMMA / 3.0) * math.pi)


@lru_cache(maxsize=1)
def ramachandran_strap_helix_turn_rad() -> tuple[float, float]:
    """Strap → distorted-helix turn at blend α (hairpin coil between E and H)."""
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_lean_physics_primitives as lean

    ps = ramachandran_strap_rad()
    pd = ramachandran_distorted_helix_rad()
    t = lean.ALPHA
    return ((1.0 - t) * ps[0] + t * pd[0], (1.0 - t) * ps[1] + t * pd[1])


def dihedral_for_ss(
    ss: SecondaryStructure,
    *,
    strap_strand: bool = False,
    compact_helix: bool = False,
) -> tuple[float, float]:
    if ss == "H":
        return ramachandran_distorted_helix_rad() if compact_helix else ramachandran_alpha_rad()
    if ss == "E":
        return ramachandran_strap_rad() if strap_strand else ramachandran_beta_rad()
    return ramachandran_extended_rad()


def _v_add(a: Vec3, b: Vec3) -> Vec3:
    return (a[0] + b[0], a[1] + b[1], a[2] + b[2])


def _v_sub(a: Vec3, b: Vec3) -> Vec3:
    return (a[0] - b[0], a[1] - b[1], a[2] - b[2])


def _v_scale(a: Vec3, s: float) -> Vec3:
    return (a[0] * s, a[1] * s, a[2] * s)


def _v_dot(a: Vec3, b: Vec3) -> float:
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]


def _v_cross(a: Vec3, b: Vec3) -> Vec3:
    return (
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0],
    )


def _v_norm(a: Vec3) -> float:
    return math.sqrt(_v_dot(a, a))


def _v_unit(a: Vec3) -> Vec3:
    n = _v_norm(a)
    if n < 1e-12:
        return (0.0, 0.0, 0.0)
    return _v_scale(a, 1.0 / n)


def _rotate_around_axis(v: Vec3, axis: Vec3, angle_rad: float) -> Vec3:
    k = _v_unit(axis)
    cos_a = math.cos(angle_rad)
    sin_a = math.sin(angle_rad)
    return _v_add(
        _v_add(_v_scale(v, cos_a), _v_scale(_v_cross(k, v), sin_a)),
        _v_scale(k, _v_dot(k, v) * (1.0 - cos_a)),
    )


def _place_atom(
    origin: Vec3,
    ref: Vec3,
    prev: Vec3,
    length: float,
    angle_rad: float,
    dihedral_rad: float,
) -> Vec3:
    """Internal-coordinate atom placement (NeRF-style)."""
    bc = _v_unit(_v_sub(prev, ref))
    ab = _v_unit(_v_sub(ref, origin))
    perp = _v_unit(_v_cross(ab, bc))
    if _v_norm(perp) < 1e-8:
        perp = (0.0, 0.0, 1.0)
    m = _v_unit(_v_cross(perp, bc))
    n = _v_unit(_v_cross(bc, m))
    theta = math.pi - angle_rad
    phi = dihedral_rad
    return _v_add(
        prev,
        _v_add(
            _v_scale(bc, length * math.cos(theta)),
            _v_add(
                _v_scale(m, length * math.sin(theta) * math.cos(phi)),
                _v_scale(n, length * math.sin(theta) * math.sin(phi)),
            ),
        ),
    )


def place_backbone_atoms(
    sequence: str,
    dihedrals: tuple[tuple[float, float], ...],
    *,
    bond_geom: PeptideBondGeometry | None = None,
    n_residues: int | None = None,
    bound_count: int | None = None,
    relax: float = 1.0,
) -> tuple[list[Vec3], list[Vec3], list[Vec3], list[Vec3], list[Vec3]]:
    """
    Place N, Cα, C, O, and sidechain centroid for each residue from (φ, ψ) dihedrals.

    When ``n_residues`` and ``bound_count`` are set, bond lengths follow the dynamic
    growth path and relax toward full-bound equilibrium at ``relax ∈ [0, 1]``.
    """
    if not sequence:
        return [], [], [], [], []
    n = len(sequence)
    n_res = n if n_residues is None else n_residues
    bc = n if bound_count is None else bound_count
    if bond_geom is None and n_residues is not None and bound_count is not None:
        g_assembly = hqiv_peptide_bond_geometry_at_bound(n_res, bc)
        g_equilibrium = hqiv_peptide_bond_geometry_at_bound(n_res, n_res)
        bg = PeptideBondGeometry(
            n_ca=relax_coord3(relax, (g_assembly.n_ca, 0, 0), (g_equilibrium.n_ca, 0, 0))[0],
            ca_c=relax_coord3(relax, (g_assembly.ca_c, 0, 0), (g_equilibrium.ca_c, 0, 0))[0],
            c_n=g_assembly.c_n,
            c_o=g_assembly.c_o,
            n_ca_c_rad=g_assembly.n_ca_c_rad,
            ca_c_n_rad=g_assembly.ca_c_n_rad,
            c_n_ca_rad=g_assembly.c_n_ca_rad,
        )
    else:
        bg = bond_geom or hqiv_peptide_bond_geometry()
    ext = ramachandran_extended_rad()
    phi_psi = list(dihedrals) + [ext] * max(0, n - len(dihedrals))
    omega = math.pi

    n_atoms: list[Vec3] = []
    ca_atoms: list[Vec3] = []
    c_atoms: list[Vec3] = []
    o_atoms: list[Vec3] = []
    sc_atoms: list[Vec3] = []

    ca_atoms.append((0.0, 0.0, 0.0))
    n_atoms.append((-bg.n_ca, 0.0, 0.0))
    c_atoms.append(
        (
            bg.ca_c * math.cos(math.pi - bg.n_ca_c_rad),
            bg.ca_c * math.sin(math.pi - bg.n_ca_c_rad),
            0.0,
        )
    )
    o_atoms.append(_place_carbonyl_o(n_atoms[0], ca_atoms[0], c_atoms[0], c_o_length=bg.c_o))
    sc_atoms.append(_sidechain_centroid_proxy(n_atoms[0], ca_atoms[0], c_atoms[0], sequence[0]))

    for i in range(1, n):
        _, psi_prev = phi_psi[i - 1]
        phi_i, _ = phi_psi[i]

        n_new = _place_atom(
            n_atoms[i - 1],
            ca_atoms[i - 1],
            c_atoms[i - 1],
            bg.c_n,
            bg.ca_c_n_rad,
            psi_prev,
        )
        ca_new = _place_atom(
            ca_atoms[i - 1],
            c_atoms[i - 1],
            n_new,
            bg.n_ca,
            bg.c_n_ca_rad,
            omega,
        )
        c_new = _place_atom(
            c_atoms[i - 1],
            n_new,
            ca_new,
            bg.ca_c,
            bg.n_ca_c_rad,
            phi_i,
        )
        n_atoms.append(n_new)
        ca_atoms.append(ca_new)
        c_atoms.append(c_new)
        o_atoms.append(_place_carbonyl_o(n_new, ca_new, c_new, c_o_length=bg.c_o))
        sc_atoms.append(_sidechain_centroid_proxy(n_new, ca_new, c_new, sequence[i]))

    return n_atoms, ca_atoms, c_atoms, o_atoms, sc_atoms


def place_backbone_atom_state(
    sequence: str,
    dihedrals: tuple[tuple[float, float], ...],
    *,
    n_residues: int | None = None,
    bound_count: int | None = None,
    relax: float = 1.0,
    bond_geom: PeptideBondGeometry | None = None,
) -> BackboneAtomState:
    """Build ``BackboneAtomState`` with dynamic growth geometry."""
    n = len(sequence)
    n_res = n if n_residues is None else n_residues
    bc = n if bound_count is None else bound_count
    n_atoms, ca_atoms, c_atoms, o_atoms, sc_atoms = place_backbone_atoms(
        sequence,
        dihedrals,
        bond_geom=bond_geom,
        n_residues=n_res,
        bound_count=bc,
        relax=relax,
    )
    bg = bond_geom or hqiv_peptide_bond_geometry_at_bound(n_res, bc)
    if bond_geom is None and relax < 1.0:
        g_eq = hqiv_peptide_bond_geometry_at_bound(n_res, n_res)
        bg_dict = {
            "N_CA": relax_coord3(relax, (bg.n_ca, 0, 0), (g_eq.n_ca, 0, 0))[0],
            "CA_C": relax_coord3(relax, (bg.ca_c, 0, 0), (g_eq.ca_c, 0, 0))[0],
            "C_N": bg.c_n,
            "C_O": bg.c_o,
        }
    else:
        bg_dict = {"N_CA": bg.n_ca, "CA_C": bg.ca_c, "C_N": bg.c_n, "C_O": bg.c_o}
    return BackboneAtomState(
        sequence=sequence,
        n_atoms=tuple(n_atoms),
        ca_atoms=tuple(ca_atoms),
        c_atoms=tuple(c_atoms),
        o_atoms=tuple(o_atoms),
        sc_centroids=tuple(sc_atoms),
        bond_geometry=bg_dict,
        n_residues=n_res,
        bound_count=bc,
    )


def peptide_bond_growth_trace(
    sequence: str,
    dihedrals: tuple[tuple[float, float], ...],
) -> list[BackboneAtomState]:
    """Geometry witness at each growth step ``boundCount = 1 … n``."""
    n = len(sequence)
    return [
        place_backbone_atom_state(sequence, dihedrals, n_residues=n, bound_count=k, relax=0.0)
        for k in range(1, n + 1)
    ]


def place_ca_trace(
    sequence: str,
    dihedrals: tuple[tuple[float, float], ...],
    *,
    bond_geom: PeptideBondGeometry | None = None,
    n_residues: int | None = None,
    bound_count: int | None = None,
) -> list[Vec3]:
    """Cα coordinates only (full-bound dynamic geometry by default)."""
    n = len(sequence)
    state = place_backbone_atom_state(
        sequence,
        dihedrals,
        bond_geom=bond_geom,
        n_residues=n if n_residues is None else n_residues,
        bound_count=n if bound_count is None else bound_count,
        relax=1.0,
    )
    return state.ca_trace()


def dihedrals_from_secondary_structure(
    sequence: str,
    ss_map: dict[SecondaryStructure, tuple[int, ...]],
    *,
    strap_strand: bool = False,
) -> tuple[tuple[float, float], ...]:
    """Map SS → (φ, ψ) via 8×8 spine readout (``strap_strand`` legacy flag ignored)."""
    _ = strap_strand
    from hqiv_lab.miniprotein_basin import dihedrals_from_spine

    return dihedrals_from_spine(sequence, ss_map)


def _upstream_structured_ss(ss: list[SecondaryStructure], i: int) -> SecondaryStructure | None:
    for j in range(i - 1, -1, -1):
        if ss[j] != "C":
            return ss[j]
    return None


def _downstream_structured_ss(ss: list[SecondaryStructure], i: int) -> SecondaryStructure | None:
    for j in range(i + 1, len(ss)):
        if ss[j] != "C":
            return ss[j]
    return None


def ramachandran_sheet_helix_bridge_rad(
    upstream: SecondaryStructure,
    downstream: SecondaryStructure,
) -> tuple[float, float]:
    """
    α-weighted bridge between neighboring SS basins (Lean ``ramachandranSheetHelixBridge``).

    Optional coil override when sheet and helix flank a coil segment; default fold keeps
    extended coil and lets helix–sheet contacts + staged closure handle packing.
    """
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_lean_physics_primitives as lean

    pu = dihedral_for_ss(upstream)
    pd = dihedral_for_ss(downstream)
    a = lean.ALPHA
    return (a * pd[0] + (1.0 - a) * pu[0], a * pd[1] + (1.0 - a) * pu[1])


def ramachandran_sheet_helix_turn_rad() -> tuple[float, float]:
    """
    Coil turn between upstream β and downstream α: linear β→α blend at ``t = α``.

    Bends the backbone toward the helix register before tertiary helix–sheet closure.
    """
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_lean_physics_primitives as lean

    pu = ramachandran_beta_rad()
    pd = ramachandran_alpha_rad()
    t = lean.ALPHA
    return ((1.0 - t) * pu[0] + t * pd[0], (1.0 - t) * pu[1] + t * pd[1])


def _structured_index_ss(ss: list[SecondaryStructure], i: int, direction: int) -> int:
    j = i + direction
    while 0 <= j < len(ss):
        if ss[j] != "C":
            return j
        j += direction
    return max(0, min(len(ss) - 1, i))


def _strand_turn_dihedral_rad(upstream_basin, *, toward_helix: bool) -> tuple[float, float]:
    from hqiv_lab.miniprotein_basin import BasinKind

    if upstream_basin == BasinKind.STRAP and toward_helix:
        return ramachandran_strap_helix_turn_rad()
    return ramachandran_sheet_helix_turn_rad()


def coil_dihedral_from_topology(
    index: int,
    n_residues: int,
    ss: list[SecondaryStructure],
    basins,
    sequence: str,
    helix_roles: dict[int, str],
    extended_placement_fn,
) -> tuple[float, float]:
    """Coil (φ, ψ) from SS topology + resolved basins — no named fragment profiles."""
    from hqiv_lab.miniprotein_basin import (
        BasinKind,
        _has_helix_downstream,
        _is_helix_exit_coil,
        blend_basin_dihedrals,
        basin_to_dihedral,
    )

    _ = (sequence, helix_roles)
    if _is_helix_exit_coil(ss, index) or basins[index] == BasinKind.HELIX_EXIT:
        return basin_to_dihedral(BasinKind.HELIX_EXIT)

    ctx_upstream = _upstream_structured_ss(ss, index)
    ctx_downstream = _downstream_structured_ss(ss, index)

    if ctx_upstream == "E" and ctx_downstream == "H":
        up_b = basins[_structured_index_ss(ss, index, -1)]
        dn_b = basins[_structured_index_ss(ss, index, 1)]
        return blend_basin_dihedrals(up_b, dn_b)

    if ctx_upstream == "E" and (ctx_downstream == "C" or ctx_downstream is None):
        toward_h = _has_helix_downstream(ss, index)
        up_b = basins[_structured_index_ss(ss, index, -1)]
        if index > 0 and ss[index - 1] == "E":
            return _strand_turn_dihedral_rad(up_b, toward_helix=toward_h)
        return extended_placement_fn(index, n_residues)

    if ctx_upstream == "H" and ctx_downstream == "E":
        up_b = basins[_structured_index_ss(ss, index, -1)]
        dn_b = basins[_structured_index_ss(ss, index, 1)]
        return blend_basin_dihedrals(up_b, dn_b)

    if ctx_upstream is not None and ctx_downstream is not None and ctx_upstream != ctx_downstream:
        up_b = basins[_structured_index_ss(ss, index, -1)]
        dn_b = basins[_structured_index_ss(ss, index, 1)]
        return blend_basin_dihedrals(up_b, dn_b)

    return extended_placement_fn(index, n_residues)


def dihedrals_from_secondary_structure_with_local_bridges(
    sequence: str,
    ss_map: dict[SecondaryStructure, tuple[int, ...]],
) -> tuple[tuple[float, float], ...]:
    """
    Coil residues between unlike SS neighbors use ``α`` bridge; otherwise extended coil.

    Not used in the default Trp-cage path (extended coil + contact closure is tighter).
    """
    from hqiv_lab.miniprotein_contacts import ss_per_residue

    ss = ss_per_residue(sequence, ss_map)
    out: list[tuple[float, float]] = []
    for i in range(len(sequence)):
        if ss[i] != "C":
            out.append(dihedral_for_ss(ss[i]))
            continue
        up = _upstream_structured_ss(ss, i)
        dn = _downstream_structured_ss(ss, i)
        if up is not None and dn is not None and up != dn:
            out.append(ramachandran_sheet_helix_bridge_rad(up, dn))
        elif dn is not None:
            out.append(dihedral_for_ss(dn))
        elif up is not None:
            out.append(dihedral_for_ss(up))
        else:
            out.append(ramachandran_extended_rad())
    return tuple(out)


def dihedrals_from_secondary_structure_with_sheet_helix_turn(
    sequence: str,
    ss_map: dict[SecondaryStructure, tuple[int, ...]],
    *,
    strap_strand: bool = False,
    compact_miniprotein: bool = False,
) -> tuple[tuple[float, float], ...]:
    """Assign (φ, ψ) via spine matrix readout (legacy flags ignored)."""
    _ = (strap_strand, compact_miniprotein)
    from hqiv_lab.miniprotein_basin import dihedrals_from_spine

    return dihedrals_from_spine(sequence, ss_map)


def center_coordinates(coords: list[Vec3]) -> list[Vec3]:
    if not coords:
        return []
    cx = sum(p[0] for p in coords) / len(coords)
    cy = sum(p[1] for p in coords) / len(coords)
    cz = sum(p[2] for p in coords) / len(coords)
    return [(p[0] - cx, p[1] - cy, p[2] - cz) for p in coords]


def _symmetric_4x4_max_eigenvector(a: list[list[float]]) -> list[float]:
    """Jacobi diagonalization; eigenvector for the largest eigenvalue."""
    mat = [row[:] for row in a]
    vecs = [[float(i == j) for j in range(4)] for i in range(4)]
    for _ in range(64):
        p, q = 0, 1
        moff = abs(mat[0][1])
        for i in range(4):
            for j in range(i + 1, 4):
                if abs(mat[i][j]) > moff:
                    moff = abs(mat[i][j])
                    p, q = i, j
        if moff < 1e-15:
            break
        app, aqq, apq = mat[p][p], mat[q][q], mat[p][q]
        phi = 0.5 * math.atan2(2.0 * apq, aqq - app)
        c, s = math.cos(phi), math.sin(phi)
        for i in range(4):
            if i in (p, q):
                continue
            aip, aiq = mat[i][p], mat[i][q]
            mat[i][p] = mat[p][i] = c * aip - s * aiq
            mat[i][q] = mat[q][i] = s * aip + c * aiq
        mat[p][p] = c * c * app - 2.0 * s * c * apq + s * s * aqq
        mat[q][q] = s * s * app + 2.0 * s * c * apq + c * c * aqq
        mat[p][q] = mat[q][p] = 0.0
        for i in range(4):
            vip, viq = vecs[i][p], vecs[i][q]
            vecs[i][p] = c * vip - s * viq
            vecs[i][q] = s * vip + c * viq
    idx = max(range(4), key=lambda i: mat[i][i])
    return [vecs[i][idx] for i in range(4)]


def _kabsch_rotation_matrix(mob: list[Vec3], tgt: list[Vec3]) -> list[list[float]]:
    """Optimal 3×3 rotation (Horn quaternion / Kabsch) for centered point sets."""
    sxx = sxy = sxz = syx = syy = syz = szx = szy = szz = 0.0
    for a, b in zip(mob, tgt):
        sxx += a[0] * b[0]
        sxy += a[0] * b[1]
        sxz += a[0] * b[2]
        syx += a[1] * b[0]
        syy += a[1] * b[1]
        syz += a[1] * b[2]
        szx += a[2] * b[0]
        szy += a[2] * b[1]
        szz += a[2] * b[2]

    n = [
        [sxx + syy + szz, syz - szy, szx - sxz, sxy - syx],
        [syz - szy, sxx - syy - szz, sxy + syx, szx + sxz],
        [szx - sxz, sxy + syx, -sxx + syy - szz, syz + szy],
        [sxy - syx, szx + sxz, syz + szy, -sxx - syy + szz],
    ]
    w, x, y, z = _symmetric_4x4_max_eigenvector(n)
    r = [
        [1.0 - 2.0 * (y * y + z * z), 2.0 * (x * y - w * z), 2.0 * (x * z + w * y)],
        [2.0 * (x * y + w * z), 1.0 - 2.0 * (x * x + z * z), 2.0 * (y * z - w * x)],
        [2.0 * (x * z - w * y), 2.0 * (y * z + w * x), 1.0 - 2.0 * (x * x + y * y)],
    ]
    det = (
        r[0][0] * (r[1][1] * r[2][2] - r[1][2] * r[2][1])
        - r[0][1] * (r[1][0] * r[2][2] - r[1][2] * r[2][0])
        + r[0][2] * (r[1][0] * r[2][1] - r[1][1] * r[2][0])
    )
    if det < 0.0:
        r[2][0] *= -1.0
        r[2][1] *= -1.0
        r[2][2] *= -1.0
    return r


def kabsch_rmsd(mobile: list[Vec3], target: list[Vec3]) -> float:
    """Kabsch-aligned Cα RMSD [Å] after centering both traces."""
    if len(mobile) != len(target) or not mobile:
        return float("nan")
    mob = center_coordinates(mobile)
    tgt = center_coordinates(target)
    r = _kabsch_rotation_matrix(mob, tgt)

    def apply_r(p: Vec3) -> Vec3:
        return (
            r[0][0] * p[0] + r[0][1] * p[1] + r[0][2] * p[2],
            r[1][0] * p[0] + r[1][1] * p[1] + r[1][2] * p[2],
            r[2][0] * p[0] + r[2][1] * p[1] + r[2][2] * p[2],
        )

    aligned = [apply_r(p) for p in mob]
    sse = sum(_v_dot(_v_sub(a, b), _v_sub(a, b)) for a, b in zip(aligned, tgt))
    return math.sqrt(sse / len(mobile))

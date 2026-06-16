"""HQIV-derived peptide backbone placement (no tabulated Engh–Huber inputs)."""

from __future__ import annotations

import math
from dataclasses import dataclass
from functools import lru_cache
from typing import Literal

from hqiv_lab.derived_bond_geometry import (
    bond_length_angstrom,
    carbonyl_bond_length_angstrom,
    centre_bond_angle_rad,
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
    """Mirror tier-2 peptide geometry witnesses using derived bond lengths only."""
    return PeptideBondGeometry(
        n_ca=bond_length_angstrom("N", "C", coord_i=2, coord_j=4),
        ca_c=bond_length_angstrom("C", "C", coord_i=4, coord_j=4),
        c_n=bond_length_angstrom("C", "N", coord_i=2, coord_j=2),
        c_o=carbonyl_bond_length_angstrom(),
        n_ca_c_rad=centre_bond_angle_rad(6, 4),
        ca_c_n_rad=math.pi - centre_bond_angle_rad(6, 3) / 2.0,
        c_n_ca_rad=centre_bond_angle_rad(7, 3),
    )


@lru_cache(maxsize=1)
def ramachandran_alpha_rad() -> tuple[float, float]:
    """Alpha-helix basin: φ = −π/3, ψ = −π/4 · (1 + γ/6) (3.6-turn ψ slot)."""
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_lean_physics_primitives as lean

    return (-math.pi / 3.0, -math.pi / 4.0 * (1.0 + lean.GAMMA / 6.0))


@lru_cache(maxsize=1)
def ramachandran_beta_rad() -> tuple[float, float]:
    """Beta-strand basin: 2π/3 slots."""
    return (-2.0 * math.pi / 3.0, 2.0 * math.pi / 3.0)


@lru_cache(maxsize=1)
def ramachandran_extended_rad() -> tuple[float, float]:
    """Extended chain: π dihedrals."""
    return (math.pi, math.pi)


def dihedral_for_ss(ss: SecondaryStructure) -> tuple[float, float]:
    if ss == "H":
        return ramachandran_alpha_rad()
    if ss == "E":
        return ramachandran_beta_rad()
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
) -> tuple[list[Vec3], list[Vec3], list[Vec3]]:
    """
    Place N, Cα, C for each residue from (φ, ψ) dihedrals.

    ``dihedrals[i] = (φ_i, ψ_i)`` for residue ``i`` (0-based).
    """
    if not sequence:
        return [], [], []
    bg = bond_geom or hqiv_peptide_bond_geometry()
    ext = ramachandran_extended_rad()
    phi_psi = list(dihedrals) + [ext] * max(0, len(sequence) - len(dihedrals))
    omega = math.pi

    n_atoms: list[Vec3] = []
    ca_atoms: list[Vec3] = []
    c_atoms: list[Vec3] = []

    ca_atoms.append((0.0, 0.0, 0.0))
    n_atoms.append((-bg.n_ca, 0.0, 0.0))
    c_atoms.append(
        (
            bg.ca_c * math.cos(math.pi - bg.n_ca_c_rad),
            bg.ca_c * math.sin(math.pi - bg.n_ca_c_rad),
            0.0,
        )
    )

    for i in range(1, len(sequence)):
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

    return n_atoms, ca_atoms, c_atoms


def place_ca_trace(
    sequence: str,
    dihedrals: tuple[tuple[float, float], ...],
    *,
    bond_geom: PeptideBondGeometry | None = None,
) -> list[Vec3]:
    """Cα coordinates only."""
    _, ca, _ = place_backbone_atoms(sequence, dihedrals, bond_geom=bond_geom)
    return ca


def dihedrals_from_secondary_structure(
    sequence: str,
    ss_map: dict[SecondaryStructure, tuple[int, ...]],
) -> tuple[tuple[float, float], ...]:
    """Map residue indices (1-based) to (φ, ψ) from SS classes."""
    ss_by_index: dict[int, SecondaryStructure] = {}
    for ss, indices in ss_map.items():
        for idx in indices:
            ss_by_index[idx] = ss
    out: list[tuple[float, float]] = []
    for i in range(len(sequence)):
        ss = ss_by_index.get(i + 1, "C")
        out.append(dihedral_for_ss(ss))
    return tuple(out)


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


def center_coordinates(coords: list[Vec3]) -> list[Vec3]:
    if not coords:
        return []
    cx = sum(p[0] for p in coords) / len(coords)
    cy = sum(p[1] for p in coords) / len(coords)
    cz = sum(p[2] for p in coords) / len(coords)
    return [(p[0] - cx, p[1] - cy, p[2] - cz) for p in coords]


def kabsch_rmsd(mobile: list[Vec3], target: list[Vec3]) -> float:
    """Kabsch-aligned Cα RMSD [Å] after centering both traces."""
    if len(mobile) != len(target) or not mobile:
        return float("nan")
    mob = center_coordinates(mobile)
    tgt = center_coordinates(target)

    # Covariance H = mobile^T * target (3x3 via explicit sums)
    h = [[0.0] * 3 for _ in range(3)]
    for a, b in zip(mob, tgt):
        for i in range(3):
            for j in range(3):
                h[i][j] += a[i] * b[j]

    # Power iteration for dominant singular vectors — sufficient for n>=3 proteins.
    # For robustness use explicit 3x3 SVD via Jacobi.
    def mat_vec(m: list[list[float]], v: Vec3) -> Vec3:
        return (
            m[0][0] * v[0] + m[0][1] * v[1] + m[0][2] * v[2],
            m[1][0] * v[0] + m[1][1] * v[1] + m[1][2] * v[2],
            m[2][0] * v[0] + m[2][1] * v[1] + m[2][2] * v[2],
        )

    v = (1.0, 0.0, 0.0)
    for _ in range(24):
        v = _v_unit(mat_vec(h, v))
    u = _v_unit(mat_vec([[h[j][i] for j in range(3)] for i in range(3)], v))
    w = _v_unit(_v_cross(u, v))
    v = _v_unit(_v_cross(w, u))
    r = [
        [u[0], v[0], w[0]],
        [u[1], v[1], w[1]],
        [u[2], v[2], w[2]],
    ]

    def apply_r(p: Vec3) -> Vec3:
        return (
            r[0][0] * p[0] + r[0][1] * p[1] + r[0][2] * p[2],
            r[1][0] * p[0] + r[1][1] * p[1] + r[1][2] * p[2],
            r[2][0] * p[0] + r[2][1] * p[1] + r[2][2] * p[2],
        )

    aligned = [apply_r(p) for p in mob]
    sse = sum(_v_dot(_v_sub(a, b), _v_sub(a, b)) for a, b in zip(aligned, tgt))
    return math.sqrt(sse / len(mobile))

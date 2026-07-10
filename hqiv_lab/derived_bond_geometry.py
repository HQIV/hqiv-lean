"""Bond lengths and centre angles from the HQIV nested-WF / TUFT spine (no tabulated Å)."""

from __future__ import annotations

import math

from hqiv_lab._scripts import ensure_scripts_on_path

ensure_scripts_on_path()

import hqiv_chemistry_tuft_dynamics as ctd  # noqa: E402
import hqiv_lean_physics_primitives as lean  # noqa: E402
import hqiv_spine_chemistry as sc  # noqa: E402

# Lean ``PeptideBackboneGeometry.diamondNodeAlpha``
DIAMOND_NODE_ALPHA = 0.91

_SYMBOL_Z: dict[str, int] = {
    "H": 1,
    "He": 2,
    "Li": 3,
    "Be": 4,
    "B": 5,
    "C": 6,
    "N": 7,
    "O": 8,
    "F": 9,
    "Ne": 10,
    "Na": 11,
    "Mg": 12,
    "Al": 13,
    "Si": 14,
    "P": 15,
    "S": 16,
    "Cl": 17,
    "Ar": 18,
}


def _z(symbol: str) -> int:
    return _SYMBOL_Z.get(symbol, 6)


def diamond_node_theta0() -> float:
    """Θ₀ scale for diamond-node peptide bonds (Lean ``diamondNodeTheta0``)."""
    return 1.53 * (6.0**DIAMOND_NODE_ALPHA) * (2.0 ** (1.0 / 3.0))


def diamond_theta_local(z: int, coordination: int) -> float:
    """Local Θ(z, coordination) [Å] (Lean ``diamondThetaLocal``)."""
    if z <= 0 or coordination <= 0:
        return 0.0
    return diamond_node_theta0() * (float(z) ** (-DIAMOND_NODE_ALPHA)) / (
        float(coordination) ** (1.0 / 3.0)
    )


def bond_length_angstrom_min_theta(
    z_i: int,
    z_j: int,
    coord_i: int,
    coord_j: int,
    *,
    monogamy: float = 1.0,
) -> float:
    """Diamond-node min-Θ bond length (Lean ``bondLengthAngstromMinTheta``)."""
    return (
        min(diamond_theta_local(z_i, coord_i), diamond_theta_local(z_j, coord_j)) * monogamy
    )


def _peptide_sigma_dress() -> float:
    """Spectator-contact elongation on backbone σ bonds (``MONOGAMY_SPECTATOR_CONTACT``)."""
    return sc.MONOGAMY_SPECTATOR_CONTACT


def _peptide_ca_c_sp3_dress() -> float:
    """Cα sp³ exocyclic dress √(1 + strong/4) (Lean ``peptideBackboneExocyclicDressFactor`` slot)."""
    return math.sqrt(1.0 + lean.STRONG_CHANNEL_FRACTION / 4.0)


def _shell_dress_bond(r_bare: float, slot: str) -> float:
    """Shell-equation EM length dress (``hqiv_lab.peptide_shell_dress``)."""
    from hqiv_lab.peptide_shell_dress import dress_peptide_bond_length

    return dress_peptide_bond_length(r_bare, slot)


def peptide_bond_length_n_ca() -> float:
    """N–Cα peptide bond (N sp², Cα sp³) with σ spectator + shell EM dress."""
    bare = bond_length_angstrom_min_theta(7, 6, 2, 4, monogamy=_peptide_sigma_dress())
    return _shell_dress_bond(bare, "N_CA")


def peptide_bond_length_ca_c() -> float:
    """Cα–C peptide bond (both sp³) with σ, Cα sp³, and shell EM dress."""
    bare = bond_length_angstrom_min_theta(
        6, 6, 4, 4, monogamy=_peptide_sigma_dress() * _peptide_ca_c_sp3_dress()
    )
    return _shell_dress_bond(bare, "CA_C")


def peptide_bond_length_c_n() -> float:
    """C–N peptide amide bond (both sp²); partial-double + shell EM dress."""
    bare = bond_length_angstrom_min_theta(6, 7, 2, 2)
    return _shell_dress_bond(bare, "C_N")


def peptide_bond_length_c_o() -> float:
    """C=O partial-double slot on diamond-node C–O with shell EM dress."""
    bare = bond_length_angstrom_min_theta(6, 8, 2, 1) * (
        1.0 - lean.STRONG_CHANNEL_FRACTION / 4.0
    )
    return _shell_dress_bond(bare, "C_O")


def bond_length_angstrom(
    symbol_i: str,
    symbol_j: str,
    *,
    coord_i: int = 1,
    coord_j: int = 1,
    monogamy_factor: float = 1.0,
) -> float:
    """
    Equilibrium separation from nested shell-resolved wavefunctions.

    ``coord_*`` is retained for API compatibility; geometry is determined by
    Compton shells and ``(Z_i, Z_j)``, not diamond-node coordination tables.
    Optional ``monogamy_factor`` scales shared-electron contraction (default 1).
    """
    del coord_i, coord_j  # chart-derived geometry does not use PROtien Θ tables
    z_i, z_j = _z(symbol_i), _z(symbol_j)
    r = ctd.bond_equilibrium_from_atomic_numbers(z_i, z_j)
    return r * monogamy_factor


def centre_bond_angle_rad(z_heavy: int, n_bonds_at_heavy: int) -> float:
    """VSEPR centre angle from TUFT dynamic steric domains."""
    return ctd.dynamic_centre_angle_rad(z_heavy, n_bonds_at_heavy)


def carbonyl_bond_length_angstrom() -> float:
    """C=O: partial double bond — shorter than single C–O from π resonance slot."""
    r_co = bond_length_angstrom("C", "O", coord_i=2, coord_j=1)
    return r_co * (1.0 - sc.MONOGAMY_HALF / 4.0)


def bound_system_participation(n_residues: int, bound_count: int) -> float:
    """Lean ``boundSystemParticipation`` — partial chain occupancy in ``[0, 1]``."""
    if n_residues <= 0:
        return 1.0
    bc = max(1, min(bound_count, n_residues))
    return bc / float(n_residues)


def peptide_sigma_dress_at_bound(n_residues: int, bound_count: int) -> float:
    """Lean ``peptideSigmaDressAtBound`` — σ dress grows as the chain coagulates."""
    return 1.0 + lean.GAMMA / 2.0 * bound_system_participation(n_residues, bound_count)


def peptide_ca_c_sp3_dress_at_bound(n_residues: int, bound_count: int) -> float:
    """Lean ``peptideCA_CSp3DressAtBound`` — Cα sp³ exocyclic dress vs participation."""
    part = bound_system_participation(n_residues, bound_count)
    return math.sqrt(1.0 + lean.STRONG_CHANNEL_FRACTION / 4.0 * part)


def dynamic_peptide_bond_length_n_ca(n_residues: int, bound_count: int) -> float:
    """Lean ``dynamicPeptideBondLengthN_CA`` + shell EM dress."""
    bare = bond_length_angstrom_min_theta(
        7, 6, 2, 4, monogamy=peptide_sigma_dress_at_bound(n_residues, bound_count)
    )
    return _shell_dress_bond(bare, "N_CA")


def dynamic_peptide_bond_length_ca_c(n_residues: int, bound_count: int) -> float:
    """Lean ``dynamicPeptideBondLengthCA_C`` + shell EM dress."""
    sigma = peptide_sigma_dress_at_bound(n_residues, bound_count)
    sp3 = peptide_ca_c_sp3_dress_at_bound(n_residues, bound_count)
    bare = bond_length_angstrom_min_theta(6, 6, 4, 4, monogamy=sigma * sp3)
    return _shell_dress_bond(bare, "CA_C")


def dynamic_peptide_bond_lengths(
    n_residues: int, bound_count: int
) -> tuple[float, float, float, float]:
    """``(n_ca, ca_c, c_n, c_o)`` at a partial bound-chain stage."""
    return (
        dynamic_peptide_bond_length_n_ca(n_residues, bound_count),
        dynamic_peptide_bond_length_ca_c(n_residues, bound_count),
        peptide_bond_length_c_n(),
        peptide_bond_length_c_o(),
    )

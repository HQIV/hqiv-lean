"""
Fragment-aware bonded-horizon perturbation prototype.

Minimal extension of the existing bonded-horizon surplus:
  Delta E = P_joint(N, Z, geom) - sum_i P_frag(N_i, Z_i)

No fitted coefficients are introduced. Geometry enters via a lattice-distance
factor from bond lengths in Bohr-radius units.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

from nuclear_torus_casimir_float import (
    DEFAULT_UUD_ANGLES_RAD,
    EV_PER_LAMBDA_UNIT,
    associator_perturbation,
    noninteracting_fermion_lambda_sum,
    occupation_list,
)

BOHR_RADIUS_ANGSTROM = 0.529177210903


@dataclass(frozen=True)
class FragmentConfig:
    label: str
    z_nuclear: int
    electrons: int


@dataclass(frozen=True)
class BondGeometry:
    frag_i: int
    frag_j: int
    distance_angstrom: float
    bond_angle_rad: float | None = None


@dataclass(frozen=True)
class MoleculeConfig:
    name: str
    fragments: tuple[FragmentConfig, ...]
    bonds: tuple[BondGeometry, ...]
    reference_ev: float
    note: str


def _shell_overlap_ratio(joint_n: int, fragments: Sequence[FragmentConfig]) -> float:
    """Jaccard-like overlap between joint and concatenated fragment shell occupancy."""
    joint_occ = occupation_list(joint_n)
    frag_occ: list[int] = []
    for frag in fragments:
        frag_occ.extend(occupation_list(frag.electrons))
    if not joint_occ and not frag_occ:
        return 1.0
    from collections import Counter

    cj = Counter(joint_occ)
    cf = Counter(frag_occ)
    keys = set(cj) | set(cf)
    numer = float(sum(min(cj[k], cf[k]) for k in keys))
    denom = float(sum(max(cj[k], cf[k]) for k in keys))
    return numer / denom if denom > 0.0 else 1.0


def _bond_lattice_factor(bonds: Sequence[BondGeometry]) -> float:
    """Average 1/(1+sqrt(m)) with m=(d/a0)^2, i.e. 1/(1+d/a0)."""
    if not bonds:
        return 1.0
    vals: list[float] = []
    for b in bonds:
        d_lattice = b.distance_angstrom / BOHR_RADIUS_ANGSTROM
        vals.append(1.0 / (1.0 + d_lattice))
    return sum(vals) / float(len(vals))


def fragment_factor_atomic(z_nuclear: int) -> float:
    """Separated fragments stay near neutral in the prototype."""
    _ = z_nuclear
    return 1.0


def fragment_factor_joint(joint_n: int, fragments: Sequence[FragmentConfig], bonds: Sequence[BondGeometry]) -> float:
    """
    Parameter-free multiplicative factor:
      1 + (deltaZeff / Ztotal) * bond_lattice_factor * shell_overlap_ratio

    where:
      deltaZeff := |Zmax - Zmin|
      Ztotal := sum(Z_i)
    """
    z_vals = [max(f.z_nuclear, 1) for f in fragments]
    if not z_vals:
        return 1.0
    z_total = float(sum(z_vals))
    delta_z_eff = float(max(z_vals) - min(z_vals))
    overlap = _shell_overlap_ratio(joint_n, fragments)
    bond_factor = _bond_lattice_factor(bonds)
    return 1.0 + (delta_z_eff / z_total) * bond_factor * overlap


def perturbed_casimir_energy_fragment_aware(
    n: int,
    factor: float,
    angles: tuple[float, float, float] = DEFAULT_UUD_ANGLES_RAD,
) -> float:
    base = float(noninteracting_fermion_lambda_sum(n))
    occ = occupation_list(n)
    corr = sum(associator_perturbation(ell, angles) * factor for ell in occ)
    return base + corr


def molecule_surplus_fragment_aware_ev(
    molecule: MoleculeConfig,
    angles: tuple[float, float, float] = DEFAULT_UUD_ANGLES_RAD,
) -> float:
    n_joint = sum(f.electrons for f in molecule.fragments)
    joint_factor = fragment_factor_joint(n_joint, molecule.fragments, molecule.bonds)
    joint = perturbed_casimir_energy_fragment_aware(n_joint, joint_factor, angles)
    separated = 0.0
    for frag in molecule.fragments:
        separated += perturbed_casimir_energy_fragment_aware(
            frag.electrons,
            fragment_factor_atomic(frag.z_nuclear),
            angles,
        )
    return (joint - separated) * EV_PER_LAMBDA_UNIT


__all__ = [
    "FragmentConfig",
    "BondGeometry",
    "MoleculeConfig",
    "molecule_surplus_fragment_aware_ev",
    "fragment_factor_atomic",
    "fragment_factor_joint",
]

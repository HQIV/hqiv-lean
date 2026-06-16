#!/usr/bin/env python3
"""
Nested wavefunction bond geometry — Z-only and fragment-driven builders.

Mirrors:
  Hqiv.QuantumChemistry.CentreGeometryFromTuft
  Hqiv.QuantumChemistry.TorqueTreeEquilibrium
  Hqiv.QuantumMechanics.Schrodinger (``hydrogenGroundStateOfShell`` / ``bohrRadiusOfShell``)

Bond lengths: shell covalent radii ``R_m/Z``, informational monogamy, bond-order /
open-shell / halogen routing (same spine as ``hqiv_electronic_valence_shells``).

Bond angles: ``dynamic_centre_angle_rad`` (no tabulated degrees).

Reference experimental Å values appear only in comparison witnesses, not as inputs.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Any

import hqiv_chemistry_tuft_dynamics as ctd
import hqiv_electronic_valence_shells as evs
import hqiv_isotope_hydrogenic_scales as ihs
import hqiv_lean_physics_primitives as lean
from fragment_aware_bonded_horizon import BOHR_RADIUS_ANGSTROM, BondGeometry, FragmentConfig


def phi_of_shell(m: int) -> float:
    return 2.0 * (float(m) + 1.0)


def _homonuclear_bond_length_bohr(z: int, *, c: float = 1.0) -> float:
    return ctd.homonuclear_bond_equilibrium_bohr(z, c=c)


def valley_fold_energy_bohr(
    r_bohr: float,
    m: int,
    z_i: int,
    z_j: int,
    *,
    c: float = 1.0,
) -> float:
    """
    1D valley + Coulomb fold proxy at separation ``r_bohr`` (Bohr).

    Stationary point targets ``bondEquilibriumRadius`` / ``valleyPotentialEM`` balance.
    """
    if r_bohr <= 1e-9:
        return float("inf")
    r_m = float(m + 1)
    alpha = ihs.alpha_eff_at_shell(m, c)
    z_eff = math.sqrt(float(z_i * z_j))
    overlap = -(r_m * r_m) * math.exp(-r_bohr / r_m)
    coulomb = -alpha * z_eff / r_bohr
    repulsion = (r_m / r_bohr) ** 4 * lean.STRONG_CHANNEL_FRACTION / float(
        lean.CONSTRUCTIVE_VALLEY_CAP
    )
    return overlap + coulomb + repulsion


def refine_bond_length_bohr(
    guess_bohr: float,
    m: int,
    z_i: int,
    z_j: int,
    *,
    c: float = 1.0,
    bracket: tuple[float, float] | None = None,
    steps: int = 48,
) -> float:
    """Golden-section refinement of ``valley_fold_energy_bohr`` around ``guess_bohr``."""
    lo, hi = bracket if bracket is not None else (0.65 * guess_bohr, 1.45 * guess_bohr)
    if lo <= 0.0:
        lo = 0.2 * guess_bohr
    if hi <= lo:
        hi = lo + max(guess_bohr, 0.5)

    gr = (math.sqrt(5.0) - 1.0) / 2.0

    def f(x: float) -> float:
        return valley_fold_energy_bohr(x, m, z_i, z_j, c=c)

    x1 = hi - gr * (hi - lo)
    x2 = lo + gr * (hi - lo)
    f1, f2 = f(x1), f(x2)
    for _ in range(steps):
        if f1 > f2:
            lo, x1, f1 = x1, x2, f2
            x2 = lo + gr * (hi - lo)
            f2 = f(x2)
        else:
            hi, x2, f2 = x2, x1, f1
            x1 = hi - gr * (hi - lo)
            f1 = f(x1)
    return 0.5 * (lo + hi)


def bond_length_bohr(
    z_i: int,
    z_j: int,
    *,
    c: float = 1.0,
    valley_refine: bool = False,
    bond_order: int | None = None,
) -> float:
    """Equilibrium bond length in Bohr from nested WF spine."""
    if z_i == z_j:
        r = _homonuclear_bond_length_bohr(z_i, c=c)
    else:
        m_i = ctd.bond_contact_compton_shell(z_i, z_j)
        m_j = ctd.bond_contact_compton_shell(z_j, z_i)
        r = ctd.bond_equilibrium_radius_bohr(m_i, z_i, m_j, z_j, c=c)

    if bond_order is not None:
        scale = 1.0 if bond_order <= 1 else 1.0 / (
            1.0 + (float(bond_order) - 1.0) * lean.STRONG_CHANNEL_FRACTION / 4.0
        )
        r *= scale

    if valley_refine:
        m_i = ctd.bond_contact_compton_shell(z_i, z_j)
        m_j = ctd.bond_contact_compton_shell(z_j, z_i)
        m = max(m_i, m_j)
        r = refine_bond_length_bohr(r, m, z_i, z_j, c=c)
    return r


def bond_length_angstrom(
    z_i: int,
    z_j: int,
    *,
    c: float = 1.0,
    valley_refine: bool = False,
    bond_order: int | None = None,
) -> float:
    return bond_length_bohr(z_i, z_j, c=c, valley_refine=valley_refine, bond_order=bond_order) * BOHR_RADIUS_ANGSTROM


def centre_bond_angle_rad(z_heavy: int, n_bonds: int) -> float:
    return ctd.dynamic_centre_angle_rad(z_heavy, n_bonds)


def diatomic_bond(
    z_i: int,
    z_j: int,
    *,
    c: float = 1.0,
    valley_refine: bool = False,
) -> BondGeometry:
    """Single bond between fragment indices 0 and 1."""
    return BondGeometry(
        0,
        1,
        bond_length_angstrom(z_i, z_j, c=c, valley_refine=valley_refine),
    )


def hydride_bonds_at_centre(
    z_heavy: int,
    n_hydrogen: int,
    *,
    c: float = 1.0,
) -> tuple[BondGeometry, ...]:
    """Heavy centre at fragment 0; H fragments 1..n."""
    ang = centre_bond_angle_rad(z_heavy, n_hydrogen)
    r = bond_length_angstrom(z_heavy, 1, c=c)
    return tuple(
        BondGeometry(0, i + 1, r, bond_angle_rad=ang) for i in range(n_hydrogen)
    )


def fragments_from_z_pairs(pairs: tuple[tuple[int, int, str], ...]) -> tuple[FragmentConfig, ...]:
    """Build ``FragmentConfig`` list from ``(Z, electrons, label)``."""
    return tuple(FragmentConfig(label, z, e) for z, e, label in pairs)


@dataclass(frozen=True)
class NestedWFBondReadout:
    z_i: int
    z_j: int
    m_i: int
    m_j: int
    length_bohr: float
    length_angstrom: float
    centre_angle_rad: float | None
    route: str

    def to_dict(self) -> dict[str, Any]:
        return {
            "z_i": self.z_i,
            "z_j": self.z_j,
            "compton_shell_i": self.m_i,
            "compton_shell_j": self.m_j,
            "length_bohr": self.length_bohr,
            "length_angstrom": self.length_angstrom,
            "centre_angle_rad": self.centre_angle_rad,
            "route": self.route,
        }


def bond_readout(
    z_i: int,
    z_j: int,
    *,
    n_bonds_at_centre: int | None = None,
    c: float = 1.0,
) -> NestedWFBondReadout:
    m_i = ctd.bond_contact_compton_shell(z_i, z_j)
    m_j = ctd.bond_contact_compton_shell(z_j, z_i)
    r_bohr = bond_length_bohr(z_i, z_j, c=c)
    ang = (
        centre_bond_angle_rad(max(z_i, z_j), n_bonds_at_centre)
        if n_bonds_at_centre is not None and min(z_i, z_j) == 1
        else None
    )
    if z_i == z_j:
        route = "homonuclear"
    elif min(z_i, z_j) == 1:
        route = "hydride"
    else:
        route = "heavy_heavy"
    return NestedWFBondReadout(
        z_i,
        z_j,
        m_i,
        m_j,
        r_bohr,
        r_bohr * BOHR_RADIUS_ANGSTROM,
        ang,
        route,
    )


def benchmark_bonds_from_fragments(
    fragments: tuple[FragmentConfig, ...],
    bond_pairs: tuple[tuple[int, int], ...],
    *,
    centre_angle_for: dict[int, int] | None = None,
    bond_orders: dict[tuple[int, int], int] | None = None,
    c: float = 1.0,
) -> tuple[BondGeometry, ...]:
    """
    Build ``BondGeometry`` for a molecule from fragment list and index pairs.

    ``centre_angle_for`` maps heavy fragment index → number of light neighbours
    (for H–X–H angles).
    """
    centre_angle_for = centre_angle_for or {}
    bond_orders = bond_orders or {}
    out: list[BondGeometry] = []
    for i, j in bond_pairs:
        fi, fj = fragments[i], fragments[j]
        key = (i, j) if (i, j) in bond_orders else (j, i) if (j, i) in bond_orders else None
        bo = bond_orders.get(key) if key is not None else None
        r = bond_length_angstrom(fi.z_nuclear, fj.z_nuclear, c=c, bond_order=bo)
        ang: float | None = None
        if fi.z_nuclear == 1 and fj.z_nuclear == 1:
            ang = None
        elif fi.z_nuclear == 1 and j in centre_angle_for:
            ang = centre_bond_angle_rad(fragments[j].z_nuclear, centre_angle_for[j])
        elif fj.z_nuclear == 1 and i in centre_angle_for:
            ang = centre_bond_angle_rad(fragments[i].z_nuclear, centre_angle_for[i])
        out.append(BondGeometry(i, j, r, bond_angle_rad=ang))
    return tuple(out)


# Known small-molecule topologies (Z / electron counts from chart).
_BENCHMARK_TOPOLOGY: dict[str, dict[str, Any]] = {
    "H2": {
        "fragments": ((1, 1, "H"), (1, 1, "H")),
        "bonds": ((0, 1),),
    },
    "LIH": {
        "fragments": ((3, 3, "Li"), (1, 1, "H")),
        "bonds": ((0, 1),),
    },
    "HF": {
        "fragments": ((9, 9, "F"), (1, 1, "H")),
        "bonds": ((0, 1),),
    },
    "H2O": {
        "fragments": ((8, 8, "O"), (1, 1, "H"), (1, 1, "H")),
        "bonds": ((0, 1), (0, 2)),
        "centre_angle_for": {0: 2},
    },
    "CH4": {
        "fragments": ((6, 6, "C"),) + tuple((1, 1, "H") for _ in range(4)),
        "bonds": tuple((0, i + 1) for i in range(4)),
        "centre_angle_for": {0: 4},
    },
    "NH3": {
        "fragments": ((7, 7, "N"),) + tuple((1, 1, "H") for _ in range(3)),
        "bonds": tuple((0, i + 1) for i in range(3)),
        "centre_angle_for": {0: 3},
    },
    "LIF": {"fragments": ((3, 3, "Li"), (9, 9, "F")), "bonds": ((0, 1),)},
    "NACL": {"fragments": ((11, 11, "Na"), (17, 17, "Cl")), "bonds": ((0, 1),)},
    "HCL": {"fragments": ((17, 17, "Cl"), (1, 1, "H")), "bonds": ((0, 1),)},
    "HBR": {"fragments": ((35, 35, "Br"), (1, 1, "H")), "bonds": ((0, 1),)},
    "H2S": {
        "fragments": ((16, 16, "S"), (1, 1, "H"), (1, 1, "H")),
        "bonds": ((0, 1), (0, 2)),
        "centre_angle_for": {0: 2},
    },
    "HCN": {
        "fragments": ((1, 1, "H"), (6, 6, "C"), (7, 7, "N")),
        "bonds": ((1, 0), (1, 2)),
        "bond_orders": {(1, 2): 3},
    },
    "C2H2": {
        "fragments": ((1, 1, "H"), (6, 6, "C"), (6, 6, "C"), (1, 1, "H")),
        "bonds": ((1, 0), (1, 2), (2, 3)),
        "bond_orders": {(1, 2): 3},
    },
    "PH3": {
        "fragments": ((15, 15, "P"),) + tuple((1, 1, "H") for _ in range(3)),
        "bonds": tuple((0, i + 1) for i in range(3)),
        "centre_angle_for": {0: 3},
    },
    "CO": {"fragments": ((6, 6, "C"), (8, 8, "O")), "bonds": ((0, 1),)},
    "N2": {"fragments": ((7, 7, "N"), (7, 7, "N")), "bonds": ((0, 1),)},
    "O2": {"fragments": ((8, 8, "O"), (8, 8, "O")), "bonds": ((0, 1),)},
    "F2": {"fragments": ((9, 9, "F"), (9, 9, "F")), "bonds": ((0, 1),)},
    "CL2": {"fragments": ((17, 17, "Cl"), (17, 17, "Cl")), "bonds": ((0, 1),)},
}


def bonds_for_molecule_name(name: str, *, c: float = 1.0) -> tuple[BondGeometry, ...]:
    key = name.strip().upper()
    topo = _BENCHMARK_TOPOLOGY.get(key)
    if topo is None:
        raise KeyError(f"no nested-WF topology for molecule: {name}")
    frags = fragments_from_z_pairs(tuple(topo["fragments"]))
    return benchmark_bonds_from_fragments(
        frags,
        tuple(topo["bonds"]),
        centre_angle_for=topo.get("centre_angle_for"),
        bond_orders=topo.get("bond_orders"),
        c=c,
    )


def geometry_witness_table(
    molecule_names: tuple[str, ...],
    *,
    reference_lengths: dict[str, tuple[float, ...]] | None = None,
) -> list[dict[str, Any]]:
    """Export derived vs reference bond lengths for chart / audit JSON."""
    reference_lengths = reference_lengths or {}
    rows: list[dict[str, Any]] = []
    for name in molecule_names:
        bonds = bonds_for_molecule_name(name)
        refs = reference_lengths.get(name.upper(), ())
        for idx, b in enumerate(bonds):
            ref = refs[idx] if idx < len(refs) else None
            err = None if ref is None or ref == 0 else 100.0 * (b.distance_angstrom - ref) / ref
            rows.append(
                {
                    "molecule": name,
                    "bond_index": idx,
                    "derived_angstrom": b.distance_angstrom,
                    "reference_angstrom": ref,
                    "error_pct": err,
                    "angle_rad": b.bond_angle_rad,
                }
            )
    return rows

"""
Atomic chart translation layer — Z → (P, N) nucleus → electronic chart → monomer geometry.

Single anchor: proton reference shell (``referenceM = 4``) and hydrogen λ-unit.
No GMTKN55 name tables; bond lengths from nested shell-resolved wavefunctions
(``hqiv_chemistry_tuft_dynamics``) and angles from ``dynamic_centre_angle_rad``.

Downstream: ``infer_monomer_geometry`` → ``derive_allotropes`` → ρ, T(P), mixtures.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import TYPE_CHECKING

from hqiv_lab._scripts import ensure_scripts_on_path

ensure_scripts_on_path()

import hqiv_chemistry_tuft_dynamics as ctd  # noqa: E402
import hqiv_derived_chemistry as hdc  # noqa: E402
import hqiv_electronic_valence_shells as evs  # noqa: E402
import hqiv_nuclear_curvature_binding as ncb  # noqa: E402
from fragment_aware_bonded_horizon import BondGeometry, FragmentConfig  # noqa: E402
from hqiv_lab.derived_bond_geometry import bond_length_angstrom, centre_bond_angle_rad  # noqa: E402

if TYPE_CHECKING:
    from hqiv_lab.coordination import IntermolecularMotif
    from hqiv_lab.spec import MoleculeSpec

_SYMBOLS: tuple[str, ...] = (
    "H",
    "He",
    "Li",
    "Be",
    "B",
    "C",
    "N",
    "O",
    "F",
    "Ne",
    "Na",
    "Mg",
    "Al",
    "Si",
    "P",
    "S",
    "Cl",
    "Ar",
)


def element_symbol(z: int) -> str:
    if 1 <= z <= len(_SYMBOLS):
        return _SYMBOLS[z - 1]
    return f"Z{z}"


@dataclass(frozen=True)
class NuclearChartNode:
    """Nuclear readout at stable main isotope: H → [P, N] on the curvature ladder."""

    z: int
    a: int
    protons: int
    neutrons: int
    electrons: int
    mass_amu: float
    m_nuc: int


@dataclass(frozen=True)
class ElectronicChartNode:
    """Valence + Compton slots from TUFT electronic chart (period offset from m_s2)."""

    z: int
    period: int
    valence: int
    m_s: int
    m_p: int | None
    compton_triplet_heavy_hydride: tuple[int, int, int]


def nuclear_chart_node(z: int, *, electrons: int | None = None) -> NuclearChartNode:
    e = electrons if electrons is not None else z
    a = ncb.stable_mass_number(z, e)
    m_nuc = ncb.nucleus_curvature_shell(a) if a > 1 else ncb.REFERENCE_M
    return NuclearChartNode(
        z=z,
        a=a,
        protons=z,
        neutrons=max(a - z, 0),
        electrons=e,
        mass_amu=hdc.derived_atomic_mass_amu(z, e),
        m_nuc=m_nuc,
    )


def electronic_chart_node(z: int) -> ElectronicChartNode:
    m_s, m_p = evs.electronic_compton_shells(z)
    return ElectronicChartNode(
        z=z,
        period=evs.chemical_period(z),
        valence=evs.valence_electron_count(z),
        m_s=m_s,
        m_p=m_p,
        compton_triplet_heavy_hydride=(m_s, m_p or 1, evs.ELECTRONIC_M_H_1S),
    )


def lean_centre_lone_pair_count(z: int, n_bonds: int) -> int:
    """
    ``Hqiv.Physics.DynamicCentreGeometry.centreLonePairCount`` for motif / allotrope.

    Period 2: ``(V − n_bonds) / 2``; period ≥ 3 delegates to ``centre_vsepr_lone_pair_count``.
    """
    if z < 3 or z > 18:
        return 0
    if evs.chemical_period(z) == 2 and z <= 10:
        v = evs.period2_valence_electron_count(z)
        if v < n_bonds:
            return 0
        return (v - n_bonds) // 2
    return evs.centre_vsepr_lone_pair_count(z, n_bonds)


def steric_domain_count(z: int, n_bonds: int) -> tuple[int, int, int]:
    """``(n_lp, n_domains, n_bonds)`` from VSEPR on heavy centre Z."""
    n_lp = lean_centre_lone_pair_count(z, n_bonds)
    n_dom = n_bonds + n_lp
    return n_lp, n_dom, n_bonds


def intermolecular_motif_from_chart(
    z_heavy: int,
    n_bonds: int,
    n_lp: int,
    h_count: int,
) -> IntermolecularMotif:
    """
    Condensed-phase motif from steric domains + hydrogen count (no ``z == 8`` table).
    """
    from hqiv_lab.coordination import IntermolecularMotif

    if z_heavy == 1:
        return IntermolecularMotif.DIATOMIC
    n_dom = n_bonds + n_lp
    if n_bonds == 1 and (z_heavy <= 3 or evs.chemical_period(z_heavy) == 2 and z_heavy >= 9):
        return IntermolecularMotif.LINEAR_CHAIN
    if z_heavy in (3, 11, 19, 37, 4, 12, 20, 13, 29, 30) and n_bonds == 0 and h_count == 0:
        return IntermolecularMotif.METALLIC_LATTICE
    if n_dom == 4 and n_bonds == 2 and n_lp == 2 and h_count >= 2:
        return IntermolecularMotif.TETRAHEDRAL_HBOND
    if n_dom == 4 and n_bonds == 3 and n_lp == 1 and h_count >= 3:
        return IntermolecularMotif.PYRAMIDAL_HBOND
    if n_dom == 4 and n_bonds == 4 and n_lp == 0 and h_count >= 4:
        return IntermolecularMotif.APOLAR_CLOSE_PACK
    if n_dom >= 3 and h_count >= n_bonds:
        return IntermolecularMotif.PYRAMIDAL_HBOND
    return IntermolecularMotif.GENERIC


def intermolecular_contact_count(
    motif: IntermolecularMotif,
    *,
    n_bonds: int,
    n_lp: int,
) -> int:
    if motif.value == "tetrahedral_hbond":
        return 4
    if motif.value == "pyramidal_hbond":
        return 4
    if motif.value == "apolar_close_pack":
        return 4
    if motif.value == "linear_chain":
        return 2
    if motif.value == "diatomic":
        return 1
    if motif.value == "ionic_lattice":
        return 6
    if motif.value == "metallic_lattice":
        return 12
    return max(2, n_bonds + n_lp)


def _hydride_formula_name(z_heavy: int, n_hydrogen: int) -> str:
    """Standard hill-style labels for common chart hydrides."""
    if z_heavy == 1 and n_hydrogen == 2:
        return "H2"
    if z_heavy == 6 and n_hydrogen == 4:
        return "CH4"
    if z_heavy == 7 and n_hydrogen == 3:
        return "NH3"
    if z_heavy == 8 and n_hydrogen == 2:
        return "H2O"
    if z_heavy == 9 and n_hydrogen == 1:
        return "HF"
    sym = element_symbol(z_heavy)
    if n_hydrogen == 1:
        return f"{sym}H"
    return f"H{n_hydrogen}{sym}" if z_heavy > 1 else f"{sym}H{n_hydrogen}"


def monomer_spec_from_atomic_chart(
    z_heavy: int,
    n_hydrogen: int,
    *,
    name: str | None = None,
) -> MoleculeSpec:
    """
    Build a single-centre hydride monomer from atomic number + H count only.

    Bond lengths: ``bond_length_angstrom``; angles: ``centre_bond_angle_rad(Z, n_bonds)``.
    """
    from hqiv_lab.spec import MoleculeSpec

    if z_heavy < 1 or n_hydrogen < 1:
        raise ValueError("need z_heavy >= 1 and n_hydrogen >= 1")
    nuc = nuclear_chart_node(z_heavy)
    sym = element_symbol(z_heavy)
    heavy = FragmentConfig(sym, z_heavy, z_heavy)
    h_frags = tuple(FragmentConfig("H", 1, 1) for _ in range(n_hydrogen))
    frags = (heavy,) + h_frags
    n_bonds = n_hydrogen
    ang = centre_bond_angle_rad(z_heavy, n_bonds)
    r_hx = bond_length_angstrom(sym, "H", coord_i=max(1, n_bonds), coord_j=1)
    bonds: list[BondGeometry] = [
        BondGeometry(0, i + 1, r_hx, bond_angle_rad=ang) for i in range(n_hydrogen)
    ]
    label = name or _hydride_formula_name(z_heavy, n_hydrogen)
    return MoleculeSpec(label, frags, tuple(bonds))


def monomer_spec_diatomic_h2() -> MoleculeSpec:
    """H₂ from Z=1 only."""
    from hqiv_lab.spec import MoleculeSpec

    r = bond_length_angstrom("H", "H", coord_i=1, coord_j=1)
    frags = (FragmentConfig("H", 1, 1), FragmentConfig("H", 1, 1))
    return MoleculeSpec("H2", frags, (BondGeometry(0, 1, r),))


def chart_readout(z_heavy: int, n_hydrogen: int) -> dict[str, object]:
    """Full translation witness for lab / mixture entry."""
    nuc = nuclear_chart_node(z_heavy)
    elec = electronic_chart_node(z_heavy)
    n_lp, n_dom, n_bonds = steric_domain_count(z_heavy, n_hydrogen)
    motif = intermolecular_motif_from_chart(z_heavy, n_bonds, n_lp, n_hydrogen)
    return {
        "anchor": {"referenceM": ncb.REFERENCE_M, "hydrogen_lambda_anchor": True},
        "nuclear": {
            "Z": nuc.z,
            "A": nuc.a,
            "P": nuc.protons,
            "N": nuc.neutrons,
            "m_nuc": nuc.m_nuc,
            "mass_amu": nuc.mass_amu,
        },
        "electronic": {
            "period": elec.period,
            "valence": elec.valence,
            "compton_triplet": list(elec.compton_triplet_heavy_hydride),
            "m_s": elec.m_s,
            "m_p": elec.m_p,
        },
        "steric": {
            "n_bonds": n_bonds,
            "n_lone_pairs": n_lp,
            "n_domains": n_dom,
            "centre_angle_rad": centre_bond_angle_rad(z_heavy, n_bonds),
        },
        "condensed_motif": motif.value,
        "input_policy": "atomic_number_only",
    }

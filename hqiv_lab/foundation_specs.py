"""Foundation-tier MoleculeSpec builders — geometry from derived_bond_geometry only."""

from __future__ import annotations

from hqiv_lab.derived_bond_geometry import (
    bond_length_angstrom,
    carbonyl_bond_length_angstrom,
    centre_bond_angle_rad,
    peptide_bond_length_c_n,
    peptide_bond_length_ca_c,
    peptide_bond_length_n_ca,
)
from hqiv_lab.spec import MoleculeSpec

from hqiv_lab._scripts import ensure_scripts_on_path

ensure_scripts_on_path()
from fragment_aware_bonded_horizon import BondGeometry, FragmentConfig  # noqa: E402

_FC = FragmentConfig
_BG = BondGeometry


def _h(label: str = "H") -> FragmentConfig:
    return _FC(label, 1, 1)


def _c(label: str = "C") -> FragmentConfig:
    return _FC(label, 6, 6)


def _n(label: str = "N") -> FragmentConfig:
    return _FC(label, 7, 7)


def _o(label: str = "O") -> FragmentConfig:
    return _FC(label, 8, 8)


def _oh_bonds(c_idx: int, o_idx: int, h_idx: int) -> tuple[BondGeometry, ...]:
    r_co = bond_length_angstrom("C", "O", coord_i=4, coord_j=1)
    r_oh = bond_length_angstrom("O", "H", coord_i=1, coord_j=1)
    ang = centre_bond_angle_rad(8, 2)
    return (
        _BG(c_idx, o_idx, r_co, bond_angle_rad=ang),
        _BG(o_idx, h_idx, r_oh),
    )


def spec_methanol() -> MoleculeSpec:
    """CH₃OH — primary alcohol monomer."""
    frags = (_c("C"), _o("O"), _h("HO"), _h("H1"), _h("H2"), _h("H3"))
    r_co = bond_length_angstrom("C", "O", coord_i=4, coord_j=1)
    r_ch = bond_length_angstrom("C", "H", coord_i=4, coord_j=1)
    r_oh = bond_length_angstrom("O", "H", coord_i=1, coord_j=1)
    ang_c = centre_bond_angle_rad(6, 4)
    ang_o = centre_bond_angle_rad(8, 2)
    bonds = (
        _BG(0, 1, r_co, bond_angle_rad=ang_o),
        _BG(1, 2, r_oh),
        _BG(0, 3, r_ch, bond_angle_rad=ang_c),
        _BG(0, 4, r_ch, bond_angle_rad=ang_c),
        _BG(0, 5, r_ch, bond_angle_rad=ang_c),
    )
    return MoleculeSpec("CH3OH", frags, bonds)


def spec_glycerol() -> MoleculeSpec:
    """HO–CH₂–CH(OH)–CH₂–OH triol backbone + three OH groups."""
    frags = (
        _c("C1"),
        _c("C2"),
        _c("C3"),
        _o("O1"),
        _o("O2"),
        _o("O3"),
        _h("HO1"),
        _h("HO2"),
        _h("HO3"),
        _h("HC2"),
        _h("H1a"),
        _h("H1b"),
        _h("H3a"),
        _h("H3b"),
    )
    r_cc = bond_length_angstrom("C", "C", coord_i=4, coord_j=4)
    r_ch = bond_length_angstrom("C", "H", coord_i=4, coord_j=1)
    ang_c = centre_bond_angle_rad(6, 4)
    bonds: list[BondGeometry] = [
        _BG(0, 1, r_cc, bond_angle_rad=ang_c),
        _BG(1, 2, r_cc, bond_angle_rad=ang_c),
        _BG(1, 9, r_ch, bond_angle_rad=ang_c),
        _BG(0, 10, r_ch, bond_angle_rad=ang_c),
        _BG(0, 11, r_ch, bond_angle_rad=ang_c),
        _BG(2, 12, r_ch, bond_angle_rad=ang_c),
        _BG(2, 13, r_ch, bond_angle_rad=ang_c),
        *_oh_bonds(0, 3, 6),
        *_oh_bonds(1, 4, 7),
        *_oh_bonds(2, 5, 8),
    ]
    return MoleculeSpec("C3H8O3", tuple(frags), tuple(bonds))


def spec_glucose_open_chain() -> MoleculeSpec:
    """
    Open-chain aldohexose representative (CH₂OH–(CHOH)₄–CHO).

    Captures polyol H-bond network without pyranose ring closure (next step).
    """
    frags: list[FragmentConfig] = [_c(f"C{i}") for i in range(6)]
    frags += [_o(f"O{i}") for i in range(5)]
    frags += [_o("Oal"), _h("Hal"), _h("HO0")]
    for i in range(1, 5):
        frags.append(_h(f"HO{i}"))
    for i in range(6):
        if i not in (0, 5):
            frags.append(_h(f"H{i}"))
    # indices: C0..C5 = 0..5, O0..O4 = 6..10, Oal=11, Hal=12, HO0=13, HO1..4=14..17, H1..4=18..21
    r_cc = bond_length_angstrom("C", "C", coord_i=4, coord_j=4)
    r_ch = bond_length_angstrom("C", "H", coord_i=4, coord_j=1)
    ang_c = centre_bond_angle_rad(6, 4)
    bonds: list[BondGeometry] = []
    for i in range(5):
        bonds.append(_BG(i, i + 1, r_cc, bond_angle_rad=ang_c))
    bonds.extend(_oh_bonds(0, 6, 13))
    for k in range(1, 5):
        bonds.extend(_oh_bonds(k, 6 + k, 13 + k))
        bonds.append(_BG(k, 17 + k, r_ch, bond_angle_rad=ang_c))
    r_co = carbonyl_bond_length_angstrom()
    bonds.append(_BG(5, 11, r_co))
    bonds.append(_BG(5, 12, bond_length_angstrom("C", "H", coord_i=2, coord_j=1)))
    return MoleculeSpec("C6H12O6_open", tuple(frags), tuple(bonds))


def spec_glucose_pyranose() -> MoleculeSpec:
    """
    α-D-glucopyranose ring graph (chair): O5–C1–C2–C3–C4–C5 closure.

    Bond lengths from ``derived_bond_geometry``; ring angles from
    ``dynamicCentreAngleRad 6 4`` (Lean ``pyranose_ring_steric_domains``).
    """
    frags = (
        _o("O5"),
        _c("C1"),
        _c("C2"),
        _c("C3"),
        _c("C4"),
        _c("C5"),
        _o("O1"),
        _o("O2"),
        _o("O3"),
        _o("O4"),
        _c("C6"),
        _o("O6"),
        _h("HO1"),
        _h("HO2"),
        _h("HO3"),
        _h("HO4"),
        _h("HO6"),
        _h("H1"),
        _h("H2"),
        _h("H3"),
        _h("H4"),
        _h("H5"),
        _h("H6a"),
        _h("H6b"),
    )
    r_co = bond_length_angstrom("C", "O", coord_i=4, coord_j=1)
    r_cc = bond_length_angstrom("C", "C", coord_i=4, coord_j=4)
    r_ch = bond_length_angstrom("C", "H", coord_i=4, coord_j=1)
    r_oh = bond_length_angstrom("O", "H", coord_i=1, coord_j=1)
    ang_c = centre_bond_angle_rad(6, 4)
    ang_o = centre_bond_angle_rad(8, 2)
    bonds: list[BondGeometry] = [
        _BG(0, 1, r_co, bond_angle_rad=ang_o),
        _BG(1, 2, r_cc, bond_angle_rad=ang_c),
        _BG(2, 3, r_cc, bond_angle_rad=ang_c),
        _BG(3, 4, r_cc, bond_angle_rad=ang_c),
        _BG(4, 5, r_cc, bond_angle_rad=ang_c),
        _BG(5, 0, r_co, bond_angle_rad=ang_o),
        _BG(1, 6, r_co, bond_angle_rad=ang_c),
        _BG(2, 7, r_co, bond_angle_rad=ang_c),
        _BG(3, 8, r_co, bond_angle_rad=ang_c),
        _BG(4, 9, r_co, bond_angle_rad=ang_c),
        _BG(5, 10, r_cc, bond_angle_rad=ang_c),
        _BG(10, 11, r_co, bond_angle_rad=ang_c),
        _BG(6, 12, r_oh),
        _BG(7, 13, r_oh),
        _BG(8, 14, r_oh),
        _BG(9, 15, r_oh),
        _BG(11, 16, r_oh),
        _BG(1, 17, r_ch, bond_angle_rad=ang_c),
        _BG(2, 18, r_ch, bond_angle_rad=ang_c),
        _BG(3, 19, r_ch, bond_angle_rad=ang_c),
        _BG(4, 20, r_ch, bond_angle_rad=ang_c),
        _BG(5, 21, r_ch, bond_angle_rad=ang_c),
        _BG(10, 22, r_ch, bond_angle_rad=ang_c),
        _BG(10, 23, r_ch, bond_angle_rad=ang_c),
    ]
    return MoleculeSpec("C6H12O6_alpha", tuple(frags), tuple(bonds))


def spec_glycylglycine() -> MoleculeSpec:
    """Gly–Gly dipeptide backbone (neutral graph; zwitterion packing via motif)."""
    frags = (
        _n("N1"),
        _c("CA1"),
        _c("C1"),
        _o("O1"),
        _n("N2"),
        _c("CA2"),
        _c("C2"),
        _o("O2"),
        _h("HN1"),
        _h("HA1"),
        _h("HN2"),
        _h("HA2"),
    )
    r_cn = peptide_bond_length_c_n()
    r_n_ca = peptide_bond_length_n_ca()
    r_ca_c = peptide_bond_length_ca_c()
    r_co = carbonyl_bond_length_angstrom()
    r_nh = bond_length_angstrom("N", "H", coord_i=2, coord_j=1)
    r_ch = bond_length_angstrom("C", "H", coord_i=2, coord_j=1)
    ang = centre_bond_angle_rad(6, 4)
    bonds = (
        _BG(0, 1, r_n_ca, bond_angle_rad=ang),
        _BG(1, 2, r_ca_c, bond_angle_rad=ang),
        _BG(2, 3, r_co),
        _BG(2, 4, r_cn, bond_angle_rad=ang),
        _BG(4, 5, r_n_ca, bond_angle_rad=ang),
        _BG(5, 6, r_ca_c, bond_angle_rad=ang),
        _BG(6, 7, r_co),
        _BG(0, 8, r_nh),
        _BG(1, 9, r_ch),
        _BG(4, 10, r_nh),
        _BG(5, 11, r_ch),
    )
    return MoleculeSpec("GlyGly", frags, bonds)


def spec_sucrose_open() -> MoleculeSpec:
    """
    Disaccharide contact monomer: two open-chain hexose units linked by glycosidic C–O–C.

    Representative for C₁₂H₂₂O₁₁ condensed network (not full crystallographic graph).
    """
    g1 = spec_glucose_pyranose()
    g2 = spec_glucose_pyranose()
    offset = len(g1.fragments)
    frags = g1.fragments + g2.fragments
    bonds = list(g1.bonds)
    for b in g2.bonds:
        bonds.append(
            BondGeometry(b.frag_i + offset, b.frag_j + offset, b.distance_angstrom, bond_angle_rad=b.bond_angle_rad)
        )
    r_co = bond_length_angstrom("C", "O", coord_i=4, coord_j=1)
    ang = centre_bond_angle_rad(6, 4)
    bonds.append(_BG(5, offset + 0, r_co, bond_angle_rad=ang))
    return MoleculeSpec("C12H22O11", tuple(frags), tuple(bonds))


FOUNDATION_SPECS: dict[str, MoleculeSpec] = {
    "CH3OH": spec_methanol(),
    "C3H8O3": spec_glycerol(),
    "C6H12O6_ALPHA": spec_glucose_pyranose(),
    "C6H12O6": spec_glucose_pyranose(),
    "C6H12O6_OPEN": spec_glucose_open_chain(),
    "GLYGLY": spec_glycylglycine(),
    "C4H8N2O3": spec_glycylglycine(),
    "C12H22O11": spec_sucrose_open(),
}


def foundation_spec(name: str) -> MoleculeSpec:
    raw = name.strip().upper()
    aliases = {
        "METHANOL": "CH3OH",
        "GLYCEROL": "C3H8O3",
        "GLUCOSE": "C6H12O6_ALPHA",
        "C6H12O6_ALPHA": "C6H12O6_ALPHA",
        "GLYCYLGLYCINE": "GLYGLY",
        "SUCROSE": "C12H22O11",
    }
    key = aliases.get(raw, raw.replace("-", "").replace("_", ""))
    if key == "C6H12O6ALPHA":
        key = "C6H12O6_ALPHA"
    if key not in FOUNDATION_SPECS:
        raise KeyError(f"unknown foundation molecule: {name!r}")
    return FOUNDATION_SPECS[key]

#!/usr/bin/env python3
"""Tests for S² / p-shell binding geometry."""

from __future__ import annotations

import math

import hqiv_curvature_contact_network as ccn
import hqiv_s2_binding_geometry as s2g
from fragment_aware_bonded_horizon import BondGeometry, FragmentConfig


def test_p_shell_degeneracy_three() -> None:
    assert s2g.s2_degeneracy(1) == 3
    assert s2g.s2_degeneracy(0) == 1


def test_dihedral_max_at_zero() -> None:
    assert abs(s2g.dihedral_budget_factor(0.0) - 1.0) < 1e-12
    assert s2g.dihedral_budget_factor(math.pi) < 0.01


def test_ch4_bond_has_p_geometry() -> None:
    frags = (FragmentConfig("C", 6, 6),) + tuple(FragmentConfig("H", 1, 1) for _ in range(4))
    bonds = tuple(
        BondGeometry(0, i + 1, 1.09, bond_angle_rad=math.radians(109.47)) for i in range(4)
    )
    net = ccn.build_network_from_molecule("CH4", frags, bonds)
    cov = [c for c in net.contacts if c.kind == ccn.ContactKind.COVALENT_BOND]
    assert cov
    bg = cov[0].bond_geometry
    assert bg is not None
    assert bg.p_shell_active
    assert abs(math.degrees(bg.bond_angle_rad) - 109.47) < 0.5
    assert bg.valley_alignment_weight > 0.99
    assert bg.eta_contact > 0.0


def test_valley_relaxation_drops_when_bent_away_from_ideal() -> None:
    ideal = math.radians(109.47)
    good = s2g.bond_angular_geometry(
        m_s_i=4,
        m_p_i=3,
        m_s_j=1,
        m_p_j=None,
        distance_weight=1.0,
        bond_angle_rad=ideal,
        molecule_name="CH4",
        n_bonds_at_centre=4,
    )
    bad = s2g.bond_angular_geometry(
        m_s_i=4,
        m_p_i=3,
        m_s_j=1,
        m_p_j=None,
        distance_weight=1.0,
        bond_angle_rad=ideal + math.radians(25.0),
        molecule_name="CH4",
        n_bonds_at_centre=4,
    )
    v_good = s2g.valley_relaxation_factor((good,))
    v_bad = s2g.valley_relaxation_factor((bad,))
    assert v_good > v_bad


def test_backbone_phi_psi_sets_peptide_angle() -> None:
    phi, psi = math.radians(-60.0), math.radians(-45.0)
    backbone = (s2g.BackboneDihedral(1, phi, psi),)
    frags = tuple(FragmentConfig("C", 6, 4) for _ in range(2))
    bonds = (BondGeometry(0, 1, 1.38),)
    net = ccn.build_network_from_molecule(
        "protein_test",
        frags,
        bonds,
        backbone_dihedrals=backbone,
    )
    cov = [c for c in net.contacts if c.kind == ccn.ContactKind.COVALENT_BOND][0]
    assert cov.bond_geometry is not None
    assert cov.bond_geometry.bond_angle_rad == s2g.backbone_peptide_bond_angle_rad(phi, psi)


def test_h2o_explicit_angle_override() -> None:
    ang = math.radians(104.5)
    geo = s2g.bond_angular_geometry(
        m_s_i=4,
        m_p_i=3,
        m_s_j=1,
        m_p_j=None,
        distance_weight=1.0,
        bond_angle_rad=ang,
    )
    assert abs(geo.bond_angle_rad - ang) < 1e-9


if __name__ == "__main__":
    test_p_shell_degeneracy_three()
    test_dihedral_max_at_zero()
    test_ch4_bond_has_p_geometry()
    test_h2o_explicit_angle_override()
    test_valley_relaxation_drops_when_bent_away_from_ideal()
    test_backbone_phi_psi_sets_peptide_angle()
    print("test_hqiv_s2_binding_geometry: OK")

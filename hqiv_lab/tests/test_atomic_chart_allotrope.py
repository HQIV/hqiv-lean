#!/usr/bin/env python3
"""Atomic chart → allotrope path (Z-only inputs)."""

from __future__ import annotations

from hqiv_lab import MaterialsLab
from hqiv_lab.atomic_chart import (
    chart_readout,
    monomer_spec_diatomic_h2,
    monomer_spec_from_atomic_chart,
    nuclear_chart_node,
)
from hqiv_lab.coordination import infer_monomer_geometry


def test_nuclear_translation_h_to_pn() -> None:
    h = nuclear_chart_node(1)
    assert h.protons == 1 and h.neutrons == 0 and h.a == 1
    o = nuclear_chart_node(8)
    assert o.protons == 8 and o.neutrons == 8 and o.a == 16


def test_water_from_z_only_matches_tetrahedral_motif() -> None:
    spec = monomer_spec_from_atomic_chart(8, 2, name="H2O")
    mono = infer_monomer_geometry(spec)
    assert mono.motif.value == "tetrahedral_hbond"
    assert mono.intermolecular_contacts == 4
    ro = chart_readout(8, 2)
    assert ro["condensed_motif"] == "tetrahedral_hbond"
    assert ro["nuclear"]["P"] == 8 and ro["nuclear"]["N"] == 8


def test_atomic_chart_allotrope_ice_ih() -> None:
    lab = MaterialsLab()
    spec = lab.spec_from_atomic_chart(8, 2)
    best = lab.preferred_allotrope(spec, temperature_k=273.15)
    assert best.label.upper() == "IH"


def test_nh3_ch4_motifs_from_z() -> None:
    assert infer_monomer_geometry(monomer_spec_from_atomic_chart(7, 3)).motif.value == "pyramidal_hbond"
    assert infer_monomer_geometry(monomer_spec_from_atomic_chart(6, 4)).motif.value == "apolar_close_pack"


def test_h2_diatomic_from_z() -> None:
    mono = infer_monomer_geometry(monomer_spec_diatomic_h2())
    assert mono.motif.value == "diatomic"


if __name__ == "__main__":
    test_nuclear_translation_h_to_pn()
    test_water_from_z_only_matches_tetrahedral_motif()
    test_atomic_chart_allotrope_ice_ih()
    test_nh3_ch4_motifs_from_z()
    test_h2_diatomic_from_z()
    print("test_atomic_chart_allotrope: OK")

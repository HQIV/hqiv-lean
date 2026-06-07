"""Unit cells and mass density from derived allotropes."""

from __future__ import annotations

import math
from dataclasses import dataclass

from hqiv_lab.coordination import MonomerGeometry, infer_monomer_geometry
from hqiv_lab.packing import CrystalSystem, PackingTemplate, lattice_constants_from_template
from hqiv_lab.spec import MoleculeSpec

AVOGADRO = 6.022_140_76e23
ANGSTROM_TO_CM = 1.0e-8


@dataclass(frozen=True)
class PhaseUnitCell:
    allotrope: str
    molecules_per_cell: int
    molecular_weight_amu: float
    a_angstrom: float
    b_angstrom: float
    c_angstrom: float
    crystal: CrystalSystem

    @property
    def volume_cm3(self) -> float:
        a = self.a_angstrom * ANGSTROM_TO_CM
        b = self.b_angstrom * ANGSTROM_TO_CM
        c = self.c_angstrom * ANGSTROM_TO_CM
        if self.crystal == CrystalSystem.HEXAGONAL:
            return (math.sqrt(3.0) / 2.0) * a * a * c
        if self.crystal == CrystalSystem.CUBIC:
            return a * a * a
        return a * b * c


def density_g_cm3(cell: PhaseUnitCell) -> float:
    mass_g = cell.molecules_per_cell * cell.molecular_weight_amu / AVOGADRO
    return mass_g / cell.volume_cm3


def unit_cell_for_allotrope(
    spec: MoleculeSpec,
    template: PackingTemplate,
    mono: MonomerGeometry | None = None,
    *,
    temperature_k: float = 273.15,
) -> PhaseUnitCell:
    """Build unit cell from spec + packing template (derived geometry)."""
    mono = mono or infer_monomer_geometry(spec)
    a, b, c = lattice_constants_from_template(mono, template, temperature_k=temperature_k)
    return PhaseUnitCell(
        allotrope=template.label,
        molecules_per_cell=template.molecules_per_cell,
        molecular_weight_amu=spec.molecular_weight_amu,
        a_angstrom=a,
        b_angstrom=b,
        c_angstrom=c,
        crystal=template.crystal,
    )

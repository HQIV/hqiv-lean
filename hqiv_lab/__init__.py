"""
HQIV chemistry and materials lab — derive phases and allotropes from molecular inputs.

No fitted potentials: monomer geometry (bonds, VSEPR, coordination) → packing templates
→ unit cells → density / melt / material response (via repo scripts).

Quick start (from repository root)::

    from hqiv_lab import MaterialsLab, MoleculeSpec

    lab = MaterialsLab()
    spec = lab.spec_from_name("H2O")
    candidates = lab.derive_allotropes(spec)
    best = lab.preferred_allotrope(spec)
    cell = lab.unit_cell(spec, best.label)
"""

from hqiv_lab.allotrope import AllotropeCandidate, derive_allotropes, preferred_allotrope
from hqiv_lab.lab import MaterialsLab
from hqiv_lab.spec import MoleculeSpec
from hqiv_lab.unit_cell import PhaseUnitCell, unit_cell_for_allotrope

__all__ = [
    "AllotropeCandidate",
    "MaterialsLab",
    "MoleculeSpec",
    "PhaseUnitCell",
    "derive_allotropes",
    "preferred_allotrope",
    "unit_cell_for_allotrope",
]

__version__ = "0.1.0"

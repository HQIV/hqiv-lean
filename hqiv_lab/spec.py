"""Molecule specifications — the primary input to the materials lab."""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import TYPE_CHECKING

from hqiv_lab._scripts import ensure_scripts_on_path

if TYPE_CHECKING:
    from fragment_aware_bonded_horizon import BondGeometry, FragmentConfig

ensure_scripts_on_path()
from fragment_aware_bonded_horizon import BondGeometry, FragmentConfig  # noqa: E402


@dataclass(frozen=True)
class MoleculeSpec:
    """Covalent monomer: fragments + bonds (+ optional reference binding for witnesses)."""

    name: str
    fragments: tuple[FragmentConfig, ...]
    bonds: tuple[BondGeometry, ...]
    reference_binding_ev: float | None = None
    reference_source: str = "derived"

    @property
    def formula_key(self) -> str:
        return self.name.upper()

    @property
    def molecular_weight_amu(self) -> float:
        from hqiv_lab.coordination import element_amu

        return sum(element_amu(f.label, f.z_nuclear) for f in self.fragments)

    @classmethod
    def from_nested_wf(cls, name: str) -> MoleculeSpec:
        """Geometry from nested shell wavefunctions; no benchmark geometry enters."""
        return resolve_spec(name)

    @classmethod
    def from_atomic_chart(cls, z_heavy: int, n_hydrogen: int, *, name: str | None = None) -> MoleculeSpec:
        from hqiv_lab.atomic_chart import monomer_spec_from_atomic_chart

        return monomer_spec_from_atomic_chart(z_heavy, n_hydrogen, name=name)

    @classmethod
    def from_chart_name(cls, name: str) -> MoleculeSpec:
        """Compatibility name: resolve from HQIV-derived specs, not benchmark tables."""
        return resolve_spec(name)

    @classmethod
    def from_formula(cls, formula: str) -> MoleculeSpec:
        """
        Build a minimal spec from a hill formula (H2O, CH4, NH3, HF, H2, LiH).

        Uses chart or foundation builders when available.
        """
        key = _normalize_formula(formula)
        return resolve_spec(key)

    @classmethod
    def from_foundation_name(cls, name: str) -> MoleculeSpec:
        from hqiv_lab.foundation_specs import foundation_spec

        return foundation_spec(name)


def resolve_spec(name: str) -> MoleculeSpec:
    """Resolve names without using benchmark geometry or reference energies as inputs."""
    key = _normalize_formula(name)
    hydrides: dict[str, tuple[int, int]] = {
        "H2": (1, 2),
        "LIH": (3, 1),
        "BH3": (5, 3),
        "CH4": (6, 4),
        "NH3": (7, 3),
        "H2O": (8, 2),
        "HF": (9, 1),
        "HCL": (17, 1),
    }
    if key in hydrides:
        z_heavy, n_h = hydrides[key]
        return MoleculeSpec.from_atomic_chart(z_heavy, n_h, name=key)
    try:
        return MoleculeSpec.from_foundation_name(key)
    except KeyError as exc:
        raise KeyError(
            f"unknown derived HQIV molecule {name!r}; add an atomic-chart or "
            "foundation spec instead of importing a benchmark table"
        ) from exc


def _normalize_formula(formula: str) -> str:
    f = formula.strip()
    if re.fullmatch(r"[A-Za-z0-9]+", f):
        return f[0].upper() + f[1:] if len(f) > 1 and f[1].islower() else f.upper()
    return f.upper()

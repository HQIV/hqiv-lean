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
        """Geometry from nested shell wavefunctions; reference binding for witnesses only."""
        import hqiv_dynamic_binding_chart as chart

        key = name.strip().upper()
        for bench in chart.ALL_MOLECULE_BENCHMARKS:
            if bench.name.upper() == key:
                derived = chart.benchmark_with_nested_wf_geometry(bench)
                return cls(
                    derived.name,
                    derived.fragments,
                    derived.bonds,
                    reference_binding_ev=derived.reference_ev,
                    reference_source=derived.reference_source,
                )
        from hqiv_lab.atomic_chart import monomer_spec_from_atomic_chart

        if key == "H2":
            return cls.from_atomic_chart(1, 2)
        raise KeyError(f"unknown molecule for nested-WF geometry: {name}")

    @classmethod
    def from_atomic_chart(cls, z_heavy: int, n_hydrogen: int, *, name: str | None = None) -> MoleculeSpec:
        from hqiv_lab.atomic_chart import monomer_spec_from_atomic_chart

        return monomer_spec_from_atomic_chart(z_heavy, n_hydrogen, name=name)

    @classmethod
    def from_chart_name(cls, name: str) -> MoleculeSpec:
        import hqiv_dynamic_binding_chart as chart

        for bench in chart.GMTKN55_SUITE:
            if bench.name.upper() == name.upper():
                return cls(
                    name=bench.name,
                    fragments=bench.fragments,
                    bonds=bench.bonds,
                    reference_binding_ev=bench.reference_ev,
                    reference_source=bench.reference_source,
                )
        raise KeyError(f"unknown GMTKN55 molecule: {name}")

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
    """GMTKN55 chart first, then foundation-tier builders."""
    try:
        return MoleculeSpec.from_chart_name(name)
    except KeyError:
        return MoleculeSpec.from_foundation_name(name)


def _normalize_formula(formula: str) -> str:
    f = formula.strip()
    if re.fullmatch(r"[A-Za-z0-9]+", f):
        return f[0].upper() + f[1:] if len(f) > 1 and f[1].islower() else f.upper()
    return f.upper()

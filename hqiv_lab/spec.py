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

        Uses chart data when available; otherwise raises.
        """
        key = _normalize_formula(formula)
        return cls.from_chart_name(key)


def _normalize_formula(formula: str) -> str:
    f = formula.strip()
    if re.fullmatch(r"[A-Za-z0-9]+", f):
        return f[0].upper() + f[1:] if len(f) > 1 and f[1].islower() else f.upper()
    return f.upper()

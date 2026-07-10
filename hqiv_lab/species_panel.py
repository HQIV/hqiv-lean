"""Condensed-phase panel: species melt witnesses and NIST comparison targets.

Witness temperature is the solidification reference for each species (not a fit knob).
Condensed packing uses Lindemann / Brownian piezo
``ε = (γ/2)·√(T/T_melt)`` (``γ/4`` on linear chains) plus apolar open
``1+(4/8)·γ`` — Lean ``lindemannThermalStrain``.

Crystal species (ionic / metallic) use lattice-contact geometry, not gas-phase diatomic
spectroscopy constants, as the primary structural readout.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

CrystalKind = Literal["molecular", "ionic", "metallic", "covalent_network"]


@dataclass(frozen=True)
class SpeciesPanelEntry:
    molecule: str
    allotrope: str
    witness_temperature_k: float
    nist_solid_density_g_cm3: float
    nist_refractive_index: float
    nist_melt_k: float
    motif_label: str
    crystal_kind: CrystalKind = "molecular"
    z_values: tuple[int, ...] = ()

    def resolved_crystal_kind(self) -> CrystalKind:
        """Prefer capacity / donor×acceptor derivation when Z is known."""
        if not self.z_values:
            return self.crystal_kind
        from hqiv_lab.crystal_geometry import derive_crystal_kind

        return derive_crystal_kind(self.z_values)  # type: ignore[return-value]


# NIST / CRC panel references for benchmark comparison only (not HQIV inputs).
CONDENSED_SPECIES_PANEL: tuple[SpeciesPanelEntry, ...] = (
    SpeciesPanelEntry(
        "H2O",
        "Ih",
        273.15,
        0.917,
        1.31,
        273.15,
        "tetrahedral / Ih",
    ),
    SpeciesPanelEntry(
        "CH4",
        "solid_I",
        90.0,
        0.523,
        1.10,
        90.7,
        "apolar / solid_I",
    ),
    SpeciesPanelEntry(
        "NH3",
        "solid",
        195.8,
        0.817,
        1.32,
        195.8,
        "pyramidal / fcc",
    ),
    SpeciesPanelEntry(
        "HF",
        "chain",
        189.6,
        1.15,
        1.20,
        189.6,
        "linear chain / Z=4",
    ),
    SpeciesPanelEntry(
        "NaCl",
        "B1",
        1074.0,
        2.17,
        1.544,
        1074.0,
        "ionic rocksalt / B1",
        crystal_kind="ionic",
        z_values=(11, 17),
    ),
    SpeciesPanelEntry(
        "KCl",
        "B1",
        1045.0,
        1.98,
        1.490,
        1045.0,
        "ionic rocksalt / B1",
        crystal_kind="ionic",
        z_values=(19, 17),
    ),
    SpeciesPanelEntry(
        "LiF",
        "B1",
        1121.0,
        2.64,
        1.392,
        1121.0,
        "ionic rocksalt / B1",
        crystal_kind="ionic",
        z_values=(3, 9),
    ),
    SpeciesPanelEntry(
        "NaF",
        "B1",
        1266.0,
        2.56,
        1.325,
        1266.0,
        "ionic rocksalt / B1",
        crystal_kind="ionic",
        z_values=(11, 9),
    ),
    SpeciesPanelEntry(
        "Li",
        "bcc",
        453.69,
        0.534,
        0.0,
        453.69,
        "metallic bcc / CN=8",
        crystal_kind="metallic",
        z_values=(3,),
    ),
    SpeciesPanelEntry(
        "Na",
        "bcc",
        370.87,
        0.968,
        0.0,
        370.87,
        "metallic bcc / CN=8",
        crystal_kind="metallic",
        z_values=(11,),
    ),
    SpeciesPanelEntry(
        "Al",
        "fcc",
        933.47,
        2.70,
        0.0,
        933.47,
        "metallic fcc / CN=12",
        crystal_kind="metallic",
        z_values=(13,),
    ),
    SpeciesPanelEntry(
        "Cu",
        "fcc",
        1357.77,
        8.96,
        0.0,
        1357.77,
        "metallic fcc / CN=12",
        crystal_kind="metallic",
        z_values=(29,),
    ),
    SpeciesPanelEntry(
        "Si",
        "diamond",
        1687.0,
        2.33,
        3.42,
        1687.0,
        "covalent diamond-cubic / k=4",
        crystal_kind="covalent_network",
        z_values=(14,),
    ),
    SpeciesPanelEntry(
        "Ge",
        "diamond",
        1211.0,
        5.32,
        4.0,
        1211.0,
        "covalent diamond-cubic / k=4",
        crystal_kind="covalent_network",
        z_values=(32,),
    ),
)


def panel_entry(molecule: str) -> SpeciesPanelEntry:
    key = molecule.upper()
    for row in CONDENSED_SPECIES_PANEL:
        if row.molecule.upper() == key:
            return row
    raise KeyError(f"no condensed panel entry for {molecule!r}")


def witness_temperature_k(molecule: str, *, at_melt: bool = True) -> float:
    """Solid witness temperature: species melt reference when ``at_melt`` else 273.15 K."""
    if not at_melt:
        return 273.15
    return panel_entry(molecule).witness_temperature_k

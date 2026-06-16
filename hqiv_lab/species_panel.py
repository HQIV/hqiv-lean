"""Condensed-phase panel: species melt witnesses and NIST comparison targets.

Witness temperature is the solidification reference for each species (not a fit knob).
Apolar CH₄ uses thermal contact breathing ``(T/T_ref)^(γ/16)`` only below melt.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class SpeciesPanelEntry:
    molecule: str
    allotrope: str
    witness_temperature_k: float
    nist_solid_density_g_cm3: float
    nist_refractive_index: float
    nist_melt_k: float
    motif_label: str


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

#!/usr/bin/env python3
"""
Canonical mirror of ``HqivSpine/Chemistry/*`` for Python scripts and ``hqiv_lab``.

Single source for lattice-forced chemistry constants — do not duplicate Slater increments,
VSEPR cosines, or monogamy spectator weights elsewhere.

Lean anchors:
  ``Chemistry.Binding`` — screening from ``α/referenceM``
  ``Chemistry.VSEPR`` — ``balanced_unit_contacts_cos``
  ``Chemistry.ShellStructure`` — octet / monogamy pair multiplicity
  ``Chemistry.Spectroscopy`` — ``monogamySpectatorContact``
  ``Chemistry.Biomolecule`` — WC H-bond counts (A·T=2, G·C=3)
  ``Chemistry.Molecule`` — ``siteModeEnergyOfCarrier``
"""

from __future__ import annotations

import math

import hqiv_lean_physics_primitives as lean

# --- Lattice rationals (Foundation / Shell) ---------------------------------

ALPHA = lean.ALPHA
GAMMA = lean.GAMMA
REFERENCE_M = lean.REFERENCE_M
CARRIER_MULTIPLICITY = 8
MONOGAMY_PAIR_MULTIPLICITY = 2
OCTET_CAPACITY = CARRIER_MULTIPLICITY  # ShellStructure.octetCapacity_eq_carrierMultiplicity

# --- Slater screening (Binding.lean) --------------------------------------

SCREEN_PENETRATION_LEAK = ALPHA / float(REFERENCE_M)  # α/referenceM = 0.15
MONOGAMY_HALF = 1.0 / float(MONOGAMY_PAIR_MULTIPLICITY)
SLATER_SAME_SHELL = MONOGAMY_HALF - SCREEN_PENETRATION_LEAK  # 0.35
SLATER_ADJACENT_SHELL = 1.0 - SCREEN_PENETRATION_LEAK  # 0.85
SLATER_DEEP_SHELL = 1.0

# --- Spectroscopy / H-bond spectator (Spectroscopy + Biomolecule) -----------

MONOGAMY_SPECTATOR_CONTACT = 1.0 + GAMMA / 2.0  # 6/5; equals 2α at γ=2/5

# --- VSEPR (VSEPR.lean) -----------------------------------------------------


def balanced_unit_contacts_cos(steric_domains: int) -> float:
    """Cosine of the common pairwise angle for ``d`` balanced unit contacts."""
    if steric_domains < 2:
        raise ValueError("steric_domains must be ≥ 2")
    return -1.0 / float(steric_domains - 1)


def tetrahedral_contact_cos() -> float:
    """sp³ equilibrium cosine ``−1/3`` (VSEPR.tetrahedral_cos)."""
    return balanced_unit_contacts_cos(4)


def slater_shielding_increment(n_target: int, n_other: int) -> float:
    """``slaterShieldingIncrement`` — same / adjacent / deep / outer."""
    if n_other == n_target:
        return SLATER_SAME_SHELL
    if n_other + 1 == n_target:
        return SLATER_ADJACENT_SHELL
    if n_other < n_target:
        return SLATER_DEEP_SHELL
    return 0.0


def site_mode_energy(m: int, *, carrier: int = CARRIER_MULTIPLICITY) -> float:
    """``siteModeEnergyOfCarrier c m = (c/2)(m+2)(m+1)²`` (Molecule.lean)."""
    if m < 0:
        raise ValueError("shell index m must be nonnegative")
    return (carrier / 2.0) * (m + 2) * (m + 1) ** 2


def h2_site_energy_same_shell(m: int, *, carrier: int = CARRIER_MULTIPLICITY) -> float:
    """Homonuclear diatomic ``2 · siteModeEnergy`` at equal shells."""
    return 2.0 * site_mode_energy(m, carrier=carrier)


# --- Biomolecule (Biomolecule.lean) — canonical WC counts -------------------

CANONICAL_WC_HBOND_COUNTS: dict[str, int] = {
    "AT": 2,
    "TA": 2,
    "GC": 3,
    "CG": 3,
}

SPINE_CHEMISTRY_MODULES = (
    "Chemistry.Binding",
    "Chemistry.VSEPR",
    "Chemistry.ShellStructure",
    "Chemistry.Spectroscopy",
    "Chemistry.Biomolecule",
    "Chemistry.Molecule",
    "Chemistry.Aufbau",
    "Chemistry.Atom",
)


def spine_manifest() -> dict[str, object]:
    """Report block for audits — values scripts should match."""
    m = REFERENCE_M
    return {
        "lean_modules": list(SPINE_CHEMISTRY_MODULES),
        "alpha": ALPHA,
        "gamma": GAMMA,
        "reference_m": REFERENCE_M,
        "screen_penetration_leak": SCREEN_PENETRATION_LEAK,
        "slater_same_shell": SLATER_SAME_SHELL,
        "slater_adjacent_shell": SLATER_ADJACENT_SHELL,
        "slater_deep_shell": SLATER_DEEP_SHELL,
        "monogamy_spectator_contact": MONOGAMY_SPECTATOR_CONTACT,
        "tetrahedral_cos": tetrahedral_contact_cos(),
        "h2_site_energy_reference_m": h2_site_energy_same_shell(m),
        "carbon_zeff_spine": 6.0 - (2 * SLATER_ADJACENT_SHELL + 3 * SLATER_SAME_SHELL),
    }

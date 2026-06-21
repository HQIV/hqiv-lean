#!/usr/bin/env python3
"""
Valence-derived isospin I₃ for HEP mass readouts.

Lean mirror: ``HepDecayReadout.baryonValenceIsospinThird`` /
``mesonValenceIsospinThird`` / ``isospinThirdSlotOfRational``.

Valence content comes from ``data/hadron-catalog.js`` (discharged quark
bookkeeping), not PDG mass tables.
"""

from __future__ import annotations

from functools import lru_cache
from typing import Literal

import hqiv_hep_decay_readout as hdr
import hqiv_mass_calculator_core as hmc

IsospinThirdSlot = hdr.IsospinThirdSlot

_LIGHT_FLAVORS = frozenset({"u", "d"})


def _light_isospin_contribution(flavor: str, role: str) -> float:
    """Single valence slot contribution to I₃ (u,d only; s,c,b,t → 0)."""
    if flavor not in _LIGHT_FLAVORS:
        return 0.0
    unit = 0.5 if flavor == "u" else -0.5
    return unit if role == "quark" else -unit


def valence_isospin_third(valence: list[tuple[str, str]], *, structure: str) -> float:
    """Total I₃ from catalog valence (baryon: quarks only; meson: q+q̄)."""
    if structure == "baryon":
        return sum(
            _light_isospin_contribution(f, r)
            for f, r in valence
            if r == "quark"
        )
    if structure == "meson":
        return sum(_light_isospin_contribution(f, r) for f, r in valence)
    return 0.0


def isospin_third_slot_from_i3(i3: float, *, tol: float = 1e-9) -> IsospinThirdSlot | None:
    """Map a discharged I₃ value to ``IsospinThirdSlot`` when exact."""
    candidates: list[tuple[float, IsospinThirdSlot]] = [
        (0.0, "zero"),
        (0.5, "halfPlus"),
        (-0.5, "halfMinus"),
        (1.0, "plus"),
        (-1.0, "minus"),
    ]
    for target, slot in candidates:
        if abs(i3 - target) <= tol:
            return slot
    return None


def _structure_for_valence(valence: list[tuple[str, str]], structure: str) -> str:
    """Meson-style I₃ whenever antiquarks appear (catalog parser may lag variety blocks)."""
    if any(role == "antiquark" for _, role in valence):
        return "meson"
    return structure if structure in {"baryon", "meson", "tetraquark", "pentaquark"} else "baryon"


def isospin_third_slot_from_valence(
    valence: list[tuple[str, str]],
    *,
    structure: str,
) -> IsospinThirdSlot | None:
    """Derive ``IsospinThirdSlot`` from explicit valence content."""
    st = _structure_for_valence(valence, structure)
    return isospin_third_slot_from_i3(valence_isospin_third(valence, structure=st))


@lru_cache(maxsize=1)
def _catalog_rows() -> tuple[dict[str, dict], dict[str, dict]]:
    by_config: dict[str, dict] = {}
    by_pdg: dict[str, dict] = {}
    for row in hmc.parse_hadron_catalog():
        by_config[row["config_id"]] = row
        pdg = str(row.get("pdgName") or "")
        if pdg:
            by_pdg[pdg] = row
    return by_config, by_pdg


def catalog_row_for_config_id(config_id: str | None) -> dict | None:
    if not config_id:
        return None
    return _catalog_rows()[0].get(config_id)


def catalog_row_for_pdg_key(key: str) -> dict | None:
    """Match panel ``key`` against catalog ``pdgName`` (with light normalisation)."""
    _, by_pdg = _catalog_rows()
    if key in by_pdg:
        return by_pdg[key]
    aliases = {
        "Jpsi": "J/psi",
        "phi(1020)": "phi",
        "Upsilon2S": "Upsilon",
        "Upsilon3S": "Upsilon",
        "psi2S": "J/psi",
        "ccd_baryon": "ccd",
        "K*+": "K*+",
        "K*-": "K*-",
        "K*0": "K*0",
        "K*0_bar": "K*0_bar",
    }
    alt = aliases.get(key)
    if alt and alt in by_pdg:
        return by_pdg[alt]
    return None


# Neutral isovector / isoscalar vectors where a single q q̄ proxy valence mis-tags I₃.
PDG_KEY_ISOSPIN_OVERRIDES: dict[str, IsospinThirdSlot] = {
    "rho0": "zero",
    "omega": "zero",
}


def isospin_third_for_entry(entry: dict) -> float | None:
    """Discharged I₃ (float) from slot or raw valence when the slot enum does not cover |I₃|>1."""
    slot = isospin_third_slot_for_entry(entry)
    if slot is not None:
        import hqiv_hep_decay_readout as hdr

        return hdr.isospin_third_of_slot(slot)
    key = str(entry.get("key") or "")
    config_id = entry.get("config_id")
    row = catalog_row_for_config_id(str(config_id) if config_id else None)
    if row is None:
        row = catalog_row_for_pdg_key(key)
    if row is None:
        return None
    i3 = valence_isospin_third(
        list(row.get("valence") or []),
        structure=str(row.get("structure") or "baryon"),
    )
    if abs(i3) < 1e-9:
        return 0.0
    return i3


def isospin_third_slot_for_entry(entry: dict) -> IsospinThirdSlot | None:
    """Resolve isospin slot from ``config_id`` or ``key`` → catalog valence."""
    key = str(entry.get("key") or "")
    override = PDG_KEY_ISOSPIN_OVERRIDES.get(key)
    if override is not None:
        return override
    config_id = entry.get("config_id")
    row = catalog_row_for_config_id(str(config_id) if config_id else None)
    if row is None:
        row = catalog_row_for_pdg_key(key)
    if row is None:
        return None
    return isospin_third_slot_from_valence(
        list(row.get("valence") or []),
        structure=str(row.get("structure") or "baryon"),
    )

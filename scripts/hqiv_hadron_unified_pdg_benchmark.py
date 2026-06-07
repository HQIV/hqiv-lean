#!/usr/bin/env python3
"""
PDG benchmark for TUFT unified hadron excited masses vs vev / trapped / refinements.

Run:
  python3 scripts/hqiv_hadron_unified_pdg_benchmark.py
"""

from __future__ import annotations

import json
from pathlib import Path

import hqiv_excited_states as hes
import hqiv_hadron_global_excitation as hge
import hqiv_tuft_mass_spectrum_pdg_eval as tmse

P = tmse.PROTON_MEV
XI = tmse.XI_LOCKIN
DATA = Path(__file__).resolve().parents[1] / "data" / "hadron_published_masses.json"

READOUTS = {
    "unified": lambda n, ell: hge.tuft_hadron_excited_mass_unified_inside_at_xi_mev(XI, n, ell),
    "unified+phase": lambda n, ell: hge.tuft_hadron_excited_mass_unified_phase_at_xi_mev(XI, n, ell),
    "unified+split": lambda n, ell: hge.tuft_hadron_excited_mass_unified_split_at_xi_mev(XI, n, ell),
    "unified+ijk×": lambda n, ell: hge.tuft_hadron_excited_mass_unified_ijk_weighted_at_xi_mev(XI, n, ell),
    "unified+B_curv": lambda n, ell: hge.tuft_hadron_excited_mass_unified_with_curvature_at_xi_mev(
        XI, n, ell
    ),
    "trapped": lambda n, ell: hes.meta_horizon_trapped_planck_mass_mev(n, ell, derived_proton_mev=P),
    "vev inline": lambda n, ell: tmse.tuft_hadron_excited_mass_at_xi_mev(XI, n, ell),
}


def load_nucleon_pdg() -> list[dict]:
    with open(DATA) as f:
        entries = json.load(f)["entries"]
    out: list[dict] = []
    seen: set[str] = set()
    for e in entries:
        if e.get("category") not in ("baryon_resonance", "baryon_decuplet"):
            continue
        name = e.get("name") or e.get("key", "")
        if not (name.startswith("N(") or "Delta" in name or name.startswith("Δ")):
            continue
        if name in seen:
            continue
        seen.add(name)
        out.append(
            {
                "name": name,
                "pdg": float(e["mass_MeV"]),
                "unc": float(e.get("uncertainty_MeV") or 20.0),
            }
        )
    return sorted(out, key=lambda x: x["pdg"])


def nearest_shell_mass(readout_fn, pdg: float) -> tuple[int, float, float]:
    best_m, best_mass, best_err = 4, readout_fn(0, 0), abs(readout_fn(0, 0) - pdg)
    for m in range(5, 14):
        n = m - 4
        mass = readout_fn(n, 0)
        err = abs(mass - pdg)
        if err < best_err:
            best_m, best_mass, best_err = m, mass, err
    return best_m, best_mass, 100.0 * (best_mass - pdg) / pdg


def main() -> None:
    pdg_list = load_nucleon_pdg()
    print("TUFT hadron excited readouts vs PDG (nearest shell m = referenceM + n, ℓ=0)\n")
    print(f"{'State':<16} {'PDG':>7} {'±':>5}", end="")
    for label in READOUTS:
        print(f"  {label:>14}", end="")
    print()
    print("-" * (30 + 16 * len(READOUTS)))

    stats: dict[str, list[float]] = {k: [] for k in READOUTS}
    for row in pdg_list:
        print(f"{row['name']:<16} {row['pdg']:7.1f} {row['unc']:5.0f}", end="")
        for label, fn in READOUTS.items():
            _m, _mass, pct = nearest_shell_mass(fn, row["pdg"])
            stats[label].append(abs(pct))
            print(f"  {pct:+13.1f}%", end="")
        print()

    print("\nMean |residual|:")
    for label, errs in stats.items():
        print(f"  {label:16s} {sum(errs) / len(errs):5.1f}%  (median {sorted(errs)[len(errs) // 2]:.1f}%)")

    print("\nFixed chart (BARYON_EXCITED_GRID labels):")
    for n, ell, key in tmse.BARYON_EXCITED_GRID:
        if not key:
            continue
        pdg = tmse.PDG_MEV[key]
        print(f"  {key:14s} (n={n},ℓ={ell})", end="")
        for label, fn in READOUTS.items():
            m = fn(n, ell)
            print(f"  {label}: {100*m/pdg:5.1f}%", end="")
        print()


if __name__ == "__main__":
    main()

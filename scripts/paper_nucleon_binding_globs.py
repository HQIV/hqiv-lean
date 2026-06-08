#!/usr/bin/env python3
"""Emit `globs` for the `paper_nucleon_binding` Lake target.

Import-closure of Lean modules cited in
``papers/nucleon_binding/hqiv_nucleon_binding_from_composite_trace.tex``
(Appendix lean index). Paste output into ``lakefile.toml`` under
``[[lean_lib]] name = "paper_nucleon_binding"``.

Usage (from repo root):
  python3 scripts/paper_nucleon_binding_globs.py
"""
from __future__ import annotations

import os
import re
from collections import deque

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

PAPER_ROOTS = (
    "Hqiv.Physics.ScaleWitness",
    "Hqiv.Physics.NuclearCurvatureBinding",
    "Hqiv.Physics.NuclearCausticBinding",
    "Hqiv.Physics.HQIVNuclei",
    "Hqiv.Physics.BoundStates",
    "Hqiv.Physics.DerivedNucleonMass",
    "Hqiv.Physics.QuarkMetaResonance",
    "Hqiv.Physics.NeutronBindingStabilityScaffold",
    "Hqiv.Physics.SpinStatistics",
    "Hqiv.Physics.DynamicBetaIsotope",
    "Hqiv.Physics.DynamicIsotopeStability",
    "Hqiv.Physics.NeutronLifetimeMethod",
    "Hqiv.Physics.WeakFanoHopfBridge",
    "Hqiv.Physics.Forces",
    "Hqiv.Physics.NuclearAndAtomicSpectra",
    "Hqiv.Physics.NuclearOutsideTemperatureDynamics",
    "Hqiv.Physics.DerivedGaugeAndLeptonSector",
    "Hqiv.Physics.DynamicNucleonPN",
    "Hqiv.Physics.HomogeneousCurvatureSecondOrder",
    "Hqiv.QuantumChemistry.BondStateNetwork",
    "Hqiv.QuantumChemistry.CurvatureBondContact",
    "Hqiv.QuantumChemistry.PhaseAllotropeDerivation",
    "Hqiv.QuantumChemistry.PhaseGeometryDensity",
    "Hqiv.QuantumChemistry.PhaseMaterialResponse",
    "Hqiv.Algebra.PhaseLiftDelta",
)


def mod_to_path(mod: str) -> str | None:
    path = os.path.join(REPO, mod.replace(".", "/") + ".lean")
    return path if os.path.isfile(path) else None


def read_hqiv_imports(path: str) -> list[str]:
    out: list[str] = []
    with open(path, encoding="utf-8") as handle:
        for line in handle:
            match = re.match(r"import\s+(Hqiv\.\S+)", line.strip())
            if match:
                out.append(match.group(1))
    return out


def import_closure() -> list[str]:
    seen: set[str] = set()
    queue: deque[str] = deque(PAPER_ROOTS)
    while queue:
        mod = queue.popleft()
        if mod in seen:
            continue
        path = mod_to_path(mod)
        if path is None:
            continue
        seen.add(mod)
        queue.extend(read_hqiv_imports(path))
    return sorted(seen)


def main() -> None:
    globs = import_closure()
    print(f"# {len(globs)} modules in paper_nucleon_binding import closure")
    print("globs = [")
    for entry in globs:
        print(f'  "{entry}",')
    print("]")


if __name__ == "__main__":
    main()

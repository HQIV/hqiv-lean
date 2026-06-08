#!/usr/bin/env python3
"""Emit `globs` for the `paper_tuft_sm_lagrangian` Lake target.

Import-closure of every Lean module cited in papers/tuft_sm_lagrangian/
(Appendix lean catalog). Paste output into `lakefile.toml` under
`[[lean_lib]] name = "paper_tuft_sm_lagrangian"`.

Usage (from repo root):
  python3 scripts/paper_tuft_sm_globs.py
"""
from __future__ import annotations

import os
import re
from collections import deque

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

PAPER_ROOTS = (
    "Hqiv.Physics.StandardModelLagrangianFromDiscreteAction",
    "Hqiv.Physics.HopfShellBeltramiMassBridge",
    "Hqiv.Physics.FanoActionToDetuningJet",
    "Hqiv.Physics.FanoOmaxwellSpectrum",
    "Hqiv.Physics.FanoDetuningFirstOrder",
    "Hqiv.Physics.GlobalDetuning",
    "Hqiv.Physics.TuftGlobalHadronReadout",
    "Hqiv.Physics.TuftElectroweakBosonReadout",
    "Hqiv.Physics.TuftShellChart",
    "Hqiv.Physics.ScaleWitness",
    "Hqiv.Geometry.UniverseAge",
    "Hqiv.Cosmology.CosmologicalShellLadder",
    "Hqiv.Geometry.Now",
    "Hqiv.Geometry.HQVMetric",
    "Hqiv.Physics.BaryogenesisEtaPaper",
    "Hqiv.Physics.DynamicBBNBaryogenesis",
    "Hqiv.Physics.Action",
    "Hqiv.Geometry.AuxiliaryField",
    "Hqiv.Topology.HopfShellComplex",
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
    print(f"# {len(globs)} modules in paper_tuft_sm_lagrangian import closure")
    print("globs = [")
    for entry in globs:
        print(f'  "{entry}",')
    print("]")


if __name__ == "__main__":
    main()

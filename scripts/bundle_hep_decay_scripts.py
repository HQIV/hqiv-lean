#!/usr/bin/env python3
"""Refresh papers/hep_decay_readout/scripts/ and scripts.zip.

Includes HEP decay reproducers plus strong-sector collider discharge/refinement witnesses.

Usage:
  python3 scripts/bundle_hep_decay_scripts.py
"""
from __future__ import annotations

import ast
import hashlib
import os
import shutil
import zipfile
from collections import deque
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
SCRIPTS_ROOT = REPO / "scripts"
DEST = REPO / "papers" / "hep_decay_readout" / "scripts"
PAPER_DATA = REPO / "papers" / "hep_decay_readout" / "data"
ZIP_PATH = REPO / "papers" / "hep_decay_readout" / "scripts.zip"

ENTRY_SCRIPTS = [
    "hqiv_hep_decay_readout.py",
    "hqiv_hep_valence_isospin.py",
    "hqiv_hep_decay_ledger_contact.py",
    "hqiv_hep_decay_chain.py",
    "hqiv_hep_multichannel_expansion.py",
    "hqiv_hep_patch_species.py",
    "hqiv_hep_decay_certificates.py",
    "hqiv_hep_production_readout.py",
    "hqiv_hep_decay_sigma.py",
    "hqiv_hep_decay_benchmark.py",
    "hqiv_spine_gap_closure_terms.py",
    "hqiv_spine_discharge_weight.py",
    "hqiv_spine_discharge_export.py",
    "hqiv_hep_readout_pipeline.py",
    "export_hep_branching_table.py",
    "export_electroweak_mass_table.py",
    "export_excited_mass_table.py",
    "hqiv_hep_anomaly_discharge.py",
    "hqiv_electroweak_mass_observation.py",
    "hqiv_electroweak_mass_benchmark.py",
    "hqiv_decay_calculator.py",
    "hqiv_strong_sector_collider_discharge.py",
    "hqiv_hep_collider_refinements.py",
    "test_hqiv_hep_decay_readout.py",
    "test_hqiv_hep_valence_isospin.py",
    "test_export_excited_mass_discharge.py",
    "test_hqiv_hep_decay_chain.py",
    "test_hqiv_hep_multichannel_expansion.py",
    "test_hqiv_hep_patch_species.py",
    "test_hqiv_hep_decay_benchmark.py",
    "hqiv_property_channels.py",
    "hqiv_property_spanning.py",
    "test_hqiv_property_channels.py",
    "test_hqiv_property_spanning.py",
    "test_hqiv_hep_readout_pipeline.py",
    "test_hqiv_decay_calculator.py",
    "test_hqiv_strong_sector_collider_discharge.py",
    "test_hqiv_hep_collider_refinements.py",
    "test_hqiv_electroweak_mass_observation.py",
    "test_hqiv_hep_smoke.py",
]

DATA_MIRROR = [
    "hep_decay_observations.json",
    "hep_decay_benchmark.json",
    "decay_chain_readout.json",
    "spine_gap_closure_terms.json",
    "spine_discharge_law.json",
    "hep_readout_pipeline_manifest.json",
    "hep_readout_pipeline_demo.json",
    "hadron_published_masses.json",
    "hadron-catalog.js",
    "hqiv_witnesses.json",
    "strong_sector_collider_observations.json",
    "strong_sector_collider_discharge.json",
    "hep_collider_refinement_observations.json",
    "hep_collider_refinement_witness.json",
    "electroweak_mass_observations.json",
    "electroweak_mass_benchmark.json",
    "electroweak_mass_witness_certificate.json",
    "excited_mass_comparison.json",
    "excited_mass_panel_audit.csv",
    "hep_anomaly_discharge.json",
    "earth_outside_closure.json",
    "accelerator_outside_dressing.json",
    "outside_curvature_calculator_example.json",
]

EXTRA_MIRROR = [
    "hqiv_lean_physics_primitives.py",
    "hqiv_excited_states.py",
    "hqiv_tuft_hadron_s7_confinement.py",
]


def module_to_script(name: str) -> str | None:
    if name.startswith("hqiv_") or name.startswith("test_hqiv_") or name == "export_hep_branching_table":
        return f"{name}.py"
    candidate = SCRIPTS_ROOT / f"{name}.py"
    if candidate.is_file():
        return f"{name}.py"
    return None


def imports_in(path: Path) -> list[str]:
    tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    out: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            out.extend(alias.name.split(".")[0] for alias in node.names)
        elif isinstance(node, ast.ImportFrom) and node.module:
            out.append(node.module.split(".")[0])
    return out


def script_closure() -> list[str]:
    seen: set[str] = set()
    queue: deque[str] = deque(ENTRY_SCRIPTS + EXTRA_MIRROR)
    while queue:
        rel = queue.popleft()
        if rel in seen:
            continue
        src = SCRIPTS_ROOT / rel
        if not src.is_file():
            continue
        seen.add(rel)
        for imp in imports_in(src):
            dep = module_to_script(imp)
            if dep:
                queue.append(dep)
    return sorted(seen)


def _readme_text() -> str:
    n = len(script_closure())
    return f"""# HEP decay readout reproducers

**{n} Python modules** (stdlib only — no ``pip install``). Imports are **local**
``hqiv_*.py`` files in this folder, closed by import tracing from
``hqiv_hep_readout_pipeline.py``.

## Quick start

```bash
cd scripts   # this directory (or unzip scripts.zip here)
export PYTHONPATH=.

# Regenerate all paper numerics + generated/*.tex (needs full HQIV-LEAN tree for TeX paths)
python3 hqiv_hep_readout_pipeline.py paper --strict

# Or explore one facility / parent
python3 hqiv_hep_readout_pipeline.py run --facility SPS_p_beam_400GeV --parent B_plus
```

## What is reproduced

| Output | Role |
|--------|------|
| ``data/hep_decay_benchmark.json`` | 81 structural passes + 567 readout rows |
| ``data/spine_discharge_law.json`` | Unified spine product registry |
| ``../generated/*.tex`` | Paper tables (branching, EW mass) |
| ``data/hep_readout_pipeline_manifest.json`` | Step log |

**Comparison-only** inputs (never fed into predictions): ``data/hep_decay_observations.json``,
``data/hadron_published_masses.json``.

**Catalog:** ``data/hadron-catalog.js`` (hadron valence content for mass readout).

## PDF

Numerics are reproducible from this folder inside the HQIV-LEAN repository:

```bash
cd ../..   # repository root (contains lakefile.toml)
latexmk -pdf papers/hep_decay_readout/hqiv_hep_decay_readout_from_multichannel.tex
```

Lean certificates: ``lake build HQIVPhysics`` (optional for Python numerics).

## Verify

Fast smoke test (< 30 s, frozen benchmark contract):

```bash
PYTHONPATH=. python3 -m unittest test_hqiv_hep_smoke -q
```

Full regression suite:

```bash
PYTHONPATH=. python3 -m unittest discover -s . -p 'test_hqiv_hep*.py' -q
```

See ``REPRODUCIBILITY.md`` for the one-command paper reproduction.
"""


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def archive_path(path: Path, root: Path) -> bool:
    rel = path.relative_to(root)
    return "__pycache__" not in rel.parts and not rel.name.endswith(".pyc")


def write_manifest(root: Path) -> None:
    lines: list[str] = []
    for path in sorted(root.rglob("*")):
        if not path.is_file() or not archive_path(path, root):
            continue
        rel = path.relative_to(root).as_posix()
        lines.append(f"{sha256_file(path)}  {rel}")
    (root / "MANIFEST.sha256").write_text("\n".join(lines) + "\n", encoding="utf-8")


def build_zip() -> None:
    if ZIP_PATH.exists():
        ZIP_PATH.unlink()
    with zipfile.ZipFile(ZIP_PATH, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        for path in sorted(DEST.rglob("*")):
            if path.is_file() and archive_path(path, DEST):
                archive.write(path, path.relative_to(DEST.parent).as_posix())


def main() -> None:
    if DEST.exists():
        shutil.rmtree(DEST)
    os.makedirs(DEST, exist_ok=True)

    for rel in script_closure():
        shutil.copy2(SCRIPTS_ROOT / rel, DEST / rel)

    if (REPO / "pyproject.toml").is_file():
        shutil.copy2(REPO / "pyproject.toml", DEST / "pyproject.toml")

    data_dest = DEST / "data"
    data_dest.mkdir(exist_ok=True)
    PAPER_DATA.mkdir(parents=True, exist_ok=True)
    for name in DATA_MIRROR:
        src = REPO / "data" / name
        if src.is_file():
            shutil.copy2(src, data_dest / name)
            shutil.copy2(src, PAPER_DATA / name)

    catalog_src = REPO / "web" / "hqiv-mass-spectrum-calculator" / "hadron-catalog.js"
    if catalog_src.is_file() and not (data_dest / "hadron-catalog.js").is_file():
        shutil.copy2(catalog_src, data_dest / "hadron-catalog.js")
        shutil.copy2(catalog_src, REPO / "data" / "hadron-catalog.js")
        shutil.copy2(catalog_src, PAPER_DATA / "hadron-catalog.js")

    readme = DEST / "README.md"
    readme.write_text(_readme_text(), encoding="utf-8")

    repro_src = REPO / "papers" / "hep_decay_readout" / "REPRODUCIBILITY.md"
    if repro_src.is_file():
        shutil.copy2(repro_src, DEST / "REPRODUCIBILITY.md")

    write_manifest(DEST)
    build_zip()
    print(f"created {ZIP_PATH} ({ZIP_PATH.stat().st_size} bytes)")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Refresh papers/gluon_curvature_artifact/scripts/ and scripts.zip for Zenodo.

Minimal self-contained bundle for the gluon curvature discharge witnesses only.

Usage (from repository root):
  python3 scripts/bundle_gluon_curvature_scripts.py
"""
from __future__ import annotations

import hashlib
import os
import shutil
import zipfile
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
SCRIPTS_ROOT = REPO / "scripts"
DEST = REPO / "papers" / "gluon_curvature_artifact" / "scripts"
PAPER_DATA = REPO / "papers" / "gluon_curvature_artifact" / "data"
ZIP_PATH = REPO / "papers" / "gluon_curvature_artifact" / "scripts.zip"

# Curated closure for this paper only (no transitive hqiv-lab dump).
BUNDLE_SCRIPTS = [
    "hqiv_repo_paths.py",
    "cubic_phase_relax_probe.py",
    "hqiv_excited_states.py",
    "hqiv_tuft_hadron_s7_confinement.py",
    "hqiv_strong_sector_collider_discharge.py",
    "hqiv_hep_collider_refinements.py",
    "test_hqiv_strong_sector_collider_discharge.py",
    "test_hqiv_hep_collider_refinements.py",
]

DATA_MIRROR = [
    "strong_sector_collider_observations.json",
    "strong_sector_collider_discharge.json",
    "hep_collider_refinement_observations.json",
    "hep_collider_refinement_witness.json",
]


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
    manifest = root / "MANIFEST.sha256"
    manifest.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_readme() -> None:
    readme = DEST / "README.md"
    readme.write_text(
        """# Reproducer scripts — gluon curvature artifact

Minimal import closure for `papers/gluon_curvature_artifact/` (Zenodo bundle).
Zenodo record: [`10.5281/zenodo.20724572`](https://doi.org/10.5281/zenodo.20724572).
Comparison JSON lives in `data/` beside these scripts (never HQIV inputs).

## Entry scripts

| Script | Role |
| --- | --- |
| `hqiv_strong_sector_collider_discharge.py` | Leading-order collider discharge (9 cases) |
| `hqiv_hep_collider_refinements.py` | HEP refinements: shower MC, thrust bins, ggH pT, QGP, PDF x |
| `test_hqiv_strong_sector_collider_discharge.py` | Unit tests for discharge witness |
| `test_hqiv_hep_collider_refinements.py` | Unit tests for refinement witness |

## Quick start (standalone, from extracted `scripts/`)

```bash
cd scripts
PYTHONPATH=. python3 hqiv_strong_sector_collider_discharge.py --strict
PYTHONPATH=. python3 hqiv_hep_collider_refinements.py --strict
python3 test_hqiv_strong_sector_collider_discharge.py
python3 test_hqiv_hep_collider_refinements.py
```

## Quick start (HQIV-LEAN repository root)

```bash
PYTHONPATH=scripts python3 scripts/hqiv_strong_sector_collider_discharge.py --strict
PYTHONPATH=scripts python3 scripts/hqiv_hep_collider_refinements.py --strict
```

Lean (full checkout only): `lake build paper_gluon_curvature`

Dependencies: Python 3.10+ stdlib only.
""",
        encoding="utf-8",
    )


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

    missing = [rel for rel in BUNDLE_SCRIPTS if not (SCRIPTS_ROOT / rel).is_file()]
    if missing:
        raise SystemExit(f"missing bundle scripts: {missing}")

    for rel in BUNDLE_SCRIPTS:
        shutil.copy2(SCRIPTS_ROOT / rel, DEST / rel)

    data_dest = DEST / "data"
    data_dest.mkdir(exist_ok=True)
    PAPER_DATA.mkdir(parents=True, exist_ok=True)
    for name in DATA_MIRROR:
        src = REPO / "data" / name
        if not src.is_file():
            raise SystemExit(f"missing data file: {src}")
        shutil.copy2(src, data_dest / name)
        shutil.copy2(src, PAPER_DATA / name)

    write_readme()
    write_manifest(DEST)
    build_zip()
    n_scripts = len(list(DEST.glob("*.py")))
    n_data = len(list(data_dest.glob("*.json")))
    zip_kb = ZIP_PATH.stat().st_size / 1024
    print(f"copied {n_scripts} scripts -> {DEST}")
    print(f"mirrored {n_data} data/*.json -> {PAPER_DATA}")
    print(f"created {ZIP_PATH} ({zip_kb:.1f} KiB)")


if __name__ == "__main__":
    main()

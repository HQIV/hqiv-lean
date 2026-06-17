#!/usr/bin/env python3
"""Refresh papers/gluon_curvature_artifact/scripts/ and scripts.zip for Zenodo.

Usage (from repository root):
  python3 scripts/bundle_gluon_curvature_scripts.py
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
DEST = REPO / "papers" / "gluon_curvature_artifact" / "scripts"
PAPER_DATA = REPO / "papers" / "gluon_curvature_artifact" / "data"
ZIP_PATH = REPO / "papers" / "gluon_curvature_artifact" / "scripts.zip"

ENTRY_SCRIPTS = [
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

EXTRA_MIRROR = [
    "hqiv_lean_physics_primitives.py",
    "hqiv_excited_states.py",
    "hqiv_tuft_hadron_s7_confinement.py",
    "hqiv_hep_decay_readout.py",
]


def module_to_script(name: str) -> str | None:
    if name.startswith("hqiv_") or name.startswith("test_hqiv_"):
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

Self-contained import closure for `papers/gluon_curvature_artifact/`.
Bundled in `papers/gluon_curvature_artifact/scripts.zip` for Zenodo.

## Entry scripts

| Script | Role |
| --- | --- |
| `hqiv_strong_sector_collider_discharge.py` | Leading-order collider discharge (9 cases) |
| `hqiv_hep_collider_refinements.py` | HEP refinements: shower MC, thrust bins, ggH pT, QGP, PDF x |
| `test_hqiv_strong_sector_collider_discharge.py` | Unit tests for discharge witness |
| `test_hqiv_hep_collider_refinements.py` | Unit tests for refinement witness |

## Quick start

```bash
PYTHONPATH=scripts python3 scripts/hqiv_strong_sector_collider_discharge.py --strict
PYTHONPATH=scripts python3 scripts/hqiv_hep_collider_refinements.py --strict
```

Lean: `lake build paper_gluon_curvature`

Comparison data live in `data/*.json` (never HQIV inputs).
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

    missing = [rel for rel in ENTRY_SCRIPTS if not (SCRIPTS_ROOT / rel).is_file()]
    if missing:
        raise SystemExit(f"missing entry scripts: {missing}")

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

    write_readme()
    write_manifest(DEST)
    build_zip()
    n_scripts = len(list(DEST.glob("*.py")))
    n_data = len(list(data_dest.glob("*.json")))
    print(f"copied {n_scripts} scripts -> {DEST}")
    print(f"mirrored {n_data} data/*.json -> {PAPER_DATA}")
    print(f"created {ZIP_PATH} ({ZIP_PATH.stat().st_size} bytes)")


if __name__ == "__main__":
    main()

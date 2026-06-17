#!/usr/bin/env python3
"""Refresh papers/bbn/scripts/ and scripts.zip for Zenodo upload.

Copies every paper-cited entry script plus its ``hqiv_*`` import closure from
``scripts/``, mirrors ``data/*.json`` witnesses, writes ``MANIFEST.sha256``,
and rebuilds ``papers/bbn/scripts.zip``.

Usage (from repository root):
  python3 scripts/bundle_bbn_scripts.py
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
DEST = REPO / "papers" / "bbn" / "scripts"
PAPER_DATA = REPO / "papers" / "bbn" / "data"
ZIP_PATH = REPO / "papers" / "bbn" / "scripts.zip"

ENTRY_SCRIPTS = [
    "hqiv_bbn_integrator.py",
    "hqiv_bbn_paper_tables.py",
    "hqiv_bbn_abundances.py",
    "hqiv_bbn_epoch_network.py",
    "hqiv_bbn_condition_decay.py",
    "hqiv_dynamic_bulk_bbn.py",
    "hqiv_integrator_lean_audit.py",
    "test_hqiv_bbn_integrator.py",
    "test_hqiv_dynamic_c2_bbn.py",
    "test_hqiv_bbn_epoch_network.py",
]

DATA_MIRROR = [
    "bbn_integrator.json",
    "bbn_paper_tables.json",
    "bbn_witnesses.json",
    "bbn_witnesses_dynamic.json",
    "dynamic_bulk_bbn_v2.json",
    "integrator_lean_audit.json",
    "hqiv_witnesses.json",
    "curvature_binding_program.json",
]

EXTRA_MIRROR = [
    "hqiv_lean_physics_primitives.py",
    "hqiv_scale_witness.py",
    "hqiv_excited_states.py",
    "hqiv_nuclear_outside_temperature_dynamics.py",
    "hqiv_curvature_binding_core.py",
    "hqiv_nuclear_curvature_binding.py",
    "hqiv_nuclear_caustic_binding.py",
    "hqiv_nuclear_inside_outside_binding.py",
    "hqiv_post_alpha_binding_program.py",
    "hqiv_post_alpha_sphere_touching.py",
    "hqiv_shell_shape_geometry.py",
    "lih_derivation_scan.py",
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

    shutil.copy2(REPO / "pyproject.toml", DEST / "pyproject.toml")

    data_dest = DEST / "data"
    data_dest.mkdir(exist_ok=True)
    PAPER_DATA.mkdir(parents=True, exist_ok=True)
    for name in DATA_MIRROR:
        src = REPO / "data" / name
        if src.is_file():
            shutil.copy2(src, data_dest / name)
            shutil.copy2(src, PAPER_DATA / name)

    write_manifest(DEST)
    build_zip()
    n_scripts = len(list(DEST.glob("hqiv_*.py"))) + len(list(DEST.glob("test_hqiv_*.py")))
    n_data = len(list(data_dest.glob("*.json")))
    print(f"copied {n_scripts} scripts + pyproject.toml + {n_data} data/*.json -> {DEST}")
    print(f"mirrored {n_data} data/*.json -> {PAPER_DATA}")
    print(f"wrote {DEST / 'MANIFEST.sha256'} ({sum(1 for _ in (DEST / 'MANIFEST.sha256').open())} lines)")
    print(f"created {ZIP_PATH} ({ZIP_PATH.stat().st_size} bytes)")


if __name__ == "__main__":
    main()

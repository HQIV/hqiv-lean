#!/usr/bin/env python3
"""Refresh papers/nucleon_binding/scripts/ and scripts.zip for Zenodo upload.

Copies every paper-cited entry script plus its ``hqiv_*`` import closure from
``scripts/``, mirrors ``hqiv_lab/`` and ``pyproject.toml``, writes
``MANIFEST.sha256``, and rebuilds ``papers/nucleon_binding/scripts.zip``.

Usage (from repository root):
  python3 scripts/bundle_nucleon_binding_scripts.py
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
DEST = REPO / "papers" / "nucleon_binding" / "scripts"
ZIP_PATH = REPO / "papers" / "nucleon_binding" / "scripts.zip"

ENTRY_SCRIPTS = [
    "hqiv_isotope_stability_halflife.py",
    "hqiv_dynamic_beta_isotope.py",
    "hqiv_isotope_pdg_benchmark.py",
    "hqiv_nuclear_outside_temperature_dynamics.py",
    "hqiv_bond_state_network.py",
    "hqiv_nuclear_caustic_binding.py",
    "hqiv_nuclear_inside_outside_binding.py",
    "hqiv_dynamic_nucleon_pn.py",
    "hqiv_phase_geometry_density.py",
    "hqiv_thermodynamic_phase_from_tp.py",
    "hqiv_homogeneous_curvature_feedback.py",
    "hqiv_phase_material_response.py",
    "test_hqiv_phase_material_response.py",
    "hqiv_curvature_contact_network.py",
    "hqiv_weak_fano_hopf_bridge.py",
]

EXTRA_MIRROR = [
    "hqiv_lean_physics_primitives.py",
    "hqiv_scale_witness.py",
    "hqiv_nuclear_curvature_binding.py",
    "hqiv_mass_calculator_core.py",
    "hqiv_continuous_shell_mass.py",
    "hqiv_excited_states.py",
    "hqiv_coupling_linear_system.py",
    "hqiv_shell_shape_geometry.py",
    "hqiv_curvature_bond_state.py",
    "hqiv_s2_binding_geometry.py",
    "hqiv_dynamic_binding_chart.py",
]


def module_to_script(name: str) -> str | None:
    if name.startswith("hqiv_") or name.startswith("test_hqiv_"):
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


def copy_tree(src: Path, dest: Path) -> None:
    if dest.exists():
        shutil.rmtree(dest)
    shutil.copytree(src, dest)


def write_manifest(root: Path) -> None:
    lines: list[str] = []
    for path in sorted(root.rglob("*")):
        if not path.is_file():
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
            if path.is_file():
                archive.write(path, path.relative_to(DEST.parent).as_posix())


def main() -> None:
    os.makedirs(DEST, exist_ok=True)
    for rel in script_closure():
        shutil.copy2(SCRIPTS_ROOT / rel, DEST / rel)

    copy_tree(REPO / "hqiv_lab", DEST / "hqiv_lab")
    shutil.copy2(REPO / "pyproject.toml", DEST / "pyproject.toml")

    readme_src = DEST / "README.md"
    if readme_src.is_file():
        pass
    write_manifest(DEST)
    build_zip()
    n_scripts = len(list(DEST.glob("hqiv_*.py"))) + len(list(DEST.glob("test_hqiv_*.py")))
    print(f"copied {n_scripts} scripts + hqiv_lab/ + pyproject.toml -> {DEST}")
    print(f"wrote {DEST / 'MANIFEST.sha256'} ({sum(1 for _ in (DEST / 'MANIFEST.sha256').open())} lines)")
    print(f"created {ZIP_PATH} ({ZIP_PATH.stat().st_size} bytes)")


if __name__ == "__main__":
    main()

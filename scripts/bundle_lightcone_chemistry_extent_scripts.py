#!/usr/bin/env python3
"""Refresh the reproducibility bundle for the light-cone chemistry extent paper.

The paper is a discrete electronic-structure substrate paper, so the bundle is
deliberately a witness and comparison bundle rather than a source of derivation
inputs.  It mirrors the Python scripts that reproduce the chemistry /
material-response / discrete electronic-stack readouts cited in the paper,
their local ``hqiv_*`` dependency closure, the ``hqiv_lab`` package, selected frozen
JSON witnesses, and a SHA-256 manifest.

Usage (from repository root):
  python3 scripts/bundle_lightcone_chemistry_extent_scripts.py
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
PAPER = REPO / "papers" / "lightcone_chemistry_extent"
DEST = PAPER / "scripts"
ZIP_PATH = PAPER / "scripts.zip"


ENTRY_SCRIPTS = [
    # Spine / formal-chemistry readouts.
    "hqiv_spine_chemistry.py",
    "hqiv_derived_chemistry.py",
    "hqiv_chemistry_binding_routes.py",
    "hqiv_chemistry_tuft_dynamics.py",
    "hqiv_chemistry_tuft_dynamics_witness.py",
    "hqiv_chemistry_coupled_readout.py",
    # Bonding / spectroscopy / dynamic binding.
    "hqiv_bond_state_network.py",
    "hqiv_curvature_bond_state.py",
    "hqiv_dynamic_binding_chart.py",
    "hqiv_molecular_spectroscopy.py",
    "test_hqiv_molecular_spectroscopy.py",
    "hqiv_period_n_outside_contact_suite.py",
    "test_hqiv_period_n_outside_contact_suite.py",
    "hqiv_nested_wf_bond_geometry.py",
    "hqiv_spectral_scale_anchor_feedback.py",
    "hqiv_graphene_mass_pin.py",
    "hqiv_chemistry_panel_accuracy.py",
    "reproduce_lightcone_chemistry_extent.py",
    "hqiv_two_way_feedback_dynamics.py",
    "hqiv_outside_contact_reduced_deltas.py",
    # Phase geometry / material response.
    "hqiv_phase_geometry_density.py",
    "hqiv_phase_material_response.py",
    "test_hqiv_phase_material_response.py",
    "hqiv_phase_diagram.py",
    "test_hqiv_phase_diagram.py",
    "hqiv_thermodynamic_phase_from_tp.py",
    "hqiv_condensed_phase_audit.py",
    "test_hqiv_condensed_phase_audit.py",
    "hqiv_chemistry_residual_correlation_audit.py",
    "test_hqiv_chemistry_residual_correlation_audit.py",
    "hqiv_allotrope_phase_cooling_audit.py",
    "test_hqiv_allotrope_phase_cooling.py",
    # Contact-network / ionic / metallic / protein-adjacent witnesses.
    "hqiv_curvature_contact_network.py",
    "hqiv_ionic_bond_network.py",
    "hqiv_metallic_bond_network.py",
    "hqiv_crystal_contact_geometry.py",
    "hqiv_crystal_fracture_witness.py",
    "hqiv_crystal_ethics_audit.py",
    "test_hqiv_crystal_contact_geometry.py",
    "test_hqiv_crystal_fracture_witness.py",
    "hqiv_miniprotein_fold_audit.py",
    "test_hqiv_miniprotein_fold.py",
    "test_hqiv_miniprotein_lean_parity.py",
    # Second-order / system-matrix / generator-dependent audits (Lean appendix targets).
    "hqiv_second_order_effect_audit.py",
    "hqiv_system_matrix_functor_audit.py",
    "hqiv_generator_dependent_coupling_audit.py",
    "hqiv_selection_weights.py",
    "hqiv_plane_local_binding.py",
    # Discrete electronic stack (bands / SCF / Fock / KS / AO / core XPS).
    "hqiv_discrete_bz_band_readout.py",
    "test_hqiv_discrete_bz_band_readout.py",
    "hqiv_multi_orbital_bz_readout.py",
    "test_hqiv_multi_orbital_bz_readout.py",
    "hqiv_discrete_scf_readout.py",
    "test_hqiv_discrete_scf_readout.py",
    "hqiv_discrete_fock_readout.py",
    "test_hqiv_discrete_fock_readout.py",
    "hqiv_discrete_ks_readout.py",
    "test_hqiv_discrete_ks_readout.py",
    "hqiv_discrete_ao_integrals_readout.py",
    "test_hqiv_discrete_ao_integrals_readout.py",
    "hqiv_discrete_core_spectroscopy_readout.py",
    "test_hqiv_discrete_core_spectroscopy_readout.py",
    "hqiv_discrete_saddle_defect_readout.py",
    "test_hqiv_discrete_saddle_defect_readout.py",
]


EXTRA_MIRROR = [
    "hqiv_lean_physics_primitives.py",
    "hqiv_scale_witness.py",
    "hqiv_curvature_binding_core.py",
    "hqiv_mass_calculator_core.py",
    "hqiv_shell_shape_geometry.py",
    "hqiv_s2_binding_geometry.py",
    "hqiv_phase_curvature_response.py",
    "hqiv_homogeneous_curvature_feedback.py",
]


DATA_MIRROR = [
    "quantum_chem_witnesses.json",
    "molecular_spectroscopy_witnesses.json",
    "period_n_outside_contact_suite.json",
    "hqiv_lab_witnesses.json",
    "chemistry_residual_correlation_audit.json",
    "phase_diagram_audit.json",
    "allotrope_phase_cooling_audit.json",
    "dynamic_binding_chart.json",
    "curvature_contact_network_rules.json",
    "nested_wf_geometry.json",
    "lih_dynamic_binding.json",
    "molecule_suite_audit.json",
    "crystal_contact_witnesses.json",
    "crystal_fracture_witnesses.json",
    "crystal_ethics_audit.json",
    "protein_folder_audit.json",
    "miniprotein_fold_audit.json",
    "miniprotein_witnesses.json",
    "second_order_effect_audit.json",
    "system_matrix_functor_audit.json",
    "generator_dependent_coupling_audit.json",
    "spectral_scale_anchor_feedback.json",
    "graphene_mass_pin_witnesses.json",
    "chemistry_panel_accuracy.json",
    "discrete_bz_band_audit.json",
    "multi_orbital_bz_audit.json",
    "discrete_scf_audit.json",
    "discrete_fock_audit.json",
    "discrete_ks_audit.json",
    "discrete_ao_integrals_audit.json",
    "discrete_core_spectroscopy_audit.json",
    "discrete_saddle_defect_audit.json",
]


README = """# Reproducer scripts -- Discrete electronic structure from the HQIV light cone

Self-contained bundle for the paper
`hqiv_lightcone_derivations_into_chemistry.tex`
(*Discrete Electronic Structure from the HQIV Light Cone*).

These scripts reproduce the Python witnesses and comparison readouts for the
discrete electronic-structure / material-response stack.  They are not derivation
inputs: NIST, CRC, GMTKN, W4, water, and related laboratory data remain
comparison quarantine.

Regenerate from the repository root:

```bash
python3 scripts/bundle_lightcone_chemistry_extent_scripts.py
```

This refreshes this directory, rewrites `MANIFEST.sha256`, and rebuilds
`../scripts.zip`.

## Representative entry scripts

| Script | Purpose |
| --- | --- |
| `hqiv_spine_chemistry.py` | Spine chemistry readouts and theorem-adjacent constants. |
| `hqiv_derived_chemistry.py` | Derived molecule/allotrope witnesses. |
| `hqiv_bond_state_network.py` | Closed-network/separated-surplus bond bookkeeping. |
| `hqiv_dynamic_binding_chart.py` | Dynamic binding chart readouts. |
| `hqiv_molecular_spectroscopy.py` | Diatomic rovibrational witness outputs. |
| `hqiv_chemistry_panel_accuracy.py` | **Public accuracy panel**: final spectral + carbon errors vs NIST/CRC quarantine; accepts optional molecule names beyond the paper tables. |
| `reproduce_lightcone_chemistry_extent.py` | **One-command check**: regenerate key payloads, compare paper headlines, run paper-scoped unit tests (`--write`, `--bundle`). |
| `hqiv_spectral_scale_anchor_feedback.py` | Shell-equation spectral scale projection used by the accuracy panel. |
| `hqiv_graphene_mass_pin.py` | Carbon network packing (graphene/diamond) used by the accuracy panel. |
| `hqiv_phase_geometry_density.py` | Unit-cell density and curvature-density readouts. |
| `hqiv_phase_material_response.py` | Optical, thermal, viscosity, and material-response slots. |
| `hqiv_phase_diagram.py` | Phase-diagram mixture witnesses. |
| `hqiv_condensed_phase_audit.py` | Condensed-phase comparison audit. |
| `hqiv_chemistry_residual_correlation_audit.py` | Residual correlations against existing HQIV-derived features. |
| `hqiv_chemistry_coupled_readout.py` | Lean-mirrored finite dynamics helper: relaxation, branches, cages, activation, propagation, geometry-binding. |
| `hqiv_curvature_contact_network.py` | Contact-network rules for chemistry/bulk phases. |
| `hqiv_ionic_bond_network.py` / `hqiv_metallic_bond_network.py` | Lattice contact witnesses. |
| `hqiv_crystal_contact_geometry.py` | Ionic, metallic, and covalent-network crystal contact witnesses. |
| `hqiv_crystal_fracture_witness.py` | Contact-derived stiffness, Griffith-scale, cleavage, and ductile-carrier witnesses. |
| `hqiv_crystal_ethics_audit.py` | Proof/readout ethics audit for crystal modules and A(Z) bookkeeping. |
| `hqiv_miniprotein_fold_audit.py` | Protein-adjacent structural witness panel. |
| `hqiv_second_order_effect_audit.py` | Second-order effect slot witnesses. |
| `hqiv_system_matrix_functor_audit.py` | System-matrix functor witnesses. |
| `hqiv_generator_dependent_coupling_audit.py` | Generator-dependent / plane-local coupling witnesses. |
| `hqiv_selection_weights.py` / `hqiv_plane_local_binding.py` | Selection weights and plane-local binding helpers. |
| `hqiv_discrete_bz_band_readout.py` | Two-band discrete BZ band audit. |
| `hqiv_multi_orbital_bz_readout.py` | Multi-orbital s/pσ/pπ EH band audit. |
| `hqiv_discrete_scf_readout.py` | Discrete SCF charge-dress fixed-point audit. |
| `hqiv_discrete_fock_readout.py` | Discrete Fock matrix audit (dress = SCF). |
| `hqiv_discrete_ks_readout.py` | Discrete local-XC KS matrix audit. |
| `hqiv_discrete_ao_integrals_readout.py` | Discrete EH AO integral audit. |
| `hqiv_discrete_core_spectroscopy_readout.py` | Discrete core XPS / chem-shift audit. |

Additional `hqiv_*.py` files are dependency modules discovered from the import
closure or mirrored as shared primitives.

## Quick start

```bash
pip install -e .
# One-command paper check (headlines + paper-scoped tests):
PYTHONPATH=. python3 reproduce_lightcone_chemistry_extent.py
python3 hqiv_chemistry_panel_accuracy.py
python3 hqiv_chemistry_panel_accuracy.py HF CO N2 Cl2
python3 hqiv_chemistry_panel_accuracy.py --list
python3 hqiv_phase_geometry_density.py
python3 hqiv_phase_material_response.py
python3 hqiv_molecular_spectroscopy.py
python3 hqiv_phase_diagram.py
python3 hqiv_crystal_contact_geometry.py
python3 hqiv_crystal_fracture_witness.py
python3 hqiv_crystal_ethics_audit.py
python3 hqiv_discrete_scf_readout.py
python3 hqiv_discrete_ks_readout.py
python3 hqiv_discrete_ao_integrals_readout.py
python3 hqiv_discrete_core_spectroscopy_readout.py
python3 -m unittest test_hqiv_phase_material_response.py test_hqiv_phase_diagram.py test_hqiv_crystal_contact_geometry.py test_hqiv_crystal_fracture_witness.py test_hqiv_discrete_scf_readout.py test_hqiv_discrete_ks_readout.py
```

`hqiv_chemistry_panel_accuracy.py` is the paper's public accuracy entry point:
it reports final predictions against quarantined NIST/CRC comparisons on the
spectral and carbon panels, and accepts any suite molecule name so readers can
test cases not tabulated in the manuscript.

When running from the full repository, use `scripts/` paths and write JSON under
`data/` as the individual scripts document.

## Manifest

`MANIFEST.sha256` gives a SHA-256 checksum for every bundled file.
"""


def module_to_script(name: str) -> str | None:
    if name.startswith("hqiv_") or name.startswith("test_hqiv_"):
        return f"{name}.py"
    candidate = SCRIPTS_ROOT / f"{name}.py"
    if candidate.is_file():
        return f"{name}.py"
    return None


def imports_in(path: Path) -> list[str]:
    try:
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    except SyntaxError:
        return []
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


def ignore_pycache(_dir: str, names: list[str]) -> set[str]:
    return {name for name in names if name == "__pycache__" or name.endswith(".pyc")}


def copy_tree(src: Path, dest: Path) -> None:
    if dest.exists():
        shutil.rmtree(dest)
    shutil.copytree(src, dest, ignore=ignore_pycache)


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
    DEST.mkdir(parents=True)

    copied_scripts = 0
    for rel in script_closure():
        src = SCRIPTS_ROOT / rel
        if src.is_file():
            shutil.copy2(src, DEST / rel)
            copied_scripts += 1

    copy_tree(REPO / "hqiv_lab", DEST / "hqiv_lab")
    shutil.copy2(REPO / "pyproject.toml", DEST / "pyproject.toml")
    (DEST / "README.md").write_text(README, encoding="utf-8")

    data_dest = DEST / "data"
    data_dest.mkdir(exist_ok=True)
    copied_data = 0
    for name in DATA_MIRROR:
        src = REPO / "data" / name
        if src.is_file():
            shutil.copy2(src, data_dest / name)
            copied_data += 1

    write_manifest(DEST)
    build_zip()
    manifest_lines = sum(1 for _ in (DEST / "MANIFEST.sha256").open(encoding="utf-8"))
    print(f"copied {copied_scripts} scripts + hqiv_lab/ + pyproject.toml + {copied_data} data/*.json -> {DEST}")
    print(f"wrote {DEST / 'MANIFEST.sha256'} ({manifest_lines} lines)")
    print(f"created {ZIP_PATH} ({ZIP_PATH.stat().st_size} bytes)")


if __name__ == "__main__":
    main()

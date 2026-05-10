#!/usr/bin/env python3
"""
Build publication inventories and a paper-reference bundle for HQIV_LEAN.

This script serves two related but distinct publication outputs:

1) `release/zenodo/*`: a compact Zenodo inventory/checksum set for publication-critical
   objects (manuscript sources/PDFs, build roots, symbolic certificates).
2) `release/paper_refs_bundle_2026-05-06/*`: a concrete mirror of the files that the
   rapidity/SO(8) paper family explicitly cites as being included in the reproducibility
   archive. This bundle must match manuscript claims about included files.

The paper-reference bundle is intentionally broader than the compact Zenodo inventory,
because the manuscripts currently claim that specific Lean modules and closure artifacts
are included alongside the paper sources and certificates.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
import shutil
import zipfile


@dataclass(frozen=True)
class PublicationFile:
    path: str
    category: str
    required: bool = True


REPO_ROOT = Path(__file__).resolve().parents[2]
OUT_DIR = REPO_ROOT / "release" / "zenodo"
PAPER_BUNDLE_NAME = "paper_refs_bundle_2026-05-06"
PAPER_BUNDLE_DIR = REPO_ROOT / "release" / PAPER_BUNDLE_NAME
PAPER_BUNDLE_ZIP = REPO_ROOT / "release" / f"{PAPER_BUNDLE_NAME}.zip"

PUBLICATION_FILES = [
    # Manuscript + appendix
    PublicationFile("papers/hqiv_rapidity_manifold_so8_closure.tex", "manuscript"),
    PublicationFile("papers/hqiv_rapidity_manifold_so8_closure.pdf", "manuscript", required=False),
    PublicationFile("papers/so8_closure_full_appendix.tex", "appendix"),
    PublicationFile("papers/so8_closure_full_appendix.pdf", "appendix", required=False),
    # Single Lean root for Appendix A (`lake build HQIVPaperClaims`); transitive deps live in-tree.
    PublicationFile("HQIVPaperClaims.lean", "lean-proof"),
    PublicationFile("lakefile.toml", "build-config"),
    PublicationFile("lean-toolchain", "build-config"),
    # Certificate generators + exact artifacts
    PublicationFile("scripts/generate_symbolic_lie_closure_certificate.py", "certificate-tool"),
    PublicationFile("scripts/generate_symbolic_so4_certificate.py", "certificate-tool"),
    PublicationFile("artifacts/so8_symbolic_certificate.json", "certificate"),
    PublicationFile("artifacts/so4_symbolic_certificate.json", "certificate"),
]


PAPER_BUNDLE_FILES = [
    # Paper sources and generated PDFs
    "papers/so8_closure_full_appendix.tex",
    "papers/hqiv_rapidity_manifold_so8_closure.tex",
    "papers/so8_closure_full_appendix.pdf",
    "papers/hqiv_rapidity_manifold_so8_closure.pdf",
    # Scripts and exact symbolic artifacts cited in the papers
    "scripts/generate_symbolic_lie_closure_certificate.py",
    "scripts/generate_symbolic_so4_certificate.py",
    "scripts/print_lie_bracket_closure.py",
    "artifacts/so8_symbolic_certificate.json",
    "artifacts/so4_symbolic_certificate.json",
    # Build roots and configuration cited by the paper
    "HQIVPaperClaims.lean",
    "HQIVSO8Closure.lean",
    "lakefile.toml",
    "lean-toolchain",
    # Lightweight Appendix A cone
    "Hqiv/Geometry/OctonionicLightCone.lean",
    "Hqiv/Geometry/SATRapidityManifold.lean",
    "Hqiv/Story/CausalRapidityForcing.lean",
    "Hqiv/SO8ClosureSymbolic.lean",
    # Full closure path explicitly cited in the papers
    "Hqiv/Generators.lean",
    "Hqiv/GeneratorsFromAxioms.lean",
    "Hqiv/OctonionLeftMultiplication.lean",
    "Hqiv/MatrixLieBracket.lean",
    "Hqiv/So8CoordMatrix.lean",
    "Hqiv/GeneratorsLieClosure.lean",
    "Hqiv/GeneratorsLieClosureData.lean",
    "Hqiv/SO8Closure.lean",
    "Hqiv/SO8ClosureInterface.lean",
    "Hqiv/Algebra/G2Embedding.lean",
    "Hqiv/Algebra/PhaseLiftDelta.lean",
    "Hqiv/Algebra/SO8ClosureAbstract.lean",
]
PAPER_BUNDLE_FILES.extend(f"Hqiv/GeneratorsLieClosureData{i}.lean" for i in range(28))
PAPER_BUNDLE_FILES.extend(f"Hqiv/LieBracketCell/Row{i}Summary.lean" for i in range(28))
for i in range(28):
    for j in range(28):
        PAPER_BUNDLE_FILES.append(f"Hqiv/LieBracketCell/R{i}C{j}.lean")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def build_inventory() -> dict:
    rows = []
    missing_required = []

    for entry in PUBLICATION_FILES:
        abs_path = REPO_ROOT / entry.path
        exists = abs_path.exists()
        row = {
            "path": entry.path,
            "category": entry.category,
            "required": entry.required,
            "exists": exists,
            "size_bytes": abs_path.stat().st_size if exists else None,
            "sha256": sha256(abs_path) if exists else None,
        }
        rows.append(row)
        if entry.required and not exists:
            missing_required.append(entry.path)

    category_counts = {}
    for row in rows:
        category_counts[row["category"]] = category_counts.get(row["category"], 0) + 1

    return {
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "repo_root": str(REPO_ROOT),
        "missing_required": missing_required,
        "category_counts": category_counts,
        "files": rows,
    }


def write_outputs(inventory: dict) -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    inv_path = OUT_DIR / "publication_inventory.json"
    inv_path.write_text(json.dumps(inventory, indent=2) + "\n", encoding="utf-8")

    checksums = OUT_DIR / "SHA256SUMS.txt"
    checksum_lines = []
    for row in inventory["files"]:
        if row["sha256"] is not None:
            checksum_lines.append(f'{row["sha256"]}  {row["path"]}')
    checksums.write_text("\n".join(checksum_lines) + "\n", encoding="utf-8")

    missing = OUT_DIR / "MISSING_REQUIRED.txt"
    if inventory["missing_required"]:
        missing.write_text("\n".join(inventory["missing_required"]) + "\n", encoding="utf-8")
    else:
        missing.write_text("none\n", encoding="utf-8")


def build_paper_bundle() -> dict:
    if PAPER_BUNDLE_DIR.exists():
        shutil.rmtree(PAPER_BUNDLE_DIR)
    PAPER_BUNDLE_DIR.mkdir(parents=True, exist_ok=True)

    included: list[str] = []
    missing: list[str] = []

    for rel in PAPER_BUNDLE_FILES:
        src = REPO_ROOT / rel
        if src.exists():
            dst = PAPER_BUNDLE_DIR / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src, dst)
            included.append(rel)
        else:
            missing.append(rel)

    manifest = {
        "source_repo": str(REPO_ROOT),
        "bundle_root": str(PAPER_BUNDLE_DIR.relative_to(REPO_ROOT)),
        "included_count": len(included),
        "missing_count": len(missing),
        "included": included,
        "missing": missing,
    }
    (PAPER_BUNDLE_DIR / "MANIFEST.json").write_text(
        json.dumps(manifest, indent=2) + "\n", encoding="utf-8"
    )
    (PAPER_BUNDLE_DIR / "README.txt").write_text(
        "Bundle of paper-referenced files for reproducibility.\n"
        f"Created: {datetime.now(timezone.utc).date().isoformat()}\n\n"
        f"Included files: {len(included)}\n"
        f"Missing files: {len(missing)}\n",
        encoding="utf-8",
    )

    if PAPER_BUNDLE_ZIP.exists():
        PAPER_BUNDLE_ZIP.unlink()
    with zipfile.ZipFile(PAPER_BUNDLE_ZIP, "w", compression=zipfile.ZIP_DEFLATED) as zf:
        for path in sorted(PAPER_BUNDLE_DIR.rglob("*")):
            if path.is_file():
                zf.write(path, path.relative_to(PAPER_BUNDLE_DIR.parent))

    return manifest


def main() -> int:
    inventory = build_inventory()
    write_outputs(inventory)
    manifest = build_paper_bundle()
    print(f'wrote {OUT_DIR / "publication_inventory.json"}')
    print(f'wrote {OUT_DIR / "SHA256SUMS.txt"}')
    print(f'required missing: {len(inventory["missing_required"])}')
    print(f'wrote {PAPER_BUNDLE_DIR / "MANIFEST.json"}')
    print(f'paper bundle missing: {manifest["missing_count"]}')
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

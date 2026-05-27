#!/usr/bin/env python3
"""
Build publication inventories, the paper-reference bundle, a bibliography audit,
and ``release/companion-code.zip`` (DOI companion archive) for HQIV_LEAN.

This script serves related publication outputs:

1) `release/zenodo/*`: compact Zenodo inventory/checksums, plus
   `paper_bibliography_audit.txt` from `scripts/audit_paper_bibliography.py`.
2) `release/paper_refs_bundle_2026-05-06/*` and `release/paper_refs_bundle_2026-05-06.zip`:
   reproducibility mirror for the submission centered on `papers/closure.tex`
   (long draft `papers/hqiv_rapidity_manifold_so8_closure.tex` is not copied here).
   The mirror omits `Hqiv/LieBracketCell/*.lean` sources (see generated README there):
   `lake build HQIVPaperClaims` (OctonionicLightCone + SO8ClosureSymbolic only; no SAT modules) is supported from the bundle; full `HQIVSO8Closure`
   requires a complete git checkout plus `scripts/build_hqiv_so8_closure_lowmem.sh`.
3) `release/companion-code.zip`: DOI companion archive (entire ``release/`` tree: Zenodo
   inventory, paper-refs bundle, inner ``paper_refs_bundle_*.zip``, audit log, etc.).
"""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
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
    # Submitted manuscript (rewrite) + appendix
    PublicationFile("papers/closure.tex", "manuscript"),
    PublicationFile("papers/closure.pdf", "manuscript", required=False),
    PublicationFile("papers/so8_closure_full_appendix.tex", "appendix"),
    PublicationFile("papers/so8_closure_full_appendix.pdf", "appendix", required=False),
    PublicationFile("papers/include/patch_theory_messaging.tex", "manuscript"),
    PublicationFile("papers/include/release_archive_macros.tex", "manuscript"),
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
    # Submitted rewrite + appendix (PDFs optional at copy time except below)
    "papers/closure.tex",
    "papers/so8_closure_full_appendix.tex",
    "papers/include/patch_theory_messaging.tex",
    "papers/include/release_archive_macros.tex",
    "papers/so8_closure_full_appendix.pdf",
    # Scripts and exact symbolic artifacts cited in the papers
    "scripts/generate_symbolic_lie_closure_certificate.py",
    "scripts/generate_symbolic_so4_certificate.py",
    "scripts/print_lie_bracket_closure.py",
    "scripts/build_hqiv_so8_closure_lowmem.sh",
    "artifacts/so8_symbolic_certificate.json",
    "artifacts/so4_symbolic_certificate.json",
    # Build roots and configuration cited by the paper
    "HQIVPaperClaims.lean",
    "lakefile.toml",
    "lean-toolchain",
    # `papers/closure.tex` Lean cone (no SAT / satisfiability modules)
    "Hqiv/Geometry/OctonionicLightCone.lean",
    "Hqiv/SO8ClosureSymbolic.lean",
    # Full closure path explicitly cited in the papers
    "Hqiv/Generators.lean",
    "Hqiv/GeneratorsFromAxioms.lean",
    "Hqiv/OctonionLeftMultiplication.lean",
    "Hqiv/MatrixLieBracket.lean",
    "Hqiv/So8CoordMatrix.lean",
    "Hqiv/GeneratorsLieClosureData.lean",
    "Hqiv/Algebra/G2Embedding.lean",
    "Hqiv/Algebra/PhaseLiftDelta.lean",
    "Hqiv/Algebra/SO8ClosureAbstract.lean",
]
PAPER_BUNDLE_FILES.extend(f"Hqiv/GeneratorsLieClosureData{i}.lean" for i in range(28))
# LieBracketCell (784× small norm_num proofs + 28 row aggregators) is NOT mirrored here:
# parallel Lake builds can exceed ~100GB RSS. Sources stay in the full git tree; see
# `write_lie_bracket_cell_readme` below and `scripts/build_hqiv_so8_closure_lowmem.sh`.

# Optional: include when present (build with pdflatex before running this script).
OPTIONAL_PAPER_BUNDLE_FILES = [
    "papers/closure.pdf",
]


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _is_blank_metadata_value(value) -> bool:
    if value is None:
        return True
    if isinstance(value, str) and not value.strip():
        return True
    return False


def zenodo_deposit_metadata_issues() -> list[str]:
    """
    Return human-readable issues that should block ``companion-code.zip`` /
    ``paper_refs_bundle_*.zip`` when Zenodo deposit metadata is incomplete.

    Empty list means metadata is non-blank for the checked deposit fields.
    """
    path = OUT_DIR / ".zenodo.json"
    if not path.exists():
        return ["release/zenodo/.zenodo.json is missing"]

    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        return [f"release/zenodo/.zenodo.json is not valid JSON ({exc})"]

    issues: list[str] = []
    for key in ("title", "description", "upload_type", "publication_type", "license"):
        if _is_blank_metadata_value(raw.get(key)):
            issues.append(f".zenodo.json field {key!r} is blank or missing")

    creators = raw.get("creators")
    if not isinstance(creators, list) or len(creators) == 0:
        issues.append(".zenodo.json creators is missing or empty")
    else:
        for idx, c in enumerate(creators):
            if not isinstance(c, dict):
                issues.append(f".zenodo.json creators[{idx}] is not an object")
                continue
            if _is_blank_metadata_value(c.get("name")):
                issues.append(f".zenodo.json creators[{idx}].name is blank")

    keywords = raw.get("keywords")
    if not isinstance(keywords, list) or len(keywords) == 0:
        issues.append(".zenodo.json keywords is missing or empty")

    return issues


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


def write_lie_bracket_cell_readme(bundle_dir: Path) -> None:
    """Explain why LieBracketCell sources are absent from the paper-refs mirror."""
    p = bundle_dir / "Hqiv" / "LieBracketCell" / "README.md"
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(
        "# LieBracketCell — sources not in this paper-reference mirror\n\n"
        "This bundle intentionally **does not** copy the 784 modules `R{i}C{j}.lean` nor "
        "the 28 `Row{k}Summary.lean` files under `Hqiv/LieBracketCell/`. Each cell proof "
        "unfolds real matrix literals and runs `norm_num` on 64 entrywise goals; with "
        "Lake’s default parallelism, total resident memory can exceed **100GB**.\n\n"
        "**From this mirror (supported):** `lake build HQIVPaperClaims` — manuscript "
        "symbolic interface; does not import LieBracketCell.\n\n"
        "**Full matrix Lie closure (`HQIVSO8Closure`):** use a **complete** checkout of "
        "the repository (all `Hqiv/LieBracketCell/*.lean` present) and run:\n\n"
        "```bash\n"
        "scripts/build_hqiv_so8_closure_lowmem.sh\n"
        "```\n\n"
        "That sets `LEAN_NUM_THREADS=1` and `lake build … -j 1` so jobs run sequentially.\n",
        encoding="utf-8",
    )


def build_paper_bundle(*, write_zips: bool = True) -> dict:
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

    for rel in OPTIONAL_PAPER_BUNDLE_FILES:
        src = REPO_ROOT / rel
        if src.exists():
            dst = PAPER_BUNDLE_DIR / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src, dst)
            included.append(rel)

    write_lie_bracket_cell_readme(PAPER_BUNDLE_DIR)

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
        "Submitted manuscript (Zenodo): papers/closure.tex\n"
        "Symbolic certificate appendix: papers/so8_closure_full_appendix.tex\n"
        "(Long draft papers/hqiv_rapidity_manifold_so8_closure.tex is not bundled; "
        "closure.tex is the standalone rewrite submitted for this record.)\n\n"
        "Zenodo companion (same DOI): companion-code.zip (contains this release/ tree).\n"
        "Reproducibility subtree for this manuscript: release/paper_refs_bundle_2026-05-06/\n\n"
        "Heavy LieBracketCell/*.lean sources are omitted from this mirror (RAM); see "
        "Hqiv/LieBracketCell/README.md and scripts/build_hqiv_so8_closure_lowmem.sh in a full clone.\n\n"
        f"Included files: {len(included)}\n"
        f"Missing files: {len(missing)}\n",
        encoding="utf-8",
    )

    if write_zips:
        if PAPER_BUNDLE_ZIP.exists():
            PAPER_BUNDLE_ZIP.unlink()
        with zipfile.ZipFile(PAPER_BUNDLE_ZIP, "w", compression=zipfile.ZIP_DEFLATED) as zf:
            for path in sorted(PAPER_BUNDLE_DIR.rglob("*")):
                if path.is_file():
                    zf.write(path, path.relative_to(PAPER_BUNDLE_DIR.parent))

    return manifest


def build_release_distribution_zip() -> Path:
    """
    Write ``release/companion-code.zip``: Zenodo/DOI companion archive containing the
    ``release/`` tree (inventory, paper-refs bundle directory, inner bundle zip, etc.).

    Skips ``companion-code.zip`` itself and legacy ``HQIV_LEAN_release_*.zip`` files when walking.
    """
    out_path = REPO_ROOT / "release" / "companion-code.zip"
    release_root = REPO_ROOT / "release"
    if out_path.exists():
        out_path.unlink()
    for legacy in release_root.glob("HQIV_LEAN_release_*.zip"):
        try:
            legacy.unlink()
        except OSError:
            pass
    with zipfile.ZipFile(out_path, "w", compression=zipfile.ZIP_DEFLATED) as zf:
        for path in sorted(release_root.rglob("*")):
            if not path.is_file():
                continue
            if path.resolve() == out_path.resolve():
                continue
            if path.name.startswith("HQIV_LEAN_release_") and path.suffix == ".zip":
                continue
            arc = path.relative_to(REPO_ROOT)
            zf.write(path, arcname=str(arc))
    return out_path


def run_paper_bibliography_audit() -> None:
    """Writes ``release/zenodo/paper_bibliography_audit.txt``; exits on missing keys."""
    audit_script = REPO_ROOT / "scripts" / "audit_paper_bibliography.py"
    report_path = OUT_DIR / "paper_bibliography_audit.txt"
    proc = subprocess.run(
        [
            sys.executable,
            str(audit_script),
            "--warn-uncited-bibitems",
            "--write",
            str(report_path),
        ],
        cwd=str(REPO_ROOT),
        check=False,
    )
    if proc.returncode != 0:
        sys.exit(proc.returncode)


def main() -> int:
    inventory = build_inventory()
    write_outputs(inventory)
    zip_blockers: list[str] = []
    zip_blockers.extend(inventory["missing_required"])
    zip_blockers.extend(zenodo_deposit_metadata_issues())
    write_zips = len(zip_blockers) == 0
    if not write_zips:
        for msg in zip_blockers:
            print(f"skip zips: {msg}", file=sys.stderr)

    manifest = build_paper_bundle(write_zips=write_zips)
    print(f'wrote {OUT_DIR / "publication_inventory.json"}')
    print(f'wrote {OUT_DIR / "SHA256SUMS.txt"}')
    print(f'required missing: {len(inventory["missing_required"])}')
    print(f'wrote {PAPER_BUNDLE_DIR / "MANIFEST.json"}')
    print(f'paper bundle missing: {manifest["missing_count"]}')
    run_paper_bibliography_audit()
    print(f'wrote {OUT_DIR / "paper_bibliography_audit.txt"}')
    if write_zips:
        rel_zip = build_release_distribution_zip()
        print(f"wrote {rel_zip}")
    else:
        print("skipped release/companion-code.zip and paper_refs_bundle zip (metadata issues)", file=sys.stderr)
    return 0 if write_zips else 1


if __name__ == "__main__":
    raise SystemExit(main())

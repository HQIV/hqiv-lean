#!/usr/bin/env python3
"""
Audit LaTeX citation keys under papers/ against local thebibliography entries
and .bib files referenced via \\bibliography{...}.

Exit code 1 if any \\cite / \\citep / \\citet / \\nocite key is missing from the
resolved key set for that source file.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
PAPERS_ROOT = REPO_ROOT / "papers"

# \cite[opt]{a,b}, \citep, \citet, \nocite
CITE_RE = re.compile(
    r"\\(?:cite|citep|citet|citeauthor|citeyearpar|citeyear|nocite)"
    r"(?:\[[^\]]*\])?\{([^}]+)\}"
)
BIBITEM_RE = re.compile(r"\\bibitem(?:\[[^\]]*\])?\{([^}]+)\}")
BIBLIOGRAPHY_RE = re.compile(r"\\bibliography\{([^}]+)\}")
# BibTeX entry keys: @type{key,
BIB_FILE_KEY_RE = re.compile(r"^@\w+\s*\{\s*([^,\s]+)\s*,", re.MULTILINE)


def _strip_tex_comments(line: str) -> str:
    out = []
    i = 0
    while i < len(line):
        if line[i] == "%" and (i == 0 or line[i - 1] != "\\"):
            break
        out.append(line[i])
        i += 1
    return "".join(out)


def read_tex_stripped_comments(path: Path) -> str:
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    return "\n".join(_strip_tex_comments(ln) for ln in lines)


def collect_bibitem_keys(tex_body: str) -> set[str]:
    return {m.group(1).strip() for m in BIBITEM_RE.finditer(tex_body)}


def collect_bibliography_bib_keys(tex_path: Path, tex_body: str) -> set[str]:
    keys: set[str] = set()
    m = BIBLIOGRAPHY_RE.search(tex_body)
    if not m:
        return keys
    names = [n.strip() for n in m.group(1).split(",") if n.strip()]
    base = tex_path.parent
    for name in names:
        bib_path = base / f"{name}.bib"
        if not bib_path.is_file():
            continue
        text = bib_path.read_text(encoding="utf-8", errors="replace")
        keys.update(BIB_FILE_KEY_RE.findall(text))
    return keys


def collect_cite_keys(tex_body: str) -> set[str]:
    found: set[str] = set()
    for m in CITE_RE.finditer(tex_body):
        inner = m.group(1)
        for part in inner.split(","):
            k = part.strip()
            if k:
                found.add(k)
    return found


def audit_file(tex_path: Path) -> tuple[list[str], list[str]]:
    """
    Returns (missing_keys, uncited_bibitem_keys) relative to inline bibitems only.
    For \\bibliography, bib file keys are merged for missing-key checks.
    """
    body = read_tex_stripped_comments(tex_path)
    bibitems = collect_bibitem_keys(body)
    bib_file_keys = collect_bibliography_bib_keys(tex_path, body)
    available = bibitems | bib_file_keys
    cites = collect_cite_keys(body)
    missing = sorted(cites - available)
    uncited = sorted(bibitems - cites) if bibitems else []
    return missing, uncited


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--warn-uncited-bibitems",
        action="store_true",
        help="Print warnings for \\bibitem keys never cited in the same file.",
    )
    ap.add_argument(
        "--write",
        type=Path,
        metavar="PATH",
        help="Write human-readable report to PATH.",
    )
    args = ap.parse_args()

    tex_files = sorted(PAPERS_ROOT.rglob("*.tex"))
    all_missing: list[tuple[str, str]] = []
    lines: list[str] = []

    for tex in tex_files:
        rel = tex.relative_to(REPO_ROOT)
        missing, uncited = audit_file(tex)
        if missing:
            for k in missing:
                all_missing.append((str(rel), k))
            lines.append(f"FAIL {rel}: missing keys: {', '.join(missing)}")
        else:
            lines.append(f"OK   {rel}")
        if args.warn_uncited_bibitems and uncited:
            lines.append(f"      (uncited \\bibitem: {', '.join(uncited)})")

    report = "\n".join(lines) + "\n"
    if args.write:
        args.write.parent.mkdir(parents=True, exist_ok=True)
        args.write.write_text(report, encoding="utf-8")

    sys.stdout.write(report)
    if all_missing:
        sys.stderr.write(
            f"\n{len(all_missing)} missing citation key(s) across {len({m[0] for m in all_missing})} file(s).\n"
        )
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

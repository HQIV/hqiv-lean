#!/usr/bin/env python3
"""Emit GitHub Actions outputs matching leanprover-community/docgen-action metadata step."""
from __future__ import annotations

import json
import os
import re
import tomllib
from pathlib import Path

# Map package name -> doc module roots (same as docgen-action index.js).
KNOWN_MAP: dict[str, list[str]] = {
    "Cli": ["Cli"],
    "LeanSearchClient": ["LeanSearchClient"],
    "Qq": ["Qq"],
    "aesop": ["Aesop"],
    "batteries": ["Batteries"],
    "importGraph": ["ImportGraph"],
    "mathlib": ["Mathlib", "Archive", "Counterexamples"],
    "plausible": ["Plausible"],
    "proofwidgets": ["ProofWidgets"],
}


def pkg_to_module_names(pkg_name: str) -> list[str]:
    if pkg_name in KNOWN_MAP:
        return KNOWN_MAP[pkg_name]
    parts = re.split(r"[-_]", pkg_name)
    upper = "".join(p[:1].upper() + p[1:] for p in parts if p)
    print(
        f"Warning: Unknown package {pkg_name}, predicted module name: {upper}. "
        "If doc cache misses, align with docgen-action pkgToModuleNames.",
        flush=True,
    )
    return [upper]


def main() -> None:
    root = Path(".")
    with open(root / "lakefile.toml", "rb") as f:
        lake = tomllib.load(f)
    with open(root / "lake-manifest.json", encoding="utf-8") as f:
        manifest = json.load(f)

    name = lake["name"]
    default_targets = lake.get("defaultTargets", [])
    docs_facets_list = [f"{t}:docs" for t in default_targets]
    extra_docs_facets = os.environ.get("EXTRA_DOCS_FACETS", "").strip()
    if extra_docs_facets:
        docs_facets_list.extend(extra_docs_facets.split())
    docs_facets = " ".join(docs_facets_list)

    explicit = [m for pkg in manifest["packages"] for m in pkg_to_module_names(pkg["name"])]
    implicit = ["Init", "Lake", "Lean", "Std"]
    cache_lines = [f"docbuild/.lake/build/doc/{dep}" for dep in explicit + implicit]
    cached_docbuild_dependencies = "\n".join(cache_lines)

    out = Path(os.environ["GITHUB_OUTPUT"])
    with out.open("a", encoding="utf-8") as fh:
        fh.write(f"name={name}\n")
        fh.write(f"docs_facets={docs_facets}\n")
        fh.write("cached_docbuild_dependencies<<EOF\n")
        fh.write(cached_docbuild_dependencies)
        fh.write("\nEOF\n")


if __name__ == "__main__":
    main()

"""Repo / Zenodo bundle root detection for HQIV witness scripts."""

from __future__ import annotations

from pathlib import Path


def repo_root(start: Path | None = None) -> Path:
    """Return directory containing witness ``data/*.json``.

    Layouts supported:
    - HQIV-LEAN checkout: ``lakefile.toml`` + top-level ``data/``
    - Zenodo bundle: ``scripts/*.py`` with ``scripts/data/*.json`` (``scripts/`` is root)
    - Repo quick-start: ``scripts/`` sibling to ``data/`` at repository root
    """
    anchor = Path(start or __file__).resolve()
    script_dir = anchor.parent if anchor.is_file() else anchor

    for parent in anchor.parents:
        if (parent / "lakefile.toml").is_file() and (parent / "data").is_dir():
            return parent

    witness = script_dir / "data" / "strong_sector_collider_observations.json"
    if witness.is_file() and any(script_dir.glob("hqiv_*.py")):
        return script_dir

    if script_dir.name == "scripts" and (script_dir.parent / "data").is_dir():
        return script_dir.parent

    return script_dir


def hadron_catalog_path(start: Path | None = None) -> Path:
    """Hadron valence catalog (bundled ``data/hadron-catalog.js`` or web calculator)."""
    root = repo_root(start)
    bundled = root / "data" / "hadron-catalog.js"
    if bundled.is_file():
        return bundled
    return root / "web" / "hqiv-mass-spectrum-calculator" / "hadron-catalog.js"

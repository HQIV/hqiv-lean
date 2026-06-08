#!/usr/bin/env python3
"""
Archive current float-style GeneratorsLieClosureData*.lean files and rewrite them
in rational form (p : ℝ) / q while preserving the exact numeric values currently
used by Lean theorems.

This does NOT change generator matrices or theorem statements; it only changes the
coefficient literal representation.
"""

from __future__ import annotations

import re
import shutil
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
HQIV = ROOT / "Hqiv"
ARCHIVE = HQIV / "ArchivedFloatLieClosureData"


PAT = re.compile(r"\(\s*([+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:e[+-]?\d+)?)\s*:\s*ℝ\s*\)")


def to_rat_literal(num_str: str) -> str:
    fr = Fraction(num_str)  # exact for decimal/scientific strings
    if fr.numerator == 0:
        return "(0 : ℝ)"
    if fr.denominator == 1:
        return f"({fr.numerator} : ℝ)"
    return f"(({fr.numerator} : ℝ) / {fr.denominator})"


def rationalize_file(path: Path) -> None:
    text = path.read_text(encoding="utf-8")
    new = PAT.sub(lambda m: to_rat_literal(m.group(1)), text)
    path.write_text(new, encoding="utf-8")


def main() -> None:
    ARCHIVE.mkdir(parents=True, exist_ok=True)

    targets = [HQIV / "GeneratorsLieClosureData.lean"]
    targets += [HQIV / f"GeneratorsLieClosureData{i}.lean" for i in range(28)]

    # Archive first
    for p in targets:
        if p.exists():
            shutil.copy2(p, ARCHIVE / p.name)

    # Rewrite in-place with rational literals
    for p in targets:
        if p.exists():
            rationalize_file(p)

    print(f"Archived {len(targets)} files to {ARCHIVE}")
    print("Rewrote active closure data files with rational literals.")


if __name__ == "__main__":
    main()

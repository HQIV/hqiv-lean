#!/usr/bin/env python3
"""Print `globs` TOML for `HQIVPhysics` / `HQIVMeaningfulPhysics` Lake libs.

BFS import closure of `HQIVPhysics.lean` and `HQIVMeaningfulPhysics.lean`. When either
root's `import` list changes materially, paste the printed `globs = [ ... ]` into the
`[[lean_lib]] name = \"HQIVMeaningfulPhysics\"` block in `lakefile.toml`.
"""
from __future__ import annotations

import os
from collections import deque

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

ROOTS = (
    "HQIVPhysics",
    "HQIVMeaningfulPhysics",
)


def mod_to_path(mod: str) -> str | None:
    p = mod.replace(".", "/") + ".lean"
    cand = os.path.join(REPO, p)
    if os.path.isfile(cand):
        return cand
    c2 = os.path.join(REPO, mod + ".lean")
    if os.path.isfile(c2):
        return c2
    return None


def read_hqiv_imports(path: str) -> list[str]:
    out: list[str] = []
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line.startswith("import "):
                continue
            imp = line.split()[1]
            if imp == "Init":
                continue
            if imp.startswith("Hqiv."):
                out.append(imp)
    return out


def import_closure() -> list[str]:
    seen: set[str] = set()
    q = deque(ROOTS)
    while q:
        m = q.popleft()
        if m in seen:
            continue
        p = mod_to_path(m)
        if p is None:
            continue
        seen.add(m)
        for imp in read_hqiv_imports(p):
            q.append(imp)
    hqiv = [m for m in seen if m.startswith("Hqiv.")]
    globs: list[str] = ["HQIVMeaningfulPhysics", "HQIVPhysics"] + sorted(hqiv, key=str)
    # Dedup, preserve order
    out, done = [], set()
    for g in globs:
        if g not in done:
            done.add(g)
            out.append(g)
    return out


def main() -> None:
    globs = import_closure()
    print(f"# {len(globs)} modules (2 roots + {len(globs) - 2} Hqiv)\n", end="")
    print("globs = [")
    for g in globs:
        print(f'  "{g}",')
    print("]")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Print `globs` TOML for the `HQIVStory` Lake lib.

BFS import closure of `HQIVStory.lean` over all `Hqiv.*` modules. Paste into the
`[[lean_lib]] name = "HQIVStory"` block in `lakefile.toml` when the story spine imports change.
"""
from __future__ import annotations

import os
import re
from collections import deque

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ROOT = "HQIVStory"


def mod_to_path(mod: str) -> str | None:
    p = os.path.join(REPO, mod.replace(".", "/") + ".lean")
    return p if os.path.isfile(p) else None


def read_hqiv_imports(path: str) -> list[str]:
    out: list[str] = []
    with open(path, encoding="utf-8") as f:
        for line in f:
            m = re.match(r"^import\s+(Hqiv\.\S+)", line.strip())
            if m:
                out.append(m.group(1))
    return out


def story_closure() -> list[str]:
    seen: set[str] = set()
    q: deque[str] = deque([ROOT])
    while q:
        mod = q.popleft()
        if mod in seen:
            continue
        p = mod_to_path(mod)
        if p is None:
            continue
        seen.add(mod)
        for imp in read_hqiv_imports(p):
            q.append(imp)
    hqiv = sorted(m for m in seen if m.startswith("Hqiv."))
    return ["HQIVStory"] + hqiv


def main() -> None:
    globs = story_closure()
    print(f"# {len(globs)} modules (HQIVStory + {len(globs) - 1} Hqiv)\n", end="")
    print("globs = [")
    for g in globs:
        print(f'  "{g}",')
    print("]")


if __name__ == "__main__":
    main()

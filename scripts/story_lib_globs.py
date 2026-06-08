#!/usr/bin/env python3
"""Print `globs` TOML for the `HQIVStory` Lake lib.

BFS over `Hqiv.Story.*` import closure starting from `HQIVStory.lean`. Paste into the
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


def read_story_imports(path: str) -> list[str]:
    out: list[str] = []
    with open(path, encoding="utf-8") as f:
        for line in f:
            m = re.match(r"^import\s+(Hqiv\.Story\.\S+)", line.strip())
            if m:
                out.append(m.group(1))
    return out


def story_closure() -> list[str]:
    seen: set[str] = set()
    q: deque[str] = deque([ROOT])
    story: set[str] = set()
    while q:
        mod = q.popleft()
        if mod in seen:
            continue
        p = mod_to_path(mod)
        if p is None:
            continue
        seen.add(mod)
        for imp in read_story_imports(p):
            story.add(imp)
            q.append(imp)
    return ["HQIVStory"] + sorted(story)


def main() -> None:
    globs = story_closure()
    print(f"# {len(globs)} modules (HQIVStory + {len(globs) - 1} Hqiv.Story)\n", end="")
    print("globs = [")
    for g in globs:
        print(f'  "{g}",')
    print("]")


if __name__ == "__main__":
    main()

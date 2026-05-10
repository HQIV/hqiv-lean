# Archived Lean modules (SAT / moiré / patch-index bridges)

These files are **kept in the build** (`HQIVLEAN`) so scripts and regression tests can still import them, but they are **not** part of the physics-first story.

| Module prefix | Role |
|---------------|------|
| `Hqiv.Archive.Algebra.Moire*` | Discrete patch score: cumulative variation, cusp/BST, jerk closed forms |
| `Hqiv.Archive.Geometry.RapidityArcPatchBridge` | Rapidity ↔ patch-index scaffolding tied to moiré bounds |
| `Hqiv.Archive.Logic.*` | CNF / assignment enumeration / encoding-completeness **skeleton** for `scripts/hqiv_geometric_3sat_demo.py` |

Agent-facing prose for this thread lives under [`AGENTS/archive/`](../AGENTS/archive/README.md).

#!/usr/bin/env python3
"""
Verify the Zenodo paper-reference bundle against what `papers/closure.tex` claims:

  - Every path in MANIFEST.json exists under the bundle root.
  - `artifacts/so8_symbolic_certificate.json` and `artifacts/so4_symbolic_certificate.json`
    satisfy minimal structural checks (paper: rank-28 / Q closure; toy so(4) data).
  - `HQIVPaperClaims.lean` imports only bundle-local formal map (no stray SAT cone).
  - `lake build HQIVPaperClaims` succeeds when run with cwd = bundle root (needs
    network on first run to fetch Mathlib into ``bundle/.lake``).

Usage (from repository root):

  python3 scripts/verify_paper_bundle_claims.py
  python3 scripts/verify_paper_bundle_claims.py /path/to/paper_refs_bundle_2026-05-06
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


def main() -> int:
    repo = Path(__file__).resolve().parents[1]
    bundle = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else repo / "release" / "paper_refs_bundle_2026-05-06"
    manifest_path = bundle / "MANIFEST.json"
    if not manifest_path.is_file():
        print(f"FAIL: missing {manifest_path}", file=sys.stderr)
        return 1

    data = json.loads(manifest_path.read_text(encoding="utf-8"))
    rels: list[str] = data.get("included", [])
    if not rels:
        print("FAIL: MANIFEST.json has empty included", file=sys.stderr)
        return 1

    missing = [r for r in rels if not (bundle / r).is_file()]
    if missing:
        print("FAIL: manifest paths missing on disk:", file=sys.stderr)
        for m in missing[:20]:
            print(f"  {m}", file=sys.stderr)
        if len(missing) > 20:
            print(f"  ... and {len(missing) - 20} more", file=sys.stderr)
        return 1
    print(f"OK manifest: {len(rels)} files present under {bundle}")

    sat_paths = [r for r in rels if "CausalRapidity" in r or "SharedManifold" in r or "SATRapidity" in r]
    if sat_paths:
        print("FAIL: SAT/causal modules unexpectedly in bundle:", sat_paths, file=sys.stderr)
        return 1
    print("OK bundle manifest excludes SAT rapidity / causal-forcing Lean sources")

    # JSON certificates (paper: exact Q / rank 28; appendix: so(4) toy)
    so8p = bundle / "artifacts" / "so8_symbolic_certificate.json"
    so4p = bundle / "artifacts" / "so4_symbolic_certificate.json"
    for label, path, checks in (
        (
            "so8",
            so8p,
            lambda o: (
                o.get("basis_count") == 28,
                isinstance(o.get("basis_packed_q"), list) and len(o["basis_packed_q"]) == 28,
                o.get("description", "").lower().find("so(8)") >= 0
                or "so8" in o.get("description", "").lower()
                or "lie-closure" in o.get("description", "").lower(),
            ),
        ),
        (
            "so4",
            so4p,
            lambda o: (
                o.get("so4_dimension") == 6,
                o.get("seed_linear_rank") == 4,
                isinstance(o.get("witness_brackets"), dict),
                len(o.get("basis_names", [])) == 6,
            ),
        ),
    ):
        if not path.is_file():
            print(f"FAIL: missing {path}", file=sys.stderr)
            return 1
        obj = json.loads(path.read_text(encoding="utf-8"))
        results = checks(obj)
        if not all(results):
            print(f"FAIL: {label} structural checks {results} on {path}", file=sys.stderr)
            return 1
        print(f"OK {label} certificate: {path.name}")

    # HQIVPaperClaims = discrete cone + symbolic SO(8) only (no CausalRapidity / SharedManifold in bundle)
    root_lean = bundle / "HQIVPaperClaims.lean"
    text = root_lean.read_text(encoding="utf-8")
    if "import Hqiv.Story.CausalRapidityForcing" in text or "import Hqiv.Geometry.SharedManifoldRapidity" in text:
        print("FAIL: HQIVPaperClaims.lean still imports SAT/causal cone", file=sys.stderr)
        return 1
    if "import Hqiv.Geometry.OctonionicLightCone" not in text or "import Hqiv.SO8ClosureSymbolic" not in text:
        print("FAIL: HQIVPaperClaims.lean missing expected imports", file=sys.stderr)
        return 1
    print("OK HQIVPaperClaims.lean: OctonionicLightCone + SO8ClosureSymbolic only")

    sym = bundle / "Hqiv" / "SO8ClosureSymbolic.lean"
    sym_t = sym.read_text(encoding="utf-8")
    if "axiom so8_closure_theorem_symbolic" not in sym_t:
        print("FAIL: expected symbolic SO(8) interface axioms in SO8ClosureSymbolic.lean", file=sys.stderr)
        return 1
    print("OK SO8ClosureSymbolic: symbolic interface uses axioms (as stated in paper)")

    print("Running: lake build HQIVPaperClaims (cwd=bundle) …")
    proc = subprocess.run(
        ["lake", "build", "HQIVPaperClaims"],
        cwd=str(bundle),
        check=False,
        capture_output=True,
        text=True,
        timeout=3600,
    )
    if proc.returncode != 0:
        tail = (proc.stderr or proc.stdout or "")[-8000:]
        print("FAIL: lake build HQIVPaperClaims", file=sys.stderr)
        print(tail, file=sys.stderr)
        return 1
    print("OK lake build HQIVPaperClaims")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

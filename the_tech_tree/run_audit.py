#!/usr/bin/env python3
"""
Run every top-level scripts/*.py and record exit status + duration.

Usage (from repo root):
  python3 the_tech_tree/run_audit.py

Writes:
  the_tech_tree/AUDIT_RESULTS.json
  the_tech_tree/AUDIT_RESULTS.md
"""

from __future__ import annotations

import json
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
OUT_JSON = Path(__file__).resolve().parent / "AUDIT_RESULTS.json"
OUT_MD = Path(__file__).resolve().parent / "AUDIT_RESULTS.md"
TIMEOUT_SEC = 30


def main() -> None:
    py_files = sorted(SCRIPTS.glob("*.py"))
    results: list[dict] = []
    for path in py_files:
        rel = path.relative_to(ROOT)
        t0 = time.perf_counter()
        try:
            proc = subprocess.run(
                [sys.executable, str(path)],
                cwd=str(SCRIPTS),
                capture_output=True,
                text=True,
                timeout=TIMEOUT_SEC,
            )
            elapsed = time.perf_counter() - t0
            err_tail = (proc.stderr or "")[-2000:]
            out_tail = (proc.stdout or "")[-500:]
            results.append(
                {
                    "path": str(rel),
                    "exit_code": proc.returncode,
                    "seconds": round(elapsed, 3),
                    "stdout_tail": out_tail,
                    "stderr_tail": err_tail,
                }
            )
        except subprocess.TimeoutExpired:
            elapsed = time.perf_counter() - t0
            results.append(
                {
                    "path": str(rel),
                    "exit_code": -124,
                    "seconds": round(elapsed, 3),
                    "stdout_tail": "",
                    "stderr_tail": f"TIMEOUT after {TIMEOUT_SEC}s",
                }
            )
        except Exception as e:  # noqa: BLE001
            elapsed = time.perf_counter() - t0
            results.append(
                {
                    "path": str(rel),
                    "exit_code": -1,
                    "seconds": round(elapsed, 3),
                    "stdout_tail": "",
                    "stderr_tail": repr(e),
                }
            )

    OUT_JSON.write_text(json.dumps(results, indent=2), encoding="utf-8")

    ok = [r for r in results if r["exit_code"] == 0]
    bad = [r for r in results if r["exit_code"] != 0]
    lines = [
        "# Script audit (top-level `scripts/*.py`)",
        "",
        f"- Timeout per script: {TIMEOUT_SEC}s",
        f"- CWD for each run: `scripts/`",
        f"- Total: {len(results)} | **pass (0)**: {len(ok)} | **fail / timeout**: {len(bad)}",
        "",
        "## Passed (exit 0)",
        "",
    ]
    for r in sorted(ok, key=lambda x: x["path"]):
        lines.append(f"- `{r['path']}` ({r['seconds']}s)")
    lines.extend(["", "## Failed or timeout", ""])
    for r in sorted(bad, key=lambda x: (x["exit_code"], x["path"])):
        lines.append(
            f"- `{r['path']}` exit={r['exit_code']} ({r['seconds']}s)"
        )
        if r.get("stderr_tail"):
            lines.append(f"  ```\n  {r['stderr_tail'][:400].replace(chr(10), chr(10)+'  ')}\n  ```")

    OUT_MD.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {OUT_JSON} and {OUT_MD}")


if __name__ == "__main__":
    main()

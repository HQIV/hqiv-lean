#!/usr/bin/env python3
"""
Export `FractionalChannelCertificate` rows as JSON for Lean review.

Schema (matches `Hqiv/Geometry/ATSPWorstCaseCertified.lean`):
  - n
  - oracleCost, seedCost, optimalCost
  - tensorResidualErr, rapidityErr, axisErr
  - rhoT, rhoR, rhoA   (fractional coefficients ρt, ρr, ρa)

Each row includes `valid` (boolean) and `validReason` from a numeric replay of
`FractionalChannelCertificate.IsValid` (tolerant checks for floating noise).
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


def envelope_root(n: int) -> float:
    nn = max(1, n)
    return float(nn) ** (1.0 / float(nn))


def check_valid(row: dict[str, Any], tol: float) -> tuple[bool, str]:
    req = (
        "n",
        "oracleCost",
        "seedCost",
        "optimalCost",
        "tensorResidualErr",
        "rapidityErr",
        "axisErr",
        "rhoT",
        "rhoR",
        "rhoA",
    )
    for k in req:
        if k not in row:
            return False, f"missing_field:{k}"
    n = int(row["n"])
    oc = float(row["oracleCost"])
    sc = float(row["seedCost"])
    opt = float(row["optimalCost"])
    et = float(row["tensorResidualErr"])
    er = float(row["rapidityErr"])
    ea = float(row["axisErr"])
    rt = float(row["rhoT"])
    rr = float(row["rhoR"])
    ra = float(row["rhoA"])
    if not math.isfinite(opt) or opt <= tol:
        return False, "optimalCost_not_positive"
    if sc > opt + et + er + ea + tol:
        return False, "projection_residual_violation"
    if oc > sc + tol:
        return False, "local_completion_violation"
    if et > opt * rt + tol:
        return False, "tensor_bound_violation"
    if er > opt * rr + tol:
        return False, "rapidity_bound_violation"
    if ea > opt * ra + tol:
        return False, "axis_bound_violation"
    eroot = envelope_root(n)
    if rt + rr + ra > eroot + tol:
        return False, "fractional_budget_violation"
    return True, "ok"


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Export / validate fractional channel certificate JSON")
    p.add_argument(
        "--input-json",
        type=str,
        default="",
        help="optional input JSON with {rows: [...]}; if empty, emit a single demo row",
    )
    p.add_argument("--output-json", type=str, default="data/fractional_channel_certificate.json")
    p.add_argument("--tol", type=float, default=1e-9)
    return p


def main() -> None:
    args = build_parser().parse_args()
    if args.tol < 0:
        raise SystemExit("--tol must be >= 0")
    rows_in: list[dict[str, Any]]
    if args.input_json:
        path = Path(args.input_json)
        if not path.exists():
            raise SystemExit(f"missing --input-json: {path}")
        payload = json.loads(path.read_text(encoding="utf-8"))
        raw = payload.get("rows")
        if not isinstance(raw, list):
            raise SystemExit("input must contain a list 'rows'")
        rows_in = [dict(x) for x in raw if isinstance(x, dict)]
    else:
        n = 12
        opt = 100.0
        eroot = envelope_root(n)
        rho_each = eroot / 3.0
        et = opt * rho_each * 0.5
        er = opt * rho_each * 0.5
        ea = opt * rho_each * 0.5
        rows_in = [
            {
                "n": n,
                "oracleCost": opt,
                "seedCost": opt + 1e-12,
                "optimalCost": opt,
                "tensorResidualErr": et,
                "rapidityErr": er,
                "axisErr": ea,
                "rhoT": rho_each,
                "rhoR": rho_each,
                "rhoA": rho_each,
                "note": "synthetic degenerate-ish demo; tighten for real oracle runs",
            }
        ]

    out_rows: list[dict[str, Any]] = []
    ok_count = 0
    for row in rows_in:
        valid, reason = check_valid(row, args.tol)
        ok_count += int(valid)
        out = dict(row)
        out["valid"] = valid
        out["validReason"] = reason
        out_rows.append(out)

    out_path = Path(args.output_json)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(
        json.dumps({"rows": out_rows, "validCount": ok_count, "total": len(out_rows)}, indent=2),
        encoding="utf-8",
    )
    print(f"wrote {out_path} valid={ok_count}/{len(out_rows)}")


if __name__ == "__main__":
    main()

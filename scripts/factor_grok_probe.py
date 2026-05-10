#!/usr/bin/env python3
"""
Probe: run ``octonion_factor`` with odd-prime sieve **off** (keep factor-2 peel + isqrt square peel).

For the input integer N:
  1) Log reference prime factors (trial division to min(isqrt(N), cap)).
  2) Run the spiral with tracing (angles, cross, legs per k).
  3) For each nontrivial divisor d of N, print the continuous angles that would
     align the crossing / leg probes with d on ``current == N`` (same geometry as the run).
"""

from __future__ import annotations

import argparse
import importlib.util
import math
import sys
from pathlib import Path

_SCRIPTS = Path(__file__).resolve().parent
_REPO = _SCRIPTS.parent


def _load_factor_grok():
    spec = importlib.util.spec_from_file_location("factor_grok", _SCRIPTS / "factor_grok.py")
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader
    spec.loader.exec_module(mod)
    return mod


def _trial_factor_ref(n: int, limit: int | None = None) -> list[int]:
    """Prime factors of n (with multiplicity) for reference; trial division."""
    if n <= 1:
        return []
    out: list[int] = []
    x = n
    while x % 2 == 0:
        out.append(2)
        x //= 2
    cap = min(limit if limit is not None else math.isqrt(x) + 1, max(2, math.isqrt(x) + 1))
    p = 3
    while p * p <= x and p <= cap:
        while x % p == 0:
            out.append(p)
            x //= p
        p += 2
    if x > 1:
        out.append(x)
    return sorted(out)


def _nontrivial_divisors(n: int) -> list[int]:
    """All d with 1 < d < n and n % d == 0."""
    if n <= 3:
        return []
    divs: set[int] = set()
    for d in range(2, math.isqrt(n) + 1):
        if n % d == 0:
            divs.add(d)
            divs.add(n // d)
    return sorted(divs)


def _recovery_angles_for_divisor(n: int, d: int) -> dict[str, float | str]:
    """
    Continuous angles (radians) on current == n, r = sqrt(n), matching factor_grok probes:

    - crossing: cross = nint(r * theta)  ~  r * theta  =>  theta ~ d / r
    - leg1: nint(r * cos(theta)) = d  =>  theta = acos(d / r)  (needs |d|<=r)
    - leg2: nint(r * sin(theta)) = d  =>  theta = asin(d / r)
    """
    r = math.sqrt(n)
    row: dict[str, float | str] = {
        "d": float(d),
        "r": r,
        "theta_cross_rad": d / r,
        "theta_cross_deg": (d / r) * 180 / math.pi,
    }
    if d < r:
        row["theta_leg1_acos_rad"] = math.acos(d / r)
        row["theta_leg1_deg"] = math.degrees(math.acos(d / r))
        row["theta_leg2_asin_rad"] = math.asin(d / r)
        row["theta_leg2_deg"] = math.degrees(math.asin(d / r))
    elif d == r:
        row["theta_leg1_deg"] = 0.0
        row["theta_leg2_deg"] = 90.0
        row["note"] = "d == r (perfect square factor)"
    else:
        row["note"] = "d > sqrt(n): no first-quadrant θ with r*cos θ = d or r*sin θ = d"
    return row


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("N", type=int, help="integer to factor (probe)")
    p.add_argument(
        "--odd-sieve",
        action="store_true",
        help="also run odd-prime trial sieve (default: off for probe)",
    )
    p.add_argument(
        "--max-trial-ref",
        type=int,
        default=None,
        help="cap for reference trial factorization (default: isqrt(N)+1)",
    )
    args = p.parse_args()

    fg = _load_factor_grok()
    N = args.N
    if N <= 1:
        print(f"N={N} trivial")
        sys.exit(0)

    ref = _trial_factor_ref(N, args.max_trial_ref)
    divs = _nontrivial_divisors(N)

    print("=== reference (trial, for logging only) ===")
    print(f"N = {N}")
    print(f"reference prime factors: {ref}")
    print(f"nontrivial divisors: {divs}")
    print()

    print("=== angles that would align probes with each divisor d (geometry at current=N) ===")
    r = math.sqrt(N)
    print(f"r = sqrt(N) = {r:.12g}")
    for d in divs:
        ang = _recovery_angles_for_divisor(N, d)
        note = ang.pop("note", "")
        print(f"  divisor d = {int(d)}:")
        for k, v in ang.items():
            if k in ("d", "r"):
                continue
            if isinstance(v, float):
                print(f"    {k}: {v:.12g}")
            else:
                print(f"    {k}: {v}")
        if note:
            print(f"    note: {note}")
    print()

    trace: list[dict] = []
    out = fg.octonion_factor(N, use_odd_sieve=args.odd_sieve, trace=trace)

    print(f"=== run (use_odd_sieve={args.odd_sieve}) ===")
    print(f"octonion_factor({N}) -> {out}")
    print()
    print("=== trace (continuous spiral: base angle + phase carry → effective angle; legs) ===")
    print(
        "(Leg divisors only apply when p_max < leg < current; "
        "with sieve off, p_max is 3.)"
    )
    for ev in trace:
        if ev.get("event") != "spiral_step":
            print(ev)
            continue
        pmax = ev.get("p_max", 0)
        eff = ev.get("effective_rad", ev.get("angle_rad"))
        pc = ev.get("phase_carry", float("nan"))
        po = ev.get("phase_offset", float("nan"))
        l1, l2 = ev.get("leg1"), ev.get("leg2")
        leg1_ok = pmax < (l1 or 0) < ev["current"] if l1 is not None else False
        leg2_ok = pmax < (l2 or 0) < ev["current"] if l2 is not None else False
        print(
            f"  current={ev['current']}  p_max={pmax}  k={ev['k']}  target={ev['target']!r}  "
            f"θ_sched={ev['angle_deg']:.8g}°  "
            f"phase_carry={pc:.8g}  phase_off={po:.8g}  "
            f"effective={ev.get('effective_deg', float('nan')):.8g}° ({eff:.12g} rad)  "
            f"leg1={l1} leg1_gate_ok={leg1_ok}  leg2={l2} leg2_gate_ok={leg2_ok}"
        )

    print()
    print("=== nearest effective angle vs θ_cross = d/r for each divisor (same k-loop order) ===")
    steps = [ev for ev in trace if ev.get("event") == "spiral_step" and ev.get("current") == N]
    for d in divs:
        need_rad = d / r
        need_deg = need_rad * 180 / math.pi
        best: tuple[float, float, str, int] | None = None
        for ev in steps:
            eff = float(ev.get("effective_rad", ev["angle_rad"]))
            delta = abs(eff - need_rad)
            if best is None or delta < best[0]:
                best = (delta, eff, ev["target"], ev["k"])
        if best:
            print(
                f"  d={d}: need θ_cross ≈ d/r = {need_deg:.8g}° ({need_rad:.12g} rad)  |  "
                f"closest step: k={best[3]} target={best[2]!r} effective={best[1]*180/math.pi:.8g}°  "
                f"Δ={best[0]*180/math.pi:.8g}°"
            )


if __name__ == "__main__":
    main()

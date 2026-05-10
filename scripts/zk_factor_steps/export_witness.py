#!/usr/bin/env python3
"""
Build a deterministic candidate scan trace for `factor_from_curvature` (mask path, no sieve).

The trace is suitable for the Circom circuit `first_divisor_at_step.circom`, which proves:
  - at public step_index (1-based), candidate factor_d divides n;
  - all earlier candidates in the same sorted order do not divide n.

**Step rule:** take `sorted(mask candidate set)`, keep only `1 < c < n`, then scan left-to-right for
the first divisor (`n % c == 0`). The index in **this filtered list** (1-based) is `step_index`
(so trivial `c = 1` is not counted as a step).

This matches disclosure of “how many probes until the mask hits a factor” for fixed oracle params.

**Size / honesty:** Tiny ``n`` (e.g. 221) makes a toy “12 steps” story trivial next to trial division on
all integers up to √n. Prefer composites whose **smallest nontrivial factor has many bits**, and
publish ``n`` large enough that naive guess-and-check over *all* candidates up to √n is irrelevant.
The SNARK still proves **only** consistency of the division trace at the announced step — not that the
mask is globally competitive with full-range trial division.

**BN254 (alt_bn128) scalar field:** All of ``n``, ``c[i]``, ``q[i]``, ``r[i]`` must embed in one field
element (no modular wraparound in ``q*c+r``). Integers must satisfy ``n < BN254_SCALAR_FIELD``.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import random
import sys
import warnings
from fractions import Fraction
from pathlib import Path
from typing import Any

_SCRIPTS = Path(__file__).resolve().parent.parent
if str(_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS))

import factor_from_curvature as ffc  # noqa: E402

# Must match `FirstDivisorAtStep(MAX_STEPS)` in `circuits/first_divisor_at_step.circom`.
DEFAULT_MAX_STEPS = ffc.MAX_PRIME_SIEVE_BOUND

# Groth16/snarkjs default curve: BN254 "scalar field" order (same as Ethereum alt_bn128).
BN254_SCALAR_FIELD = 21888242871839275222246405745257275088548364400416034343698204186575808495617

# Disclosure example: ~27-bit semiprime, ~14-bit factors, mask hits at step 25 (see README).
EXAMPLE_LARGE_N = 118472447
EXAMPLE_LARGE_PHI = 2.412733316043902
EXAMPLE_LARGE_T = 0.40301219419426426
EXAMPLE_LARGE_WINDOW = 8


def assert_fits_snark_field(*values: int) -> None:
    for v in values:
        if v < 0 or v >= BN254_SCALAR_FIELD:
            raise SystemExit(
                f"Value {v} does not fit BN254 scalar field [0, {BN254_SCALAR_FIELD}). "
                "Use a smaller composite or a bigint / multi-limb circuit."
            )


def auto_tune_mask_params(
    n: int,
    *,
    curvature: Fraction,
    arity: int,
    omega_mode: str,
    omega_imprint: float | None,
    phase_shell_mode: str,
    max_steps: int,
    trials: int,
    seed: int,
) -> tuple[float, float, int, int, int]:
    """
    Random search for (phi, t, window) such that the mask lists a nontrivial divisor
    within the first ``max_steps`` filtered candidates.

    Returns (phi, t, window, step_index, factor_d).
    """
    rng = random.Random(seed)
    windows = [8, 16, 24, 32, 48, 64, 96, 128]
    for _ in range(trials):
        phi = rng.uniform(0.05, 5.0)
        t = rng.uniform(0.1, 10.0)
        window = rng.choice(windows)
        _, dbg = ffc.factor_pair_from_3spiral_mask(
            n=n,
            curvature=curvature,
            phi=phi,
            t=t,
            window=window,
            arity=arity,
            omega_override=omega_imprint,
            omega_mode=omega_mode,
            phase_shell_mode=phase_shell_mode,
            use_sieve=False,
        )
        ordered = sorted(dbg["candidates"])
        step_idx, factor_d, _ = first_divisor_step_trace(n, ordered)
        if step_idx != 0 and step_idx <= max_steps:
            return phi, t, window, step_idx, factor_d
    raise SystemExit(
        f"auto-tune failed after {trials} trials: mask never hit a divisor within "
        f"{max_steps} filtered steps. Try larger --max-steps, other phase_shell, or a different n."
    )


def warn_if_toy_disclosure(n: int, factor_d: int, *, min_n_bits: int = 24, min_factor_bits: int = 10) -> None:
    """Warn when public integers are small enough to trivialize the narrative."""
    nb = n.bit_length()
    fb = factor_d.bit_length()
    if nb < min_n_bits or fb < min_factor_bits:
        warnings.warn(
            f"Small public integers (n≈{nb} bits, factor_d≈{fb} bits): "
            "for meaningful disclosure, prefer larger composites and multi-bit factors "
            f"(e.g. n={EXAMPLE_LARGE_N} with --example-large-params).",
            stacklevel=2,
        )


def build_ordered_candidates(
    n: int,
    *,
    curvature: Fraction,
    phi: float,
    t: float,
    window: int,
    arity: int,
    omega_mode: str,
    omega_imprint: float | None,
    phase_shell_mode: str,
) -> list[int]:
    """Sorted unique mask candidates (same set as factor_pair_from_3spiral_mask, no sieve)."""
    if n <= 1:
        return []
    _, dbg = ffc.factor_pair_from_3spiral_mask(
        n=n,
        curvature=curvature,
        phi=phi,
        t=t,
        window=window,
        arity=arity,
        omega_override=omega_imprint,
        omega_mode=omega_mode,
        phase_shell_mode=phase_shell_mode,
        use_sieve=False,
    )
    return sorted(dbg["candidates"])


def first_divisor_step_trace(
    n: int,
    ordered: list[int],
) -> tuple[int, int, list[tuple[int, int, int]]]:
    """
    Returns (step_index_1based, factor_d, rows) where each row is (c, q, r) with n = q*c + r.

    Only candidates with **1 < c < n** are probed (so every non-terminal row has r ≠ 0).
    step_index is 0 if no divisor found in that filtered order.
    """
    rows: list[tuple[int, int, int]] = []
    filtered = [c for c in ordered if 1 < c < n]
    for i, c in enumerate(filtered, start=1):
        if c <= 0:
            raise ValueError("candidate must be positive")
        q, r = divmod(n, c)
        rows.append((c, q, r))
        if r == 0:
            return i, c, rows
    return 0, 0, rows


def pad_trace(
    rows: list[tuple[int, int, int]],
    n: int,
    max_steps: int,
) -> list[tuple[int, int, int]]:
    """Pad or truncate to exactly `max_steps` rows for the fixed-unroll circuit."""
    out: list[tuple[int, int, int]] = []
    for i in range(max_steps):
        if i < len(rows):
            out.append(rows[i])
        else:
            out.append((1, n, 0))  # inactive dummy: n === n*1 + 0
    return out


def disclosure_commitment(payload: dict[str, Any]) -> str:
    """SHA-256 of canonical JSON (algorithm + params + candidate digest)."""
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def export_payload(
    n: int,
    *,
    curvature: Fraction,
    phi: float,
    t: float,
    window: int,
    arity: int,
    omega_mode: str,
    omega_imprint: float | None,
    phase_shell_mode: str,
    max_steps: int,
) -> dict[str, Any]:
    ordered = build_ordered_candidates(
        n,
        curvature=curvature,
        phi=phi,
        t=t,
        window=window,
        arity=arity,
        omega_mode=omega_mode,
        omega_imprint=omega_imprint,
        phase_shell_mode=phase_shell_mode,
    )
    step_idx, factor_d, scan_rows = first_divisor_step_trace(n, ordered)
    if step_idx == 0:
        raise SystemExit(
            "No nontrivial divisor found in ordered mask candidates; "
            "increase --window or change params (cannot build step proof)."
        )
    if step_idx > max_steps:
        raise SystemExit(f"step_index {step_idx} exceeds MAX_STEPS={max_steps}; raise MAX_STEPS in Circom.")

    padded = pad_trace(scan_rows, n, max_steps)
    assert_fits_snark_field(n, *[x for row in padded for x in row])

    circom_input = {
        "n": str(n),
        "step_index": str(step_idx),
        "factor_d": str(factor_d),
        "c": [str(padded[i][0]) for i in range(max_steps)],
        "q": [str(padded[i][1]) for i in range(max_steps)],
        "r": [str(padded[i][2]) for i in range(max_steps)],
    }

    meta = {
        "n": n,
        "step_index": step_idx,
        "factor_d": factor_d,
        "ordered_candidate_count": len(ordered),
        "ordered_candidates_prefix": ordered[: min(20, len(ordered))],
        "curvature_rational": str(curvature),
        "phi": phi,
        "t": t,
        "window": window,
        "arity": arity,
        "omega_mode": omega_mode,
        "omega_imprint": omega_imprint,
        "phase_shell_mode": phase_shell_mode,
        "max_steps": max_steps,
    }
    commit_body = {**meta, "ordered_candidates_sha256": hashlib.sha256(json.dumps(ordered).encode()).hexdigest()}
    meta["disclosure_commitment_sha256"] = disclosure_commitment(commit_body)

    return {
        "meta": meta,
        "circom_input": circom_input,
        "ordered_candidates": ordered,
    }


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("n", type=int, help="composite integer to factor (mask must hit a divisor)")
    p.add_argument("--curvature-rational", type=str, default="0", help="e.g. 0 or -1/30")
    p.add_argument("--phi", type=float, default=1.0)
    p.add_argument("--t", type=float, default=1.0)
    p.add_argument("--window", type=int, default=8)
    p.add_argument("--arity", type=int, default=2)
    p.add_argument("--omega-mode", type=str, default="rational", choices=("rational", "ramanujan_arity"))
    p.add_argument("--omega-imprint", type=float, default=None, help="override Ω_k imprint")
    p.add_argument("--phase-shell", type=str, default="n")
    p.add_argument("--max-steps", type=int, default=DEFAULT_MAX_STEPS)
    p.add_argument(
        "--auto-tune",
        action="store_true",
        help="search random (phi,t,window) until the mask hits a divisor within --max-steps",
    )
    p.add_argument("--auto-tune-trials", type=int, default=40000)
    p.add_argument("--auto-tune-seed", type=int, default=0)
    p.add_argument(
        "--example-large-params",
        action="store_true",
        help=f"use fixed (phi,t,window) for n={EXAMPLE_LARGE_N} (~14-bit factors, step 25)",
    )
    p.add_argument("--no-toy-warn", action="store_true", help="disable warning on small n/factor_d")
    p.add_argument("--out", type=Path, help="write full JSON payload here")
    p.add_argument("--circom-out", type=Path, help="write snarkjs input.json here")
    args = p.parse_args()

    if args.n <= 1:
        raise SystemExit("n must be > 1")
    curv = ffc.parse_rational(args.curvature_rational)

    phi, t, window = args.phi, args.t, args.window
    if args.example_large_params:
        if args.n != EXAMPLE_LARGE_N:
            raise SystemExit(f"--example-large-params requires n={EXAMPLE_LARGE_N}")
        phi, t, window = EXAMPLE_LARGE_PHI, EXAMPLE_LARGE_T, EXAMPLE_LARGE_WINDOW

    if args.auto_tune:
        if args.example_large_params:
            raise SystemExit("use either --auto-tune or --example-large-params, not both")
        phi, t, window, _, _ = auto_tune_mask_params(
            args.n,
            curvature=curv,
            arity=args.arity,
            omega_mode=args.omega_mode,
            omega_imprint=args.omega_imprint,
            phase_shell_mode=args.phase_shell,
            max_steps=args.max_steps,
            trials=args.auto_tune_trials,
            seed=args.auto_tune_seed,
        )

    payload = export_payload(
        args.n,
        curvature=curv,
        phi=phi,
        t=t,
        window=window,
        arity=args.arity,
        omega_mode=args.omega_mode,
        omega_imprint=args.omega_imprint,
        phase_shell_mode=args.phase_shell,
        max_steps=args.max_steps,
    )
    if args.auto_tune:
        payload["meta"]["auto_tune"] = True
        payload["meta"]["auto_tune_trials"] = args.auto_tune_trials
        payload["meta"]["auto_tune_seed"] = args.auto_tune_seed
    if args.example_large_params:
        payload["meta"]["example_large_params"] = True

    if not args.no_toy_warn:
        warn_if_toy_disclosure(args.n, int(payload["meta"]["factor_d"]))

    if args.out:
        args.out.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    if args.circom_out:
        args.circom_out.write_text(json.dumps(payload["circom_input"]), encoding="utf-8")

    if not args.out and not args.circom_out:
        print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

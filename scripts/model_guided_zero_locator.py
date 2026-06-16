#!/usr/bin/env python3
"""
Hybrid geometric + classical zero locator (Option 1).

Lean chart (S3ModelGuidedZeroLocator.lean):
  Model candidates t_k = 3π/4 + kπ  (balance locus of A(θ) = cos(θ − π/4))
  cumulativeHarmonicPhaseSum N θ = A(θ) · W_N  →  same zero locus for N > 0

Classical side:
  Search sign changes of Hardy Z(t) = mp.siegelz(t) in small windows around each
  candidate.  Sign changes indicate ordinates of zeros of ζ(½ + it).

This is unconditional numerics — model supplies "where to look", not a proof that
all zeros lie near model points.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable, Sequence

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUT = ROOT / "data" / "model_guided_zero_locator.json"

BALANCE_OFFSET = 3 * math.pi / 4
CANDIDATE_PERIOD = math.pi


@dataclass(frozen=True)
class ModelCandidate:
    index: int
    height: float


@dataclass(frozen=True)
class LocatedZero:
    candidate_index: int
    candidate_height: float
    located_height: float
    hardy_z_at_located: float
    distance_to_candidate: float


def model_candidates_up_to(T: float) -> list[ModelCandidate]:
    """Return model ordinates t_k = 3π/4 + kπ with 0 ≤ t_k ≤ T."""
    if T < BALANCE_OFFSET:
        return []
    k_max = math.floor((T - BALANCE_OFFSET) / CANDIDATE_PERIOD)
    return [
        ModelCandidate(index=k, height=BALANCE_OFFSET + k * CANDIDATE_PERIOD)
        for k in range(0, k_max + 1)
    ]


def nearest_model_candidate(t: float) -> ModelCandidate:
    """Nearest balance candidate to ordinate t."""
    k = round((t - BALANCE_OFFSET) / CANDIDATE_PERIOD)
    return ModelCandidate(index=k, height=BALANCE_OFFSET + k * CANDIDATE_PERIOD)


def hardy_z(t: float, prec: int = 50) -> float:
    import mpmath as mp

    mp.mp.dps = prec
    return float(mp.siegelz(mp.mpf(t)))


def _sign_changes(
    f,
    a: float,
    b: float,
    n_steps: int,
) -> list[tuple[float, float]]:
    """Bracket intervals where f changes sign on [a, b]."""
    if b <= a:
        return []
    step = (b - a) / n_steps
    xs = [a + i * step for i in range(n_steps + 1)]
    ys = [f(x) for x in xs]
    brackets: list[tuple[float, float]] = []
    for i in range(len(xs) - 1):
        y0, y1 = ys[i], ys[i + 1]
        if y0 == 0.0:
            brackets.append((xs[i], xs[i]))
        elif y1 == 0.0:
            brackets.append((xs[i + 1], xs[i + 1]))
        elif y0 * y1 < 0:
            brackets.append((xs[i], xs[i + 1]))
    return brackets


def locate_zeros_near(
    candidate: float,
    window: float,
    *,
    grid_steps: int = 80,
    prec: int = 50,
) -> list[float]:
    """
    Find Hardy-Z zeros near `candidate` inside [candidate − window, candidate + window].
    """
    import mpmath as mp

    mp.mp.dps = prec
    a = candidate - window
    b = candidate + window

    def z(x: float) -> float:
        return float(mp.siegelz(mp.mpf(x)))

    roots: list[float] = []
    seen: list[float] = []
    for left, right in _sign_changes(z, a, b, grid_steps):
        if left == right:
            t0 = left
        else:
            try:
                t0 = float(mp.findroot(lambda x: mp.siegelz(x), (left, right)))
            except Exception:
                continue
        if any(abs(t0 - s) < 1e-6 for s in seen):
            continue
        seen.append(t0)
        roots.append(t0)
    return sorted(roots)


def model_guided_zero_locator(
    T: float,
    window: float,
    *,
    grid_steps: int = 80,
    prec: int = 50,
) -> tuple[list[ModelCandidate], list[LocatedZero]]:
    """Generate candidates up to T and locate classical zeros near each."""
    candidates = model_candidates_up_to(T)
    located: list[LocatedZero] = []
    for cand in candidates:
        for t0 in locate_zeros_near(cand.height, window, grid_steps=grid_steps, prec=prec):
            z0 = hardy_z(t0, prec=prec)
            dist = abs(t0 - cand.height)
            located.append(
                LocatedZero(
                    candidate_index=cand.index,
                    candidate_height=cand.height,
                    located_height=t0,
                    hardy_z_at_located=z0,
                    distance_to_candidate=dist,
                )
            )
    return candidates, located


def zeta_zero_ordinates(count: int, prec: int = 40) -> list[float]:
    import mpmath as mp

    mp.mp.dps = prec
    return [float(mp.im(mp.zetazero(n))) for n in range(1, count + 1)]


def compare_to_known_zeros(
    located: Sequence[LocatedZero],
    known: Sequence[float],
) -> list[dict]:
    """Match each known zero to nearest located entry."""
    rows: list[dict] = []
    for gamma in known:
        nearest = nearest_model_candidate(gamma)
        best_loc = min(located, key=lambda r: abs(r.located_height - gamma), default=None)
        rows.append(
            {
                "known_zero": gamma,
                "nearest_model_index": nearest.index,
                "nearest_model_height": nearest.height,
                "model_distance": abs(gamma - nearest.height),
                "located_height": best_loc.located_height if best_loc else None,
                "located_distance": abs(best_loc.located_height - gamma) if best_loc else None,
            }
        )
    return rows


def print_table(candidates: Iterable[ModelCandidate], located: Iterable[LocatedZero]) -> None:
    print("Model candidates:")
    for c in candidates:
        print(f"  k={c.index:4d}  t_k={c.height:14.8f}")
    print("\nLocated zeros (Hardy Z sign changes):")
    for z in located:
        print(
            f"  k={z.candidate_index:4d}  candidate={z.candidate_height:12.6f}  "
            f"located={z.located_height:14.8f}  |Z|={abs(z.hardy_z_at_located):.3e}  "
            f"dist={z.distance_to_candidate:.6f}"
        )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--T", type=float, default=50.0, help="cover height")
    parser.add_argument("--window", type=float, default=1.0, help="search half-width")
    parser.add_argument("--grid-steps", type=int, default=80, help="grid per window")
    parser.add_argument("--prec", type=int, default=50, help="mpmath precision")
    parser.add_argument("--compare", type=int, default=0, help="compare first N known zeros")
    parser.add_argument("--json", action="store_true", help="print JSON")
    parser.add_argument("--write", type=Path, default=None, help="write JSON report")
    args = parser.parse_args()

    candidates, located = model_guided_zero_locator(
        args.T,
        args.window,
        grid_steps=args.grid_steps,
        prec=args.prec,
    )
    payload: dict = {
        "description": "Model-guided Hardy-Z zero locator (Option 1)",
        "model": {
            "balance_offset": BALANCE_OFFSET,
            "candidate_period": CANDIDATE_PERIOD,
            "candidate_formula": "t_k = 3π/4 + kπ",
        },
        "parameters": {
            "cover_height": args.T,
            "window": args.window,
            "grid_steps": args.grid_steps,
            "prec": args.prec,
        },
        "candidates": [asdict(c) for c in candidates],
        "located_zeros": [asdict(z) for z in located],
    }
    if args.compare > 0:
        known = zeta_zero_ordinates(args.compare, prec=args.prec)
        payload["known_zero_comparison"] = compare_to_known_zeros(located, known)

    if args.json:
        print(json.dumps(payload, indent=2))
    else:
        print_table(candidates, located)
        if args.compare > 0:
            print("\nKnown zero comparison:")
            for row in payload["known_zero_comparison"]:
                print(row)

    out = args.write or (DEFAULT_OUT if not args.json else None)
    if out is not None:
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(payload, indent=2) + "\n")
        if not args.json:
            print(f"\nWrote {out}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())

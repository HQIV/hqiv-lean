#!/usr/bin/env python3
"""
Falsification helper for **AGENTS/archive/FT_PATCH_CLOSED_TARGET.md** Target 0 / A.

Computes a naive DFT of the **toy** score ``S(j)`` from :func:`moire_score_samples` and reports
energy fractions in low bins vs total. For a **named** Lean mirror of the peak sum see
:func:`hqiv_geometric_3sat_demo.fourier_patch_peak_correlation_complex` (Target 0a partial).

If energy is spread across all frequencies, the *current* toy is a poor match to a single-mode
concentration story; if one bin dominates, you have empirical evidence to tighten hypotheses.

Example::

  python3 scripts/ft_patch_closed_target_probe.py --formula-name \"Example (4 vars, 3 clauses)\"
  python3 scripts/ft_patch_closed_target_probe.py --random 5 21 0
"""

from __future__ import annotations

import argparse
import cmath
import importlib.util
import math
import sys
from pathlib import Path

_scripts = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("hqiv_geometric_3sat_demo", _scripts / "hqiv_geometric_3sat_demo.py")
_g3 = importlib.util.module_from_spec(_spec)
assert _spec.loader is not None
sys.modules["hqiv_geometric_3sat_demo"] = _g3
_spec.loader.exec_module(_g3)


def dft_energy_fractions(samples: list[float], *, max_bin_report: int = 8) -> dict[str, float]:
    """Unitary-agnostic energy: |hat f(k)|^2 / sum_k |hat f(k)|^2 for k = 0..n-1."""

    n = len(samples)
    if n == 0:
        return {"n": 0.0}
    hat: list[complex] = []
    for k in range(n):
        s = sum(samples[j] * cmath.exp(-2j * math.pi * k * j / n) for j in range(n))
        hat.append(s)
    pows = [abs(z) ** 2 for z in hat]
    tot = sum(pows) or 1.0
    out: dict[str, float] = {"n": float(n), "energy_total": tot}
    for k in range(min(n, max_bin_report)):
        out[f"frac_bin_{k}"] = pows[k] / tot
    out["frac_max_bin"] = max(pows) / tot
    out["argmax_bin"] = float(pows.index(max(pows)))
    return out


def main() -> None:
    p = argparse.ArgumentParser(description="DFT energy diagnostic on toy moiré samples")
    p.add_argument("--formula-name", type=str, help="TRIAL_FORMULAS or ALL_SAT_BENCHMARKS name")
    p.add_argument("--random", nargs=3, type=int, metavar=("N", "M", "SEED"), help="random 3-SAT n vars, m clauses, seed")
    args = p.parse_args()

    fm = None
    name = " ad hoc"
    if args.random:
        n, m, seed = args.random
        fm = _g3.random_3sat_formula(n, m, __import__("random").Random(seed))
        name = f"random n={n} m={m} seed={seed}"
    elif args.formula_name:
        for title, f in _g3.TRIAL_FORMULAS:
            if title == args.formula_name:
                fm = f
                name = title
                break
        if fm is None:
            for row in _g3.ALL_SAT_BENCHMARKS:
                if row[0] == args.formula_name:
                    fm = row[1]
                    name = row[0]
                    break
        if fm is None:
            p.error(f"formula not found: {args.formula_name!r}")
    else:
        fm = _g3.EXAMPLE
        name = "EXAMPLE"

    M, _, _ = _g3.encode_formula_to_M(fm)
    k = _g3.omega_M_exact(fm)
    c = len(fm.clauses)
    n_patch = _g3.patch_window_length(c)
    samples = _g3.moire_score_samples(M, k, c, n=n_patch)
    fr = dft_energy_fractions(samples)

    print(f"FT patch probe: {name}")
    print(f"  M bits={M.bit_length()}  k_enc={k}  n_patch={n_patch}")
    print(f"  DFT: frac_max_bin={fr['frac_max_bin']:.4f}  argmax_bin={int(fr['argmax_bin'])}")
    for i in range(min(8, int(fr['n']))):
        print(f"    frac_bin_{i}={fr.get(f'frac_bin_{i}', 0):.4f}")


if __name__ == "__main__":
    main()

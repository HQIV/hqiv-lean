"""
Heuristic / geometry tests for ``hqiv_geometric_3sat_demo`` — **not** SAT correctness (that is brute force).

Goals:

1. **Invariants** — moiré cumulative variation monotone, threshold in range, BST indices sane, rapidity
   Lipschitz when φ·t ≥ 0, wrap outputs in ``[0,1)``.
2. **Falsification** — simple functions of patch scores are **not** reliable SAT classifiers; we assert
   high error rates so CI fails if someone mistakes these for a solver (or if labels leak).

Run: ``python3 scripts/test_hqiv_geometric_3sat_heuristics.py``
Pytest: ``pytest scripts/test_hqiv_geometric_3sat_heuristics.py -v``
"""

from __future__ import annotations

import importlib.util
import math
import random
import sys
from pathlib import Path
from typing import Callable

_DEMO = Path(__file__).resolve().parent / "hqiv_geometric_3sat_demo.py"
_spec = importlib.util.spec_from_file_location("hqiv_geometric_3sat_demo", _DEMO)
_demo = importlib.util.module_from_spec(_spec)
assert _spec.loader is not None
sys.modules["hqiv_geometric_3sat_demo"] = _demo
_spec.loader.exec_module(_demo)

def _patch_search_for_formula(fm: _demo.Formula3SAT) -> _demo.PatchSearchScore:
    M, _, _ = _demo.encode_formula_to_M(fm)
    k = _demo.omega_M_exact(fm)
    c = len(fm.clauses)
    n = _demo.patch_window_length(c)
    return _demo.patch_search_score_driven(M, k, c, n)


def _iter_all_benchmarks():
    for row in _demo.ALL_SAT_BENCHMARKS:
        yield row[0], row[1], row[2]


def test_heuristic_cum_nondecreasing_all_benchmarks() -> None:
    """Moiré cumulative |ΔS| must be monotone in j for every benchmark instance."""

    n_ok = 0
    for name, fm, _exp in _iter_all_benchmarks():
        ps = _patch_search_for_formula(fm)
        cum = ps.cum
        for j in range(1, len(cum)):
            assert cum[j] + 1e-12 >= cum[j - 1], f"{name}: cum[{j}] < cum[{j-1}]"
        n_ok += 1
    assert n_ok == len(_demo.ALL_SAT_BENCHMARKS)


def test_heuristic_threshold_within_total_all_benchmarks() -> None:
    """T = variation_threshold(M, total) stays in [0, total] when total > 0."""

    for name, fm, _exp in _iter_all_benchmarks():
        ps = _patch_search_for_formula(fm)
        total = ps.cum_total
        T = ps.threshold
        assert 0.0 <= T <= total + 1e-9 or total <= 0.0, f"{name}: threshold {T} vs total {total}"
        if total <= 0.0:
            assert T == 0.0, name


def test_heuristic_bst_indices_consistent_with_cum() -> None:
    """
    ``j_first_ge_threshold`` is first index with cum[j] >= T (when such j exists); ``j_last_below`` last
    with cum[j] < T when the right-BST predicate applies — spot-check against direct scan.
    """

    for name, fm, _exp in _iter_all_benchmarks():
        ps = _patch_search_for_formula(fm)
        n, cum, T = ps.n, ps.cum, ps.threshold
        if n <= 0:
            continue
        jf = ps.j_first_ge_threshold
        # Smallest j with cum[j] >= T, if any; else binary_search returns n-1 when pred never true.
        direct_first = next((j for j in range(n) if cum[j] >= T), None)
        if direct_first is not None:
            assert jf == direct_first, f"{name}: j_first {jf} != scan {direct_first}"
        else:
            assert all(cum[j] < T for j in range(n)), name
            assert jf == n - 1, name

        jl = ps.j_last_below_threshold
        direct_last = max((j for j in range(n) if cum[j] < T), default=-1)
        assert jl == direct_last, f"{name}: j_last {jl} != scan {direct_last}"


def test_heuristic_rapidity_lipschitz_random_stress() -> None:
    """sin ∘ polarAngle cumulative variation ≤ Δs when φ·t ≥ 0 (many random sizes)."""

    rng = random.Random(2026)
    for _ in range(200):
        n = rng.randint(4, 96)
        phi = rng.uniform(0.1, 2.0)
        t = rng.uniform(0.1, 2.0)
        r = _demo.lean_rapidity_bridge_report(phi, t, n)
        assert r["shell_parameter_monotone"] is True
        assert r["bound_ok"] is True, r


def test_heuristic_wrap_probe_unit_intervals() -> None:
    """rapidity_root_wrap_probe wraps stay in [0,1)."""

    p = _demo.rapidity_root_wrap_probe(
        1100570625,
        12,
        9,
        1.0,
        1.0,
        min_j_samples=16,
        max_rows=16,
        max_rows_hard_cap=64,
    )
    for row in p["rows"]:
        assert 0.0 <= row["wrap_u"] < 1.0
        for w in row["wraps"].values():
            assert 0.0 <= w < 1.0


def _misclassifications(
    rule: Callable[[_demo.PatchSearchScore, _demo.Formula3SAT], bool],
) -> tuple[int, list[str]]:
    wrong = 0
    names: list[str] = []
    for name, fm, exp_sat, _w, _note in _demo.ALL_SAT_BENCHMARKS:
        ps = _patch_search_for_formula(fm)
        guess = rule(ps, fm)
        if guess != exp_sat:
            wrong += 1
            if len(names) < 12:
                names.append(name)
    return wrong, names


def test_heuristic_naive_rules_misclassify_often() -> None:
    """
    Several **ad hoc** SAT guesses from patch statistics must err a lot vs brute-force labels.

    If this fails with "too few errors", some rule accidentally tracks SAT — worth investigating.
    If it fails with "too many", thresholds are wrong — but we use fixed rules independent of tuning.
    """

    rules: list[tuple[str, Callable[[_demo.PatchSearchScore, _demo.Formula3SAT], bool]]] = [
        ("guess_sat_if_j_first_strictly_before_mid", lambda ps, _: ps.j_first_ge_threshold < ps.n // 2),
        ("guess_sat_if_j_first_at_or_after_mid", lambda ps, _: ps.j_first_ge_threshold >= ps.n // 2),
        ("guess_sat_if_high_cum_total", lambda ps, _: ps.cum_total > 1.25),
        ("guess_sat_if_low_cum_total", lambda ps, _: ps.cum_total <= 1.25),
        ("guess_sat_if_large_slope_jump", lambda ps, _: ps.max_slope_jump_abs > 0.2),
        ("guess_sat_if_small_slope_jump", lambda ps, _: ps.max_slope_jump_abs <= 0.2),
    ]
    n_all = len(_demo.ALL_SAT_BENCHMARKS)
    # Loose floor: ad hoc features may correlate a bit by chance — aim to catch "almost perfect" guesses.
    min_wrong = max(5, int(0.10 * n_all))
    for rule_name, rule in rules:
        wrong, examples = _misclassifications(rule)
        assert wrong >= min_wrong, (
            f"{rule_name}: only {wrong}/{n_all} mismatches vs brute-force SAT "
            f"(expected >= {min_wrong} to show heuristic ≠ SAT). Examples: {examples}"
        )


def test_heuristic_fourier_peak_toy_finite() -> None:
    """Sanity: toy Fourier peak is finite for typical k,n."""

    for k in (1, 3, 12):
        for n in (8, 32):
            v = _demo.fourier_peak_toy(k, n)
            assert math.isfinite(v) and v >= 0.0


_ALL = (
    test_heuristic_cum_nondecreasing_all_benchmarks,
    test_heuristic_threshold_within_total_all_benchmarks,
    test_heuristic_bst_indices_consistent_with_cum,
    test_heuristic_rapidity_lipschitz_random_stress,
    test_heuristic_wrap_probe_unit_intervals,
    test_heuristic_naive_rules_misclassify_often,
    test_heuristic_fourier_peak_toy_finite,
)


if __name__ == "__main__":
    import time

    t0 = time.perf_counter()
    for fn in _ALL:
        fn()
    ms = (time.perf_counter() - t0) * 1000.0
    print(f"hqiv_geometric_3sat_heuristics: OK ({ms:.2f} ms total)")

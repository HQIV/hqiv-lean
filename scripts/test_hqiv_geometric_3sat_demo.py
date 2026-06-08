"""Regression tests for `hqiv_geometric_3sat_demo` (3-SAT encoding + Lean rapidity mirror).

Includes **golden** moiré checker outputs (known ``sat_by_checker`` bit patterns) — no trial division on ``M``.

Optional Ω cross-check (small ``M`` only): ``python3 scripts/test_hqiv_geometric_3sat_optional_omega_trial_div.py``

Run: ``python3 scripts/test_hqiv_geometric_3sat_demo.py`` (prints per-test and total wall time).

Pytest: ``.venv/bin/python -m pytest scripts/test_hqiv_geometric_3sat_demo.py -v --durations=0``
(``--durations=0`` lists timing for every test; omit for failures-only slowest list).
"""

from __future__ import annotations

import importlib.util
import itertools
import sys
import time
from pathlib import Path

_DEMO = Path(__file__).resolve().parent / "hqiv_geometric_3sat_demo.py"
_spec = importlib.util.spec_from_file_location("hqiv_geometric_3sat_demo", _DEMO)
_demo = importlib.util.module_from_spec(_spec)
assert _spec.loader is not None
sys.modules["hqiv_geometric_3sat_demo"] = _demo
_spec.loader.exec_module(_demo)


def test_lipschitz_bound_holds_sin_pullback_positive_rapidity() -> None:
    r = _demo.lean_rapidity_bridge_report(1.0, 1.0, 32)
    assert r["shell_parameter_monotone"] is True
    assert r["bound_ok"] is True
    assert r["max_cumulative_minus_K_delta_s"] <= 1e-7


def test_shell_not_monotone_when_phi_times_t_negative() -> None:
    r = _demo.lean_rapidity_bridge_report(1.0, -1.0, 16)
    assert r["shell_parameter_monotone"] is False


def test_delta_theta_prime_at_zero() -> None:
    assert abs(_demo.delta_theta_prime(0.0)) < 1e-15


def test_moire_phase_fraction_mpmath_large_M() -> None:
    """Previously overflowed float V8; :func:`moire_phase_fraction_from_M` must stay in [0,1)."""

    import random

    M = _demo.encode_formula_to_M(_demo.random_3sat_formula(5, 21, random.Random(1)))[0]
    u = _demo.moire_phase_fraction_from_M(M)
    assert 0.0 <= u < 1.0
    assert _demo.mp_dps_for_shell_M(M) >= 80


def test_rapidity_root_wrap_probe_ranges() -> None:
    p = _demo.rapidity_root_wrap_probe(221, 3, 12, 1.0, 1.0, min_j_samples=8, max_rows=8)
    assert p["M"] == 221
    assert p["rows_sampled"] == 8
    assert "trend_linear_slope_vs_j" in p
    assert "wrap_moduli_rad" in p
    for row in p["rows"]:
        assert 0.0 <= row["wrap_u"] < 1.0
        assert 0.0 <= row["blend_u_plus_root_frac"] < 1.0
        assert 0 <= row["slot8"] < 8
        assert 0.0 <= row["wrap_s_times_root_mod1"] < 1.0
        wraps = row["wraps"]
        for key in ("unit_2pi", "half_pi", "quarter_pi", "arity_theta_k", "mod_1"):
            assert 0.0 <= wraps[key] < 1.0
        blends = row["blends_root_frac"]
        for key in ("unit_2pi", "half_pi", "quarter_pi", "arity_theta_k", "mod_1"):
            assert 0.0 <= blends[key] < 1.0


def test_min_j_samples_extends_small_patch() -> None:
    """Score patch n=8 but min_j=32 ⇒ 32 rapidity samples for trends."""

    p = _demo.rapidity_root_wrap_probe(100, 2, 8, 1.0, 1.0, min_j_samples=32, max_rows_hard_cap=500)
    assert p["rows_sampled"] == 32
    assert p["j_span_effective"] == 32


def test_predictive_patch_prune_trace_has_residue_filtered_subset() -> None:
    import math

    ps = _demo.patch_search_score_driven(221, 3, 2, 12)
    pr = _demo.predictive_patch_prune_trace(
        ps,
        3,
        shell_m=221,
        residue_mod=5,
        allowed_residues=(0, 3),
        merge_score_landmarks=False,
    )
    assert pr["residue_mod"] == 5
    cap = min(12, max(4, math.isqrt(221)))
    assert pr["visit_cap_walk"] == cap
    assert pr["visit_count"] <= cap
    for j in pr["walk_residue_snapped_j"]:
        assert (j % 5) in {0, 3}
    assert pr["visit_count"] == len(pr["visited_j"])
    assert set(pr["walk_residue_snapped_j"]).issubset(set(pr["kept_j"]))


def test_first_n_primes_skips_two() -> None:
    assert _demo.first_n_primes(5) == [3, 5, 7, 11, 13]


def test_trial_formulas_encode_without_factorization_smoke() -> None:
    """All built-in trials: literal-sum Ω and brute-force SAT."""

    assert len(_demo.TRIAL_FORMULAS) >= 7
    for _title, fm in _demo.TRIAL_FORMULAS:
        M, _primes, _cprods = _demo.encode_formula_to_M(fm)
        k = _demo.omega_M_exact(fm)
        assert k >= 1
        assert M >= 3
        sat, _w = _demo.is_satisfiable_bruteforce(fm)
        assert isinstance(sat, bool)


def test_run_formula_json_uses_encoding_omega_without_factorization_check() -> None:
    """End-to-end record: default path skips trial division on M; JSON flags match."""

    results: list[dict] = []
    tiny = _demo.Formula3SAT(
        num_vars=1,
        clauses=((_demo.Literal(0, False), _demo.Literal(0, False), _demo.Literal(0, False)),),
    )
    _demo.run_formula(
        "tiny SAT clause",
        tiny,
        json_out=True,
        results=results,
        wrap_min_j=8,
        wrap_max_rows=12,
        wrap_hard_cap=32,
        verify_omega_factorization=False,
    )
    assert len(results) == 1
    r = results[0]
    assert r["verify_omega_trial_div"] is False
    assert r["omega_literal_sum"] == 3
    assert "omega_trial_div_count_on_M" not in r


def test_all_sat_benchmarks_bruteforce_matches_labels() -> None:
    """All of :data:`ALL_SAT_BENCHMARKS`: brute force must match stored label; optional exact witness."""

    for name, fm, exp_sat, w_exp, _note in _demo.ALL_SAT_BENCHMARKS:
        sat, w = _demo.is_satisfiable_bruteforce(fm)
        assert sat == exp_sat, name
        if w_exp is not None:
            assert w == w_exp, name
        elif sat:
            assert w is not None
            assert all(_demo.eval_clause(c, w) for c in fm.clauses), name


def test_bruteforce_sat_matches_expectations() -> None:
    assert _demo.is_satisfiable_bruteforce(_demo.EXAMPLE)[0] is True

    unsat = _demo.Formula3SAT(
        num_vars=1,
        clauses=(
            (_demo.Literal(0, False), _demo.Literal(0, False), _demo.Literal(0, False)),
            (_demo.Literal(0, True), _demo.Literal(0, True), _demo.Literal(0, True)),
        ),
    )
    ok, w = _demo.is_satisfiable_bruteforce(unsat)
    assert ok is False and w is None

    sat_one = _demo.Formula3SAT(
        num_vars=1,
        clauses=((_demo.Literal(0, False), _demo.Literal(0, False), _demo.Literal(0, False)),),
    )
    ok, w = _demo.is_satisfiable_bruteforce(sat_one)
    # Three positive literals x ∨ x ∨ x — satisfied by x = True.
    assert ok is True and w is not None and w == (True,)


def test_binary_search_mod_predicate_matches_direct() -> None:
    for M, n in [(10007, 16), (221, 12), (1, 5)]:
        j_exp = _demo.toy_transition_mod(M, n)
        j_got, _ = _demo.binary_search_mod_predicate(M, n)
        assert j_got == j_exp


def test_assignment_from_patch_matches_bruteforce_order() -> None:
    for nv in (1, 2, 3):
        for j, bits in enumerate(itertools.product((False, True), repeat=nv)):
            assert _demo.assignment_from_patch_index(j, nv) == tuple(bits)


def test_moire_checker_finds_sat_on_patch_when_small() -> None:
    f = _demo.EXAMPLE
    M, _, _ = _demo.encode_formula_to_M(f)
    k = _demo.omega_M_exact(f)
    c = len(f.clauses)
    n = _demo.patch_window_length(c)
    tr = _demo.moire_patch_sat_checker_trace(f, M, k, c, n)
    sat_bf, w = _demo.is_satisfiable_bruteforce(f)
    if sat_bf and w is not None:
        assert tr["count_patch_steps_sat"] >= 1


def test_golden_moire_checker_unsat_x_and_not_x() -> None:
    """Hand-known: UNSAT (x) ∧ (¬x) — no assignment works; every patch j fails clause eval."""

    fm = _demo.Formula3SAT(
        num_vars=1,
        clauses=(
            (_demo.Literal(0, False), _demo.Literal(0, False), _demo.Literal(0, False)),
            (_demo.Literal(0, True), _demo.Literal(0, True), _demo.Literal(0, True)),
        ),
    )
    M, _, _ = _demo.encode_formula_to_M(fm)
    k = _demo.omega_M_exact(fm)
    assert k == 9
    c = len(fm.clauses)
    n = _demo.patch_window_length(c)
    assert n == 8
    tr = _demo.moire_patch_sat_checker_trace(fm, M, k, c, n)
    assert tr["count_patch_steps_sat"] == 0
    assert tr["first_j_with_sat_assignment"] is None
    assert [s["sat_by_checker"] for s in tr["steps"]] == [False] * 8


def test_golden_moire_checker_sat_single_positive_clause() -> None:
    """Hand-known: one clause (x ∨ x ∨ x); assignment alternates F,T on j — SAT iff j odd."""

    fm = _demo.Formula3SAT(
        num_vars=1,
        clauses=((_demo.Literal(0, False), _demo.Literal(0, False), _demo.Literal(0, False)),),
    )
    M, _, _ = _demo.encode_formula_to_M(fm)
    k = _demo.omega_M_exact(fm)
    assert k == 3
    n = _demo.patch_window_length(len(fm.clauses))
    tr = _demo.moire_patch_sat_checker_trace(fm, M, k, len(fm.clauses), n)
    assert [s["sat_by_checker"] for s in tr["steps"]] == [False, True, False, True, False, True, False, True]
    assert tr["count_patch_steps_sat"] == 4
    assert tr["first_j_with_sat_assignment"] == 1


def test_literal_and_clause_products() -> None:
    primes = _demo.first_n_primes(2)
    c = (
        _demo.Literal(0, False),
        _demo.Literal(1, True),
        _demo.Literal(0, False),
    )
    assert _demo.clause_product(c, primes) == primes[0] * (primes[1] ** 2) * primes[0]


def test_moire_sine_factor_matches_sin_of_phase_plus_theta() -> None:
    """Target 0a: sin(φ+θj) = Im(exp(i(φ+θj))) — same as first factor of moire_score_samples before cos mod."""

    import math
    import random

    rng = random.Random(0)
    for _ in range(40):
        M = rng.randint(2, 50_000)
        k_enc = 1 + rng.randint(0, 30)
        j = rng.randint(0, 200)
        phase = _demo.moire_phase_fraction_from_M(M) * (2.0 * math.pi)
        theta = math.pi / (2.0 * max(k_enc, 1))
        expected = math.sin(phase + theta * j)
        got = _demo.moire_sine_factor_without_modulation(M, k_enc, j)
        assert abs(got - expected) < 1e-9, (M, k_enc, j, got, expected)


def test_fourier_peak_correlation_matches_lean_phasor_sum() -> None:
    """Numeric peak sum equals explicit sum of w·exp(iθj)·κ (Target 0a mirror)."""

    import cmath
    import math

    k_enc = 3
    n = 5
    w = [1 + 0j] * n
    kappa = [1 + 0j] * n
    z = _demo.fourier_patch_peak_correlation_complex(k_enc, n, w, kappa)
    theta = math.pi / (2.0 * k_enc)
    geom = sum(cmath.exp(1j * theta * j) for j in range(n))
    assert abs(z - geom) < 1e-9


def test_kernel_harmonic_matches_lean_character() -> None:
    import cmath
    import math

    n = 8
    k = 2
    for j in range(n):
        u = _demo.kernel_harmonic_character_j(n, k, j)
        v = cmath.exp(2j * math.pi * k * j / n)
        assert abs(u - v) < 1e-15


_ALL_TESTS = (
    test_lipschitz_bound_holds_sin_pullback_positive_rapidity,
    test_shell_not_monotone_when_phi_times_t_negative,
    test_delta_theta_prime_at_zero,
    test_moire_phase_fraction_mpmath_large_M,
    test_rapidity_root_wrap_probe_ranges,
    test_min_j_samples_extends_small_patch,
    test_predictive_patch_prune_trace_has_residue_filtered_subset,
    test_first_n_primes_skips_two,
    test_trial_formulas_encode_without_factorization_smoke,
    test_run_formula_json_uses_encoding_omega_without_factorization_check,
    test_all_sat_benchmarks_bruteforce_matches_labels,
    test_bruteforce_sat_matches_expectations,
    test_binary_search_mod_predicate_matches_direct,
    test_assignment_from_patch_matches_bruteforce_order,
    test_moire_checker_finds_sat_on_patch_when_small,
    test_golden_moire_checker_unsat_x_and_not_x,
    test_golden_moire_checker_sat_single_positive_clause,
    test_literal_and_clause_products,
    test_moire_sine_factor_matches_sin_of_phase_plus_theta,
    test_fourier_peak_correlation_matches_lean_phasor_sum,
    test_kernel_harmonic_matches_lean_character,
)


if __name__ == "__main__":
    t_session = time.perf_counter()
    timings: list[tuple[str, float]] = []
    for fn in _ALL_TESTS:
        t0 = time.perf_counter()
        fn()
        timings.append((fn.__name__, (time.perf_counter() - t0) * 1000.0))
    total_ms = (time.perf_counter() - t_session) * 1000.0
    print("hqiv_geometric_3sat_demo tests: OK")
    print("timing (wall, ms):")
    for name, ms in timings:
        print(f"  {ms:9.3f}  {name}")
    print(f"  {total_ms:9.3f}  TOTAL")

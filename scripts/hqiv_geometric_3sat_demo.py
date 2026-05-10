#!/usr/bin/env python3
"""
HQIV geometric 3SAT pipeline — encoding + **score-driven patch search** (demo).

**What this is *not* (common confusion)**

- **Deciding SAT from geometry:** satisfiability in the output is computed **only** by exhaustive
  brute force over assignments (:func:`is_satisfiable_bruteforce`). The moiré score, ``V₈``, rapidity
  bridge, etc. are **not** a sound SAT solver; they are exploratory diagnostics / Lean numeric mirrors.
- **“Factoring everything”:** the demo does **not** run an integer factorization algorithm to split
  ``M`` into primes. **Ω(M)** (total prime factor count with multiplicity) is **computed from the
  formula** by summing per-literal contributions — no factorization of ``M`` required. The optional flag
  ``--verify-omega-factorization`` runs a separate **prime-factor counting** pass on ``M`` only as a
  regression check that this sum matches arithmetic ``Ω(M)``; that still is not “factoring ``M``” in
  the sense of finding divisors for cryptography.

- 3SAT → M (prime per variable; literal products; clause products).
- **Primes are fixed to 3,5,7,…** (smallest prime **3** only): embedding **2** hits poles and wrecks
  the analytic lens; there is no ``--min-prime`` switch.
- **k = Ω(M) exact:** sum over every literal of 1 (positive p_i) or 2 (negative p_i²); this is the
  arithmetic ``Ω`` with multiplicity, computable **without factoring M**. The demo uses this encoding
  Ω by default; use ``--verify-omega-factorization`` to cross-check against ``Ω(M)`` from trial division.
- θ = π/(2k) for the toy moiré score S(j). The phase uses ``V₈(√M) mod 1``; ``float`` is used when safe,
  otherwise ``mpmath`` with :func:`mp_dps_for_shell_M` so huge encoded ``M`` still work.
- **Search:** monotone binary search for the **first** j with cumulative |ΔS| ≥ T(M); a **second**
  search from the **right** finds the **last** j below threshold (patch boundaries bracket the arc).
  Discrete **slopes** ΔS and **slope jumps** (second differences) are reported for moiré analysis
  (formal bounds: Gaussian / triangle-inequality lens — not proved here).
- **Lean rapidity bridge (numeric):** ``δθ'(x)=arctan(x)·(π/2)``, ``s(m)=φ·t·δθ'(m)`` as in
  ``ModifiedMaxwell`` / ``SpatialSliceRapidityScaffold``; with ``S(j)=sin(s(j))`` (1-Lipschitz), each run
  checks ``shell_parameter_monotone`` (for ``φ·t≥0``) and ``cum[j] ≤ s(j)−s(0)`` vs
  ``moireCumulativeAbsVariation_le_K_mul_sub_endpoints`` (``K=1``).
- **Rapidity × root-scale toy (heuristic):** ``rapidity_root_wrap_probe`` samples many patch indices
  (default: full ``n_patch`` up to a cap), wraps ``s(j)=φ·t·δθ'(j)`` by several moduli (``2π``, ``π``,
  ``π/2``, ``π/(2k)``, ``1``), blends with ``frac(M^{1/k})``, and reports **linear slope vs. j** per
  series to surface trends — for intuition only.
- **SAT truth:** brute force (only reliable **global** solver here).
- **Per patch step:** each moiré index ``j`` is paired with a **deterministic assignment** (same order as
  :func:`is_satisfiable_bruteforce` / ``itertools.product``) and run through the **cheap clause checker**
  :func:`eval_formula` — polynomial-time, no factoring. This ties every score change to Boolean evaluation.

Run:
  python3 scripts/hqiv_geometric_3sat_demo.py
  python3 scripts/hqiv_geometric_3sat_demo.py --json
  python3 scripts/hqiv_geometric_3sat_demo.py --mod-demo   # M mod n binary-search sanity only
"""

from __future__ import annotations

import argparse
import cmath
import itertools
import json
import math
import random
import sys
from contextlib import contextmanager
from dataclasses import dataclass, asdict
from typing import Any, Callable

import mpmath as mp


# --- Octonion R^8 proxies -------------------------------------------------------------


def continuous_ball_volume8(r: float) -> float:
    return (math.pi**4 / 24.0) * (r**8)


def continuous_sphere_area7(r: float) -> float:
    return (math.pi**4 / 3.0) * (r**7)


def mp_dps_for_shell_M(M: int) -> int:
    """
    **Decimal** precision (``mpmath`` ``mp.mp.dps``) for continuum quantities derived from ``M``.

    Scales with ``M.bit_length()`` because ``r = √M`` and ``V₈(r) ∝ r⁸ ∝ M⁴`` — we reserve roughly
    four times as many **decimal** digits as bits in ``M`` (capped) so ``mpf`` work is not silently
    truncated. This is **not** IEEE float; only the shell/moiré real pipeline uses it.

    ``M`` itself stays a Python ``int``; we never round the encoding integer to float.
    """

    if M < 2:
        return 80
    b = M.bit_length()
    return max(80, min(10000, int(4.0 * b * math.log10(2.0) + 120)))


def mp_nstr_display_digits(M: int) -> int:
    """Digits for :func:`mp.nstr` shell displays — tied to :func:`mp_dps_for_shell_M`, not a fixed 10."""

    d = mp_dps_for_shell_M(M)
    return max(10, min(60, d // 150 + 12))


@contextmanager
def mp_shell_precision(M: int):
    """Temporarily set ``mpmath`` ``dps`` for shell radii / volumes derived from ``M``."""

    dps = mp_dps_for_shell_M(M)
    ctx = mp.mp
    old = ctx.dps
    ctx.dps = dps
    try:
        yield dps
    finally:
        ctx.dps = old


def moire_phase_fraction_from_M(M: int) -> float:
    """
    Fractional part of ``V₈(r)`` with ``r = √M`` in ``[0,1)`` — drives the moiré phase.

    Fast path: IEEE ``float`` when ``float(M)`` and ``V₈`` are finite. Large ``M``: ``mpmath``
    ``mp.mpf`` with :func:`mp_dps_for_shell_M` (precision ∝ ``M.bit_length()``). Return value is still
    a Python ``float`` in ``[0,1)`` for downstream ``math.sin`` / scores.
    """

    if M < 2:
        return 0.0
    try:
        rf = math.sqrt(float(M))
        if math.isfinite(rf):
            v8 = continuous_ball_volume8(rf)
            if math.isfinite(v8):
                x = v8 % 1.0
                return x + 1.0 if x < 0.0 else x
    except OverflowError:
        pass
    with mp_shell_precision(M):
        r = mp.sqrt(mp.mpf(M))
        v8 = (mp.pi**4 / 24) * (r**8)
        frac = mp.fmod(v8, 1)
        return float(frac)


def shell_volume8_area7_strings(M: int) -> tuple[str, str]:
    """
    Printable ``V₈(√M)`` and ``A₇(√M)`` (continuous proxies).

    Same rule as :func:`moire_phase_fraction_from_M`: IEEE when safe, else ``mp.mpf`` with
    :func:`mp_dps_for_shell_M` / :func:`mp_nstr_display_digits`.
    """

    if M < 2:
        return "0", "0"
    try:
        rf = math.sqrt(float(M))
        if math.isfinite(rf):
            v8 = continuous_ball_volume8(rf)
            a7 = continuous_sphere_area7(rf)
            if math.isfinite(v8) and math.isfinite(a7):
                return f"{v8:.6e}", f"{a7:.6e}"
    except OverflowError:
        pass
    nd = mp_nstr_display_digits(M)
    with mp_shell_precision(M):
        r = mp.sqrt(mp.mpf(M))
        v8 = (mp.pi**4 / 24) * (r**8)
        a7 = (mp.pi**4 / 3) * (r**7)
        return mp.nstr(v8, nd), mp.nstr(a7, nd)


# --- 3SAT ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Literal:
    var: int
    neg: bool


@dataclass(frozen=True)
class Formula3SAT:
    num_vars: int
    clauses: tuple[tuple[Literal, Literal, Literal], ...]


@dataclass(frozen=True)
class FormulaCNF:
    """
    Conjunctive normal form: each clause is a disjunction of any finite number of literals
    (same prime encoding / Ω story as 3-SAT — **clause width is not fixed**).
    """

    num_vars: int
    clauses: tuple[tuple[Literal, ...], ...]


def formula3sat_to_cnf(f: Formula3SAT) -> FormulaCNF:
    """Embed 3-SAT in general CNF (three literals per clause)."""

    return FormulaCNF(num_vars=f.num_vars, clauses=tuple(tuple(t) for t in f.clauses))


def as_cnf(formula: Formula3SAT | FormulaCNF) -> FormulaCNF:
    if isinstance(formula, FormulaCNF):
        return formula
    return formula3sat_to_cnf(formula)


def _is_prime(x: int) -> bool:
    """Trial division (must test 2 separately — not only primes in the output list)."""

    if x < 2:
        return False
    if x % 2 == 0:
        return x == 2
    lim = int(math.sqrt(x)) + 1
    d = 3
    while d <= lim:
        if x % d == 0:
            return False
        d += 2
    return True


def first_n_primes(n: int) -> list[int]:
    """
    First ``n`` primes with each prime ≥ **3** (odd alphabet only).

    Prime **2** is intentionally excluded: it introduces 2-adic / pole artifacts that distort the toy
    geometry and analytic checks even when everything else is well-behaved.
    """

    if n <= 0:
        return []
    min_prime = 3
    primes: list[int] = []
    x = min_prime
    while len(primes) < n:
        if _is_prime(x) and x >= min_prime:
            primes.append(x)
        x += 1
    return primes


def literal_value(lit: Literal, primes: list[int]) -> int:
    p = primes[lit.var]
    return p * p if lit.neg else p


def clause_product(clause: tuple[Literal, ...], primes: list[int]) -> int:
    p = 1
    for lit in clause:
        p *= literal_value(lit, primes)
    return p


def literal_omega(lit: Literal) -> int:
    """Ω contribution of one literal in the encoding: p → 1, p² → 2."""

    return 2 if lit.neg else 1


def omega_big_omega_factorization(n: int) -> int:
    """Arithmetic Ω(n): total prime factors with multiplicity (for sanity-checking ``M``)."""

    if n < 2:
        return 0
    x, s, d = n, 0, 2
    while d * d <= x:
        while x % d == 0:
            s += 1
            x //= d
        d += 1 if d == 2 else 2
    if x > 1:
        s += 1
    return s


def omega_M_exact(formula: Formula3SAT | FormulaCNF) -> int:
    """
    Exact **Ω(M)** for the prime-product encoding — **no factoring of M** required.

    Sum over every literal occurrence: **1** if positive (factor ``p_i``), **2** if negative
    (``p_i²``). For ``M = ∏_c (clause product)_c``, this equals the usual arithmetic
    ``Ω(M)`` (multiplicative over coprime pieces; exponents add across clauses sharing variables).

    This is the **only** ``k`` used for ``θ = π/(2k)`` in this demo (not ``3c``, not an
    independent factorization pass).
    """

    f = as_cnf(formula)
    s = 0
    for cl in f.clauses:
        for lit in cl:
            s += literal_omega(lit)
    return max(s, 1)


def omega_total_from_encoding(formula: Formula3SAT | FormulaCNF) -> int:
    """Backward-compatible name for :func:`omega_M_exact`."""

    return omega_M_exact(formula)


def omega_integer_big_omega(n: int) -> int:
    """Backward-compatible name for :func:`omega_big_omega_factorization`."""

    return omega_big_omega_factorization(n)


def assert_omega_exact_matches_factorization(M: int, formula: Formula3SAT | FormulaCNF) -> None:
    """Regression guard: encoding Ω must agree with factorization Ω(M)."""

    enc = omega_M_exact(formula)
    fac = omega_big_omega_factorization(M)
    if enc != fac:
        raise ValueError(
            f"Ω mismatch: encoding sum = {enc}, factorization Ω({M}) = {fac}. "
            "Check encode_formula_to_M / literal_omega."
        )


def encode_formula_to_M(formula: Formula3SAT | FormulaCNF) -> tuple[int, list[int], tuple[int, ...]]:
    """
    Exact prime-product encoding: ``M = ∏_c (∏_{ℓ ∈ c} enc(ℓ))`` using Python ``int`` (arbitrary precision).

    Very large CNFs yield very large ``M``; :func:`moire_phase_fraction_from_M` and shell strings use
    ``mpmath`` when IEEE ``float`` cannot represent ``√M`` or ``V₈``.
    """

    f = as_cnf(formula)
    if f.num_vars < 1:
        raise ValueError("need at least one variable")
    primes = first_n_primes(f.num_vars)
    cprods: list[int] = []
    for cl in f.clauses:
        cprods.append(clause_product(cl, primes))
    acc = 1
    for cp in cprods:
        acc *= cp
    return acc, primes, tuple(cprods)


def eval_clause(clause: tuple[Literal, ...], assignment: tuple[bool, ...]) -> bool:
    def lit_ok(lit: Literal) -> bool:
        v = assignment[lit.var]
        return not v if lit.neg else v

    if len(clause) == 0:
        return False
    return any(lit_ok(lit) for lit in clause)


def eval_formula(formula: Formula3SAT | FormulaCNF, assignment: tuple[bool, ...]) -> bool:
    """Cheap checker: all clauses satisfied (polynomial in formula size)."""

    f = as_cnf(formula)
    return all(eval_clause(c, assignment) for c in f.clauses)


def assignment_from_patch_index(j: int, num_vars: int) -> tuple[bool, ...]:
    """
    Map patch index ``j`` to a full assignment, **same iteration order** as
    ``itertools.product((False, True), repeat=num_vars)`` (last variable toggles fastest).

    ``j`` wraps modulo ``2**num_vars`` so long patches revisit assignments cyclically.
    """

    if num_vars < 1:
        return ()
    r = j % (2**num_vars)
    out = [False] * num_vars
    for i in range(num_vars):
        out[num_vars - 1 - i] = bool((r >> i) & 1)
    return tuple(out)


def eval_sat_at_patch_index(formula: Formula3SAT | FormulaCNF, j: int) -> bool:
    """Whether :func:`eval_formula` holds for the assignment at patch index ``j`` (via :func:`assignment_from_patch_index`)."""

    f = as_cnf(formula)
    if f.num_vars < 1:
        return False
    return eval_formula(f, assignment_from_patch_index(j, f.num_vars))


def moire_patch_sat_checker_trace(
    formula: Formula3SAT | FormulaCNF,
    M: int,
    k_enc: int,
    num_clauses: int,
    n_patch: int,
) -> dict[str, Any]:
    """
    For each moiré sample index ``j``, run :func:`eval_formula` on :func:`assignment_from_patch_index`
    — **no integer factorization**, only clause evaluation alongside ``S(j)``.
    """

    f = as_cnf(formula)
    samples = moire_score_samples(M, k_enc, num_clauses, n=n_patch)
    nv = f.num_vars
    steps: list[dict[str, Any]] = []
    first_j_sat: int | None = None
    count_sat = 0
    for j in range(len(samples)):
        assign = assignment_from_patch_index(j, nv)
        sat_j = eval_formula(f, assign)
        if sat_j:
            count_sat += 1
            if first_j_sat is None:
                first_j_sat = j
        steps.append(
            {
                "j": j,
                "S": samples[j],
                "assignment": list(assign),
                "sat_by_checker": sat_j,
            }
        )
    first_wit = list(steps[first_j_sat]["assignment"]) if first_j_sat is not None else None
    return {
        "steps": steps,
        "count_patch_steps_sat": count_sat,
        "first_j_with_sat_assignment": first_j_sat,
        "first_sat_assignment_on_patch": first_wit,
    }


def is_satisfiable_bruteforce(formula: Formula3SAT | FormulaCNF) -> tuple[bool, tuple[bool, ...] | None]:
    f = as_cnf(formula)
    if any(len(c) == 0 for c in f.clauses):
        return False, None
    n = f.num_vars
    for bits in itertools.product((False, True), repeat=n):
        if eval_formula(f, bits):
            return True, bits
    return False, None


# --- Moiré score + variation ----------------------------------------------------------


def patch_window_length(num_clauses: int, *, min_len: int = 8) -> int:
    return max(min_len, 3 * num_clauses)


def moire_score_samples(
    M: int,
    k_axis: int,
    num_clauses: int,
    *,
    n: int | None = None,
) -> list[float]:
    n = n if n is not None else patch_window_length(num_clauses)
    phase = moire_phase_fraction_from_M(M) * (2.0 * math.pi)
    theta = math.pi / (2.0 * max(k_axis, 1))
    out: list[float] = []
    for j in range(n):
        t = theta * j
        out.append(math.sin(phase + t) * math.cos((M % (j + 7)) / float(j + 7)))
    return out


# --- Lean `fourierPatchPeakCorrelation` mirror (AGENTS/archive/FT_PATCH_CLOSED_TARGET 0a) ---


def intrinsic_axis_angle_rad(k_enc: int) -> float:
    """Lean `Hqiv.Algebra.axisAngle k hk` = `π / (2 * k)` for `k ≥ 1` (use `max(k_enc,1)`)."""

    return math.pi / (2.0 * max(k_enc, 1))


def intrinsic_shell_phasor_j(k_enc: int, j: int) -> complex:
    """
    One factor of the peak sum: `exp(i · axisAngle(k) · j)` — matches
    `Complex.exp (I * (intrinsicShellAxisAngle … * j))` when `Ω m = k` (`OctonionSphereFourierPatch`).
    """

    return cmath.exp(1j * intrinsic_axis_angle_rad(k_enc) * j)


def kernel_harmonic_character_j(n: int, k: int, j: int) -> complex:
    """Lean `KernelIsHarmonic`: `κ j = exp(2π i k j / n)` on `Fin n`."""

    return cmath.exp(2j * math.pi * k * j / n)


def fourier_patch_peak_correlation_complex(
    k_enc: int,
    n: int,
    w: list[complex],
    kappa: list[complex],
) -> complex:
    """
    Numeric mirror of Lean ``fourierPatchPeakCorrelation`` (complex sum, same axis as
    ``fourierPatchPeakCorrelation_eq_axisAngle`` when ``Ω m = k_enc``).

    This is **not** the toy ``moire_score_samples`` (which multiplies by an extra ``cos`` modulation);
    it is the named object from the formal layer for apples-to-apples checks.
    """

    if len(w) != n or len(kappa) != n:
        raise ValueError("w and kappa must have length n")
    return sum(w[j] * intrinsic_shell_phasor_j(k_enc, j) * kappa[j] for j in range(n))


def moire_combined_phasor(M: int, k_enc: int, j: int) -> complex:
    """
    Combined phasor ``exp(i · (φ + θ j))`` with ``φ = 2π · {V₈(√M)}`` and ``θ = π/(2 k_enc)``.

    Then ``moire_combined_phasor(M,k,j).imag == sin(φ + θ j)`` — the **first** factor of each
    ``moire_score_samples`` term **before** the ``cos((M mod (j+7))/(j+7))`` modulation.
    """

    phi = moire_phase_fraction_from_M(M) * (2.0 * math.pi)
    t = intrinsic_axis_angle_rad(k_enc) * j
    return cmath.exp(1j * (phi + t))


def moire_sine_factor_without_modulation(M: int, k_enc: int, j: int) -> float:
    """``sin(φ + θ j)`` = ``Im`` of :func:`moire_combined_phasor` — aligns the toy sine with one complex phasor."""

    return moire_combined_phasor(M, k_enc, j).imag


def cumulative_abs_variation(samples: list[float]) -> list[float]:
    """cum[j] = ∑_{i=0}^{j-1} |S[i+1]−S[i]|; non-decreasing in j."""

    n = len(samples)
    if n == 0:
        return []
    cum = [0.0] * n
    for j in range(1, n):
        cum[j] = cum[j - 1] + abs(samples[j] - samples[j - 1])
    return cum


# --- Lean `Hqiv.Archive.Geometry.RapidityArcPatchBridge` / `ModifiedMaxwell` mirror -------


def horizon_quarter_period() -> float:
    """Lean: `Hqiv.Physics.horizonQuarterPeriod` = `twoPi/4` = `π/2` (`horizonQuarterPeriod_eq_pi_div_two`)."""

    return math.pi / 2.0


def delta_theta_prime(e_prime: float) -> float:
    """
    Lean: `Hqiv.Physics.delta_theta_prime` — tipping angle δθ′(E′) = arctan(E′) · (quarter period).

    The polar-angle scaffold evaluates this at **shell coordinate** `(m : ℝ)` for `m : ℕ`.
    """

    return math.atan(e_prime) * horizon_quarter_period()


def polar_angle_from_rapidity(phi: float, t: float, m: int) -> float:
    """Lean: `Hqiv.Geometry.polarAngleFromRapidity φ t m` = `φ * t * delta_theta_prime (m : ℝ)`."""

    return phi * t * delta_theta_prime(float(m))


def lean_pullback_sin_scores(
    phi: float,
    t: float,
    n: int,
) -> tuple[list[float], list[float]]:
    """
    Discrete score `S(j) = sin(s(j))` with `s(j) = polar_angle_from_rapidity(φ,t,j)`.

    `sin` is 1-Lipschitz on ℝ, so this matches `scoreFromPullback` + `LipschitzWith 1 Real.sin`
    in the formal bound `moireCumulativeAbsVariation_le_K_mul_sub_endpoints` (K = 1).
    """

    s_vals = [polar_angle_from_rapidity(phi, t, j) for j in range(n)]
    samples = [math.sin(sv) for sv in s_vals]
    return samples, s_vals


def shell_parameter_monotone_nondecreasing(s_vals: list[float], *, eps: float = 1e-12) -> bool:
    """`IdxMonotone` + identity indexing ⇒ `s(j)` lifts shell order; check `s[j] ≤ s[j+1]`."""

    return all(s_vals[j + 1] + eps >= s_vals[j] for j in range(len(s_vals) - 1))


def lipschitz_bound_violation_max(
    cum: list[float],
    s_vals: list[float],
    *,
    K: float = 1.0,
    eps: float = 1e-9,
) -> tuple[float, list[tuple[int, float, float]]]:
    """
    Return (max_j cum[j] − K·(s(j)−s(0)), list of (j, cum[j], rhs) where violation > eps).

    Theorem target: `cum[j] ≤ K * (s[j] - s[0])` for monotone `s` and `K`-Lipschitz pullback.
    """

    if not cum or not s_vals or len(cum) != len(s_vals):
        return 0.0, []
    s0 = s_vals[0]
    worst = 0.0
    bad: list[tuple[int, float, float]] = []
    for j in range(len(cum)):
        rhs = K * (s_vals[j] - s0)
        gap = cum[j] - rhs
        if gap > worst:
            worst = gap
        if gap > eps:
            bad.append((j, cum[j], rhs))
    return worst, bad


def lean_rapidity_bridge_report(
    phi: float,
    t: float,
    n: int,
) -> dict[str, Any]:
    """Single JSON-serializable dict: monotonicity + Lipschitz cumulative bound check."""

    samples, s_vals = lean_pullback_sin_scores(phi, t, n)
    cum = cumulative_abs_variation(samples)
    mono_ok = shell_parameter_monotone_nondecreasing(s_vals)
    max_gap, violations = lipschitz_bound_violation_max(cum, s_vals, K=1.0)
    return {
        "phi": phi,
        "t": t,
        "phi_times_t": phi * t,
        "shell_s0": s_vals[0] if s_vals else 0.0,
        "shell_s_last": s_vals[-1] if s_vals else 0.0,
        "shell_parameter_monotone": mono_ok,
        "lipschitz_K": 1.0,
        "max_cumulative_minus_K_delta_s": max_gap,
        "bound_violations_strict": [(v[0], v[1], v[2]) for v in violations[:8]],
        "bound_ok": len(violations) == 0,
    }


def _wrap_norm_rad(s: float, mod_rad: float) -> float:
    """``(s mod mod_rad) / mod_rad`` in ``[0,1)`` for ``mod_rad > 0``."""

    m = float(mod_rad)
    if m <= 0.0:
        return 0.0
    return (s % m) / m


def _linear_slope_vs_j(ys: list[float]) -> float:
    """Least-squares slope of ``y[j]`` vs ``j`` for ``j = 0 … n−1``."""

    n = len(ys)
    if n < 2:
        return 0.0
    sx = n * (n - 1) / 2.0
    sxx = (n - 1) * n * (2 * n - 1) / 6.0
    sy = sum(ys)
    sxy = sum(j * ys[j] for j in range(n))
    den = n * sxx - sx * sx
    if abs(den) < 1e-30:
        return 0.0
    return (n * sxy - sx * sy) / den


def _slope_dict(prefix: str, keys: list[str], series: dict[str, list[float]]) -> dict[str, float]:
    out: dict[str, float] = {}
    for k in keys:
        ys = series.get(k)
        if ys is None:
            continue
        out[f"{prefix}{k}"] = _linear_slope_vs_j(ys)
    return out


def rapidity_root_wrap_probe(
    M: int,
    k_enc: int,
    n_patch: int,
    phi: float,
    t: float,
    *,
    min_j_samples: int = 64,
    max_rows: int | None = None,
    max_rows_hard_cap: int = 2048,
) -> dict[str, Any]:
    """
    Heuristic toy: mix **rapidity** on patch indices with **M^{1/k}** (peel ``⌊m^{1/k}⌋`` spirit).

    **Sampling:** evaluates ``s(j)`` for ``j = 0 … J−1`` with ``J = min(max(n_patch, min_j_samples), …)`` so
    small 3SAT patches still get enough points for trend fits. Upper limit: ``max_rows`` (if set) and
    ``max_rows_hard_cap``.

    **Wraps** (each normalized to ``[0,1)``): ``s(j) mod L`` divided by ``L`` for

    - ``unit_2pi`` — full turn;
    - ``half_pi`` — ``π``;
    - ``quarter_pi`` — ``π/2`` (horizon quarter period scale);
    - ``arity_theta_k`` — ``π/(2k)`` (toy moiré θ);
    - ``mod_1`` — ``s mod 1`` (dimensionless strip).

    **Blends:** ``(wrap + frac(M^{1/k})) mod 1`` for each wrap name.

    **Trends:** ``trend_linear_slope_vs_j`` gives LS slope vs ``j`` for wrap and blend series (unwrap
    mod 1 slope — useful when ``s(j)`` drifts monotonically).

    Legacy keys ``wrap_u``, ``blend_u_plus_root_frac``, ``slot8``, ``wrap_s_times_root_mod1`` alias
    the ``unit_2pi`` wrap and root product wrap.

    This is **not** a Lean theorem — JSON-friendly for comparing 3SAT and ``factor_peel_intercept``.
    """

    k_safe = max(1, int(k_enc))
    MM = max(1, int(M))
    root_m = float(MM) ** (1.0 / float(k_safe))
    v = root_m % 1.0
    n = max(0, int(n_patch))
    mj = max(0, int(min_j_samples))
    floor_j = max(n, mj)
    hard = max(8, int(max_rows_hard_cap))
    if max_rows is None:
        cap = min(floor_j, hard) if floor_j > 0 else 0
    else:
        cap = min(floor_j, max(1, int(max_rows)), hard) if floor_j > 0 else 0

    two_pi = 2.0 * math.pi
    pi_half = math.pi / 2.0
    theta_k = math.pi / (2.0 * float(k_safe))
    moduli: list[tuple[str, float]] = [
        ("unit_2pi", two_pi),
        ("half_pi", math.pi),
        ("quarter_pi", pi_half),
        ("arity_theta_k", theta_k),
        ("mod_1", 1.0),
    ]

    rows: list[dict[str, Any]] = []
    series_wrap: dict[str, list[float]] = {name: [] for name, _ in moduli}
    series_blend: dict[str, list[float]] = {name: [] for name, _ in moduli}
    series_root_prod: list[float] = []

    for j in range(cap):
        s_j = polar_angle_from_rapidity(phi, t, j)
        wraps: dict[str, float] = {}
        blends: dict[str, float] = {}
        for name, L in moduli:
            wn = _wrap_norm_rad(s_j, L)
            wraps[name] = wn
            bn = (wn + v) % 1.0
            blends[name] = bn
            series_wrap[name].append(wn)
            series_blend[name].append(bn)

        u = wraps["unit_2pi"]
        blend = blends["unit_2pi"]
        slot8 = int(8.0 * blend) % 8
        wrap_s_times_root = ((s_j * root_m) % two_pi) / two_pi
        series_root_prod.append(wrap_s_times_root)

        rows.append(
            {
                "j": j,
                "s_j_rad": s_j,
                "wrap_u": u,
                "blend_u_plus_root_frac": blend,
                "slot8": slot8,
                "wrap_s_times_root_mod1": wrap_s_times_root,
                "wraps": wraps,
                "blends_root_frac": blends,
            }
        )

    wkeys = [name for name, _ in moduli]
    trend: dict[str, float] = {}
    trend.update(_slope_dict("wrap_", wkeys, series_wrap))
    trend.update(_slope_dict("blend_", wkeys, series_blend))
    trend["wrap_s_times_root_mod1"] = _linear_slope_vs_j(series_root_prod)

    return {
        "M": MM,
        "k_enc": k_safe,
        "M_pow_1_over_k": root_m,
        "root_frac_mod1": v,
        "n_patch": n,
        "min_j_samples": mj,
        "j_span_effective": cap,
        "max_rows_cap": hard,
        "max_rows_requested": max_rows,
        "rows_sampled": len(rows),
        "wrap_moduli_rad": {name: L for name, L in moduli},
        "trend_linear_slope_vs_j": trend,
        "rows": rows,
    }


def variation_threshold(M: int, cum_total: float) -> float:
    """
    Deterministic threshold in [0, cum_total] from M only (shell + encoding integer).
    Uses fractional part of M in a fixed modulus so different formulas give different cuts.
    """

    if cum_total <= 0.0:
        return 0.0
    # Normalized "phase" of M — not a free parameter
    frac = (M % 10_000) / 10_000.0
    return frac * cum_total


def max_step_change_index(samples: list[float]) -> tuple[int, float]:
    if len(samples) < 2:
        return 0, 0.0
    best_j, best_abs = 0, 0.0
    for j in range(len(samples) - 1):
        d = samples[j + 1] - samples[j]
        a = abs(d)
        if a > best_abs:
            best_j, best_abs = j, a
    return best_j, best_abs


def discrete_slopes(samples: list[float]) -> list[float]:
    """First differences ΔS[j] = S[j+1] − S[j] along the patch arc."""

    return [samples[j + 1] - samples[j] for j in range(len(samples) - 1)]


def slope_jumps(deltas: list[float]) -> list[float]:
    """Second differences (curvature of the discrete score): Δ²S[j] = ΔS[j+1] − ΔS[j]."""

    return [deltas[j + 1] - deltas[j] for j in range(len(deltas) - 1)]


def max_abs_index(values: list[float]) -> tuple[int, float]:
    if not values:
        return -1, 0.0
    best_i, best_a = 0, abs(values[0])
    for i in range(1, len(values)):
        a = abs(values[i])
        if a > best_a:
            best_i, best_a = i, a
    return best_i, best_a


def fourier_peak_toy(k_axis: int, n: int) -> float:
    theta = math.pi / (2.0 * max(k_axis, 1))
    z = 0j
    for j in range(n):
        w = 1.0 / math.sqrt(j + 1.0)
        t = theta * j
        z += w * complex(math.cos(t), math.sin(t))
    return abs(z)


# --- Binary search (generic + score-based) ------------------------------------------


def binary_search_smallest_true(n: int, pred: Callable[[int], bool]) -> tuple[int, int]:
    """
    Smallest j ∈ [0, n−1] with pred(j) == True. Requires pred(n−1) == True and pred monotone.
    Returns (j, number of pred evaluations).
    """

    if n <= 0:
        return 0, 0
    probes = 0

    def P(j: int) -> bool:
        nonlocal probes
        probes += 1
        return pred(j)

    if not P(n - 1):
        return n - 1, probes
    lo, hi = 0, n - 1
    while lo < hi:
        mid = (lo + hi) // 2
        if P(mid):
            hi = mid
        else:
            lo = mid + 1
    return lo, probes


def binary_search_largest_true(n: int, pred: Callable[[int], bool]) -> tuple[int, int]:
    """
    Largest j ∈ [0, n−1] with pred(j) == True. Requires pred monotone in the sense:
    ∃J such that pred(j) is True for all j ≤ J and False for j > J (step at J+1).
    Returns (j, number of pred evaluations); j = −1 if pred(0) is False.
    """

    if n <= 0:
        return -1, 0
    probes = 0

    def P(j: int) -> bool:
        nonlocal probes
        probes += 1
        return pred(j)

    if P(n - 1):
        return n - 1, probes
    if not P(0):
        return -1, probes
    lo, hi = 0, n - 1
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if P(mid):
            lo = mid
        else:
            hi = mid - 1
    return lo, probes


@dataclass
class PatchSearchScore:
    """Result of score-driven binary search on Fin n (left + right patch boundaries)."""

    n: int
    samples: list[float]
    cum: list[float]
    threshold: float
    cum_total: float
    j_first_ge_threshold: int
    j_last_below_threshold: int
    predicate_probes_left: int
    predicate_probes_right: int
    log2_n_ceil: int
    slopes: list[float]
    slope_jumps: list[float]
    max_slope_jump_j: int
    max_slope_jump_abs: float


def patch_search_score_driven(M: int, k_enc: int, num_clauses: int, n: int) -> PatchSearchScore:
    samples = moire_score_samples(M, k_enc, num_clauses, n=n)
    cum = cumulative_abs_variation(samples)
    total = cum[-1] if cum else 0.0
    T = variation_threshold(M, total)

    def pred_ge(j: int) -> bool:
        return cum[j] >= T

    def pred_lt(j: int) -> bool:
        return cum[j] < T

    j_first, probes_l = binary_search_smallest_true(n, pred_ge)
    j_last_lt, probes_r = binary_search_largest_true(n, pred_lt)
    logn = math.ceil(math.log2(n)) if n > 1 else 0

    deltas = discrete_slopes(samples)
    jumps = slope_jumps(deltas)
    j_mx, jmp_abs = max_abs_index(jumps)

    return PatchSearchScore(
        n=n,
        samples=samples,
        cum=cum,
        threshold=T,
        cum_total=total,
        j_first_ge_threshold=j_first,
        j_last_below_threshold=j_last_lt,
        predicate_probes_left=probes_l,
        predicate_probes_right=probes_r,
        log2_n_ceil=logn,
        slopes=deltas,
        slope_jumps=jumps,
        max_slope_jump_j=j_mx,
        max_slope_jump_abs=jmp_abs,
    )


def crossing_density(theta: float) -> float:
    """Slope envelope used by the predictive jump heuristic: ``|sin θ| + |cos θ|``."""

    return abs(math.sin(theta)) + abs(math.cos(theta))


def _first_allowed_residue_at_least(lo: int, mod: int, allow: set[int], n_max: int) -> int | None:
    """Smallest ``j ∈ [lo, n_max]`` with ``j % mod ∈ allow``, or ``None`` if the interval is empty or has no hit."""

    n_max = int(n_max)
    a = max(0, min(int(lo), n_max))
    for cand in range(a, n_max + 1):
        if cand % mod in allow:
            return cand
    return None


def _predictive_jump_cap(n: int) -> int:
    """Cap step size so we do not leap over the whole patch in one hop."""

    if n <= 1:
        return 1
    root = int(math.isqrt(max(1, n - 1)))
    return max(3, min(n - 1, max(8, 2 * root)))


def _local_delta_phi_proxy(ps: PatchSearchScore, j: int, theta_step: float) -> float:
    """
    Local ``Δφ`` proxy from moiré **slope jumps** (second differences) near ``j``,
    blended with a fraction of the global max jump so flat patches still move.
    """

    jumps = ps.slope_jumps
    local: list[float] = []
    if jumps:
        if j > 0 and j - 1 < len(jumps):
            local.append(abs(jumps[j - 1]))
        if j < len(jumps):
            local.append(abs(jumps[j]))
        if j + 1 < len(jumps):
            local.append(abs(jumps[j + 1]))
    mx = max(local) if local else 0.0
    floor_phi = max(float(theta_step) * 0.25, 1e-6)
    global_floor = 0.0
    if ps.max_slope_jump_abs and ps.max_slope_jump_abs > 0:
        global_floor = max(floor_phi, 0.12 * float(ps.max_slope_jump_abs))
    base = max(mx, global_floor, floor_phi)
    return max(1e-6, min(abs(base), math.pi / 2.0))


def _casimir_rows_for_kept_j_import():
    """Resolve `nuclear_torus_casimir_float` whether the demo is run as ``scripts/`` or module."""
    try:
        from nuclear_torus_casimir_float import casimir_rows_for_kept_j
    except ImportError:
        from scripts.nuclear_torus_casimir_float import casimir_rows_for_kept_j

    return casimir_rows_for_kept_j


def _bond_rows_for_kept_j_import():
    try:
        from bonded_horizon_casimir_float import bond_diagnostics_for_kept_j
    except ImportError:
        from scripts.bonded_horizon_casimir_float import bond_diagnostics_for_kept_j

    return bond_diagnostics_for_kept_j


def predictive_patch_prune_trace(
    ps: PatchSearchScore,
    k_enc: int,
    *,
    shell_m: int | None = None,
    residue_mod: int = 5,
    allowed_residues: tuple[int, ...] = (0, 3),
    merge_score_landmarks: bool = True,
    attach_nuclear_torus_casimir: bool = False,
    casimir_electron_count_for_j: Any | None = None,
    attach_bond_horizon_casimir: bool = False,
    bond_electron_count_for_j: Any | None = None,
) -> dict[str, Any]:
    """
    Heuristic jump + **forward residue snap** over patch indices ``j``.

    * ``k ≈ 1/(s(θ)·sin(Δφ))`` with ``s(θ)=|sin θ|+|cos θ|``, ``θ = axisAngle(k)·j``.
    * ``Δφ`` from local slope-jump magnitudes + a floor from ``max_slope_jump_abs``.
    * **Snap:** after a raw target ``j_raw``, advance to the next ``j_snapped ≥ j_raw`` with
      ``j_snapped % mod`` allowed (so the ξ gate selects a shell, not a dead skip).
    * **Landmarks:** optionally union BST + jerk indices so the sparse walk never drops the
      score-driven anchors used elsewhere (factor trial map + SAT heuristics).
    * **Shell budget:** when ``shell_m`` is set (odd cofactor / encoding ``M``), the walk does at most
      ``min(n_patch, max(4, ⌊√shell_m⌋))`` probe iterations — so probe depth stays **O(√m)** and never
      scales with oversized ``n_patch``.
    * **Nuclear torus Casimir (optional):** when ``attach_nuclear_torus_casimir`` is true, the result
      includes ``nuclear_torus_casimir``: per ``j`` in ``kept_j``, the float mirror of
      ``Hqiv.Geometry.NuclearTorusPerturbation`` (octonion associator + S⁷ λ-sum) in dimensionless
      units and eV under the hydrogen anchor.  ``casimir_electron_count_for_j`` maps patch index
      ``j → N`` (default ``min(j+1, 256)``).
    * **Bond horizon surplus (optional):** when ``attach_bond_horizon_casimir`` is true, adds
      ``bond_horizon_casimir``: per ``j``, joint-vs-separated surpluses from
      ``Hqiv.Geometry.BondedHorizonCasimir`` (H₂-style ``(2,1,1)``, ionic peel ``(N,1,N-1)``, symmetric
      split).  ``bond_electron_count_for_j`` defaults to the same map as the nuclear attachment.

    ``kept_j`` is the union used for downstream candidate extraction; ``walk_residue_snapped_j``
    is only the snapped ray-landing indices (all satisfy the residue filter).
    """

    n = max(0, int(ps.n))
    empty = {
        "residue_mod": residue_mod,
        "allowed_residues": list(allowed_residues),
        "shell_m_for_sqrt_cap": shell_m,
        "isqrt_shell_m": int(math.isqrt(int(shell_m))) if shell_m is not None and int(shell_m) >= 0 else None,
        "visit_cap_walk": None,
        "visited_j": [],
        "walk_residue_snapped_j": [],
        "landmark_j_merged": [],
        "sqrt_shell_probe_j": [],
        "kept_j": [],
        "pruned_j": [],
        "coverage_ratio": 0.0,
        "walk_coverage_ratio": 0.0,
        "visit_count": 0,
        "residue_adjust_steps": 0,
        "jump_cap": 1,
        "steps": [],
    }
    if n <= 0:
        return empty

    mod = max(2, int(residue_mod))
    allow = {int(r) % mod for r in allowed_residues}
    theta_step = intrinsic_axis_angle_rad(k_enc)
    jump_cap = _predictive_jump_cap(n)
    visit_cap: int | None = None
    if shell_m is not None and int(shell_m) >= 2:
        r = int(math.isqrt(int(shell_m)))
        visit_cap = min(n, max(4, r))
        mean_step = max(1, (n + visit_cap - 1) // visit_cap)
        jump_cap = min(n - 1, max(jump_cap, mean_step))
    max_visits = visit_cap if visit_cap is not None else max(50_000, 4 * n)
    visited: list[int] = []
    walk_snapped: list[int] = []
    per_step: list[dict[str, Any]] = []
    residue_adjust = 0
    j = 0
    visits = 0

    while j < n and visits < max_visits:
        if visit_cap is not None and len(visited) >= visit_cap:
            break
        visits += 1
        visited.append(j)
        theta = theta_step * float(j)
        s = max(1e-12, crossing_density(theta))
        dphi = _local_delta_phi_proxy(ps, j, theta_step)
        denom = s * max(1e-6, abs(math.sin(dphi)))
        k_float = 1.0 / denom
        k_jump = max(1, min(jump_cap, int(math.ceil(k_float))))
        j_raw = min(n - 1, j + k_jump)
        lo = min(n - 1, max(j, j_raw))
        j_snap = _first_allowed_residue_at_least(lo, mod, allow, n - 1)
        if j_snap is None:
            per_step.append(
                {
                    "j": j,
                    "theta_rad": theta,
                    "crossing_density": s,
                    "delta_phi_proxy_rad": dphi,
                    "predicted_jump_raw": k_float,
                    "predicted_jump_int": k_jump,
                    "j_raw": j_raw,
                    "j_snapped": None,
                    "residue_adjusted": False,
                    "no_allowed_shell_ahead": True,
                }
            )
            j += 1
            continue
        if j_snap != j_raw:
            residue_adjust += 1
        walk_snapped.append(j_snap)
        per_step.append(
            {
                "j": j,
                "theta_rad": theta,
                "crossing_density": s,
                "delta_phi_proxy_rad": dphi,
                "predicted_jump_raw": k_float,
                "predicted_jump_int": k_jump,
                "j_raw": j_raw,
                "j_snapped": j_snap,
                "j_snapped_mod": j_snap % mod,
                "residue_adjusted": j_snap != j_raw,
                "no_allowed_shell_ahead": False,
            }
        )
        if j_snap > j:
            j = j_snap
        else:
            j += 1

    landmarks: list[int] = []
    sqrt_probe: list[int] = []
    if merge_score_landmarks:
        for x in (
            0,
            n - 1,
            ps.j_first_ge_threshold,
            ps.j_last_below_threshold,
            ps.max_slope_jump_j,
        ):
            if 0 <= int(x) < n:
                landmarks.append(int(x))
    # ``j+1`` is a trial divisor lane; include a few indices with ``j+1 ≈ √m`` so sparse walks
    # still hit the hyperbola neighborhood when ``⌊√m⌋`` is small (e.g. ``m=221`` → ``j=12`` → ``13``).
    if shell_m is not None and int(shell_m) >= 2:
        r = int(math.isqrt(int(shell_m)))
        for delta in (-2, -1, 0, 1):
            jj = r + delta - 1
            if 0 <= jj < n:
                sqrt_probe.append(jj)
                landmarks.append(jj)
    landmark_set = sorted(set(landmarks))
    walk_set = sorted(set(walk_snapped))
    kept_sorted = sorted(set(walk_set) | set(landmark_set))

    out: dict[str, Any] = {
        "residue_mod": mod,
        "allowed_residues": sorted(allow),
        "shell_m_for_sqrt_cap": int(shell_m) if shell_m is not None else None,
        "isqrt_shell_m": int(math.isqrt(int(shell_m))) if shell_m is not None and int(shell_m) >= 0 else None,
        "visit_cap_walk": visit_cap,
        "jump_cap": jump_cap,
        "visited_j": visited,
        "walk_residue_snapped_j": walk_set,
        "landmark_j_merged": landmark_set,
        "sqrt_shell_probe_j": sorted(set(sqrt_probe)),
        "kept_j": kept_sorted,
        "pruned_j": [x for x in visited if x not in set(kept_sorted)],
        "coverage_ratio": float(len(kept_sorted)) / float(max(1, n)),
        "walk_coverage_ratio": float(len(walk_set)) / float(max(1, n)),
        "visit_count": len(visited),
        "residue_adjust_steps": residue_adjust,
        "steps": per_step,
    }
    if attach_nuclear_torus_casimir:
        casimir_rows_for_kept_j = _casimir_rows_for_kept_j_import()
        out["nuclear_torus_casimir"] = casimir_rows_for_kept_j(
            kept_sorted, electron_count_for_j=casimir_electron_count_for_j
        )
    if attach_bond_horizon_casimir:
        bond_diagnostics_for_kept_j = _bond_rows_for_kept_j_import()
        bmap = bond_electron_count_for_j
        if bmap is None:
            bmap = casimir_electron_count_for_j
        out["bond_horizon_casimir"] = bond_diagnostics_for_kept_j(
            kept_sorted, electron_count_for_j=bmap
        )
    return out


def geometric_sat_heuristics(
    formula: Formula3SAT | FormulaCNF,
    ps: PatchSearchScore,
    n_patch: int,
) -> dict[str, Any]:
    """
    Benchmark geometry vs SAT labels.

    * **Early / late** — ad hoc thresholds on where the BST crossing ``j_first_ge_threshold`` falls
      along the patch (still **not** sound).
    * **``sat_at_bst_j_first``** — the **checked** part: :func:`eval_sat_at_patch_index` at the same
      index the BST returned (one explicit assignment — not a blind scalar guess).
    * **``legacy_cum_total_guess_sat``** — old ``cum_total >= 1.0`` toy; kept only so falsification
      tests can show it is not a SAT classifier.
    """

    if n_patch <= 0:
        return {
            "guess_early_cross_sat": False,
            "guess_late_cross_sat": False,
            "sat_at_bst_j_first": False,
            "legacy_cum_total_guess_sat": False,
            "frac_j_first": None,
        }
    denom = max(n_patch - 1, 1)
    frac = ps.j_first_ge_threshold / denom
    sat_bst = eval_sat_at_patch_index(formula, ps.j_first_ge_threshold)
    return {
        "guess_early_cross_sat": frac <= 0.35,
        "guess_late_cross_sat": frac >= 0.65,
        "sat_at_bst_j_first": sat_bst,
        "legacy_cum_total_guess_sat": ps.cum_total >= 1.0,
        "frac_j_first": frac,
        "j_first": ps.j_first_ge_threshold,
        "cum_total": ps.cum_total,
        "threshold_T": ps.threshold,
    }


def run_geometric_cnf_pipeline(
    formula: Formula3SAT | FormulaCNF,
    *,
    include_moire_checker: bool = False,
) -> dict[str, Any]:
    """
    Prime encode **any** CNF + full moiré / BST patch pipeline + brute-force SAT (feasible only for
    small ``num_vars``). Returns geometry heuristics alongside ground truth when brute force finishes.
    """

    f = as_cnf(formula)
    M, _primes, _cprods = encode_formula_to_M(f)
    k_enc = omega_M_exact(f)
    c = len(f.clauses)
    n_patch = patch_window_length(c)
    ps = patch_search_score_driven(M, k_enc, c, n_patch)
    sat_bf: bool | None
    witness: tuple[bool, ...] | None
    if f.num_vars > 22:
        sat_bf, witness = None, None
    else:
        sat_bf, witness = is_satisfiable_bruteforce(f)
    out: dict[str, Any] = {
        "n_vars": f.num_vars,
        "n_clauses": c,
        "total_literal_occurrences": sum(len(cl) for cl in f.clauses),
        "M": M,
        "M_bit_length": M.bit_length(),
        "omega_literal_sum": k_enc,
        "n_patch": n_patch,
        "mp_dps_shell": mp_dps_for_shell_M(M),
        "sat_bruteforce": sat_bf,
        "witness": list(witness) if witness is not None else None,
        "score_search": {
            "threshold": ps.threshold,
            "cum_total": ps.cum_total,
            "j_first_ge_threshold": ps.j_first_ge_threshold,
            "j_last_below_threshold": ps.j_last_below_threshold,
            "max_slope_jump_abs": ps.max_slope_jump_abs,
        },
        "geometry_heuristics": geometric_sat_heuristics(f, ps, n_patch),
    }
    if include_moire_checker:
        out["moire_sat_checker"] = moire_patch_sat_checker_trace(f, M, k_enc, c, n_patch)
    return out


# --- Legacy: M mod n (for regression / --mod-demo) -----------------------------------


def toy_transition_mod(M: int, n: int) -> int:
    if n <= 0:
        return 0
    return M % n


def binary_search_mod_predicate(M: int, n: int) -> tuple[int, int]:
    if n <= 0:
        return 0, 0
    j_star = toy_transition_mod(M, n)
    probes = 0

    def pred(j: int) -> bool:
        nonlocal probes
        probes += 1
        return j >= j_star

    j_, pr = binary_search_smallest_true(n, pred)
    return j_, pr


# --- Built-in formulas ---------------------------------------------------------------


EXAMPLE = Formula3SAT(
    num_vars=4,
    clauses=(
        (Literal(0, False), Literal(1, True), Literal(2, False)),
        (Literal(0, True), Literal(1, False), Literal(3, False)),
        (Literal(1, False), Literal(2, False), Literal(3, True)),
    ),
)

# Deterministic extra demos (same encoding / brute-force SAT as `main` trials).
TRIAL_FORMULAS: tuple[tuple[str, Formula3SAT], ...] = (
    ("Example (4 vars, 3 clauses)", EXAMPLE),
    (
        "UNSAT: x ∧ ¬x",
        Formula3SAT(
            num_vars=1,
            clauses=(
                (Literal(0, False), Literal(0, False), Literal(0, False)),
                (Literal(0, True), Literal(0, True), Literal(0, True)),
            ),
        ),
    ),
    (
        "SAT: x ∨ x ∨ x",
        Formula3SAT(num_vars=1, clauses=((Literal(0, False), Literal(0, False), Literal(0, False)),)),
    ),
    (
        "SAT: (x0 ∨ x1 ∨ x2)",
        Formula3SAT(
            num_vars=3,
            clauses=((Literal(0, False), Literal(1, False), Literal(2, False)),),
        ),
    ),
    (
        "SAT: 2 vars one clause",
        Formula3SAT(
            num_vars=2,
            clauses=((Literal(0, False), Literal(1, True), Literal(1, False)),),
        ),
    ),
    (
        "UNSAT: 2 vars (x0 ∧ ¬x0), x1 unused",
        Formula3SAT(
            num_vars=2,
            clauses=(
                (Literal(0, False), Literal(0, False), Literal(0, False)),
                (Literal(0, True), Literal(0, True), Literal(0, True)),
            ),
        ),
    ),
    (
        "SAT: 5 vars mixed",
        Formula3SAT(
            num_vars=5,
            clauses=(
                (Literal(0, False), Literal(1, True), Literal(2, False)),
                (Literal(2, True), Literal(3, False), Literal(4, False)),
                (Literal(0, True), Literal(4, True), Literal(1, False)),
            ),
        ),
    ),
)


def formula_unsat_forbids_all_assignments_2vars() -> Formula3SAT:
    """
    Four clauses on two variables: for each assignment in ``{0,1}²`` one clause false **only** there
    (third literal repeats ``x0`` so each clause stays 3-CNF). Unsatisfiable by design.
    """

    clauses: list[tuple[Literal, Literal, Literal]] = []
    for mask in range(4):
        b0 = bool(mask & 1)
        b1 = bool(mask & 2)
        clauses.append((Literal(0, b0), Literal(1, b1), Literal(0, b0)))
    return Formula3SAT(num_vars=2, clauses=tuple(clauses))


def formula_unsat_forbids_all_assignments_3vars() -> Formula3SAT:
    """
    Eight clauses on three variables: for each ``(x0,x1,x2) ∈ {0,1}³`` one clause that is false **only**
    on that assignment (the “maxterm” / “forbidden corner” construction). Unsatisfiable by design.
    """

    clauses: list[tuple[Literal, Literal, Literal]] = []
    for mask in range(8):
        v0 = bool(mask & 1)
        v1 = bool(mask & 2)
        v2 = bool(mask & 4)
        clauses.append((Literal(0, v0), Literal(1, v1), Literal(2, v2)))
    return Formula3SAT(num_vars=3, clauses=tuple(clauses))


def random_3sat_formula(num_vars: int, num_clauses: int, rng: random.Random) -> Formula3SAT:
    """Uniform random 3-CNF: each literal picks a variable and a sign (reproducible given ``rng``)."""

    if num_vars < 1:
        raise ValueError("num_vars must be >= 1")
    if num_clauses < 0:
        raise ValueError("num_clauses must be >= 0")
    clauses: list[tuple[Literal, Literal, Literal]] = []
    for _ in range(num_clauses):
        clauses.append(
            tuple(Literal(rng.randrange(num_vars), rng.choice((False, True))) for _ in range(3))
        )
    return Formula3SAT(num_vars=num_vars, clauses=tuple(clauses))


# Hand-labelled expected satisfiability (verified by reasoning; tests re-check via brute force).
# Tuple: (short name, formula, expected satisfiable, exact witness if unique/forced else None, note).
KNOWN_SAT_BENCHMARKS: tuple[tuple[str, Formula3SAT, bool, tuple[bool, ...] | None, str], ...] = (
    (
        "unsat_8_maxterms_3vars",
        formula_unsat_forbids_all_assignments_3vars(),
        False,
        None,
        "Each of 8 assignments falsifies exactly one clause",
    ),
    (
        "unsat_x_and_not_x",
        Formula3SAT(
            num_vars=1,
            clauses=(
                (Literal(0, False), Literal(0, False), Literal(0, False)),
                (Literal(0, True), Literal(0, True), Literal(0, True)),
            ),
        ),
        False,
        None,
        "Two clauses force x and ¬x",
    ),
    (
        "sat_single_clause_x",
        Formula3SAT(num_vars=1, clauses=((Literal(0, False), Literal(0, False), Literal(0, False)),)),
        True,
        (True,),
        "x ∨ x ∨ x — witness x=True is forced",
    ),
    (
        "sat_two_literals_or",
        Formula3SAT(
            num_vars=2,
            clauses=((Literal(0, False), Literal(0, False), Literal(1, False)),),
        ),
        True,
        None,
        "x0 ∨ x0 ∨ x1 — multiple witnesses; brute force must say SAT",
    ),
    (
        "sat_horn_one_neg",
        Formula3SAT(
            num_vars=3,
            clauses=((Literal(0, True), Literal(1, True), Literal(2, False)),),
        ),
        True,
        (False, False, False),
        "¬x0 ∨ ¬x1 ∨ x2 — first witness in scan order is (F,F,F)",
    ),
    (
        "sat_chain_3vars",
        Formula3SAT(
            num_vars=3,
            clauses=(
                (Literal(0, False), Literal(1, False), Literal(2, False)),
                (Literal(0, True), Literal(1, True), Literal(2, True)),
            ),
        ),
        True,
        None,
        "(x0∨x1∨x2) ∧ (¬x0∨¬x1∨¬x2) — e.g. (T,F,F)",
    ),
)


def _more_hand_sat_benchmarks() -> tuple[tuple[str, Formula3SAT, bool, tuple[bool, ...] | None, str], ...]:
    """Extra small crafted instances (not from SAT competitions — see :data:`ALL_SAT_BENCHMARKS` doc)."""

    return (
        (
            "unsat_4corners_2vars",
            formula_unsat_forbids_all_assignments_2vars(),
            False,
            None,
            "Four maxterms on 2 vars (third literal repeats x0)",
        ),
        (
            "sat_tautology_x_or_not_x",
            Formula3SAT(num_vars=2, clauses=((Literal(0, False), Literal(0, True), Literal(1, False)),)),
            True,
            None,
            "x0 ∨ ¬x0 ∨ x1 — tautological clause",
        ),
        (
            "sat_duplicate_clause",
            Formula3SAT(
                num_vars=2,
                clauses=(
                    (Literal(0, False), Literal(1, False), Literal(1, True)),
                    (Literal(0, False), Literal(1, False), Literal(1, True)),
                ),
            ),
            True,
            None,
            "Same clause twice",
        ),
        (
            "sat_4vars_two_clauses",
            Formula3SAT(
                num_vars=4,
                clauses=(
                    (Literal(0, False), Literal(1, True), Literal(2, False)),
                    (Literal(1, False), Literal(3, True), Literal(2, True)),
                ),
            ),
            True,
            None,
            "Two mixed clauses",
        ),
        (
            "unsat_embed_3var_in_4var",
            Formula3SAT(
                num_vars=4,
                clauses=tuple(
                    formula_unsat_forbids_all_assignments_3vars().clauses
                    + ((Literal(3, False), Literal(3, False), Literal(3, False)),)
                ),
            ),
            False,
            None,
            "UNSAT on first 3 vars + redundant clause on x3",
        ),
        (
            "sat_all_pos_one_clause_4vars",
            Formula3SAT(
                num_vars=4,
                clauses=((Literal(0, False), Literal(1, False), Literal(2, False)),),
            ),
            True,
            None,
            "Single clause x0 ∨ x1 ∨ x2",
        ),
        (
            "sat_6vars_cycle",
            Formula3SAT(
                num_vars=6,
                clauses=(
                    (Literal(0, False), Literal(1, False), Literal(2, False)),
                    (Literal(2, False), Literal(3, False), Literal(4, False)),
                    (Literal(4, False), Literal(5, False), Literal(0, False)),
                ),
            ),
            True,
            None,
            "Weak cycle of ORs — easily satisfied",
        ),
    )


def _build_all_sat_benchmarks() -> tuple[tuple[str, Formula3SAT, bool, tuple[bool, ...] | None, str], ...]:
    """
    Full regression list: core :data:`KNOWN_SAT_BENCHMARKS`, extra hand instances, and **reproducible**
    random 3-CNF formulas with brute-force labels. For industrial **SAT Competition** / SATLIB
    corpora, use DIMACS ``.cnf`` files and a parser — not embedded here to keep the repo light.
    """

    rows: list[tuple[str, Formula3SAT, bool, tuple[bool, ...] | None, str]] = []
    rows.extend(KNOWN_SAT_BENCHMARKS)
    rows.extend(_more_hand_sat_benchmarks())
    for seed in range(100):
        rng = random.Random(seed)
        nv = 4 + seed % 5
        nc = 8 + (seed * 13 % 33)
        f = random_3sat_formula(nv, nc, rng)
        sat, _ = is_satisfiable_bruteforce(f)
        rows.append(
            (
                f"random3sat_n{nv}_m{nc}_seed{seed}",
                f,
                sat,
                None,
                "reproducible random 3-CNF; label from brute force",
            )
        )
    return tuple(rows)


#: Every entry is ``(name, formula, expected_sat, witness_or_None, note)``. Witness is checked only
#: when not ``None``. Includes 100 seeded random formulas (``n`` in ``4..8``, varied ``m``).
ALL_SAT_BENCHMARKS: tuple[tuple[str, Formula3SAT, bool, tuple[bool, ...] | None, str], ...] = _build_all_sat_benchmarks()


def run_formula(
    name: str,
    formula: Formula3SAT | FormulaCNF,
    *,
    json_out: bool,
    results: list[dict[str, Any]],
    phi: float = 1.0,
    t: float = 1.0,
    wrap_min_j: int = 64,
    wrap_max_rows: int | None = None,
    wrap_hard_cap: int = 2048,
    verify_omega_factorization: bool = False,
) -> None:
    """
    Run encoding + geometry pipeline for one formula.

    If ``verify_omega_factorization`` is False (default), Ω(M) is taken **only** from the encoding
    sum (:func:`omega_M_exact`); no trial division on ``M`` is run. Set True for an independent
    check via :func:`omega_big_omega_factorization` (can be costly for large ``M``).
    """
    f = as_cnf(formula)
    sat, witness = is_satisfiable_bruteforce(f)
    M, primes, cprods = encode_formula_to_M(f)
    k_enc = omega_M_exact(f)
    if verify_omega_factorization:
        assert_omega_exact_matches_factorization(M, f)
        omega_m = omega_big_omega_factorization(M)
    else:
        omega_m = k_enc
    try:
        r_float = math.sqrt(float(M))
        r_show = f"{r_float:.6f}" if math.isfinite(r_float) else ""
    except OverflowError:
        r_show = ""
    if not r_show:
        with mp_shell_precision(M):
            r_show = mp.nstr(mp.sqrt(mp.mpf(M)), mp_nstr_display_digits(M))
    v8_str, a7_str = shell_volume8_area7_strings(M)
    c = len(f.clauses)
    n_patch = patch_window_length(c)
    literal_occ = sum(len(cl) for cl in f.clauses)

    ps = patch_search_score_driven(M, k_enc, c, n_patch)
    moire_checker = moire_patch_sat_checker_trace(f, M, k_enc, c, n_patch)
    j_lin, jump = max_step_change_index(ps.samples)
    peak = fourier_peak_toy(k_enc, n_patch)
    k_naive_3c = 3 * c

    lean_bridge = lean_rapidity_bridge_report(phi, t, n_patch)
    root_wrap = rapidity_root_wrap_probe(
        M,
        k_enc,
        n_patch,
        phi,
        t,
        min_j_samples=wrap_min_j,
        max_rows=wrap_max_rows,
        max_rows_hard_cap=wrap_hard_cap,
    )
    predictive_patch = predictive_patch_prune_trace(ps, k_enc, shell_m=M)

    record: dict[str, Any] = {
        "name": name,
        "sat": sat,
        "witness": list(witness) if witness is not None else None,
        "M": M,
        "omega_literal_sum": k_enc,
        "n_patch": n_patch,
        "lean_rapidity_bridge": lean_bridge,
        "rapidity_root_wrap_probe": root_wrap,
        "predictive_patch_prune": predictive_patch,
        "score_search": {
            "threshold": ps.threshold,
            "cum_total": ps.cum_total,
            "j_first_ge_threshold": ps.j_first_ge_threshold,
            "j_last_below_threshold": ps.j_last_below_threshold,
            "predicate_probes_left": ps.predicate_probes_left,
            "predicate_probes_right": ps.predicate_probes_right,
            "log2_n_ceil": ps.log2_n_ceil,
            "max_slope_jump_j": ps.max_slope_jump_j,
            "max_slope_jump_abs": ps.max_slope_jump_abs,
        },
        "contrast_max_delta_j": j_lin,
        "contrast_max_delta_abs": jump,
        "fourier_peak_toy": peak,
        "shell_V8": v8_str,
        "shell_A7": a7_str,
        "r_sqrt_display": r_show,
        "mp_dps_shell": mp_dps_for_shell_M(M),
        "moire_sat_checker": moire_checker,
        "total_literal_occurrences": literal_occ,
        "geometry_heuristics": geometric_sat_heuristics(f, ps, n_patch),
    }
    if verify_omega_factorization:
        record["omega_trial_div_count_on_M"] = omega_m
        record["verify_omega_trial_div"] = True
    else:
        record["verify_omega_trial_div"] = False
    results.append(record)

    if json_out:
        return

    print(f"\n=== {name} ===")
    print(f"  variables: {f.num_vars}, clauses: {c}, literal occurrences: {literal_occ}")
    print(f"  primes (per var): {primes}")
    print(f"  clause products: {cprods}")
    print(f"  M = {M}")
    if verify_omega_factorization:
        print(f"  Ω(M) exact = {k_enc}  (= factorization Ω(M) = {omega_m});  naive 3c = {k_naive_3c}")
    else:
        print(f"  Ω from literal sum = {k_enc}  (naive 3c = {k_naive_3c})")
    print(f"  θ = π/(2·Ω(M)) = {math.pi / (2.0 * k_enc):.8f} rad")
    print(f"  r = √M = {r_show}  |  V₈(r) = {v8_str}  A₇(r) = {a7_str}")
    print(f"  SAT (brute force): {sat}" + (f", witness = {witness}" if witness else ""))
    print(f"  patch Fin n = {n_patch}")
    mchk = moire_checker
    print(
        f"  **cheap checker @ each moiré j:** {mchk['count_patch_steps_sat']}/{n_patch} indices satisfy "
        f"all clauses; first such j = {mchk['first_j_with_sat_assignment']}"
    )
    if n_patch <= 14:
        for row in mchk["steps"]:
            a = row["assignment"]
            print(
                f"      j={row['j']}: sat={row['sat_by_checker']}  bits={a}  S={row['S']:.6f}"
            )
    print("    (assignment(j) cycles in brute-force order; clause eval is O(clauses).)")
    print(
        f"  **score search:** cum. |ΔS| threshold = {ps.threshold:.6f} / total variation = {ps.cum_total:.6f}"
    )
    print(
        f"    → BST left: smallest j with cum[j] ≥ T is j = {ps.j_first_ge_threshold} "
        f"({ps.predicate_probes_left} pred calls)"
    )
    print(
        f"    → BST right: largest j with cum[j] < T is j = {ps.j_last_below_threshold} "
        f"({ps.predicate_probes_right} pred calls); ⌈log₂ n⌉ = {ps.log2_n_ceil}"
    )
    print(
        f"  moiré: max |Δ²S| (slope jump) at segment j = {ps.max_slope_jump_j} "
        f"(|Δ²| = {ps.max_slope_jump_abs:.6f})"
    )
    print(
        f"  contrast: linear max |ΔS| at j = {j_lin} (|Δ|={jump:.6f}); "
        f"toy Fourier peak = {peak:.6f}"
    )
    lb = lean_bridge
    print(
        f"  **Lean bridge (sin ∘ polarAngle):** φ={lb['phi']}, t={lb['t']}, φ·t={lb['phi_times_t']:.6g}; "
        f"s(0)={lb['shell_s0']:.6f} → s(n−1)={lb['shell_s_last']:.6f}"
    )
    print(
        f"    shell monotone: {lb['shell_parameter_monotone']}  |  "
        f"Lipschitz check cum ≤ K·Δs (K={lb['lipschitz_K']}): "
        f"{'OK' if lb['bound_ok'] else 'FAIL'} "
        f"(max cum−KΔs = {lb['max_cumulative_minus_K_delta_s']:.3e})"
    )
    rw = root_wrap
    rhi = max(0, int(rw["rows_sampled"]) - 1)
    tr = rw.get("trend_linear_slope_vs_j") or {}
    s_u = tr.get("wrap_unit_2pi")
    s_th = tr.get("wrap_arity_theta_k")
    s_bq = tr.get("blend_quarter_pi")
    trend_bits = []
    if s_u is not None:
        trend_bits.append(f"slope_wrap_2π={s_u:.4e}")
    if s_th is not None:
        trend_bits.append(f"slope_wrap_θk={s_th:.4e}")
    if s_bq is not None:
        trend_bits.append(f"slope_blend_π/2={s_bq:.4e}")
    trend_str = "  " + "  ".join(trend_bits) if trend_bits else ""
    print(
        f"  **rapidity×M^(1/k) toy:** k_enc={rw['k_enc']}  M^(1/k)={rw['M_pow_1_over_k']:.6f}  "
        f"frac(M^(1/k))={rw['root_frac_mod1']:.6f}  "
        f"j=0..{rhi} (score n_patch={rw['n_patch']}, min_j={rw.get('min_j_samples')}, "
        f"span={rw.get('j_span_effective')})"
    )
    if trend_str.strip():
        print(f"    trends vs j:{trend_str}")
    pp = predictive_patch
    print(
        "  predictive patch prune: "
        f"kept={len(pp['kept_j'])}/{ps.n} cov={pp['coverage_ratio']:.3f} "
        f"walk_cov={pp.get('walk_coverage_ratio', 0):.3f} "
        f"visits={pp.get('visit_count', 0)}/walk_cap={pp.get('visit_cap_walk')} "
        f"(isqrt M={pp.get('isqrt_shell_m')}) snap_adj={pp.get('residue_adjust_steps', 0)} "
        f"jump_cap={pp.get('jump_cap')} mod={pp['residue_mod']} allowed={pp['allowed_residues']}"
    )


def main(argv: list[str] | None = None) -> None:
    p = argparse.ArgumentParser(description="HQIV geometric 3SAT encoding + score patch search demo")
    p.add_argument("--json", action="store_true", help="emit one JSON array to stdout (no banners)")
    p.add_argument("--mod-demo", action="store_true", help="print legacy M mod n binary search sanity only")
    p.add_argument(
        "--phi",
        type=float,
        default=1.0,
        metavar="φ",
        help="rapidity φ for Lean polar-angle shell curve s(m)=φ·t·δθ'(m) (default 1)",
    )
    p.add_argument(
        "--rapidity-t",
        type=float,
        default=1.0,
        metavar="T",
        dest="rapidity_t",
        help="rapidity t for s(m)=φ·t·δθ'(m) (default 1); need φ·t≥0 for monotone s(m)",
    )
    p.add_argument(
        "--wrap-min-j",
        type=int,
        default=64,
        metavar="J",
        help="minimum number of shell indices j for rapidity_root_wrap_probe (default 64; trends need many points)",
    )
    p.add_argument(
        "--wrap-max-rows",
        type=int,
        default=None,
        metavar="N",
        help="optional cap on wrap-probe rows (default: use span=min(max(n_patch,min_j), hard cap))",
    )
    p.add_argument(
        "--wrap-hard-cap",
        type=int,
        default=2048,
        metavar="N",
        help="safety ceiling on j samples in rapidity_root_wrap_probe (default 2048)",
    )
    p.add_argument(
        "--verify-omega-factorization",
        action="store_true",
        help="independently compute Ω(M) by factoring M and assert it matches the encoding (slow for large M)",
    )
    args = p.parse_args(argv)

    results: list[dict[str, Any]] = []

    if args.mod_demo:
        M_s, n_s = 10007, 16
        j_exp = toy_transition_mod(M_s, n_s)
        j_got, pr = binary_search_mod_predicate(M_s, n_s)
        out = {"M": M_s, "n": n_s, "j_star_mod": j_exp, "j_binary_search": j_got, "probes": pr}
        print(json.dumps(out, indent=2))
        return

    if not args.json:
        print(
            "HQIV geometric 3SAT — score-driven patch search (see module docstring)\n"
            "SAT via brute force only; geometry implements **monotone P(j)** from S(j).\n"
        )

    for title, fm in TRIAL_FORMULAS:
        run_formula(
            title,
            fm,
            json_out=args.json,
            results=results,
            phi=args.phi,
            t=args.rapidity_t,
            wrap_min_j=args.wrap_min_j,
            wrap_max_rows=args.wrap_max_rows,
            wrap_hard_cap=args.wrap_hard_cap,
            verify_omega_factorization=args.verify_omega_factorization,
        )

    # Extra score-search sanity: ensure non-trivial threshold when total > 0
    if args.json:
        json.dump(results, sys.stdout, indent=2)
        print()
    else:
        print(
            "\n--- Notes ---\n"
            "  • Ω: literal-sum (1 per positive literal, 2 per negated). Default JSON uses `omega_literal_sum` only.\n"
            "    Optional `--verify-omega-factorization` runs trial division on M to count primes (slow on huge M).\n"
            "  • P(j) := (cumulative |ΔS| at j) ≥ T(M); T from M and total variation only.\n"
            "  • Two BSTs bracket the patch: first j with cum[j] ≥ T (from the left), last j with\n"
            "    cum[j] < T (from the right). ΔS and Δ²S along the arc are diagnostics for moiré;\n"
            "    formal bounds tie to Gaussian / triangle-inequality lenses (not proved in this script).\n"
            "  • Use `--json` for machine-readable output.\n"
            "  • `--mod-demo` runs M mod n binary search sanity only.\n"
            "  • `--phi` / `--rapidity-t` set the scalars for the Lean `polarAngleFromRapidity` mirror "
            "(default 1 / 1); `lean_rapidity_bridge` in JSON checks monotone s and cum ≤ K·Δs.\n"
            "  • `--verify-omega-factorization` — optional: independent prime-factor count on M vs literal sum.\n"
        )


if __name__ == "__main__":
    main()

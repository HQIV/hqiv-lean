#!/usr/bin/env python3
"""
Peel → sqrt gate → **Fin 4 × Fin 4 (torus) 2D FT** patch selection → **moiré BST** on that patch
(slope / jerk data from ``patch_search_score_driven``) → **divisor test** using **only** jerk/BST
indices mapped to integers (``j+7``, ``m % (j+7)``, ``j+1``, …).

**S³/S⁴ arc (modality):** ``n_patch`` gains a nonnegative term from a **unit** ``u ∈ [0,1)`` built from
the **ratio of sphere surface areas** at ``r = √m``: ``A₃(r)=2π²r³`` (``S³ ⊂ ℝ⁴``) over
``A₄(r)=(8π²/3)r⁴`` (``S⁴ ⊂ ℝ⁵``), then **wrap** ``ln(A₃/A₄)+ln(k)`` to fractional part — a point on the
modality quarter-strip (arity ``k``). Contrasts **three-square** obstructions (``S³`` lattice story)
vs **four-square** completeness (``S⁴`` side) in the number-theory layer.
**No** curvature / spiral-ray intercept factor oracle.

The 3SAT demo module is **imported only** for ``patch_search_score_driven`` / ``patch_window_length`` /
``moire_phase_fraction_from_M`` — **that file is not modified**.

Pipeline:

1. Peel factors of **2** only.
2. **Sqrt gate** — ``isqrt`` perfect square or floor divisor.
3. **S4×S4-style patch:** build a **4×4** real grid from ``m``, apply **2D DFT** on ``(ℤ/4ℤ)²``
   using **mpmath** ``mpf`` / ``mpc``. Working precision ``mp.prec`` (bits) scales with
   ``m.bit_length()`` (capped) so large odd cofactors do not silently use IEEE-double accuracy only
   in the torus FT step. Patch length ``n_patch`` **grows** with ``|m|`` and arity ``k`` (smaller
   intrinsic angle ``π/(2k)`` per step ⇒ longer ``j`` arc so slope/jerk landmarks are not squeezed
   into a tiny window). No artificial cap on that length here — **BST** itself uses ``O(log n)``
   predicate probes on the cumulative score. Note: the imported ``patch_search_score_driven`` still
   **materializes** the full ``samples[0‥n)`` array first, so runtime/memory are ``Θ(n_patch)`` unless
   the demo is changed to lazy/on-demand scores (pole-scale arcs with few jerks are exactly the
   regime where lazy evaluation matters).
4. **Moiré BST (every arity arc):** for ``k = 1, 2, …`` until ``⌊m^{1/k}⌋ < 2`` (same stop as the old
   intercept bound), run **Fin4×Fin4 FT → patch →** ``patch_search_score_driven(M, k, k, n_patch)``,
   then map BST / jerk indices to trial divisors. **First** ``d`` that divides ``m`` at any arity
   wins that split; cofactors recurse through the **same** sqrt + full arity sweep.
5. **No** single fixed ``k_enc`` for factoring — the pipeline **isolates a path on each arity arc**
   (BST / slope jerks) and trial-divides.

Optional ``--max-arity`` caps ``k`` for safety (default: full sweep to root bound).

``--json`` includes ``s4s4_ft_patch``, ``moire_arity_sweep``, ``moire_winning_arity_k``, ``moire_patch_bst``,
``hqiv_lean_alignment``.

Example::

  python3 scripts/factor_peel_intercept.py 221
  python3 scripts/factor_peel_intercept.py 221 --json
  python3 scripts/factor_peel_intercept.py 61 1949
  python3 scripts/factor_peel_intercept.py 61 1949 --wrap-k 2 --json
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from contextlib import contextmanager
from pathlib import Path
from typing import Any

from mpmath import mp

_SCRIPTS = Path(__file__).resolve().parent
if str(_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS))

import factor_from_curvature as ffc  # noqa: E402 — integer_kth_root_floor only (arity bound)
import hqiv_geometric_3sat_demo as g3sat  # noqa: E402


def hqiv_lean_alignment_payload() -> dict[str, Any]:
    return {
        "theorems_index": "AGENTS/THEOREMS.md",
        "role": "Python mirror: Fin4×Fin4 torus FT + n_patch arc from (A₃/A₄) wrap at √m + moiré/BST (hqiv_geometric_3sat_demo).",
        "mirrors_lean_definitions": [
            "Classical A(S³,r)=2π²r³, A(S⁴,r)=8π²r⁴/3 — ratio at r=√m, wrap ln(ratio)+ln(k)",
            "Hqiv.Algebra.OctonionSphereFourierPatch — Fourier patch / DFT concentration narrative",
            "Hqiv.Algebra.MoireJerkSphereModeBridge — slope-jerk ↔ moiré toy bridge",
            "hqiv_geometric_3sat_demo.patch_search_score_driven — unchanged import",
        ],
        "lean_theorems_not_claimed_by_this_cli": [
            "FT peak ⇒ divisor of m",
            "Moire BST crossing ⇒ factor",
        ],
    }


# --- peel / sqrt / bounded trial ----------------------------------------------


def prime_factors_mult_list(n: int) -> list[int]:
    if n < 2:
        return []
    x, fac = n, []
    d = 2
    while d * d <= x:
        while x % d == 0:
            fac.append(d)
            x //= d
        d += 1 if d == 2 else 2
    if x > 1:
        fac.append(x)
    return fac


def arithmetic_big_omega_cheap(m: int, *, trial_isqrt_cap: int = 10**6) -> int:
    if m < 2:
        return 0
    if math.isqrt(m) <= trial_isqrt_cap:
        return len(prime_factors_mult_list(m))
    return 0


def format_caret_from_prime_multiset(factors: list[int]) -> str:
    if not factors:
        return "1"
    fac = sorted(factors)
    parts: list[str] = []
    i = 0
    while i < len(fac):
        p = fac[i]
        j = i + 1
        while j < len(fac) and fac[j] == p:
            j += 1
        e = j - i
        parts.append(f"{p}^{e}" if e > 1 else str(p))
        i = j
    return ", ".join(parts)


def peel_twos(n: int) -> tuple[list[int], int]:
    out: list[int] = []
    while n % 2 == 0 and n > 1:
        out.append(2)
        n //= 2
    return out, n


def sqrt_floor_factor(n: int) -> tuple[int | None, str]:
    if n < 4:
        return None, "n_lt_4"
    r = math.isqrt(n)
    if r < 2:
        return None, "isqrt_lt_2"
    if r * r == n:
        return r, "perfect_square"
    if n % r == 0:
        return r, "floor_sqrt_divides"
    return None, "sqrt_gate_miss"


# --- Fin 4 × Fin 4 torus FT (S4×S4 indexing: two 4-cycles) -----------------------


def mpmath_prec_bits_for_m(m: int) -> int:
    """
    Binary precision (bits) for mpmath ``mp.prec``, scaled with the size of ``m``.
    Capped so pathological inputs do not allocate extreme precision.
    """
    bl = max(1, abs(m).bit_length())
    # 4×4 DFT: O(16) terms per bin; tie precision to bit length of the fingerprinted integer.
    return min(20000, max(64, bl * 4 + 64))


@contextmanager
def mpmath_prec_scope_for_m(m: int):
    """Set ``mp.prec`` from ``m.bit_length()`` for the torus FT, then restore the previous context."""
    old_prec, old_dps = mp.prec, mp.dps
    try:
        mp.prec = mpmath_prec_bits_for_m(m)
        yield
    finally:
        mp.prec = old_prec
        mp.dps = old_dps


def _fin4_fin4_grid_mpf(m: int) -> list[list[Any]]:
    """Real 4×4 grid fingerprinting ``m`` on ``(ℤ/4ℤ)²`` indices (mpmath ``mpf``)."""
    g: list[list[Any]] = []
    for i in range(4):
        row: list[Any] = []
        for j in range(4):
            mod = max(1, 11 + i + j)
            num = (m * (i + 1) + (j + 1) * (i + 3)) % mod
            den = mp.mpf(mod)
            row.append(mp.mpf(num) / den)
        g.append(row)
    return g


def _dft2_power_matrix_mpf(a: list[list[Any]]) -> tuple[list[list[Any]], int, int]:
    """2D DFT on 4×4; returns |F|² grid (mpf) and argmax index (k1,k2)."""
    n = 4
    pows: list[list[Any]] = [[mp.mpf(0) for _ in range(n)] for _ in range(n)]
    best_i, best_j = 0, 0
    best_v = mp.mpf(-1)
    pi = mp.pi
    for k1 in range(n):
        for k2 in range(n):
            s = mp.mpc(0)
            for i in range(n):
                for j in range(n):
                    angle = -2 * pi * (k1 * i + k2 * j) / n
                    w = mp.exp(mp.mpc(0, angle))
                    s += a[i][j] * w
            p = abs(s) ** 2
            pows[k1][k2] = p
            if p > best_v:
                best_v = p
                best_i, best_j = k1, k2
    return pows, best_i, best_j


def fin4_fin4_grid_from_m(m: int) -> list[list[float]]:
    """Real 4×4 grid as Python floats (for callers/tests); uses mpf internally at ``m``'s precision."""
    with mpmath_prec_scope_for_m(m):
        g = _fin4_fin4_grid_mpf(m)
    return [[float(x) for x in row] for row in g]


def s3_s4_surface_areas_at_sqrt_m(m: int) -> tuple[float, float, float]:
    """
    Round unit spheres: ``S³ ⊂ ℝ⁴`` has ``A₃(r)=2π²r³``; ``S⁴ ⊂ ℝ⁵`` has ``A₄(r)=(8π²/3)r⁴``.
    Evaluate at ``r = √m``. Then ``A₃/A₄ = 3/(4r) = 3/(4√m)`` (dimensionless ratio of areas).
    """

    with mpmath_prec_scope_for_m(m):
        r = mp.sqrt(mp.mpf(m))
        A3 = mp.mpf(2) * mp.pi**2 * r**3
        A4 = (mp.mpf(8) / mp.mpf(3)) * mp.pi**2 * r**4
        ratio = A3 / A4
        return float(A3), float(A4), float(ratio)


def shell_modality_arc_unit(m: int, k_enc: int) -> tuple[float, dict[str, Any]]:
    """
    **Wrap** ``ln(A₃/A₄) + ln(k)`` to fractional part in ``[0,1)`` — a “point” on the modality strip
    from the **S³ vs S⁴** surface-area ratio at the ``√m`` shell (three-square vs four-square ladder
    narrative: obstructions on the ``S³`` side vs full coverage toward ``S⁴``).
    """

    k = max(1, int(k_enc))
    A3, A4, ratio = s3_s4_surface_areas_at_sqrt_m(m)
    if ratio <= 0.0:
        u = 0.0
        lm_val: float | None = None
    else:
        lm = math.log(ratio) + math.log(k)
        u = lm - math.floor(lm)
        lm_val = lm
    meta: dict[str, Any] = {
        "s3_surface_area_sqrt_m": A3,
        "s4_surface_area_sqrt_m": A4,
        "s3_over_s4_surface_area_ratio": ratio,
        "shell_modality_ln_sum": lm_val,
        "shell_modality_arc_unit": u,
        "shell_modality_note": "u = frac(ln(A₃/A₄)+ln k) at r=√m; A₃=2π²r³, A₄=8π²r⁴/3",
    }
    return u, meta


def n_patch_moire_arc_length(m: int, k_enc: int, base: int, bump: int) -> tuple[int, dict[str, Any]]:
    """
    Number of samples ``j = 0 … n_patch−1`` passed into ``moire_score_samples`` / ``patch_search_score_driven``.

    **Arc scaling:** nonnegative length from ``shell_modality_arc_unit`` (``S³/S⁴`` area ratio wrap +
    ``ln k``), plus a linear baseline in ``bitlen(m)`` and ``k``. Full-array materialization note unchanged.

    ``base + bump`` retains the Fin4×Fin4 FT modulation on top of the 3SAT-style window.
    """
    bl = max(1, abs(m).bit_length())
    k = max(1, int(k_enc))
    u, surf_meta = shell_modality_arc_unit(m, k_enc)
    arc_extra_linear = bl * (4 + k // 4) + k * 12
    arc_from_shell = int(u * (bl * 64 + k * 48 + 32))
    raw = int(base) + int(bump) + arc_extra_linear + arc_from_shell
    n_patch = max(8, raw)
    meta: dict[str, Any] = {
        **surf_meta,
        "n_patch_arc_extra_linear": arc_extra_linear,
        "n_patch_arc_from_shell_surface": arc_from_shell,
    }
    return n_patch, meta


def ratio_pair_angle_report(a: int, b: int, *, wrap_k: int = 2) -> dict[str, Any]:
    """
    For positive integers ``a``, ``b``:

    * ``atan2(a,b)`` — angle (radians) attached to the ratio ``a/b`` in the standard plane sense.
    * ``atan2(b,a)`` — angle for ``b/a``.
    * For ``m = a*b``, the **S³/S⁴ wrap** ``shell_modality_arc_unit(m, wrap_k)`` and the same unit
      interpreted as rotation on a **full** turn ``2π`` and on a **quarter** arc ``π/2``.
    """
    if a < 1 or b < 1:
        raise ValueError("a and b must be >= 1")
    ang_ab = math.atan2(float(a), float(b))
    ang_ba = math.atan2(float(b), float(a))
    m = a * b
    k = max(1, int(wrap_k))
    u, s3_meta = shell_modality_arc_unit(m, k)
    tau = 2.0 * math.pi
    quarter = math.pi / 2.0
    return {
        "a": a,
        "b": b,
        "product_m": m,
        "ratio_a_over_b": a / float(b),
        "ratio_b_over_a": b / float(a),
        "angle_atan2_a_b_rad": ang_ab,
        "angle_atan2_a_b_deg": math.degrees(ang_ab),
        "angle_atan2_b_a_rad": ang_ba,
        "angle_atan2_b_a_deg": math.degrees(ang_ba),
        "wrap_arity_k": k,
        "shell_modality_arc_unit_u": u,
        "wrap_angle_full_turn_rad": u * tau,
        "wrap_angle_full_turn_deg": math.degrees(u * tau),
        "wrap_angle_quarter_arc_rad": u * quarter,
        "wrap_angle_quarter_arc_deg": math.degrees(u * quarter),
        "s3s4_wrap_meta": s3_meta,
    }


def s4s4_ft_patch_spec(m: int, k_enc: int) -> dict[str, Any]:
    """
    Use **2D FT energy** on Fin4×Fin4 to modulate ``n_patch`` around ``patch_window_length(k_enc)``,
    and **S³/S⁴ surface-area ratio wrap** at ``√m`` to set arc contribution.
    """
    prec_bits = mpmath_prec_bits_for_m(m)
    with mpmath_prec_scope_for_m(m):
        grid_mpf = _fin4_fin4_grid_mpf(m)
        _pows_mpf, k1, k2 = _dft2_power_matrix_mpf(grid_mpf)
    grid = [[float(x) for x in row] for row in grid_mpf]
    base = g3sat.patch_window_length(max(1, k_enc))
    bump = (k1 + k2) % 5
    n_patch, arc_meta = n_patch_moire_arc_length(m, k_enc, base, bump)
    out: dict[str, Any] = {
        "fin4_fin4_grid": grid,
        "ft_argmax_k1": k1,
        "ft_argmax_k2": k2,
        "n_patch": n_patch,
        "patch_window_length_k_enc_only": base,
        "n_patch_ft_bump": bump,
        "n_patch_arc_extra_formula": "base+bump + linear(bl,k) + u*(64*bl+48*k+32) with u=frac(ln(A₃/A₄)+ln k)",
        "m_bit_length": abs(m).bit_length(),
        "mpmath_prec_bits": prec_bits,
        "note": "Fin4×Fin4 torus FT + n_patch arc from S³/S⁴ surface area ratio at √m (wrapped)",
    }
    out.update(arc_meta)
    return out


def _trial_integers_for_odd_cofactor(m: int, cand: set[int]) -> set[int]:
    """After peeling 2s, odd ``m`` has no even proper divisors — drop even trial integers."""
    if m % 2 == 1:
        return {x for x in cand if x % 2 == 1}
    return set(cand)


def moire_divisor_trial_trace(m: int, ps: g3sat.PatchSearchScore) -> dict[str, Any]:
    """
    Full trial-divisor picture for one ``patch_search_score_driven`` result: raw integer candidates
    from BST/jerk landmarks, which lie in ``(1, m)``, which divide ``m`` (tried in sorted order),
    and which are in-band but not divisors.
    """
    cand: set[int] = set()
    js = {ps.j_first_ge_threshold, ps.j_last_below_threshold, ps.max_slope_jump_j}
    per_j: list[dict[str, Any]] = []
    for j in sorted(js):
        if j < 0 or j >= ps.n:
            per_j.append({"j": j, "skipped": "j_outside_0_n"})
            continue
        mod = j + 7
        r = m % mod if mod > 0 else None
        step: dict[str, Any] = {
            "j": j,
            "j_plus_1": j + 1,
            "j_plus_7": j + 7,
            "m_mod_j_plus_7": r,
        }
        cand.add(j + 1)
        cand.add(j + 7)
        if mod > 0:
            if r is not None and r > 1:
                cand.add(r)
            if mod > 1 and mod < m:
                cand.add(mod)
        per_j.append(step)

    cand = _trial_integers_for_odd_cofactor(m, cand)
    raw_sorted = sorted(cand)
    in_open_interval = sorted(x for x in cand if 1 < x < m)
    divisors_sorted = [x for x in in_open_interval if m % x == 0]
    rejected = [x for x in in_open_interval if m % x != 0]
    return {
        "j_landmarks": {
            "j_first_ge_threshold": ps.j_first_ge_threshold,
            "j_last_below_threshold": ps.j_last_below_threshold,
            "max_slope_jump_j": ps.max_slope_jump_j,
            "n_patch": ps.n,
        },
        "per_j_landmark": per_j,
        "raw_candidates_sorted": raw_sorted,
        "candidates_in_1_lt_x_lt_m": in_open_interval,
        "rejected_in_range_not_divisor": rejected,
        "divisors_accepted_sorted": divisors_sorted,
        "first_trial_winner": divisors_sorted[0] if divisors_sorted else None,
    }


def divisor_candidates_from_j_indices(m: int, n_patch: int, js: set[int]) -> list[int]:
    """Map arbitrary patch indices ``j`` to trial divisors using the moire integer map."""

    cand: set[int] = set()
    for j in js:
        if j < 0 or j >= n_patch:
            continue
        cand.add(j + 1)
        cand.add(j + 7)
        mod = j + 7
        if mod > 0:
            r = m % mod
            if r > 1:
                cand.add(r)
            if mod > 1 and mod < m:
                cand.add(mod)
    cand = _trial_integers_for_odd_cofactor(m, cand)
    return sorted(x for x in cand if 1 < x < m and m % x == 0)


def divisor_candidates_from_moire_indices(m: int, ps: g3sat.PatchSearchScore) -> list[int]:
    """
    Map BST / **slope jerk** indices to trial divisors (same ``j`` lane as ``moire_score_samples``).
    """
    js = {ps.j_first_ge_threshold, ps.j_last_below_threshold, ps.max_slope_jump_j}
    return divisor_candidates_from_j_indices(m, ps.n, js)


def first_factor_moire_s4s4(
    m: int,
    k_enc: int,
    *,
    return_trial_trace: bool = False,
) -> tuple[int | None, g3sat.PatchSearchScore, dict[str, Any], dict[str, Any] | None]:
    spec = s4s4_ft_patch_spec(m, k_enc)
    n_patch = int(spec["n_patch"])
    k_safe = max(1, k_enc)
    ps = g3sat.patch_search_score_driven(m, k_safe, k_safe, n_patch)
    divs_legacy = divisor_candidates_from_moire_indices(m, ps)
    pred = g3sat.predictive_patch_prune_trace(ps, k_safe, shell_m=int(m))
    divs_predictive = divisor_candidates_from_j_indices(m, ps.n, set(pred.get("kept_j") or []))
    divs = sorted(set(divs_legacy) | set(divs_predictive))
    best = divs[0] if divs else None
    spec["predictive_patch_prune"] = pred
    spec["divisors_from_legacy_landmarks"] = divs_legacy
    spec["divisors_from_predictive_prune"] = divs_predictive
    spec["divisors_union_sorted"] = divs
    trace = moire_divisor_trial_trace(m, ps) if return_trial_trace else None
    return best, ps, spec, trace


def _moire_root_bound_stop(m: int, k: int) -> bool:
    """True when we stop increasing k: same as old intercept (⌊m^{1/k}⌋ < 2 for k ≥ 2)."""
    if k < 2:
        return False
    return ffc.integer_kth_root_floor(m, k) < 2


def moire_arity_sweep_first_divisor(
    m: int,
    *,
    max_arity: int | None = None,
    trial_trace: bool = False,
) -> tuple[int | None, int | None, list[dict[str, Any]], g3sat.PatchSearchScore | None, dict[str, Any] | None]:
    """
    For k = 1, 2, … until ⌊m^{1/k}⌋ < 2 (and optionally max_arity), run S4×S4 FT + moiré BST + jerk
    trial divide. Returns first divisor, winning arity k, per-k records, last ps/spec.
    """
    records: list[dict[str, Any]] = []
    ps_last: g3sat.PatchSearchScore | None = None
    spec_last: dict[str, Any] | None = None
    k = 1
    while k <= m:
        if max_arity is not None and k > max_arity:
            break
        if _moire_root_bound_stop(m, k):
            break
        root_k = ffc.integer_kth_root_floor(m, k)
        fac, ps, spec, tr = first_factor_moire_s4s4(m, k, return_trial_trace=trial_trace)
        ps_last, spec_last = ps, spec
        row: dict[str, Any] = {
            "arity_k": k,
            "root_bound_k": root_k,
            "n_patch": spec["n_patch"],
            "jerk_divisor": fac,
            "j_first_ge_threshold": ps.j_first_ge_threshold,
            "j_last_below_threshold": ps.j_last_below_threshold,
            "max_slope_jump_j": ps.max_slope_jump_j,
        }
        if trial_trace and tr is not None:
            row["trial_divisor_trace"] = tr
        records.append(row)
        if fac is not None:
            return fac, k, records, ps, spec
        k += 1
        if k > 100000:
            break
    return None, None, records, ps_last, spec_last


def _first_split_factor(m: int, *, max_arity: int | None = None) -> int | None:
    if m < 2:
        return None
    ds, _ = sqrt_floor_factor(m)
    if ds is not None:
        return ds
    fac, _, _, _, _ = moire_arity_sweep_first_divisor(m, max_arity=max_arity, trial_trace=False)
    return fac


def _pipeline_prime_multiset_odd(m: int, *, max_arity: int | None = None) -> list[int]:
    if m <= 1:
        return []
    d = _first_split_factor(m, max_arity=max_arity)
    if d is not None and 1 < d < m and m % d == 0:
        c = m // d
        return _pipeline_prime_multiset_odd(d, max_arity=max_arity) + _pipeline_prime_multiset_odd(
            c, max_arity=max_arity
        )
    # No trial division — only sqrt + moiré jerk candidates (module doc).
    return [m]


def pipeline_prime_multiset(n0: int, *, max_arity: int | None = None) -> list[int]:
    twos, odd = peel_twos(n0)
    out = [2] * len(twos)
    if odd <= 1:
        return sorted(out)
    out.extend(_pipeline_prime_multiset_odd(odd, max_arity=max_arity))
    return sorted(out)


def _patch_search_score_summary(ps: g3sat.PatchSearchScore, *, head: int = 64) -> dict[str, Any]:
    n = len(ps.samples)
    h = min(n, head)
    return {
        "n_patch": ps.n,
        "threshold": ps.threshold,
        "cum_total": ps.cum_total,
        "j_first_ge_threshold": ps.j_first_ge_threshold,
        "j_last_below_threshold": ps.j_last_below_threshold,
        "predicate_probes_left": ps.predicate_probes_left,
        "predicate_probes_right": ps.predicate_probes_right,
        "log2_n_ceil": ps.log2_n_ceil,
        "max_slope_jump_j": ps.max_slope_jump_j,
        "max_slope_jump_abs": ps.max_slope_jump_abs,
        "samples_len": n,
        "samples_head": ps.samples[:h],
        "cum_head": ps.cum[:h],
        "slopes_head": ps.slopes[: min(len(ps.slopes), h)] if ps.slopes else [],
        "slope_jumps_head": ps.slope_jumps[: min(len(ps.slope_jumps), h)] if ps.slope_jumps else [],
    }


def run_pipeline(
    n0: int,
    *,
    max_arity: int | None = None,
    debug: bool = False,
) -> dict[str, Any]:
    twos, m = peel_twos(n0)

    if m <= 1:
        pm0 = pipeline_prime_multiset(n0, max_arity=max_arity)
        facm0 = [p for p in pm0 if p != 2]
        return {
            "input": n0,
            "twos_peeled": twos,
            "odd_cofactor": m,
            "factorization_caret": format_caret_from_prime_multiset(pm0),
            "m_arithmetic_big_omega": len(facm0),
            "m_prime_factors_with_multiplicity": facm0,
            "stage": "trivial_after_peel",
            "factor_found": None,
            "hqiv_lean_alignment": hqiv_lean_alignment_payload(),
        }

    d_sqrt, sqrt_reason = sqrt_floor_factor(m)
    fac_m: int | None = None
    k_win: int | None = None
    arity_records: list[dict[str, Any]] = []
    ps_out: g3sat.PatchSearchScore | None = None
    spec_out: dict[str, Any] | None = None

    if d_sqrt is not None:
        factor_found: int | None = d_sqrt
        factor_source: str | None = "sqrt_gate"
    else:
        fac_m, k_win, arity_records, ps_out, spec_out = moire_arity_sweep_first_divisor(
            m, max_arity=max_arity, trial_trace=debug
        )
        if fac_m is not None:
            factor_found, factor_source = fac_m, "moire_s4s4_jerk_candidates"
        else:
            factor_found, factor_source = None, None

    if factor_found is None:
        stage = "moire_jerk_miss"
    elif factor_source == "sqrt_gate":
        stage = "sqrt_gate"
    else:
        stage = "moire_s4s4"

    pm_full = pipeline_prime_multiset(n0, max_arity=max_arity)
    facm = [p for p in pm_full if p != 2]
    om = len(facm)

    if d_sqrt is not None:
        s4_payload: dict[str, Any] = {"note": "moire_arity_sweep_not_run_sqrt_gate_hit"}
        moire_bst_payload: dict[str, Any] | None = None
    elif spec_out is not None and ps_out is not None:
        s4_payload = spec_out
        k_display = k_win if k_win is not None else (arity_records[-1]["arity_k"] if arity_records else None)
        moire_bst_payload = {
            "same_pipeline_as": "hqiv_geometric_3sat_demo.patch_search_score_driven",
            "M": int(m),
            "moire_winning_arity_k": k_win,
            "k_enc": k_display,
            "num_clauses": k_display,
            "n_patch": spec_out["n_patch"],
            "score_search": _patch_search_score_summary(ps_out),
            "moire_phase_fraction_V8_mod1": g3sat.moire_phase_fraction_from_M(int(m)),
            "shell_V8_A7_strings": g3sat.shell_volume8_area7_strings(int(m)),
        }
    else:
        s4_payload = {}
        moire_bst_payload = None

    out: dict[str, Any] = {
        "input": n0,
        "twos_peeled": twos,
        "odd_cofactor": m,
        "factorization_caret": format_caret_from_prime_multiset(pm_full),
        "moire_winning_arity_k": k_win,
        "moire_arity_sweep": arity_records,
        "max_arity_cap": max_arity,
        "m_arithmetic_big_omega": om,
        "m_prime_factors_with_multiplicity": facm,
        "sqrt_reason": sqrt_reason,
        "factor_found": factor_found,
        "factor_source": factor_source,
        "stage": stage,
        "s4s4_ft_patch": s4_payload,
        "moire_patch_bst": moire_bst_payload,
        "hqiv_lean_alignment": hqiv_lean_alignment_payload(),
    }
    return out


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__.split("Example::", 1)[0].strip())
    p.add_argument(
        "nums",
        nargs="+",
        type=int,
        help="one integer n (factor pipeline), or two integers a b (ratio / wrap angles)",
    )
    p.add_argument(
        "--max-arity",
        type=int,
        default=None,
        metavar="K",
        help="optional cap on arity k in the moiré sweep (default: sweep until ⌊m^{1/k}⌋<2)",
    )
    p.add_argument(
        "--wrap-k",
        type=int,
        default=2,
        metavar="K",
        help="arity k in ln(A₃/A₄)+ln(k) for two-arg mode (default: 2)",
    )
    p.add_argument("--json", action="store_true")
    p.add_argument(
        "--debug",
        action="store_true",
        help="verbose text: sqrt reason, FT summary, and per-arity raw trial divisors vs divisors that divide m",
    )
    args = p.parse_args()
    nums = args.nums
    if len(nums) > 2:
        raise SystemExit("provide one integer n, or exactly two integers a b")
    if len(nums) == 2:
        a, b = nums[0], nums[1]
        if a < 1 or b < 1:
            raise SystemExit("a and b must be >= 1")
        if args.wrap_k < 1:
            raise SystemExit("--wrap-k must be >= 1")
        rep = ratio_pair_angle_report(a, b, wrap_k=args.wrap_k)
        if args.json:
            print(json.dumps(rep, indent=2, sort_keys=True))
        else:
            print(f"a={rep['a']}  b={rep['b']}  product_m={rep['product_m']}")
            print(
                f"atan2(a,b)  (angle for a/b): {rep['angle_atan2_a_b_rad']:.12f} rad  "
                f"({rep['angle_atan2_a_b_deg']:.6f}°)"
            )
            print(
                f"atan2(b,a)  (angle for b/a): {rep['angle_atan2_b_a_rad']:.12f} rad  "
                f"({rep['angle_atan2_b_a_deg']:.6f}°)"
            )
            print(
                f"S³/S⁴ wrap (m=a*b, k={rep['wrap_arity_k']}):  "
                f"u = frac(ln(A₃/A₄)+ln k) = {rep['shell_modality_arc_unit_u']:.12f}"
            )
            print(
                f"  as angle on full turn 2π: {rep['wrap_angle_full_turn_rad']:.12f} rad  "
                f"({rep['wrap_angle_full_turn_deg']:.6f}°)"
            )
            print(
                f"  as angle on quarter arc π/2: {rep['wrap_angle_quarter_arc_rad']:.12f} rad  "
                f"({rep['wrap_angle_quarter_arc_deg']:.6f}°)"
            )
        return

    n0 = nums[0]
    if n0 < 1:
        raise SystemExit("n must be >= 1")
    if args.max_arity is not None and args.max_arity < 1:
        raise SystemExit("--max-arity must be >= 1 when set")

    out = run_pipeline(n0, max_arity=args.max_arity, debug=args.debug)
    if args.json:
        print(json.dumps(out, indent=2, sort_keys=True))
    elif not args.debug:
        print(out.get("factorization_caret", "1"))
    else:
        print(f"input={out['input']}")
        print(f"twos_peeled={out['twos_peeled']} odd_cofactor={out['odd_cofactor']}")
        print(f"factorization_caret={out.get('factorization_caret', '1')}")
        print(f"sqrt_reason={out.get('sqrt_reason')}")
        mas = out.get("moire_arity_sweep") or []
        print(f"moire_arity_sweep_steps={len(mas)} moire_winning_arity_k={out.get('moire_winning_arity_k')}")
        sp = out.get("s4s4_ft_patch") or {}
        print(
            f"s4s4_ft: k1={sp.get('ft_argmax_k1')} k2={sp.get('ft_argmax_k2')} "
            f"n_patch={sp.get('n_patch')}"
        )
        mpb = out.get("moire_patch_bst")
        if mpb:
            ss = mpb.get("score_search") or {}
            print(
                "moire_patch_bst: "
                f"k_enc={mpb.get('k_enc')} n_patch={mpb.get('n_patch')}  "
                f"j_first_T={ss.get('j_first_ge_threshold')} max_slope_jump_j={ss.get('max_slope_jump_j')}  "
                f"T={ss.get('threshold')}"
            )
        pp = (sp.get("predictive_patch_prune") or {}) if isinstance(sp, dict) else {}
        if pp:
            kept = pp.get("kept_j") or []
            print(
                "predictive_patch_prune: "
                f"kept={len(kept)} cov={pp.get('coverage_ratio')} "
                f"walk_cov={pp.get('walk_coverage_ratio')} "
                f"visits={pp.get('visit_count')}/cap={pp.get('visit_cap_walk')} "
                f"isqrt_m={pp.get('isqrt_shell_m')} "
                f"mod={pp.get('residue_mod')} allowed={pp.get('allowed_residues')}"
            )
        for rec in mas:
            tr = rec.get("trial_divisor_trace")
            if not tr:
                continue
            ak = rec.get("arity_k")
            print(f"--- trial_divisors arity_k={ak} ---")
            jl = tr.get("j_landmarks") or {}
            print(
                f"  BST/jerk j: j_first_ge_T={jl.get('j_first_ge_threshold')} "
                f"j_last_below_T={jl.get('j_last_below_threshold')} max_slope_jump_j={jl.get('max_slope_jump_j')} "
                f"n_patch={jl.get('n_patch')}"
            )
            print(f"  raw_candidates_sorted: {tr.get('raw_candidates_sorted')}")
            print(f"  in_(1,m)_interval: {tr.get('candidates_in_1_lt_x_lt_m')}")
            print(f"  rejected_in_range_not_divisor: {tr.get('rejected_in_range_not_divisor')}")
            print(f"  divisors_accepted_sorted (smallest used first): {tr.get('divisors_accepted_sorted')}")
            print(f"  first_trial_winner: {tr.get('first_trial_winner')}")
        print(f"stage={out.get('stage')} factor_source={out.get('factor_source')} factor_found={out.get('factor_found')}")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
Lean-aligned 3-spiral factor oracle with optional curvature weighting.

Design mirrors the scaffold:
- rapidity phase is weighted by omega_k_imprint (rational **or** Ramanujan τ(arity) / arity^{11/2})
- three rotated rays (0, 2π/3, 4π/3): base angle at the **pole** of the **−arity** rotation axis
  (``wrap(-π/(2k) + π/2)`` on **S¹**), then ``φ·t·Ω·δθ′(E′)`` with **``E′ = (shell number)/2``**
  (turns tied to **m/2**, same convention as equator bookkeeping)
- projection candidates from rays only (no neighbor-shell integer anchors); even ``n`` peels a 2 first
  when the sieve is on
- exact divisibility check and canonical pair selection

**Discrete time:** In the HQIV shell story, `t` is best read as a **step count** (integer horizon
steps). Scripts accept `float` for CLI convenience; use **`--t 1`**, **`--t 2`**, … for a literal
integer-step interpretation. (Lean still types `t : ℝ` in `timeAngle φ t`.)

**Rapidity / intercept (equator):** The hit you care about is the **intercept on the equator** after
stripping full windings: take **``m/2``** full turns, **reduce mod 1 turn** (fractional part only),
then **``cos``/``sin``** of **``τ``** times that fraction — same as **``(π·m) mod τ``** for integer
shell **``m``** (parity: even **``m``** → angle **0**, odd **``m``** → angle **``π``**). Optional
discrete band **``[2,⌊m/2⌋]``** is secondary; turn-index list is capped or omitted for huge ``m``.
Continuum phase is still ``φ·t·Ω·δθ′(E′)`` on ℝ.

**Phase index:** Rays use **`delta_theta_prime(E′)`** with **`E′ = n/2`** (Lean `E′ : ℝ`). **`--phase-shell`**
adds **diagnostics** only: **`neighbor_curve_mid`** records Maxwell midpoint data; **`triplet_residue`**
records which shell was picked — neither changes **`E′`** on the rays. **Not** the arithmetic mean of
bracket **``atan2(b,a)``** for ``((m-1)/2,2)`` and ``(2,(m+1)/2)``, which tends to **π/4** for large `m`.
Use **`triplet_residue`** for a discrete pick among `{m-1,m,m+1}`.

**Spiral / periodicity (arity k):** The bracket gives **two** directions in the factor quadrant; the
oracle’s rays are a **single** base angle plus **three** arms separated by **2π/3** (triadic
period), then tilted by the **arity axis** ``π/(2k)``. So meeting a target direction is a **wrap**
problem on **S¹**: one winds with the shell phase (``φ·t·Ω·δθ′``), again with the **−arity** (axis)
offset, and the 3‑fold repetition—often **more than one** full turn before a ray aligns with a
discrete factor direction. For **k = 2**, ``π/4`` is only the **arity axis / diagonal** (eight sectors
around ``S¹``); it is **not** the typical **pair angle** ``atan2(b,a)`` for a nontrivial factor pair
(unless ``a=b``). Pairs like **(3,5)** vs **(5,3)** are **swap‑symmetric** about that diagonal and
can appear from **opposite** quadrants on a normalized ``S²`` slice depending on wrap / arm.

**Rapidity vs shell (equator):** On the picture where each **branch** of the spiral is a curve on
``S²``, that curve crosses a fixed **equatorial** slice **once** — **one crossing per factor**
direction (a nontrivial semiprime has **two** factors, hence **two** such curves / two crossings).
The oracle uses **one triad** at **``E′ = n/2``** for ``δθ′`` (turns tied to **m/2**) and a base angle
at the **pole** of the **−arity** axis on **S¹**; seeding is from spiral projections only (no
integer anchors on neighbor shells).

**Parity (odd vs even shell):** The nontrivial **equator** crossing picture is for **odd** ``n``:
generic intersections with the mid sphere, not through the rotation poles. **Even** ``n`` sits in the
**pole** / degenerate case: the branch meets the axis (and classically **2** is always a factor),
so the “trivial” peel is the analogue of **trivial zeros** (ζ on negative even integers) — not the
same phase as an odd-shell equator hit. With the sieve on, even ``n`` is handled by the fast **2**
path first.

**Phase-shell modes** (``neighbor_curve_mid``, ``triplet_residue``) still emit **diagnostic** bracket /
triplet metadata; **rays** always use ``E′ = n/2`` and the **−arity pole** scaffold above.

Examples:
  python scripts/factor_from_curvature.py 221
  python scripts/factor_from_curvature.py 221 --curvature-rational +1/60
  python scripts/factor_from_curvature.py 945 --curvature-rational -1/30 --json

Visualization (same arity axis + 3-ray geometry): `scripts/plot_arity_spiral_meets.py`
(`--png out.png` needs matplotlib; `--csv` / `--meet-scan` work without it).
"""

from __future__ import annotations

import argparse
import json
import math
from fractions import Fraction
from typing import Any


EPS = 1e-12

# Same semantics as factor_from_curvature.py — why found_factor can differ from gradient_best_d.
PRIME_GRADIENT_WALK_EXPLAINED = (
    "Prime-step walk (deterministic, not magic): seeds come from spiral ray projections, "
    "expanded by --window, plus phase-shell anchors; outer loop order is sorted(seeds), "
    "inner loop is primes p up to min(root_bound, 257). Each inner iteration: increment the global step "
    "counter; then if 2≤cur≤root_bound and n%cur==0, return cur immediately; else move cur to cur−p or "
    "cur+p according to which of the two candidate pairs has smaller angular gap to the three rays. "
    "gradient_best_d tracks the integer cur that achieved the smallest such gap anywhere in the walk; "
    "it need not divide n. The returned factor is the first cur that passes the divisibility test in "
    "that fixed seed×prime order."
)


def wrap_pi(x: float) -> float:
    """Wrap angle to ``(-π, π]`` (same convention as ``wrapped_angle_diff``)."""
    return (x + math.pi) % (2.0 * math.pi) - math.pi


def spiral_turn_e_prime(shell_n: int) -> float:
    """
    Shell index **E′** for ``δθ′(E′)`` in the rapidity **tipping** term: **half** the shell number.

    Aligns the Maxwell turn with **m/2** full turns (see ``rapidity_turn_shell_bookkeeping``).
    """
    if shell_n <= 0:
        return 0.0
    return float(shell_n) / 2.0


def parse_rational(value: str) -> Fraction:
    """Parse strings like '+1/60', '-2/15', '0', '3'."""
    try:
        return Fraction(value)
    except Exception as exc:  # pragma: no cover - argparse path
        raise argparse.ArgumentTypeError(f"invalid rational value: {value!r}") from exc


def horizon_quarter_period() -> float:
    return (2.0 * math.pi) / 4.0


def delta_theta_prime_float(e_prime: float) -> float:
    """Lean `ModifiedMaxwell.delta_theta_prime E′` with `E′` real (here: shell index on the tipping curve)."""
    return math.atan(e_prime) * horizon_quarter_period()


def delta_theta_prime(m: int) -> float:
    return delta_theta_prime_float(float(m))


# OEIS A000594 τ(1)..τ(40) for environments without sympy (index n = τ(n)).
_TAU_FALLBACK: tuple[int, ...] = (
    0,
    1,
    -24,
    252,
    -1472,
    4830,
    -6048,
    -16744,
    84480,
    -113643,
    -115920,
    534612,
    -370944,
    -577738,
    401856,
    1217160,
    987136,
    -6905934,
    2727432,
    10661420,
    -7109760,
    -4219488,
    -18636864,
    52756480,
    195035040,
    -284447232,
    -732120000,
    396474480,
    1284060384,
    -703791360,
    -1060270048,
    -6905938944,
    7627169752,
    32794991616,
    -16506489600,
    -36497349696,
    90467805120,
    7004052480,
    -114690867152,
    153959554944,
    -259637719600,
)


def ramanujan_tau(n: int) -> int:
    """
    Ramanujan's τ(n): coefficient of q^n in the weight-12 cusp form Δ (modular discriminant).

    Uses sympy when installed; otherwise a built-in table for n <= 40.
    Not a proof hook to classical factoring — only a **normalized** imprint for Ω_k.
    """
    if n < 1:
        raise ValueError("ramanujan_tau requires n >= 1")
    try:
        from sympy.functions.combinatorial.numbers import ramanujan_tau as rtau

        return int(rtau(n))
    except Exception:
        if n < len(_TAU_FALLBACK):
            return _TAU_FALLBACK[n]
        raise RuntimeError(
            f"ramanujan_tau({n}): install sympy (pip install sympy) or use n <= {len(_TAU_FALLBACK) - 1}"
        ) from None


def omega_k_ramanujan_arity(arity: int) -> float:
    """
    Petersson-style normalization on the arity index k (weight-11/2 denominator):

        Ω_k = 1 + τ(k) / k^{11/2}

    so |τ(k)|/k^{11/2} is O(1) at primes (Ramanujan–Petersson bound |a_p| <= 2).

    This ties Ω_k to the **same index k** as `--arity` / the factor-sphere arity in the oracle.
    """
    k = max(2, int(arity))
    tau_k = ramanujan_tau(k)
    denom = float(k) ** (11.0 / 2.0)
    return 1.0 + float(tau_k) / denom


def omega_k_imprint(
    curvature: Fraction,
    omega_override: float | None = None,
    *,
    arity: int = 2,
    omega_mode: str = "rational",
) -> float:
    """
    Curvature imprint channel Ω_k used in the rapidity phase.

    - If `omega_override` is provided, use it directly (Lean-style free real slot).
    - ``omega_mode == "rational"``: Ω_k = 1 + curvature_rational (legacy).
    - ``omega_mode == "ramanujan_arity"``: Ω_k = 1 + τ(arity)/arity^{11/2} (arity-sphere Ramanujan slot).
    """
    if omega_override is not None:
        return float(omega_override)
    if omega_mode == "ramanujan_arity":
        return omega_k_ramanujan_arity(arity)
    return 1.0 + float(curvature)


def rapidity_phase_from_omega(phi: float, t: float, omega_k: float) -> float:
    """Scalar factor ``φ·t·Ω`` applied before tipping by shell (see ``polar_angle_from_rapidity_omega``)."""
    return (phi * t) * omega_k


def polar_angle_from_rapidity_omega(phi: float, t: float, omega_k: float, e_prime: float) -> float:
    """``φ·t·Ω·δθ′(E′)``: tipping angle depends on shell index ``E′`` (Lean ``delta_theta_prime``)."""
    return rapidity_phase_from_omega(phi, t, omega_k) * delta_theta_prime_float(e_prime)


def three_spiral_rays(phi: float, t: float, omega_k: float, e_prime: float) -> list[float]:
    base = polar_angle_from_rapidity_omega(phi, t, omega_k, e_prime)
    return [base + 0.0, base + (2.0 * math.pi / 3.0), base + (4.0 * math.pi / 3.0)]


def axis_angle_for_arity(arity: int) -> float:
    """
    Baseline axis in the first quadrant: π/(2k) for factor arity k ≥ 2.

    For **k = 2** this is **π/4** (the a = b diagonal). A full turn has **2π/(π/4) = 8**, so the
    arity‑2 axis step matches **eight congruent sectors** (eight copies of that curve patch around
    **S¹**).
    """
    return math.pi / float(2 * max(2, arity))


def three_spiral_rays_about_axis(phi: float, t: float, omega_k: float, e_prime: float, arity: int) -> list[float]:
    """
    Three arms at ``base + {0, 2π/3, 4π/3}``.

    **Base** starts at one **pole** of the rotation axis for **−arity**: the axis direction is
    ``π/(2k)`` on **S¹**; its negative is **``-axis``**; a pole (orthogonal to that axis) is
    **``wrap(-axis + π/2)``**. Then add **``φ·t·Ω·δθ′(E′)``** with ``E′`` the (half-)shell index
    from ``spiral_turn_e_prime`` at the oracle.

    Together with ``δθ′(E′)`` this is the **spiral** meeting bracket directions: triadic
    periodicity on the arms and multiple **wraps** on ``S¹``.
    """
    axis = axis_angle_for_arity(arity)
    pole = wrap_pi(-axis + math.pi / 2.0)
    base = pole + polar_angle_from_rapidity_omega(phi, t, omega_k, e_prime)
    return [base + 0.0, base + (2.0 * math.pi / 3.0), base + (4.0 * math.pi / 3.0)]


def shell_neighbor_auxiliary_triads(phi: float, t: float, omega_k: float, n: int, arity: int) -> list[float]:
    """
    Two extra triads at shell indices ``n-1`` and ``n+1`` (six angles).

    **Not** “a second equator crossing” for the same curve: in the sphere story, **each** factor
    branch crosses the equator **once**. These neighbors **sample** ``δθ′`` at shells **one step**
    below/above ``n``; in the spiral story those two anchors are **one winding period** apart
    (one turn **into** each other’s shell around ``n``), which is why pairing them tightens the search.
    """
    e_lo = float(max(1, n - 1))
    e_hi = float(n + 1)
    return three_spiral_rays_about_axis(phi, t, omega_k, e_lo, arity) + three_spiral_rays_about_axis(
        phi, t, omega_k, e_hi, arity
    )


def combined_rays_primary_and_neighbor_triads(
    phi: float, t: float, omega_k: float, n: int, arity: int
) -> tuple[list[float], list[float]]:
    """
    ``(primary_3, scoring_rays)`` — single triad at **E′ = n/2** (no adjacent-shell auxiliary rays).
    """
    e_ray = spiral_turn_e_prime(n)
    primary = three_spiral_rays_about_axis(phi, t, omega_k, e_ray, arity)
    return primary, primary


def neighbor_shell_seeds(n: int) -> tuple[int, int, int]:
    """
    Integer shells around ``m``: ``m-1``, ``m``, ``m+1`` (lower clamped to 1).

    The outer pair ``m±1`` are the **bracket anchors** one step from ``m``; along the spiral they
    are **one full turn** from each other’s shell chart (neighbor shells interleaved around ``m``).
    """
    if n <= 0:
        return (1, 1, 1)
    return (max(1, n - 1), n, n + 1)


def e_prime_mid_neighbor_shells_on_maxwell_curve(m: int) -> float:
    """
    ``E′`` from the **midpoint in tipping angle** ``δθ′`` between **shell indices** ``m-1`` and
    ``m+1`` (Lean ``ModifiedMaxwell.delta_theta_prime``), then invert.

    We **do not** use the arithmetic mean of bracket **pair angles** ``atan2(b,a)`` for the integer
    pairs ``((m-1)/2, 2)`` and ``(2, (m+1)/2)``: that average tends to **π/4** as ``m`` grows (limits
    ``0`` and ``π/2``), i.e. the **(√m,√m)** diagonal — **not** discrete factor directions such as
    ``(3,5)`` / ``(5,3)`` for ``m=15``.
    """
    if m < 1:
        return 1.0
    lo = max(0.0, float(m - 1))
    hi = float(m + 1)
    t_lo = delta_theta_prime_float(lo)
    t_hi = delta_theta_prime_float(hi)
    t_mid = (t_lo + t_hi) / 2.0
    hp = horizon_quarter_period()
    return math.tan(t_mid / hp)


def anchor_neighbor_shells_sorted_unique(n: int) -> list[int]:
    """Deduped sorted {m-1, m, m+1} for divisor / phase residue picks."""
    a, b, c = neighbor_shell_seeds(n)
    return sorted({x for x in (a, b, c) if x > 0})


# Max length for ``turn_index_2_through_floor_m_half`` — huge ``m`` would overflow ``range``/list.
_RAPIDITY_TURN_LIST_CAP = 8192


def _fractional_turn_m_half(m: int) -> float:
    """
    Fractional part of ``m/2`` full turns, exact for integer ``m >= 0``: ``(m/2) mod 1 = (m mod 2)/2``.
    """
    if m <= 0:
        return 0.0
    return (m % 2) / 2.0


def rapidity_turn_shell_bookkeeping(m: int) -> dict[str, Any]:
    """
    Intercept on the **equator**: mod the winding by **full-turn count**, then take **cos/sin**.

    Let **T = m/2** full turns. Use **``T mod 1``** (one turn = **``τ``** rad), then
    **``θ_eq = τ · (T mod 1)``** and **``cos(θ_eq)``**, **``sin(θ_eq)``**. For integer **``m``** this is
    **``(π·m) mod τ``** (even **``m``** → **0**, odd **``m``** → **``π``**).

    **Secondary:** optional integer band **``2..⌊m/2⌋``** (capped list or omitted for huge ``m``).
    """
    if m < 1:
        return {
            "full_turns_like_m_over_2": 0.0,
            "fractional_turn_m_half_mod_1": 0.0,
            "intercept_angle_rad_equator": 0.0,
            "intercept_cos_equator": 1.0,
            "intercept_sin_equator": 0.0,
            "intercept_angle_rad_pi_m_unmod": 0.0,
            "turn_index_2_through_floor_m_half": [],
            "turn_index_floor_m_half": 0,
            "turn_index_list_omitted": False,
        }
    fm = float(m)
    frac_turn = _fractional_turn_m_half(m)
    angle_eq = math.tau * frac_turn
    angle_unmod = math.pi * fm  # π·m = τ·(m/2); useful reference, huge m loses float precision
    out: dict[str, Any] = {
        "full_turns_like_m_over_2": fm / 2.0,
        "fractional_turn_m_half_mod_1": frac_turn,
        "intercept_angle_rad_equator": angle_eq,
        "intercept_cos_equator": math.cos(angle_eq),
        "intercept_sin_equator": math.sin(angle_eq),
        "intercept_angle_rad_pi_m_unmod": angle_unmod,
    }
    hi = max(2, m // 2)
    span = hi - 1
    if span <= _RAPIDITY_TURN_LIST_CAP:
        turn_list: list[int] | None = list(range(2, hi + 1))
        omitted = False
    else:
        turn_list = None
        omitted = True
    out["turn_index_floor_m_half"] = hi
    out["turn_index_list_omitted"] = omitted
    if turn_list is not None:
        out["turn_index_2_through_floor_m_half"] = turn_list
    else:
        out["turn_index_2_through_floor_m_half"] = None
    return out


def phase_e_prime_for_n(
    n: int,
    phase_shell_mode: str,
    *,
    phi: float = 1.0,
    t: float = 1.0,
    omega_k: float = 1.0,
    arity: int = 2,
) -> tuple[float, dict[str, Any]]:
    """
    Shell index **E′** recorded for ``δθ′(E′)`` on the **spiral** (always **``n/2``** at the oracle).

    Rays use ``spiral_turn_e_prime(n)``; this matches **m/2** full-turn bookkeeping on the equator.
    Mode-specific fields below are **diagnostics** only (neighbor mid / triplet pick), not extra ray
    triads.

    All modes merge ``rapidity_turn_shell_bookkeeping``.
    """
    shells = anchor_neighbor_shells_sorted_unique(n)
    rtb = rapidity_turn_shell_bookkeeping(n)
    ep_ray = spiral_turn_e_prime(n)
    if phase_shell_mode == "n":
        return ep_ray, {
            "phase_shell_mode": phase_shell_mode,
            "e_prime": ep_ray,
            "neighbor_shells": shells,
            **rtb,
        }
    if phase_shell_mode == "neighbor_curve_mid":
        ep_maxwell = e_prime_mid_neighbor_shells_on_maxwell_curve(n)
        a1 = (n - 1) / 2.0 if n >= 2 else 1.0
        th1 = math.atan2(2.0, a1) if n >= 2 else 0.0
        th2 = math.atan2((n + 1) / 2.0, 2.0) if n >= 2 else 0.0
        return ep_ray, {
            "phase_shell_mode": phase_shell_mode,
            "e_prime": ep_ray,
            "e_prime_neighbor_curve_mid_maxwell": ep_maxwell,
            "neighbor_shells": shells,
            "bracket_anchor_shells": [max(1, n - 1), n + 1],
            "bracket_one_turn_between_shells": (
                "m-1 and m+1 bracket m; one spiral winding links these neighbor shells"
            ),
            "bracket_ray_a": [a1, 2.0],
            "bracket_ray_b": [2.0, (n + 1) / 2.0],
            "bracket_theta_mean_rad": (th1 + th2) / 2.0 if n >= 2 else 0.0,
            **rtb,
        }
    if phase_shell_mode == "triplet_residue":
        if not shells:
            return ep_ray, {
                "phase_shell_mode": phase_shell_mode,
                "e_prime": ep_ray,
                "neighbor_shells": [],
                "triplet_index": 0,
                **rtb,
            }
        qi = n % len(shells)
        return ep_ray, {
            "phase_shell_mode": phase_shell_mode,
            "e_prime": ep_ray,
            "triplet_shell_picked": int(shells[qi]),
            "neighbor_shells": shells,
            "triplet_index": qi,
            **rtb,
        }
    raise ValueError(f"unknown phase_shell_mode: {phase_shell_mode!r}")


def spiral_projection_candidate(m: int, theta: float) -> int:
    tan_theta = abs(math.tan(theta))
    if tan_theta < EPS:
        return max(1, int(math.isqrt(m)))
    # geometric projection spot from hyperbola a*b=m
    return max(1, int(round(math.sqrt(float(m) / tan_theta))))


def wrapped_angle_diff(a: float, b: float) -> float:
    return (b - a + math.pi) % (2.0 * math.pi) - math.pi


def score_candidate(a: int, b: int, rays: list[float]) -> float:
    pair_theta = math.atan2(float(b), float(a))
    return min(abs(wrapped_angle_diff(ray, pair_theta)) for ray in rays)


def geometry_snapshot(n: int, a: int, b: int, arity: int, rays: list[float]) -> dict[str, Any]:
    aa, bb = (a, b) if a <= b else (b, a)
    pair_theta = math.atan2(float(bb), float(aa))
    axis = axis_angle_for_arity(arity)
    ray_err = min(abs(wrapped_angle_diff(ray, pair_theta)) for ray in rays) if rays else 0.0
    return {
        "sqrt_n": math.sqrt(float(n)),
        "pair_angle_deg": math.degrees(pair_theta),
        "axis_angle_deg": math.degrees(axis),
        "pair_minus_axis_deg": math.degrees(pair_theta - axis),
        "best_ray_error_deg": math.degrees(ray_err),
    }


def crossing_angle_snapshot(n: int, d: int, rays: list[float], arity: int) -> dict[str, Any] | None:
    """
    Angular “crossing check” for a putative factor ``d`` | ``n``: canonical pair ``(a,b)``,
    ``atan2(b,a)``, and minimum gap to any spiral ray (same score convention as ``score_candidate``).
    """
    if not rays or n <= 1 or d <= 1 or d >= n or n % d != 0:
        return None
    a, b = d, n // d
    aa, bb = (a, b) if a <= b else (b, a)
    pair_theta = math.atan2(float(bb), float(aa))
    best_gap = min(abs(wrapped_angle_diff(ray, pair_theta)) for ray in rays)
    axis = axis_angle_for_arity(arity)
    return {
        "factor_d": int(d),
        "pair_a": int(aa),
        "pair_b": int(bb),
        "pair_angle_deg": math.degrees(pair_theta),
        "best_ray_gap_deg": math.degrees(best_gap),
        "pair_minus_axis_deg": math.degrees(pair_theta - axis),
    }


def first_factor_crossing_preview_from_ranked(
    ranked: list[tuple[int, float, int, int]],
    *,
    limit: int,
    arity: int,
) -> list[dict[str, Any]]:
    """First ``limit`` nontrivial divisor pairs from mask ranking, with crossing angles (degrees)."""
    out: list[dict[str, Any]] = []
    seen: set[tuple[int, int]] = set()
    for _trivial_penalty, sc, aa, bb in ranked:
        if aa <= 1:
            continue
        key = (aa, bb)
        if key in seen:
            continue
        seen.add(key)
        if len(out) >= max(0, limit):
            break
        pair_theta = math.atan2(float(bb), float(aa))
        axis = axis_angle_for_arity(arity)
        out.append(
            {
                "pair_a": int(aa),
                "pair_b": int(bb),
                "pair_angle_deg": math.degrees(pair_theta),
                "best_ray_gap_deg": math.degrees(sc),
                "pair_minus_axis_deg": math.degrees(pair_theta - axis),
            }
        )
    return out


def _merge_factor_crossing_angle(
    n: int, d: int, dbg: dict[str, Any], rays: list[float] | None, arity: int
) -> dict[str, Any]:
    if rays and 1 < d < n:
        ca = crossing_angle_snapshot(n, d, rays, arity)
        if ca:
            return {**dbg, "factor_crossing_angle": ca}
    return dbg


def integer_kth_root_floor(n: int, k: int) -> int:
    """Largest r with r^k <= n, using integer binary search."""
    if k <= 1:
        return n
    lo, hi = 1, max(1, n)
    ans = 1
    while lo <= hi:
        mid = (lo + hi) // 2
        p = mid**k
        if p <= n:
            ans = mid
            lo = mid + 1
        else:
            hi = mid - 1
    return ans


def primes_up_to(limit: int) -> list[int]:
    if limit < 2:
        return []
    sieve = [True] * (limit + 1)
    sieve[0] = sieve[1] = False
    p = 2
    while p * p <= limit:
        if sieve[p]:
            step = p
            start = p * p
            sieve[start : limit + 1 : step] = [False] * (((limit - start) // step) + 1)
        p += 1
    return [i for i in range(2, limit + 1) if sieve[i]]


def deterministic_small_prime_factor(n: int, bound: int) -> int:
    """
    Deterministic trial division by primes up to `bound`.
    Returns a non-trivial factor if found, else 1.
    """
    if n % 2 == 0:
        return 2
    for p in primes_up_to(bound):
        if p == 2:
            continue
        if n % p == 0:
            return p
    return 1


def factor_pair_from_3spiral_mask(
    n: int,
    curvature: Fraction,
    phi: float,
    t: float,
    window: int,
    arity: int,
    omega_override: float | None = None,
    *,
    omega_mode: str = "rational",
    phase_shell_mode: str = "n",
    crossing_preview_limit: int = 5,
    use_sieve: bool = True,
) -> tuple[int, int, dict[str, Any]]:
    """3-ray mask: θ uses `delta_theta_prime(E′)` with **`E′ = n/2`**; ``phase_shell_mode`` adds diagnostics."""
    if n <= 1:
        return (1, n), {
            "omega_k_imprint": omega_k_imprint(
                curvature, omega_override, arity=arity, omega_mode=omega_mode
            ),
            "rays": [],
            "candidates": [],
        }
    if use_sieve and n % 2 == 0:
        return (2, n // 2), {
            "omega_k_imprint": omega_k_imprint(
                curvature, omega_override, arity=arity, omega_mode=omega_mode
            ),
            "rays": [],
            "base_candidates": [2],
            "candidates": [2],
            "divisors": [2],
            "best_score": 0.0,
            "strategy": "deterministic_even_guard",
        }

    omega_k = omega_k_imprint(curvature, omega_override, arity=arity, omega_mode=omega_mode)
    _, phase_meta = phase_e_prime_for_n(
        n,
        phase_shell_mode,
        phi=phi,
        t=t,
        omega_k=omega_k,
        arity=arity,
    )
    rays_primary, rays = combined_rays_primary_and_neighbor_triads(phi, t, omega_k, n, arity)

    base_candidates: set[int] = set()
    for ray in rays:
        base_candidates.add(spiral_projection_candidate(n, ray))

    candidates: set[int] = set()
    for c in base_candidates:
        for d in range(-window, window + 1):
            cand = c + d
            if 1 <= cand <= n:
                candidates.add(cand)

    divisors: list[int] = sorted({a for a in candidates if 1 <= a <= n and n % a == 0})
    if not divisors:
        if use_sieve:
            d_small = deterministic_small_prime_factor(n, min(int(math.isqrt(n)), 257))
            if 1 < d_small < n:
                return (d_small, n // d_small), {
                    "omega_k_imprint": omega_k,
                    "rays": rays,
                    "candidates": sorted(candidates),
                    "base_candidates": sorted(base_candidates),
                    "divisors": [d_small],
                    "best_score": 0.0,
                    "strategy": "deterministic_small_prime_guard",
                    **phase_meta,
                }
        return (1, n), {
            "omega_k_imprint": omega_k,
            "rays": rays,
            "candidates": sorted(candidates),
            "base_candidates": sorted(base_candidates),
            "divisors": [],
            "best_score": None,
            "strategy": "mask_no_factor",
            **phase_meta,
        }

    ranked: list[tuple[int, float, int, int]] = []
    for a in divisors:
        b = n // a
        aa, bb = (a, b) if a <= b else (b, a)
        # Prefer non-trivial factorization when available; then angle score.
        trivial_penalty = 1 if aa == 1 else 0
        ranked.append((trivial_penalty, score_candidate(aa, bb, rays), aa, bb))
    ranked.sort(key=lambda x: (x[0], x[1], x[2]))
    _, best_score, a_best, b_best = ranked[0]
    preview: list[dict[str, Any]] = []
    if crossing_preview_limit > 0 and ranked:
        preview = first_factor_crossing_preview_from_ranked(
            ranked, limit=crossing_preview_limit, arity=arity
        )
    debug = {
        "omega_k_imprint": omega_k,
        "rays": rays,
        "rays_primary": rays_primary,
        "ray_count": len(rays),
        "base_candidates": sorted(base_candidates),
        "candidates": sorted(candidates),
        "divisors": divisors,
        "best_score": best_score,
        "best_mask_pair": (a_best, b_best),
        "first_factor_crossing_angles": preview,
        **phase_meta,
    }
    return (a_best, b_best), debug


def prime_gradient_factor(
    n: int,
    curvature: Fraction,
    phi: float,
    t: float,
    window: int,
    arity: int,
    omega_override: float | None = None,
    *,
    omega_mode: str = "rational",
    phase_shell_mode: str = "n",
    use_sieve: bool = True,
) -> tuple[int, dict[str, Any]]:
    """
    Prime-stepped rapidity-gradient search up to floor(n^(1/arity)).
    Returns one factor d (or 1 if no non-trivial factor found).
    """
    if n <= 3:
        ak = max(2, arity)
        ok = omega_k_imprint(curvature, omega_override, arity=ak, omega_mode=omega_mode)
        _, phase_meta = phase_e_prime_for_n(
            n,
            phase_shell_mode,
            phi=phi,
            t=t,
            omega_k=ok,
            arity=ak,
        )
        return 1, {
            "root_bound": 1,
            "tested_primes": 0,
            "steps": 0,
            "found_factor": None,
            "gradient_best_d": None,
            "gradient_best_score": None,
            **phase_meta,
        }
    if arity < 2:
        arity = 2

    omega_k = omega_k_imprint(curvature, omega_override, arity=arity, omega_mode=omega_mode)
    _, phase_meta = phase_e_prime_for_n(
        n,
        phase_shell_mode,
        phi=phi,
        t=t,
        omega_k=omega_k,
        arity=arity,
    )
    _rays_primary, rays = combined_rays_primary_and_neighbor_triads(phi, t, omega_k, n, arity)
    root_bound = integer_kth_root_floor(n, arity)

    # First case: direct 2-factor geometric mask (no sieve).
    (a2, b2), _mask_dbg = factor_pair_from_3spiral_mask(
        n=n,
        curvature=curvature,
        phi=phi,
        t=t,
        window=window,
        arity=2,
        omega_override=omega_override,
        omega_mode=omega_mode,
        phase_shell_mode=phase_shell_mode,
        use_sieve=use_sieve,
    )
    if 1 < a2 < n:
        dbg_fc = {
            "root_bound": root_bound,
            "tested_primes": 0,
            "steps": 0,
            "strategy": "first_case_2factor_mask",
            "used_sieve": False,
            "sieve_bound": 0,
            **phase_meta,
        }
        dbg_fc = {
            **dbg_fc,
            "found_factor": a2,
            "best_mask_pair": _mask_dbg.get("best_mask_pair"),
            "mask_best_score": _mask_dbg.get("best_score"),
            "gradient_best_d": None,
            "gradient_best_score": None,
        }
        return a2, _merge_factor_crossing_angle(n, a2, dbg_fc, _mask_dbg.get("rays"), 2)
    if 1 < b2 < n:
        dbg_fc = {
            "root_bound": root_bound,
            "tested_primes": 0,
            "steps": 0,
            "strategy": "first_case_2factor_mask",
            "used_sieve": False,
            "sieve_bound": 0,
            **phase_meta,
        }
        dbg_fc = {
            **dbg_fc,
            "found_factor": b2,
            "best_mask_pair": _mask_dbg.get("best_mask_pair"),
            "mask_best_score": _mask_dbg.get("best_score"),
            "gradient_best_d": None,
            "gradient_best_score": None,
        }
        return b2, _merge_factor_crossing_angle(n, b2, dbg_fc, _mask_dbg.get("rays"), 2)

    # Fallback: bounded prime list for stepping + trial guard (optional).
    # ``use_sieve`` gates small-prime trial and mask shortcuts only; the prime-step walk always uses primes.
    sieve_bound = min(root_bound, 257)
    prime_steps = primes_up_to(sieve_bound)

    if use_sieve:
        # Deterministic guard: never miss obvious composites (especially even numbers).
        d_small = deterministic_small_prime_factor(n, sieve_bound)
        if 1 < d_small < n:
            dbg_sg = {
                "root_bound": root_bound,
                "tested_primes": len(prime_steps),
                "steps": 0,
                "strategy": "deterministic_small_prime_guard",
                "used_sieve": True,
                "sieve_bound": sieve_bound,
                "found_factor": d_small,
                "gradient_best_d": None,
                "gradient_best_score": None,
                **phase_meta,
            }
            return d_small, _merge_factor_crossing_angle(n, d_small, dbg_sg, rays, arity)

    # Seed candidates from the same geometric mask as the direct oracle.
    base_candidates: set[int] = set()
    for ray in rays:
        base_candidates.add(spiral_projection_candidate(n, ray))
    for anchor in neighbor_shell_seeds(n):
        if anchor > 0:
            base_candidates.add(anchor)

    seeds: set[int] = set()
    for c in base_candidates:
        for d in range(-window, window + 1):
            cand = c + d
            if 2 <= cand <= max(2, root_bound):
                seeds.add(cand)
    if not seeds:
        seeds.add(max(2, min(root_bound, int(math.isqrt(n)))))

    steps = 0
    best_d = 1
    best_score = float("inf")
    for seed in sorted(seeds):
        cur = seed
        for p in prime_steps:
            steps += 1
            if 2 <= cur <= root_bound and n % cur == 0:
                _gbs = None if best_score == float("inf") else best_score
                dbg_hit = {
                    "root_bound": root_bound,
                    "tested_primes": len(prime_steps),
                    "steps": steps,
                    "seed": seed,
                    "hit_prime_step": p,
                    "strategy": "prime_gradient_sieve_fallback",
                    "used_sieve": use_sieve,
                    "sieve_bound": sieve_bound,
                    "found_factor": cur,
                    "gradient_best_d": best_d,
                    "gradient_best_score": _gbs,
                    **phase_meta,
                }
                return cur, _merge_factor_crossing_angle(n, cur, dbg_hit, rays, arity)
            # Discrete gradient step: choose +/- p by angular score.
            cand_minus = max(2, cur - p)
            cand_plus = min(root_bound, cur + p)
            score_minus = score_candidate(cand_minus, n // cand_minus if cand_minus > 0 else n, rays)
            score_plus = score_candidate(cand_plus, n // cand_plus if cand_plus > 0 else n, rays)
            if score_minus <= score_plus:
                cur = cand_minus
                cur_score = score_minus
            else:
                cur = cand_plus
                cur_score = score_plus
            if cur_score < best_score:
                best_score = cur_score
                best_d = cur
        if 2 <= cur <= root_bound and n % cur == 0:
            _gbs = None if best_score == float("inf") else best_score
            dbg_seed = {
                "root_bound": root_bound,
                "tested_primes": len(prime_steps),
                "steps": steps,
                "seed": seed,
                "strategy": "prime_gradient_sieve_fallback",
                "used_sieve": use_sieve,
                "sieve_bound": sieve_bound,
                "found_factor": cur,
                "gradient_best_d": best_d,
                "gradient_best_score": _gbs,
                **phase_meta,
            }
            return cur, _merge_factor_crossing_angle(n, cur, dbg_seed, rays, arity)

    # Final exact check on best gradient candidate.
    if 2 <= best_d <= root_bound and n % best_d == 0:
        _gbs = None if best_score == float("inf") else best_score
        dbg_bg = {
            "root_bound": root_bound,
            "tested_primes": len(prime_steps),
            "steps": steps,
            "seed": "best_gradient",
            "strategy": "prime_gradient_sieve_fallback",
            "used_sieve": use_sieve,
            "sieve_bound": sieve_bound,
            "found_factor": best_d,
            "gradient_best_d": best_d,
            "gradient_best_score": _gbs,
            **phase_meta,
        }
        return best_d, _merge_factor_crossing_angle(n, best_d, dbg_bg, rays, arity)
    _gbs = None if best_score == float("inf") else best_score
    return 1, {
        "root_bound": root_bound,
        "tested_primes": len(prime_steps),
        "steps": steps,
        "strategy": "prime_gradient_sieve_fallback",
        "used_sieve": use_sieve,
        "sieve_bound": sieve_bound,
        "found_factor": None,
        "gradient_best_d": best_d,
        "gradient_best_score": _gbs,
        **phase_meta,
    }


def recursive_prime_gradient_factorization(
    n: int,
    curvature: Fraction,
    phi: float,
    t: float,
    window: int,
    arity: int,
    depth: int,
    omega_override: float | None = None,
    *,
    omega_mode: str = "rational",
    phase_shell_mode: str = "n",
    use_sieve: bool = True,
) -> tuple[list[int], list[dict[str, Any]]]:
    """
    Recursively peel one factor using prime-gradient search.
    Falls back to [n] when no non-trivial factor is found.
    """
    trace: list[dict[str, Any]] = []
    factors: list[int] = []

    def rec(m: int, k: int, dleft: int) -> None:
        if m <= 1:
            return
        if dleft <= 0 or k < 2:
            factors.append(m)
            return
        d, dbg = prime_gradient_factor(
            m,
            curvature,
            phi,
            t,
            window,
            k,
            omega_override=omega_override,
            omega_mode=omega_mode,
            phase_shell_mode=phase_shell_mode,
            use_sieve=use_sieve,
        )
        dbg = {"n": m, "arity": k, **dbg}
        trace.append(dbg)
        if d <= 1 or d >= m:
            factors.append(m)
            return
        factors.append(d)
        rec(m // d, max(2, k - 1), dleft - 1)

    rec(n, arity, depth)
    factors.sort()
    return factors, trace


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Return a factor pair for n with optional rational-curvature bias."
    )
    parser.add_argument("n", type=int, help="positive integer to factor")
    parser.add_argument(
        "--curvature-rational",
        type=parse_rational,
        default=Fraction(0, 1),
        help="rational curvature offset (examples: +1/60, -1/30, 0)",
    )
    parser.add_argument(
        "--omega-imprint",
        type=float,
        default=None,
        help="direct Ω_k imprint value (overrides --curvature-rational when provided)",
    )
    parser.add_argument(
        "--omega-mode",
        choices=("rational", "ramanujan_arity"),
        default="rational",
        help=(
            "how to set Ω_k when --omega-imprint is omitted: "
            "'rational' uses 1+curvature; "
            "'ramanujan_arity' uses 1+τ(arity)/arity^{11/2} (weight-12 cusp form τ on the arity index)"
        ),
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="print structured JSON output",
    )
    parser.add_argument("--phi", type=float, default=1.0, help="rapidity φ in φ·t·Ω·δθ′ (default: 1)")
    parser.add_argument(
        "--t",
        type=float,
        default=1.0,
        help="rapidity t (discrete step count; default 1 = one shell-time step). Prefer integers.",
    )
    parser.add_argument(
        "--window",
        type=int,
        default=8,
        help="candidate expansion window around projections/anchors (default: 8)",
    )
    parser.add_argument(
        "--mode",
        choices=["mask", "prime_gradient"],
        default="prime_gradient",
        help="factor mode: direct 3-spiral mask or prime-stepped gradient (default: prime_gradient)",
    )
    parser.add_argument(
        "--arity",
        type=int,
        default=2,
        help="target factor arity k; uses root bound floor(n^(1/k)) in prime_gradient mode",
    )
    parser.add_argument(
        "--max-depth",
        type=int,
        default=8,
        help="maximum recursive depth for prime_gradient mode",
    )
    parser.add_argument(
        "--visualize-text",
        action="store_true",
        help="print geometric diagnostics (axis angle, pair angle, ray error)",
    )
    parser.add_argument(
        "--phase-shell",
        choices=("n", "neighbor_curve_mid", "triplet_residue"),
        default="n",
        help=(
            "phase-shell diagnostics (rays always use E′=n/2 for δθ′): "
            "'n' is the default label; "
            "'neighbor_curve_mid' adds Maxwell midpoint metadata; "
            "'triplet_residue' records triplet shell pick among {m-1,m,m+1}"
        ),
    )
    parser.add_argument(
        "--crossing-preview",
        type=int,
        default=5,
        metavar="N",
        help=(
            "print first N ranked mask divisor pairs with crossing angles (pair vs spiral rays); "
            "0 disables. Also limits how many gradient-trace steps show factor_crossing_angle in text."
        ),
    )
    parser.add_argument(
        "--no-sieve",
        action="store_true",
        help=(
            "disable the small-prime trial guard and the fast even shortcut in the 3-spiral mask; "
            "the prime-step gradient walk still uses primes up to min(root_bound, 257)"
        ),
    )
    return parser


def main() -> None:
    args = build_parser().parse_args()
    if args.n <= 0:
        raise SystemExit("n must be a positive integer")

    if args.window < 0:
        raise SystemExit("--window must be non-negative")
    if args.arity < 2:
        raise SystemExit("--arity must be >= 2")
    if args.max_depth < 1:
        raise SystemExit("--max-depth must be >= 1")
    if args.crossing_preview < 0:
        raise SystemExit("--crossing-preview must be >= 0")

    if args.mode == "mask":
        (a, b), debug = factor_pair_from_3spiral_mask(
            n=args.n,
            curvature=args.curvature_rational,
            phi=args.phi,
            t=args.t,
            window=args.window,
            arity=args.arity,
            omega_override=args.omega_imprint,
            omega_mode=args.omega_mode,
            phase_shell_mode=args.phase_shell,
            crossing_preview_limit=args.crossing_preview,
            use_sieve=not args.no_sieve,
        )
        if a > b:
            a, b = b, a
        factors = [a, b]
        gradient_trace: list[dict[str, Any]] = []
    else:
        factors, gradient_trace = recursive_prime_gradient_factorization(
            n=args.n,
            curvature=args.curvature_rational,
            phi=args.phi,
            t=args.t,
            window=args.window,
            arity=args.arity,
            depth=args.max_depth,
            omega_override=args.omega_imprint,
            omega_mode=args.omega_mode,
            phase_shell_mode=args.phase_shell,
            use_sieve=not args.no_sieve,
        )
        if len(factors) == 1:
            a, b = 1, factors[0]
        else:
            a, b = factors[0], args.n // factors[0]
        # Keep direct mask diagnostics as geometric context.
        (_, _), debug = factor_pair_from_3spiral_mask(
            n=args.n,
            curvature=args.curvature_rational,
            phi=args.phi,
            t=args.t,
            window=args.window,
            arity=args.arity,
            omega_override=args.omega_imprint,
            omega_mode=args.omega_mode,
            phase_shell_mode=args.phase_shell,
            crossing_preview_limit=args.crossing_preview,
            use_sieve=not args.no_sieve,
        )

    geom = geometry_snapshot(args.n, a, b, args.arity, debug["rays"])

    payload: dict[str, Any] = {
        "n": args.n,
        "mode": args.mode,
        "use_sieve": not args.no_sieve,
        "phase_shell": args.phase_shell,
        "curvature_rational": str(args.curvature_rational),
        "omega_mode": args.omega_mode,
        "phi": args.phi,
        "t": args.t,
        "arity": args.arity,
        "omega_k_imprint": debug["omega_k_imprint"],
        "rays": debug["rays"],
        "rays_primary": debug.get("rays_primary"),
        "ray_count": debug.get("ray_count", len(debug["rays"])),
        "candidate_count": len(debug["candidates"]),
        "base_candidate_count": len(debug["base_candidates"]),
        "a": a,
        "b": b,
        "factors": factors,
        "is_trivial_pair": a == 1,
        "product_check": a * b,
        "best_score": debug.get("best_score"),
        "best_mask_pair": list(debug["best_mask_pair"])
        if debug.get("best_mask_pair") is not None
        else None,
        "first_factor_crossing_angles": debug.get("first_factor_crossing_angles") or [],
        "gradient_trace": gradient_trace,
        "geometry": geom,
        "prime_gradient_peel0": gradient_trace[0]
        if gradient_trace
        else None,
        "prime_gradient_walk_explained": (
            PRIME_GRADIENT_WALK_EXPLAINED if args.mode == "prime_gradient" else None
        ),
    }

    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(f"n={args.n}")
        print(
            f"mode={args.mode} arity={args.arity} phase_shell={args.phase_shell} "
            f"omega_mode={args.omega_mode} use_sieve={not args.no_sieve}"
        )
        print(f"curvature_rational={args.curvature_rational}")
        print(f"phi={args.phi} t={args.t} omega_k_imprint={debug['omega_k_imprint']}")
        rc = debug.get("ray_count", len(debug["rays"]))
        print(f"rays({rc})={', '.join(f'{x:.6f}' for x in debug['rays'])}")
        print(f"base_candidate_count={len(debug['base_candidates'])} candidate_count={len(debug['candidates'])}")
        bmp = debug.get("best_mask_pair")
        if bmp is not None:
            bs = debug.get("best_score")
            bs_s = f"{bs:.6e}" if isinstance(bs, (int, float)) and bs is not None else str(bs)
            print(f"best_mask_candidate: {bmp[0]} x {bmp[1]}  (mask angular score vs rays={bs_s})")
        else:
            print("best_mask_candidate: (n/a — not from ranked mask divisors)")
        print(f"found_candidate (returned pair): {a} x {b}")
        if gradient_trace:
            g0 = gradient_trace[0]
            fd = g0.get("found_factor")
            gd = g0.get("gradient_best_d")
            gs = g0.get("gradient_best_score")
            gs_s = f"{gs:.6e}" if isinstance(gs, (int, float)) and gs is not None else str(gs)
            print(
                "prime_gradient peel[0]: "
                f"found_factor={fd}  gradient_best_d={gd}  gradient_best_score={gs_s}"
            )
            if any(s.get("strategy") == "prime_gradient_sieve_fallback" for s in gradient_trace):
                print("prime_gradient_walk_explained:")
                print(f"  {PRIME_GRADIENT_WALK_EXPLAINED}")
        print(f"factors: {a} x {b}")
        print(f"factor_list={factors}")
        if payload["best_score"] is not None:
            print(f"best_score={payload['best_score']:.6e}")
        if gradient_trace:
            last = gradient_trace[-1]
            print(
                "gradient_trace_last="
                f"n={last.get('n')} arity={last.get('arity')} "
                f"root_bound={last.get('root_bound')} steps={last.get('steps')}"
            )
        preview = debug.get("first_factor_crossing_angles") or []
        if preview and args.crossing_preview > 0:
            print("first_factor_crossing_angles (ranked mask pairs, degrees):")
            for row in preview[: args.crossing_preview]:
                print(
                    "  "
                    f"pair=({row['pair_a']},{row['pair_b']}) "
                    f"pair_angle={row['pair_angle_deg']:.3f} "
                    f"best_ray_gap={row['best_ray_gap_deg']:.3f} "
                    f"pair-axis={row['pair_minus_axis_deg']:.3f}"
                )
        if gradient_trace and args.crossing_preview > 0:
            for i, step in enumerate(gradient_trace[: args.crossing_preview]):
                ca = step.get("factor_crossing_angle")
                if not ca:
                    continue
                print(
                    f"gradient_trace[{i}] factor_crossing_angle:"
                    f" n={step.get('n')} d={ca['factor_d']} "
                    f"pair=({ca['pair_a']},{ca['pair_b']}) "
                    f"pair_angle={ca['pair_angle_deg']:.3f}deg "
                    f"best_ray_gap={ca['best_ray_gap_deg']:.3f}deg "
                    f"pair-axis={ca['pair_minus_axis_deg']:.3f}deg"
                )
        if args.visualize_text:
            print(
                "geometry:"
                f" sqrt(n)={geom['sqrt_n']:.6f}"
                f" axis={geom['axis_angle_deg']:.3f}deg"
                f" pair={geom['pair_angle_deg']:.3f}deg"
                f" pair-axis={geom['pair_minus_axis_deg']:.3f}deg"
                f" best-ray-err={geom['best_ray_error_deg']:.3f}deg"
            )
        print(f"product_check={a * b}")


if __name__ == "__main__":
    main()
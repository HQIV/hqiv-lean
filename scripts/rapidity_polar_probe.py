#!/usr/bin/env python3
"""
Probe the Lean rapidity->polar scaffold numerically.

Lean alignment:
- delta_theta_prime(E') = arctan(E') * horizonQuarterPeriod (= arctan(E') * pi/2; see ModifiedMaxwell.delta_theta_prime_eq_arctan_mul_pi_div_two)
- horizonQuarterPeriod = twoPi / 4 = pi/2
- zeta phase cexp(I*phi*t*delta_theta') = cexp(I*polarAngleFromRapidity); see Hqiv.Physics.RapidityZetaPhaseBridge
- Prefer integer `--t` (shell step count); Lean uses `t : ℝ` in `timeAngle φ t`.
- polarAngleFromRapidity(phi, t, m) = phi * t * delta_theta_prime(m)
- polarRadiusShellSucc(m) = m + 1
- polarRadiusReciprocal(m) = 1 / (m + 1)

Phase / factors (aligns with `zetaHQIVTerm` phase `cexp (I * angle)` in ℂ):
- unit: exp(I * angle) = (cos(angle), sin(angle))
- spiral: r * exp(I * angle) for r = radius_shell_succ or radius_reciprocal
"""

from __future__ import annotations

import argparse
import cmath
import collections
import json
import math
from pathlib import Path
from typing import Any

ALPHA = 3.0 / 5.0
CURVATURE_NORM_COMBINATORIAL = 279_936.0 * math.sqrt(3.0)


def horizon_quarter_period() -> float:
    return (2.0 * math.pi) / 4.0


def delta_theta_prime(e_prime: float) -> float:
    return math.atan(e_prime) * horizon_quarter_period()


def polar_angle_from_rapidity(phi: float, t: float, m: int) -> float:
    return phi * t * delta_theta_prime(float(m))


def polar_radius_shell_succ(m: int) -> float:
    return float(m + 1)


def polar_radius_reciprocal(m: int) -> float:
    return 1.0 / float(m + 1)


def rapidity_polar_point(phi: float, t: float, m: int) -> tuple[float, float]:
    return polar_radius_shell_succ(m), polar_angle_from_rapidity(phi, t, m)


def rapidity_polar_point_reciprocal(phi: float, t: float, m: int) -> tuple[float, float]:
    return polar_radius_reciprocal(m), polar_angle_from_rapidity(phi, t, m)


def exp_i_angle(angle: float) -> tuple[float, float]:
    """Unit complex factor exp(I * angle): real, imag (matches `Complex.cexp` on ℝ→ℂ embedding)."""
    z = cmath.exp(1j * angle)
    return z.real, z.imag


def curvature_density(m: int) -> float:
    x = float(m + 1)
    return (1.0 / x) * (1.0 + ALPHA * math.log(x))


def shell_shape(m: int) -> float:
    return curvature_density(m)


def delta_e_combinatorial(m: int) -> float:
    return CURVATURE_NORM_COMBINATORIAL * shell_shape(m)


def intrinsic_sphere_curvature_norm(sphere_dim: int) -> float:
    """
    Scalar-curvature style normalization for unit sphere S^n: R = n(n-1).
    For S3 -> 6, S4 -> 12.
    """
    return float(sphere_dim * (sphere_dim - 1))


def angle_mod_two_pi(angle: float) -> float:
    return angle % (2.0 * math.pi)


def infer_divisor_from_angle(angle: float, eps: float = 1e-12) -> dict[str, float | int | None]:
    """
    Reconstruct a central-angle divisor d from theta ~= 2*pi/d.
    Returns nearest integer d and residual error in radians.
    """
    theta = angle_mod_two_pi(angle)
    if theta <= eps:
        return {
            "theta_mod_two_pi": theta,
            "inferred_divisor": None,
            "reconstructed_theta": 0.0,
            "reconstruction_error": 0.0,
        }
    d_float = (2.0 * math.pi) / theta
    d_int = max(1, int(round(d_float)))
    theta_recon = (2.0 * math.pi) / float(d_int)
    return {
        "theta_mod_two_pi": theta,
        "inferred_divisor": d_int,
        "reconstructed_theta": theta_recon,
        "reconstruction_error": abs(theta - theta_recon),
    }


def adjacent_shell_mod3(m: int) -> int:
    """
    Pick an adjacent shell anchor via m mod 3:
    - residue 0 -> m-1
    - residue 1 -> m+1
    - residue 2 -> m-1
    Clamped to >= 0.
    """
    if m <= 0:
        return 0
    r = m % 3
    if r == 1:
        return m + 1
    return max(0, m - 1)


def even_anchor_shell(m: int) -> int:
    """Nearest even shell (prefer m itself when even, else m+1)."""
    if m % 2 == 0:
        return m
    return m + 1


def odd_multiple_of_three_anchor_shell(m: int) -> int:
    """
    Nearest odd multiple-of-3 shell n:
      n % 3 == 0 and n % 2 != 0, with n != m when possible.
    """
    if m < 0:
        m = 0
    # Search outward by radius; prefer upward shell on ties.
    for d in range(0, m + 64):
        cand_up = m + d
        if cand_up % 3 == 0 and cand_up % 2 != 0 and cand_up != m:
            return cand_up
        cand_dn = m - d
        if cand_dn >= 0 and cand_dn % 3 == 0 and cand_dn % 2 != 0 and cand_dn != m:
            return cand_dn
    # Fallback should never trigger in practical ranges.
    return 3


def original_shell_valid_for_triplet(m: int) -> bool:
    """
    Original shell validity requested by user:
    false when m is divisible by 2 or 3.
    """
    return (m % 2 != 0) and (m % 3 != 0)


def wrapped_angle_diff(a: float, b: float) -> float:
    """Wrapped difference (b-a) in (-pi, pi]."""
    return (b - a + math.pi) % (2.0 * math.pi) - math.pi


def nearest_ray8_index(theta: float) -> int:
    step = math.pi / 4.0
    return int(round((theta % (2.0 * math.pi)) / step)) % 8


def ray8_scores_from_steps(step_a: float, step_b: float) -> tuple[list[float], int, float]:
    """
    Build 8-ray alignment scores from local spiral increments.
    Vector direction is atan2(step_b, step_a). Score is cosine alignment to each ray.
    """
    theta = math.atan2(step_b, step_a) % (2.0 * math.pi)
    ray_angles = [(math.pi / 4.0) * k for k in range(8)]
    scores = [math.cos(theta - ra) for ra in ray_angles]
    best = max(range(8), key=lambda k: scores[k])
    return scores, best, theta


def factor_pairs(n: int) -> list[tuple[int, int]]:
    out: list[tuple[int, int]] = []
    if n <= 0:
        return out
    r = int(math.isqrt(n))
    for a in range(1, r + 1):
        if n % a == 0:
            out.append((a, n // a))
    return out


def rank_factor_pairs_by_ray(n: int, ray_angle: float) -> list[dict[str, float | int]]:
    """
    Rank factor pairs by angular proximity of pair-vector angle atan2(b, a)
    to the selected ray angle.
    """
    pairs = factor_pairs(n)
    ranked: list[dict[str, float | int]] = []
    for a, b in pairs:
        pair_theta = math.atan2(float(b), float(a)) % (2.0 * math.pi)
        err = abs(wrapped_angle_diff(ray_angle, pair_theta))
        ranked.append(
            {
                "a": int(a),
                "b": int(b),
                "pair_theta": pair_theta,
                "ray_error_rad": err,
            }
        )
    ranked.sort(key=lambda x: x["ray_error_rad"])
    return ranked


def rank_factor_pairs_by_three_axis_orbit(
    n: int,
    base_angle: float,
    copy_count: int = 3,
    copy_rotation: float = (2.0 * math.pi / 3.0),
) -> list[dict[str, float | int]]:
    """
    Rank factor pairs against multiple rotated copies of the same spiral curve
    (3-axis symmetry model).
    """
    pairs = factor_pairs(n)
    ranked: list[dict[str, float | int]] = []
    orbit_angles = [((base_angle + j * copy_rotation) % (2.0 * math.pi)) for j in range(copy_count)]
    for a, b in pairs:
        pair_theta = math.atan2(float(b), float(a)) % (2.0 * math.pi)
        errs = [abs(wrapped_angle_diff(oa, pair_theta)) for oa in orbit_angles]
        best_branch = min(range(copy_count), key=lambda j: errs[j])
        ranked.append(
            {
                "a": int(a),
                "b": int(b),
                "pair_theta": pair_theta,
                "orbit_error_rad": errs[best_branch],
                "orbit_branch": int(best_branch),
            }
        )
    ranked.sort(key=lambda x: x["orbit_error_rad"])
    return ranked


def factor_pair_from_3spiral_mask(m: int, phi: float = 0.6, t: float = 1.0) -> tuple[int, int] | None:
    """
    Direct geometric factor extraction from the 3-spiral mask + mod-2/3 anchors.
    Projects a0 onto three rotated rays, adds anchor spots, then performs exact divisibility check.
    Returns canonical pair (min(a,b), max(a,b)) when found, else None.
    """
    if m <= 1:
        return (1, m) if m == 1 else None

    angle = polar_angle_from_rapidity(phi, t, m)
    rotations = [0.0, 2.0 * math.pi / 3.0, 4.0 * math.pi / 3.0]
    ray_angles = [(angle + rot) % (2.0 * math.pi) for rot in rotations]

    candidates: set[int] = set()
    for theta in ray_angles:
        tan_theta = math.tan(theta)
        abs_tan = abs(tan_theta) if abs(tan_theta) > 1e-12 else 0.0
        if abs_tan < 1e-12:
            a0 = int(math.isqrt(m))
        else:
            a0 = int(round(math.sqrt(m / abs_tan)))
        candidates.add(max(1, a0))
        if a0 > 0 and m % a0 == 0:
            candidates.add(m // a0)

    anchors = (m, adjacent_shell_mod3(m), even_anchor_shell(m), odd_multiple_of_three_anchor_shell(m))
    for anchor in anchors:
        if anchor > 0:
            candidates.add(anchor)

    # Prefer non-trivial factors first.
    ordered = sorted(candidates, key=lambda a: (a == 1 or a == m, a))
    for a in ordered:
        if a < 1 or a > m:
            continue
        if m % a == 0:
            b = m // a
            return (min(a, b), max(a, b))
    return None


def sparse_pruned_factor_candidates(n: int, ray_angle: float, window: int = 8) -> list[int]:
    """
    Sparse-sim inspired heuristic candidate list for divisor `a`:
    - project along ray: a0 ≈ sqrt(n / tan(theta))
    - keep a small +/- window
    - parity/mod-3 pruning from n
    This is heuristic and not complete; use for fast pre-filtering.
    """
    if n <= 1:
        return [1]
    t = abs(math.tan(ray_angle))
    if t < 1e-9:
        a0 = int(math.isqrt(n))
    else:
        a0 = int(round(math.sqrt(n / t)))
    lo = max(1, a0 - window)
    hi = max(lo, min(int(math.isqrt(n)), a0 + window))

    out: list[int] = []
    for a in range(lo, hi + 1):
        # Simple congruence pruning.
        if n % 2 == 1 and a % 2 == 0:
            continue
        if n % 3 != 0 and a % 3 == 0:
            continue
        out.append(a)
    # Deduplicate and keep sorted.
    return sorted(set(out))


def spiral_locked_factor_candidates(n: int, ray_angle: float, window: int = 3) -> list[int]:
    """
    Candidate set from the locked spiral spot between mod-2/mod-3 neighbors:
    - Use locked ray angle (derived from neighbor-step geometry in build_report).
    - Project to divisor axis: a0 ~ sqrt(n / |tan(ray_angle)|).
    - Test only a small +/- window around a0 with mod-2/mod-3 pruning.
    """
    if n <= 1:
        return [1]
    t = abs(math.tan(ray_angle))
    if t < 1e-9:
        a0 = int(math.isqrt(n))
    else:
        a0 = int(round(math.sqrt(n / t)))
    lo = max(1, a0 - window)
    hi = max(lo, min(int(math.isqrt(n)), a0 + window))
    out: list[int] = []
    for a in range(lo, hi + 1):
        if (n % 2 == 1 and a % 2 == 0) or (n % 3 != 0 and a % 3 == 0):
            continue
        out.append(a)
    return sorted(set(out))


def rank_sparse_pruned_pairs_by_ray(
    n: int,
    ray_angle: float,
    window: int = 8,
    guarantee_no_prune: bool = True,
    candidate_mode: str = "projected_window",
    target_angle: float | None = None,
    angle_eps: float = 0.2,
    bidirectional: bool = True,
) -> dict[str, Any]:
    if candidate_mode == "spiral_locked":
        candidates = spiral_locked_factor_candidates(n, ray_angle, window=window)
    else:
        candidates = sparse_pruned_factor_candidates(n, ray_angle, window=window)
    ranked: list[dict[str, float | int]] = []
    seen_a: set[int] = set()
    target_mod = None if target_angle is None else (target_angle % (2.0 * math.pi))
    reverse_target = None if target_mod is None else ((-target_mod) % (2.0 * math.pi))
    filtered_out_by_angle = 0
    for a in candidates:
        if a <= 0:
            continue
        if n % a != 0:
            continue
        b = n // a
        seen_a.add(a)
        pair_theta = math.atan2(float(b), float(a)) % (2.0 * math.pi)
        if target_mod is not None:
            d1 = abs(wrapped_angle_diff(target_mod, pair_theta))
            keep = d1 <= angle_eps
            if bidirectional and not keep and reverse_target is not None:
                d2 = abs(wrapped_angle_diff(reverse_target, pair_theta))
                keep = d2 <= angle_eps
            if not keep:
                filtered_out_by_angle += 1
                continue
        err = abs(wrapped_angle_diff(ray_angle, pair_theta))
        ranked.append(
            {
                "a": int(a),
                "b": int(b),
                "pair_theta": pair_theta,
                "ray_error_rad": err,
            }
        )

    fallback_used = False
    fallback_checked = 0
    # Guarantee mode: never prune valid targets.
    if guarantee_no_prune:
        r = int(math.isqrt(max(0, n)))
        for a in range(1, r + 1):
            if a in seen_a:
                continue
            fallback_checked += 1
            if n % a != 0:
                continue
            fallback_used = True
            b = n // a
            pair_theta = math.atan2(float(b), float(a)) % (2.0 * math.pi)
            if target_mod is not None:
                d1 = abs(wrapped_angle_diff(target_mod, pair_theta))
                keep = d1 <= angle_eps
                if bidirectional and not keep and reverse_target is not None:
                    d2 = abs(wrapped_angle_diff(reverse_target, pair_theta))
                    keep = d2 <= angle_eps
                if not keep:
                    filtered_out_by_angle += 1
                    continue
            err = abs(wrapped_angle_diff(ray_angle, pair_theta))
            ranked.append(
                {
                    "a": int(a),
                    "b": int(b),
                    "pair_theta": pair_theta,
                    "ray_error_rad": err,
                }
            )
    ranked.sort(key=lambda x: x["ray_error_rad"])
    return {
        "candidates_checked": len(candidates),
        "candidate_mode": candidate_mode,
        "target_angle": target_mod,
        "target_angle_reverse": reverse_target,
        "angle_eps": angle_eps,
        "bidirectional": bidirectional,
        "filtered_out_by_angle": filtered_out_by_angle,
        "guarantee_no_prune": guarantee_no_prune,
        "fallback_scan_used": fallback_used,
        "fallback_checked": fallback_checked,
        "pairs_found": ranked,
    }


def divisor_count(n: int) -> int:
    if n <= 0:
        return 0
    c = 0
    r = int(math.isqrt(n))
    for d in range(1, r + 1):
        if n % d == 0:
            c += 1 if d * d == n else 2
    return c


def dim_weight_normalizer(p: int, m_min: int, m_max: int) -> float:
    return sum(float((m + 1) ** p) for m in range(m_min, m_max + 1))


def dim_shell_weight(p: int, m_min: int, m_max: int, m: int) -> float:
    z = dim_weight_normalizer(p, m_min, m_max)
    if z == 0.0:
        return 0.0
    # Follows Lean template `dimShellWeight`: ((m+1)^(p+1))/Z.
    return float((m + 1) ** (p + 1)) / z


def octant_index(theta_mod: float) -> int:
    step = math.pi / 4.0
    return int(round(theta_mod / step)) % 8


def nearest_octant_error(theta_mod: float) -> float:
    step = math.pi / 4.0
    k = int(round(theta_mod / step))
    theta_ref = k * step
    return abs((theta_mod - theta_ref + math.pi) % (2.0 * math.pi) - math.pi)


def circular_sector_hist(theta_mods: list[float], sectors: int) -> list[int]:
    counts = [0 for _ in range(sectors)]
    width = (2.0 * math.pi) / float(sectors)
    for th in theta_mods:
        j = int(math.floor(th / width)) % sectors
        counts[j] += 1
    return counts


def summarize_aliasing(rows: list[dict[str, Any]], lock_eps_deg: float) -> dict[str, Any]:
    theta_mods = [float(r["theta_mod_two_pi"]) for r in rows]
    weights = [float(r["ramanujan_dim_imprint"]) for r in rows]

    oct_counts = [0 for _ in range(8)]
    oct_wcounts = [0.0 for _ in range(8)]
    lock_eps = math.radians(lock_eps_deg)
    lock_hits = 0
    lock_whits = 0.0

    for th, w in zip(theta_mods, weights):
        k = octant_index(th)
        oct_counts[k] += 1
        oct_wcounts[k] += w
        if nearest_octant_error(th) <= lock_eps:
            lock_hits += 1
            lock_whits += w

    n = max(1, len(theta_mods))
    wsum = max(1e-16, sum(weights))
    oct_top = max(range(8), key=lambda k: oct_counts[k])
    oct_wtop = max(range(8), key=lambda k: oct_wcounts[k])

    # Multi-harmonic view: if aliasing hides secondary peaks in 8 sectors,
    # inspect finer sector counts.
    peak_bins: dict[str, int] = {}
    for sectors in (8, 16, 24, 32):
        hist = circular_sector_hist(theta_mods, sectors)
        peak_bins[str(sectors)] = int(max(range(sectors), key=lambda j: hist[j]))

    return {
        "octant_counts": oct_counts,
        "octant_weighted_counts": oct_wcounts,
        "octant_peak_index": int(oct_top),
        "octant_peak_fraction": oct_counts[oct_top] / float(n),
        "octant_peak_weighted_index": int(oct_wtop),
        "octant_peak_weighted_fraction": oct_wcounts[oct_wtop] / float(wsum),
        "octant_lock_eps_deg": lock_eps_deg,
        "octant_lock_hits": int(lock_hits),
        "octant_lock_fraction": lock_hits / float(n),
        "octant_lock_weighted_fraction": lock_whits / float(wsum),
        "peak_bin_by_sector_count": peak_bins,
        "recovery_hint": (
            "Recover aliased secondary peaks by increasing sector count (8->16->24->32), "
            "then tracking stable peak bins under weighting."
        ),
    }


def build_report(
    phi: float,
    t: float,
    m_min: int,
    m_max: int,
    dim_p: int,
    curvature_model: str,
    sphere_dim: int,
    sparse_candidate_mode: str,
    sparse_allow_fallback: bool,
    spiral_window: int,
    target_angle: float | None,
    angle_eps: float,
    bidirectional: bool,
) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    max_abs_unit_dev = 0.0
    z_weight = dim_weight_normalizer(dim_p, m_min, m_max)
    if curvature_model == "intrinsic_sphere":
        curvature_norm_selected = intrinsic_sphere_curvature_norm(sphere_dim)
    else:
        curvature_norm_selected = CURVATURE_NORM_COMBINATORIAL
    for m in range(m_min, m_max + 1):
        angle = polar_angle_from_rapidity(phi, t, m)
        m_adj = adjacent_shell_mod3(m)
        angle_adj = polar_angle_from_rapidity(phi, t, m_adj)
        m_even = even_anchor_shell(m)
        m_odd3 = odd_multiple_of_three_anchor_shell(m)
        angle_even = polar_angle_from_rapidity(phi, t, m_even)
        angle_odd3 = polar_angle_from_rapidity(phi, t, m_odd3)
        triplet_valid = original_shell_valid_for_triplet(m)
        step_be = wrapped_angle_diff(angle, angle_even)
        step_eo = wrapped_angle_diff(angle_even, angle_odd3)
        step_bo = wrapped_angle_diff(angle, angle_odd3)
        ray8_scores, best_ray8, local_theta = ray8_scores_from_steps(step_be, step_eo)
        # For strict spiral-locked search, use the continuous local spiral angle
        # (ray8 is useful for diagnostics but too coarse for projection targets).
        sparse_ray_angle = local_theta if sparse_candidate_mode == "spiral_locked" else (math.pi / 4.0) * best_ray8
        spiral_tan = abs(math.tan(sparse_ray_angle))
        if spiral_tan < 1e-9:
            spiral_target_a = int(math.isqrt(m))
        else:
            spiral_target_a = int(round(math.sqrt(m / spiral_tan)))
        spiral_target_a = max(1, spiral_target_a)
        ranked_pairs = rank_factor_pairs_by_ray(m, (math.pi / 4.0) * best_ray8)
        orbit_ranked_pairs = rank_factor_pairs_by_three_axis_orbit(
            m,
            local_theta,
            copy_count=3,
            copy_rotation=(2.0 * math.pi / 3.0),
        )
        sparse_ranked = rank_sparse_pruned_pairs_by_ray(
            m,
            sparse_ray_angle,
            window=spiral_window,
            guarantee_no_prune=sparse_allow_fallback,
            candidate_mode=sparse_candidate_mode,
            target_angle=target_angle,
            angle_eps=angle_eps,
            bidirectional=bidirectional,
        )
        topk = ranked_pairs[:8]
        orbit_topk = orbit_ranked_pairs[:8]
        sparse_topk = sparse_ranked["pairs_found"][:8]
        has_11_17_topk = any((p["a"], p["b"]) == (11, 17) for p in topk)
        has_11_17_any = any((p["a"], p["b"]) == (11, 17) for p in ranked_pairs)
        sparse_has_11_17_topk = any((p["a"], p["b"]) == (11, 17) for p in sparse_topk)
        sparse_has_11_17_any = any((p["a"], p["b"]) == (11, 17) for p in sparse_ranked["pairs_found"])
        direct_pair = factor_pair_from_3spiral_mask(m, phi=phi, t=t)
        radius_succ = polar_radius_shell_succ(m)
        radius_rec = polar_radius_reciprocal(m)
        pr, pi_ = exp_i_angle(angle)
        mag = math.hypot(pr, pi_)
        max_abs_unit_dev = max(max_abs_unit_dev, abs(mag - 1.0))
        recon = infer_divisor_from_angle(angle)
        recon_adj = infer_divisor_from_angle(angle_adj)
        d_e = delta_e_combinatorial(m)
        d_e_selected = curvature_norm_selected * shell_shape(m)
        d_w = dim_shell_weight(dim_p, m_min, m_max, m)
        ramanujan_imprint = d_w * d_e_selected
        rows.append(
            {
                "m": float(m),
                "delta_theta_prime_m": delta_theta_prime(float(m)),
                "angle": angle,
                "triplet_rule_valid_original": triplet_valid,
                "adjacent_shell_mod3": float(m_adj),
                "angle_adjacent": angle_adj,
                "shell_even_anchor": float(m_even),
                "shell_odd_multiple3_anchor": float(m_odd3),
                "angle_even_anchor": angle_even,
                "angle_odd_multiple3_anchor": angle_odd3,
                "spiral_step_base_to_even": step_be,
                "spiral_step_even_to_odd_multiple3": step_eo,
                "spiral_step_base_to_odd_multiple3": step_bo,
                "local_spiral_theta": local_theta,
                "ray8_scores": ray8_scores,
                "best_ray8_index": float(best_ray8),
                "best_ray8_angle": (math.pi / 4.0) * best_ray8,
                "spiral_target_divisor_spot": float(spiral_target_a),
                "factor_pair_ranking_top8": topk,
                "factor_pair_orbit3_ranking_top8": orbit_topk,
                "factor_pair_contains_11_17_any": has_11_17_any,
                "factor_pair_contains_11_17_top8": has_11_17_topk,
                "direct_factor_pair_3spiral_mask": None if direct_pair is None else [int(direct_pair[0]), int(direct_pair[1])],
                "sparse_pruned_candidates_checked": float(sparse_ranked["candidates_checked"]),
                "sparse_candidate_mode": sparse_ranked["candidate_mode"],
                "sparse_target_angle": sparse_ranked["target_angle"],
                "sparse_target_angle_reverse": sparse_ranked["target_angle_reverse"],
                "sparse_angle_eps": sparse_ranked["angle_eps"],
                "sparse_bidirectional": sparse_ranked["bidirectional"],
                "sparse_filtered_out_by_angle": float(sparse_ranked["filtered_out_by_angle"]),
                "sparse_guarantee_no_prune": sparse_ranked["guarantee_no_prune"],
                "sparse_fallback_scan_used": sparse_ranked["fallback_scan_used"],
                "sparse_fallback_checked": float(sparse_ranked["fallback_checked"]),
                "sparse_factor_pair_ranking_top8": sparse_topk,
                "sparse_factor_pair_contains_11_17_any": sparse_has_11_17_any,
                "sparse_factor_pair_contains_11_17_top8": sparse_has_11_17_topk,
                "radius_shell_succ": radius_succ,
                "radius_reciprocal": radius_rec,
                "phase_argument_match": angle,  # same scalar used in zetaHQIVTerm phase argument
                # exp(I * angle)
                "exp_i_angle_re": pr,
                "exp_i_angle_im": pi_,
                # angle -> divisor reconstruction channel (theta ~ 2*pi/d)
                "theta_mod_two_pi": recon["theta_mod_two_pi"],
                "inferred_divisor_from_angle": recon["inferred_divisor"],
                "reconstructed_theta_from_divisor": recon["reconstructed_theta"],
                "angle_to_divisor_error_rad": recon["reconstruction_error"],
                "inferred_divisor_from_angle_adjacent": recon_adj["inferred_divisor"],
                "reconstructed_theta_from_divisor_adjacent": recon_adj["reconstructed_theta"],
                "angle_to_divisor_error_rad_adjacent": recon_adj["reconstruction_error"],
                # arithmetic comparator
                "divisor_count_tau_m": divisor_count(m),
                # HQIV curvature imprint channel (combinatorial deltaE) + dimension scaffold
                "curvature_density": curvature_density(m),
                "shell_shape": shell_shape(m),
                "deltaE_combinatorial": d_e,
                "deltaE_selected": d_e_selected,
                "dim_shell_weight": d_w,
                "ramanujan_dim_imprint": ramanujan_imprint,
                "phase_curvature_imprint": phi * t * d_e_selected,
                # Cartesian spiral: r * exp(I * angle)
                "spiral_succ_x": radius_succ * pr,
                "spiral_succ_y": radius_succ * pi_,
                "spiral_rec_x": radius_rec * pr,
                "spiral_rec_y": radius_rec * pi_,
            }
        )

    m0_angle = polar_angle_from_rapidity(phi, t, 0)
    checks = {
        "angle_zero_at_m0": abs(m0_angle) <= 1e-12,
        "horizon_quarter_period_equals_pi_over_2": abs(horizon_quarter_period() - (math.pi / 2.0)) <= 1e-12,
        "unit_phase_magnitude_deviation_max": max_abs_unit_dev,
        "unit_phase_magnitude_near_one": max_abs_unit_dev <= 1e-14,
    }
    aliasing = summarize_aliasing(rows, lock_eps_deg=5.0)

    return {
        "inputs": {
            "phi": phi,
            "t": t,
            "m_min": m_min,
            "m_max": m_max,
            "dim_p": dim_p,
            "curvature_model": curvature_model,
            "sphere_dim": sphere_dim,
            "sparse_candidate_mode": sparse_candidate_mode,
            "sparse_allow_fallback": sparse_allow_fallback,
            "spiral_window": spiral_window,
            "target_angle": target_angle,
            "angle_eps": angle_eps,
            "bidirectional": bidirectional,
        },
        "constants": {
            "horizon_quarter_period": horizon_quarter_period(),
            "pi_over_2": math.pi / 2.0,
            "alpha": ALPHA,
            "curvature_norm_combinatorial": CURVATURE_NORM_COMBINATORIAL,
            "curvature_norm_selected": curvature_norm_selected,
            "dim_weight_normalizer": z_weight,
        },
        "checks": checks,
        "aliasing_summary": aliasing,
        "points": rows,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Numerical rapidity->polar wave-spiral probe.")
    parser.add_argument("--phi", type=float, default=0.6, help="Rapidity factor phi (default: 0.6).")
    parser.add_argument(
        "--t",
        type=float,
        default=1.0,
        help="Time factor t — discrete step count (default: 1). Prefer integers.",
    )
    parser.add_argument("--m", type=int, help="Single shell index shortcut (overrides --m-min/--m-max).")
    parser.add_argument("--m-min", type=int, default=0, help="Minimum shell index m (default: 0).")
    parser.add_argument("--m-max", type=int, default=16, help="Maximum shell index m (default: 16).")
    parser.add_argument(
        "--dim-p",
        type=int,
        default=2,
        help="Dimension-template exponent p for dimShellWeight (default: 2, i.e. R3 template).",
    )
    parser.add_argument(
        "--curvature-model",
        choices=["intrinsic_sphere", "hqiv_o3"],
        default="intrinsic_sphere",
        help="Curvature norm source: intrinsic sphere n(n-1) or HQIV 3D+O combinatorial.",
    )
    parser.add_argument(
        "--sphere-dim",
        type=int,
        default=3,
        help="Sphere dimension n for intrinsic curvature model S^n (default: 3).",
    )
    parser.add_argument(
        "--sparse-candidate-mode",
        choices=["projected_window", "spiral_locked"],
        default="projected_window",
        help="Sparse prefilter mode for factor candidates.",
    )
    parser.add_argument(
        "--sparse-allow-fallback",
        action="store_true",
        help="Enable fallback full scan (off by default).",
    )
    parser.add_argument(
        "--spiral-window",
        type=int,
        default=8,
        help="Window around spiral target spot for candidate checks (default: 8).",
    )
    parser.add_argument(
        "--target-angle",
        type=float,
        default=None,
        help="Optional target angle (radians) for direct branch pruning.",
    )
    parser.add_argument(
        "--angle-eps",
        type=float,
        default=0.2,
        help="Angle tolerance (radians) when --target-angle is used.",
    )
    parser.add_argument(
        "--single-branch",
        action="store_true",
        help="Disable bidirectional branch matching (default is both directions).",
    )
    parser.add_argument(
        "--output",
        default="data/rapidity_polar_probe.json",
        help="Output JSON path (default: data/rapidity_polar_probe.json).",
    )
    args = parser.parse_args()

    if args.m is not None:
        args.m_min = args.m
        args.m_max = args.m

    if args.m_min < 0 or args.m_max < 0:
        raise SystemExit("--m-min and --m-max must be non-negative.")
    if args.dim_p < 0:
        raise SystemExit("--dim-p must be non-negative.")
    if args.sphere_dim < 2:
        raise SystemExit("--sphere-dim must be >= 2.")
    if args.m_min > args.m_max:
        raise SystemExit("--m-min must be <= --m-max.")
    if args.spiral_window < 0:
        raise SystemExit("--spiral-window must be non-negative.")

    report = build_report(
        phi=args.phi,
        t=args.t,
        m_min=args.m_min,
        m_max=args.m_max,
        dim_p=args.dim_p,
        curvature_model=args.curvature_model,
        sphere_dim=args.sphere_dim,
        sparse_candidate_mode=args.sparse_candidate_mode,
        sparse_allow_fallback=args.sparse_allow_fallback,
        spiral_window=args.spiral_window,
        target_angle=args.target_angle,
        angle_eps=args.angle_eps,
        bidirectional=(not args.single_branch),
    )

    output_path = Path(args.output)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(report, indent=2))

    print("Rapidity polar probe")
    print("=" * 21)
    print(f"phi,t               : {args.phi}, {args.t}")
    print(f"m range             : {args.m_min}..{args.m_max}")
    print(f"dimension exponent p: {args.dim_p}")
    print(f"curvature model     : {args.curvature_model} (sphere_dim={args.sphere_dim})")
    print(f"check m=0 angle=0   : {report['checks']['angle_zero_at_m0']}")
    print(f"check quarter=pi/2  : {report['checks']['horizon_quarter_period_equals_pi_over_2']}")
    print(f"check |exp(iθ)|≈1   : {report['checks']['unit_phase_magnitude_near_one']}")
    print(f"octant lock frac    : {report['aliasing_summary']['octant_lock_fraction']:.3f}")
    print(f"octant peak frac    : {report['aliasing_summary']['octant_peak_fraction']:.3f}")
    print(
        "peak bins (8/16/24/32): "
        f"{report['aliasing_summary']['peak_bin_by_sector_count']['8']}/"
        f"{report['aliasing_summary']['peak_bin_by_sector_count']['16']}/"
        f"{report['aliasing_summary']['peak_bin_by_sector_count']['24']}/"
        f"{report['aliasing_summary']['peak_bin_by_sector_count']['32']}"
    )
    print(f"output              : {output_path}")
    print("preview (m, angle, inferred d, tau(m), deltaE_selected, ramanujan_imprint):")
    for row in report["points"][: min(6, len(report["points"]))]:
        print(
            f"  {int(row['m']):>3d}, {row['angle']:.6f}, "
            f"{row['inferred_divisor_from_angle']}, {row['divisor_count_tau_m']}, "
            f"{row['deltaE_selected']:.6f}, {row['ramanujan_dim_imprint']:.6f}"
        )

    # Single-shell friendly print block requested by user.
    if args.m is not None and report["points"]:
        row = report["points"][0]
        sparse_top = row.get("sparse_factor_pair_ranking_top8", [])
        best_pair = sparse_top[0] if sparse_top else None
        print("\nSingle-shell spiral trace")
        print("=" * 25)
        print(f"m                    : {int(row['m'])}")
        print(f"mod-2 anchor         : {int(row['shell_even_anchor'])}")
        print(f"mod-3 odd anchor     : {int(row['shell_odd_multiple3_anchor'])}")
        print(f"spiral target spot a : {int(row['spiral_target_divisor_spot'])}")
        if row.get("sparse_target_angle") is not None:
            print(
                "target angle filter  : "
                f"theta={float(row['sparse_target_angle']):.6f}, "
                f"rev={float(row['sparse_target_angle_reverse']):.6f}, "
                f"eps={float(row['sparse_angle_eps']):.6f}, "
                f"filtered={int(row['sparse_filtered_out_by_angle'])}"
            )
        if best_pair is None:
            print("output               : no factor pair found in current sparse mode")
        else:
            print(
                "output               : "
                f"({int(best_pair['a'])}, {int(best_pair['b'])}) "
                f"err={float(best_pair['ray_error_rad']):.6f}"
            )
        direct_pair = row.get("direct_factor_pair_3spiral_mask")
        if direct_pair is None:
            print("direct 3-spiral pair : none")
        else:
            print(f"direct 3-spiral pair : ({int(direct_pair[0])}, {int(direct_pair[1])})")
        orbit_top = row.get("factor_pair_orbit3_ranking_top8", [])
        if orbit_top:
            o0 = orbit_top[0]
            print(
                "orbit3 top           : "
                f"({int(o0['a'])}, {int(o0['b'])}) "
                f"branch={int(o0['orbit_branch'])} "
                f"err={float(o0['orbit_error_rad']):.6f}"
            )


if __name__ == "__main__":
    main()

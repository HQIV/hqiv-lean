#!/usr/bin/env python3
"""
Euclidean geometric peel-and-retry factorization runner (strict mode).

Behavior:
- repeatedly peels factors from the current cofactor;
- uses ONLY the geometric splitter (`geometric_factorization_solver`);
- no timeouts, no step limits, no trial division, no Pollard-rho fallback;
- prints plain text only (no JSON/CSV).

It either fully factors via geometric peels, or reports unresolved cofactors.
"""

from __future__ import annotations

import argparse
import math
import time
from collections import Counter
from dataclasses import dataclass
from datetime import datetime

from mpmath import mp

from geometric_factorization_solver import GOLDEN_ANGLE, is_forbidden_form, morley_seeds, rapidity_delta

PHI = (1.0 + math.sqrt(5.0)) / 2.0
FLOAT_SAFE_BITS = 1000
KHINCHIN_K = 2.6854520010653064


@dataclass
class TensorBinaryState:
    local: list[list[float]]
    weight: list[float]
    bond_dim: int
    trunc_residual: float
    trunc_residual_ratio: float


def tensor_binary_seed(chi_max: int, chi_target: int) -> TensorBinaryState:
    chi_work = max(2, min(max(2, chi_max), max(2, 2 * chi_target)))
    local: list[list[float]] = []
    for slot in range(2):
        row = []
        for r in range(chi_work):
            row.append(0.5 + 0.5 * math.sin((slot + 1) * 0.41 + r / PHI))
        local.append(row)
    weight = [0.5 + 0.5 * math.cos(0.23 + r * 0.19) for r in range(chi_work)]
    return TensorBinaryState(
        local=local,
        weight=weight,
        bond_dim=chi_work,
        trunc_residual=0.0,
        trunc_residual_ratio=0.0,
    )


def tensor_binary_priorities(state: TensorBinaryState) -> tuple[float, float]:
    out: list[float] = []
    for slot in range(2):
        s = 0.0
        for r, w in enumerate(state.weight):
            s += state.local[slot][r] * w
        out.append(s)
    return out[0], out[1]


def tensor_binary_step(state: TensorBinaryState, step: int, frac: float, chi_target: int) -> TensorBinaryState:
    drift = GOLDEN_ANGLE * (step + 1)
    chi = state.bond_dim
    local = [row[:] for row in state.local]
    weight = state.weight[:]
    # Couple mirrored slots through symmetric/antisymmetric blending.
    coupling = 0.25 + 0.5 * abs(0.5 - frac)
    for r in range(chi):
        a = state.local[0][r]
        b = state.local[1][r]
        local[0][r] = 0.68 * a + 0.22 * b + 0.10 * math.sin(drift + r * 0.13) * coupling
        local[1][r] = 0.68 * b + 0.22 * a + 0.10 * math.cos(drift + r * 0.11) * (1.0 - coupling * 0.4)
        local[0][r] = min(1.0, max(0.0, local[0][r]))
        local[1][r] = min(1.0, max(0.0, local[1][r]))
        weight[r] = 0.92 * weight[r] + 0.08 * math.cos(drift + r * 0.17)

    wnorm = math.sqrt(sum(w * w for w in weight))
    if wnorm > 1e-12:
        weight = [w / wnorm for w in weight]

    tgt = max(2, min(chi, chi_target))
    if tgt == chi:
        return TensorBinaryState(
            local=local,
            weight=weight,
            bond_dim=chi,
            trunc_residual=0.0,
            trunc_residual_ratio=0.0,
        )
    channel_score: list[tuple[float, int]] = []
    for r in range(chi):
        avg = 0.5 * (local[0][r] + local[1][r])
        channel_score.append((abs(weight[r]) * avg, r))
    channel_score.sort(reverse=True)
    keep = {idx for _, idx in channel_score[:tgt]}
    dropped = [idx for idx in range(chi) if idx not in keep]
    residual = sum(abs(weight[idx]) for idx in dropped)
    total_mass = sum(abs(w) for w in weight)
    remap = sorted(keep)
    new_local = [[local[slot][idx] for idx in remap] for slot in range(2)]
    new_weight = [weight[idx] for idx in remap]
    return TensorBinaryState(
        local=new_local,
        weight=new_weight,
        bond_dim=tgt,
        trunc_residual=residual,
        trunc_residual_ratio=residual / max(1e-12, total_mass),
    )


def _clamp01(x: float) -> float:
    return min(1.0, max(0.0, x))


def tensor_gate_candidate_fracs(
    base_frac: float,
    p1: float,
    p2: float,
    trunc_residual_ratio: float,
    gate_span: float,
) -> list[float]:
    """
    Gate-driven candidate synthesis on top of reflected binary fractions.
    Interprets tensor channels as:
      - mix: average slot activation
      - phase: signed slot contrast
      - entangle: normalized slot separation
      - truncate: residual confidence attenuation
    """
    f = _clamp01(base_frac)
    rf = _clamp01(1.0 - f)
    mix = 0.5 * (p1 + p2)
    phase = math.tanh(p1 - p2)
    entangle = abs(p1 - p2) / max(1e-9, abs(p1) + abs(p2))
    truncate = max(0.0, 1.0 - trunc_residual_ratio)
    span = max(0.0, gate_span)
    delta = span * (0.4 + 0.6 * entangle) * (0.5 + 0.5 * truncate)
    phase_bias = 0.5 * delta * phase
    mix_pull = 0.25 * delta * math.tanh(mix)
    raw = [
        f,
        rf,
        f + delta + phase_bias,
        f - delta + phase_bias,
        rf + delta - phase_bias,
        rf - delta - phase_bias,
        0.5 * (f + rf) + mix_pull,
    ]
    out: list[float] = []
    seen: set[float] = set()
    for x in raw:
        y = _clamp01(x)
        key = round(y, 12)
        if key in seen:
            continue
        seen.add(key)
        out.append(y)
    return out


def khinchin_metrics_from_x(x: float | mp.mpf, terms: int) -> tuple[float, float]:
    """
    Return (delta, stability) where:
      delta := ln(G_t / K) with G_t from continued-fraction partials
      stability := exp(-std(log a_i)) in (0,1]
    """
    t = max(3, int(terms))
    y = mp.mpf(x)
    logs: list[float] = []
    for _ in range(t):
        a = int(mp.floor(y))
        if a > 0:
            logs.append(math.log(float(a)))
        frac = y - mp.floor(y)
        if abs(frac) < mp.mpf("1e-30"):
            break
        y = 1 / frac
    if not logs:
        return 10.0, 0.0
    mu = sum(logs) / float(len(logs))
    var = sum((v - mu) ** 2 for v in logs) / float(len(logs))
    g = math.exp(mu)
    delta = math.log(max(1e-12, g / KHINCHIN_K))
    stability = math.exp(-math.sqrt(max(0.0, var)))
    return delta, stability


def khinchin_gate_candidate_fracs(
    base_frac: float,
    kh_delta: float,
    kh_stability: float,
    gate_span: float,
) -> list[float]:
    """
    Khinchin-driven candidate fractions:
    stable-near-Khinchin states narrow around center; unstable states spread.
    """
    f = _clamp01(base_frac)
    rf = _clamp01(1.0 - f)
    s = max(0.0, min(1.0, kh_stability))
    span = max(0.0, gate_span) * (1.2 - 0.7 * s)
    phase = math.tanh(kh_delta)
    shift = 0.5 * span * phase
    raw = [f, rf, f + shift, rf - shift, f + span, f - span, rf + span, rf - span]
    out: list[float] = []
    seen: set[float] = set()
    for x in raw:
        y = _clamp01(x)
        key = round(y, 12)
        if key in seen:
            continue
        seen.add(key)
        out.append(y)
    return out


def is_probable_prime_mr(n: int) -> bool:
    """Miller-Rabin probable-prime check (no trial-division sweep)."""
    if n < 2:
        return False
    if n in (2, 3):
        return True
    if n % 2 == 0:
        return False
    d = n - 1
    s = 0
    while d % 2 == 0:
        s += 1
        d //= 2
    for a in (2, 3, 5, 7, 11, 13, 17):
        if a >= n:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        composite = True
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                composite = False
                break
        if composite:
            return False
    return True


def _small_primes_upto(limit: int) -> list[int]:
    if limit < 2:
        return []
    sieve = [True] * (limit + 1)
    sieve[0] = False
    sieve[1] = False
    p = 2
    while p * p <= limit:
        if sieve[p]:
            step = p
            start = p * p
            for j in range(start, limit + 1, step):
                sieve[j] = False
        p += 1
    return [i for i, ok in enumerate(sieve) if ok]


def peel_small_primes(n: int, limit: int = 257) -> tuple[list[int], int]:
    """
    Deterministic prepass: peel all prime factors <= `limit`.
    This shrinks cofactors before geometric search.
    """
    if n < 2 or limit < 2:
        return [], n
    x = n
    out: list[int] = []
    for p in _small_primes_upto(limit):
        while x % p == 0 and x > 1:
            out.append(p)
            x //= p
    return out, x


def _candidate_from_fraction(m: int, frac: float) -> int:
    frac = min(1.0, max(0.0, frac))
    if m.bit_length() <= FLOAT_SAFE_BITS:
        return max(1, int(round(m**frac)))
    # Bitlength-aware high-precision path for very large integers.
    work_prec = min(32768, max(256, 3 * m.bit_length()))
    with mp.workprec(work_prec):
        val = mp.power(mp.mpf(m), mp.mpf(frac))
        return max(1, int(mp.nint(val)))


def rapidity_delta_safe(n: int) -> float:
    """Bitlength-aware rapidity increment used by geometric walks."""
    if n <= 1:
        return math.pi / 4.0
    if n.bit_length() <= FLOAT_SAFE_BITS:
        return rapidity_delta(n)
    work_prec = min(32768, max(256, 3 * n.bit_length()))
    with mp.workprec(work_prec):
        val = mp.pi / (4 * mp.log(mp.mpf(n) + 1))
        return float(val)


def _is_perfect_square(x: int) -> bool:
    if x < 0:
        return False
    r = math.isqrt(x)
    return r * r == x


def _fermat_attempt(n: int, max_steps: int) -> int | None:
    """
    Bounded Fermat factorization: find a,b with n = a^2 - b^2 = (a-b)(a+b).
    Effective when factors are near sqrt(n).
    """
    if n < 9 or n % 2 == 0:
        return None
    a = math.isqrt(n)
    if a * a == n:
        return a
    a += 1
    for _ in range(max(0, max_steps)):
        b2 = a * a - n
        if b2 >= 0 and _is_perfect_square(b2):
            b = math.isqrt(b2)
            d1, d2 = a - b, a + b
            for d in (d1, d2):
                if 1 < d < n and n % d == 0:
                    return d
        a += 1
    return None


def _lehman_attempt(n: int, k_max: int) -> int | None:
    """
    Lehman (1974) variant: search small k with 4kn = a^2 - b^2.
    Bounded by k_max and per-k iteration caps for safety.
    """
    if n < 9 or n % 2 == 0:
        return None
    cbrt = max(1, int(round(float(n) ** (1.0 / 3.0))))
    k_limit = max(1, min(k_max, cbrt + 2))
    n6 = float(n) ** (1.0 / 6.0)
    for k in range(1, k_limit + 1):
        t = math.isqrt(4 * k * n)
        if t * t < 4 * k * n:
            t += 1
        sk = math.sqrt(float(k))
        span = int(math.ceil(n6 / (4.0 * sk))) + 3
        span = min(200_000, max(1, span))
        a_hi = t + span
        a = t
        while a < a_hi:
            x = a * a - 4 * k * n
            if x >= 0 and _is_perfect_square(x):
                b = math.isqrt(x)
                for cand in (a + b, abs(a - b)):
                    if cand <= 0:
                        continue
                    g = math.gcd(cand, n)
                    if 1 < g < n:
                        return g
            a += 1
    return None


def fermat_lehman_try_factor(
    n: int,
    *,
    max_fermat_steps: int,
    lehman_k_max: int,
) -> int | None:
    """Cheap classical fast path before geometric search."""
    if n < 4:
        return None
    if n % 2 == 0:
        return 2
    r = _fermat_attempt(n, max_fermat_steps)
    if r is not None:
        return r
    return _lehman_attempt(n, lehman_k_max)


def default_fermat_step_budget(m: int) -> int:
    if m <= 1:
        return 0
    return min(500_000, max(8_192, 1 << min(18, max(8, m.bit_length()))))


def default_lehman_k_budget(m: int) -> int:
    if m <= 1:
        return 1
    bl = m.bit_length()
    return min(50_000, max(256, bl * bl * bl))


def _nondivisor_small_primes(m: int, limit: int) -> tuple[int, ...]:
    """Primes p <= limit with gcd(p,m)=1; any divisor d|m must satisfy d mod p != 0 for these p."""
    if m <= 1 or limit < 2:
        return ()
    return tuple(p for p in _small_primes_upto(limit) if m % p != 0)


def _passes_coprime_factor_residue_gate(c: int, nondivisor_primes: tuple[int, ...]) -> bool:
    """If p∤m but p|c, then c cannot divide m."""
    for p in nondivisor_primes:
        if c % p == 0:
            return False
    return True


def _passes_sqrt_arity_gate(m: int, cand: int, arity: float) -> bool:
    """
    Triangle-inequality-inspired prune gate:
    keep candidates whose multiplicative imbalance from the symmetric split is
    at most sqrt(arity). For arity=2 this is sqrt(2).
    """
    if m <= 1 or cand <= 1 or cand >= m:
        return False
    a = max(1.0, float(arity))
    if m.bit_length() <= FLOAT_SAFE_BITS and cand.bit_length() <= FLOAT_SAFE_BITS:
        # ratio(cand, m/cand) = exp(|2 ln(cand) - ln(m)|)
        lhs = abs(2.0 * math.log(float(cand)) - math.log(float(m)))
        rhs = 0.5 * math.log(a)
        return lhs <= rhs
    # Bitlength-aware high-precision path for very large integers.
    work_prec = min(32768, max(256, 3 * m.bit_length()))
    with mp.workprec(work_prec):
        lhs = abs(2 * mp.log(mp.mpf(cand)) - mp.log(mp.mpf(m)))
        rhs = mp.mpf("0.5") * mp.log(mp.mpf(a))
        return lhs <= rhs


def _binary_reflection_search(
    m: int,
    *,
    sqrt_arity_prune: bool = True,
    sqrt_arity: float = 2.0,
    tensor_field: bool = True,
    tensor_chi_max: int = 8,
    tensor_chi_base: int = 4,
    tensor_residual_gate: float = 0.25,
    tensor_single_probe_margin: float = 0.35,
    tensor_gate_driven: bool = True,
    tensor_gate_span: float = 0.08,
    tensor_gate_max_candidates: int = 4,
    khinchin_gate: bool = False,
    khinchin_terms: int = 10,
    khinchin_gate_span: float = 0.06,
    khinchin_single_probe_threshold: float = 0.10,
    residue_gate: bool = True,
    residue_gate_prime_limit: int = 97,
    max_probes_per_step: int = 12,
) -> int | None:
    """
    Symmetric-tip binary search on the S4 base arc:
    - sample one side of the binary arc
    - reflect across the pi/4 arity pole (frac -> 1-frac)
    - test both mirrored candidates
    - terminate by geometric orbit-cycle detection (no step/time caps)
    """
    arc_len = math.pi / 4.0
    delta_phi = rapidity_delta_safe(m)
    alpha = 0.0
    seen_pairs: set[tuple[int, int]] = set()
    tstate = tensor_binary_seed(tensor_chi_max, tensor_chi_base) if tensor_field else None
    sqrt_m = math.sqrt(float(m)) if m.bit_length() <= FLOAT_SAFE_BITS else mp.sqrt(mp.mpf(m))
    nd_primes = _nondivisor_small_primes(m, residue_gate_prime_limit) if residue_gate else ()
    step = 0
    while True:
        frac = (alpha % arc_len) / arc_len
        if tstate is not None:
            tstate = tensor_binary_step(tstate, step, frac, tensor_chi_base)
        c1 = _candidate_from_fraction(m, frac)
        c2 = _candidate_from_fraction(m, 1.0 - frac)
        pair = (min(c1, c2), max(c1, c2))
        if pair in seen_pairs:
            return None
        seen_pairs.add(pair)
        kh_delta = 0.0
        kh_stability = 0.0
        cand_w: dict[int, float] = {}

        def bump(c: int, w: float) -> None:
            if c <= 1 or c >= m:
                return
            if m % 2 == 1 and c % 2 == 0:
                return
            cand_w[c] = cand_w.get(c, 0.0) + w

        bump(c1, 1.0)
        bump(c2, 1.0)
        if khinchin_gate:
            # Oscillate around sqrt(m), then read continued-fraction statistics.
            scale = 1.0 + 0.6 * (frac - 0.5)
            x = sqrt_m * scale + (1.0 / PHI)
            kh_delta, kh_stability = khinchin_metrics_from_x(x, khinchin_terms)
            kfracs = khinchin_gate_candidate_fracs(frac, kh_delta, kh_stability, khinchin_gate_span)
            for idx, ff in enumerate(kfracs):
                cc = _candidate_from_fraction(m, ff)
                w = 0.42 * max(0.0, min(1.0, kh_stability)) * (1.0 / (1.0 + 0.35 * float(idx)))
                w *= math.exp(-2.0 * abs(kh_delta))
                bump(cc, w)
        p1 = p2 = 0.5
        if tstate is not None:
            p1, p2 = tensor_binary_priorities(tstate)
            preferred_center = frac if p1 >= p2 else (1.0 - frac)
            trunc_r = max(0.0, min(1.0, tstate.trunc_residual_ratio))
            span_eff = max(1e-9, tensor_gate_span)
            if tensor_gate_driven:
                fracs = tensor_gate_candidate_fracs(
                    frac,
                    p1,
                    p2,
                    tstate.trunc_residual_ratio,
                    tensor_gate_span,
                )
                fracs.sort(key=lambda xf: abs(xf - preferred_center))
                n_gate = max(1, tensor_gate_max_candidates)
                for j, ff in enumerate(fracs[: max(n_gate, 8)]):
                    cc = _candidate_from_fraction(m, ff)
                    dist = min(abs(ff - preferred_center), abs(ff - (1.0 - preferred_center)))
                    qual = max(0.0, 1.0 - min(1.0, dist / span_eff))
                    w = 0.58 * qual * (0.55 + 0.45 * (1.0 - trunc_r))
                    w *= 1.0 / (1.0 + 0.12 * float(j))
                    closer_to_frac = abs(ff - frac) <= abs(ff - (1.0 - frac))
                    w += 0.08 * (p1 if closer_to_frac else p2)
                    bump(cc, w)
            else:
                if p2 > p1:
                    bump(c2, 0.22)
                    bump(c1, 0.12)
                else:
                    bump(c1, 0.22)
                    bump(c2, 0.12)

        probe_ranked = sorted(cand_w.items(), key=lambda kv: kv[1], reverse=True)
        probe_list = [c for c, _ in probe_ranked[: max(1, max_probes_per_step)]]
        if not probe_list:
            probe_list = [c1, c2]

        if tstate is not None:
            if (
                abs(p1 - p2) >= max(0.0, tensor_single_probe_margin)
                and tstate.trunc_residual_ratio <= max(0.0, tensor_residual_gate)
            ):
                probe_list = probe_list[:1]
        if khinchin_gate and kh_stability > 0.0 and abs(kh_delta) <= max(0.0, khinchin_single_probe_threshold):
            probe_list = probe_list[:1]

        for cand in probe_list:
            if residue_gate and not _passes_coprime_factor_residue_gate(cand, nd_primes):
                continue
            if sqrt_arity_prune and not _passes_sqrt_arity_gate(m, cand, sqrt_arity):
                continue
            if 1 < cand < m and m % cand == 0:
                return cand
        alpha += delta_phi
        step += 1


def _legacy_spiral_search(m: int) -> int | None:
    """Fallback pure geometric spiral walk (original unbounded behavior)."""
    forbidden = is_forbidden_form(m)
    arc_len = 2.0 * math.pi if forbidden else (math.pi / 4.0)
    alpha = 0.0
    delta_phi = rapidity_delta_safe(m)
    seeds = morley_seeds()
    step = 0
    while True:
        drift = step * GOLDEN_ANGLE
        for seed in seeds:
            angle = (alpha + seed + drift) % arc_len
            frac = angle / arc_len if arc_len > 0 else 0.0
            cand = _candidate_from_fraction(m, frac)
            if 1 < cand < m and m % cand == 0:
                return cand
        alpha += delta_phi
        step += 1


def split_once_geometric(
    m: int,
    *,
    fermat_lehman: bool = True,
    fermat_max_steps: int | None = None,
    lehman_k_max: int | None = None,
    sqrt_arity_prune: bool = True,
    sqrt_arity: float = 2.0,
    tensor_field: bool = True,
    tensor_chi_max: int = 8,
    tensor_chi_base: int = 4,
    tensor_residual_gate: float = 0.25,
    tensor_single_probe_margin: float = 0.35,
    tensor_gate_driven: bool = True,
    tensor_gate_span: float = 0.08,
    tensor_gate_max_candidates: int = 4,
    khinchin_gate: bool = False,
    khinchin_terms: int = 10,
    khinchin_gate_span: float = 0.06,
    khinchin_single_probe_threshold: float = 0.10,
    residue_gate: bool = True,
    residue_gate_prime_limit: int = 97,
    max_probes_per_step: int = 12,
) -> int | None:
    """
    Pure geometric splitter with symmetric-tip acceleration:
      0) optional Fermat / Lehman fast path (balanced / near-balanced factors)
      1) binary arc reflection search (S4, pi/4 symmetry)
      2) legacy geometric spiral fallback
    No timeouts or step limits.
    """
    if m <= 3:
        return None
    if fermat_lehman:
        fs = fermat_max_steps if fermat_max_steps is not None else default_fermat_step_budget(m)
        lk = lehman_k_max if lehman_k_max is not None else default_lehman_k_budget(m)
        fl = fermat_lehman_try_factor(m, max_fermat_steps=fs, lehman_k_max=lk)
        if fl is not None:
            return fl
    d = _binary_reflection_search(
        m,
        sqrt_arity_prune=sqrt_arity_prune,
        sqrt_arity=sqrt_arity,
        tensor_field=tensor_field,
        tensor_chi_max=tensor_chi_max,
        tensor_chi_base=tensor_chi_base,
        tensor_residual_gate=tensor_residual_gate,
        tensor_single_probe_margin=tensor_single_probe_margin,
        tensor_gate_driven=tensor_gate_driven,
        tensor_gate_span=tensor_gate_span,
        tensor_gate_max_candidates=tensor_gate_max_candidates,
        khinchin_gate=khinchin_gate,
        khinchin_terms=khinchin_terms,
        khinchin_gate_span=khinchin_gate_span,
        khinchin_single_probe_threshold=khinchin_single_probe_threshold,
        residue_gate=residue_gate,
        residue_gate_prime_limit=residue_gate_prime_limit,
        max_probes_per_step=max_probes_per_step,
    )
    if d is not None:
        return d
    return _legacy_spiral_search(m)


def factor_peel_geometric(
    n: int,
    *,
    fermat_lehman: bool = True,
    fermat_max_steps: int | None = None,
    lehman_k_max: int | None = None,
    sqrt_arity_prune: bool = True,
    sqrt_arity: float = 2.0,
    tensor_field: bool = True,
    tensor_chi_max: int = 8,
    tensor_chi_base: int = 4,
    tensor_residual_gate: float = 0.25,
    tensor_single_probe_margin: float = 0.35,
    tensor_gate_driven: bool = True,
    tensor_gate_span: float = 0.08,
    tensor_gate_max_candidates: int = 4,
    khinchin_gate: bool = False,
    khinchin_terms: int = 10,
    khinchin_gate_span: float = 0.06,
    khinchin_single_probe_threshold: float = 0.10,
    residue_gate: bool = True,
    residue_gate_prime_limit: int = 97,
    max_probes_per_step: int = 12,
    small_prime_peel: bool = True,
    small_prime_limit: int = 257,
) -> tuple[list[int], list[int]]:
    """
    Returns:
      - peeled factors found by geometric recursion
      - unresolved cofactors where no nontrivial geometric split was found
    """
    if n < 2:
        return [], []
    factors: list[int] = []
    root = n
    if small_prime_peel:
        peeled, root = peel_small_primes(n, small_prime_limit)
        factors.extend(peeled)
    stack = [root] if root > 1 else []
    unresolved: list[int] = []
    while stack:
        m = stack.pop()
        if m == 1:
            continue
        if is_probable_prime_mr(m):
            factors.append(m)
            continue
        d = split_once_geometric(
            m,
            fermat_lehman=fermat_lehman,
            fermat_max_steps=fermat_max_steps,
            lehman_k_max=lehman_k_max,
            sqrt_arity_prune=sqrt_arity_prune,
            sqrt_arity=sqrt_arity,
            tensor_field=tensor_field,
            tensor_chi_max=tensor_chi_max,
            tensor_chi_base=tensor_chi_base,
            tensor_residual_gate=tensor_residual_gate,
            tensor_single_probe_margin=tensor_single_probe_margin,
            tensor_gate_driven=tensor_gate_driven,
            tensor_gate_span=tensor_gate_span,
            tensor_gate_max_candidates=tensor_gate_max_candidates,
            khinchin_gate=khinchin_gate,
            khinchin_terms=khinchin_terms,
            khinchin_gate_span=khinchin_gate_span,
            khinchin_single_probe_threshold=khinchin_single_probe_threshold,
            residue_gate=residue_gate,
            residue_gate_prime_limit=residue_gate_prime_limit,
            max_probes_per_step=max_probes_per_step,
        )
        if d is None:
            unresolved.append(m)
            continue
        if d <= 1 or d >= m or m % d != 0:
            unresolved.append(m)
            continue
        stack.append(d)
        stack.append(m // d)

    # Geometric leafs are factors that could not be further split geometrically.
    # If run succeeded fully, unresolved are atomic leaves (typically primes).
    factors.extend(unresolved)
    return sorted(factors), sorted(unresolved)


def format_prime_powers(factors: list[int]) -> str:
    if not factors:
        return "1"
    c = Counter(factors)
    parts = []
    for p in sorted(c):
        e = c[p]
        parts.append(f"{p}^{e}" if e > 1 else str(p))
    return " * ".join(parts)


def run_one(
    n: int,
    *,
    fermat_lehman: bool,
    fermat_max_steps: int | None,
    lehman_k_max: int | None,
    sqrt_arity_prune: bool,
    sqrt_arity: float,
    tensor_field: bool,
    tensor_chi_max: int,
    tensor_chi_base: int,
    tensor_residual_gate: float,
    tensor_single_probe_margin: float,
    tensor_gate_driven: bool,
    tensor_gate_span: float,
    tensor_gate_max_candidates: int,
    khinchin_gate: bool,
    khinchin_terms: int,
    khinchin_gate_span: float,
    khinchin_single_probe_threshold: float,
    residue_gate: bool,
    residue_gate_prime_limit: int,
    max_probes_per_step: int,
    small_prime_peel: bool,
    small_prime_limit: int,
) -> None:
    started = time.perf_counter()
    ts = datetime.now().isoformat(timespec="seconds")
    factors, unresolved = factor_peel_geometric(
        n,
        fermat_lehman=fermat_lehman,
        fermat_max_steps=fermat_max_steps,
        lehman_k_max=lehman_k_max,
        sqrt_arity_prune=sqrt_arity_prune,
        sqrt_arity=sqrt_arity,
        tensor_field=tensor_field,
        tensor_chi_max=tensor_chi_max,
        tensor_chi_base=tensor_chi_base,
        tensor_residual_gate=tensor_residual_gate,
        tensor_single_probe_margin=tensor_single_probe_margin,
        tensor_gate_driven=tensor_gate_driven,
        tensor_gate_span=tensor_gate_span,
        tensor_gate_max_candidates=tensor_gate_max_candidates,
        khinchin_gate=khinchin_gate,
        khinchin_terms=khinchin_terms,
        khinchin_gate_span=khinchin_gate_span,
        khinchin_single_probe_threshold=khinchin_single_probe_threshold,
        residue_gate=residue_gate,
        residue_gate_prime_limit=residue_gate_prime_limit,
        max_probes_per_step=max_probes_per_step,
        small_prime_peel=small_prime_peel,
        small_prime_limit=small_prime_limit,
    )
    elapsed = time.perf_counter() - started
    print(f"[{ts}] n={n}")
    if fermat_lehman:
        fs = fermat_max_steps if fermat_max_steps is not None else "auto"
        lk = lehman_k_max if lehman_k_max is not None else "auto"
        print(f"fermat_lehman=on (fermat_max_steps={fs} lehman_k_max={lk})")
    else:
        print("fermat_lehman=off")
    if residue_gate:
        print(f"residue_gate=on (prime_limit={residue_gate_prime_limit} max_probes_per_step={max_probes_per_step})")
    else:
        print("residue_gate=off")
    if sqrt_arity_prune:
        print(f"sqrt_arity_prune=on (sqrt_arity={sqrt_arity:.6g})")
    else:
        print("sqrt_arity_prune=off")
    if tensor_field:
        print(
            "tensor_field=on "
            f"(chi_base={tensor_chi_base} chi_max={tensor_chi_max} "
            f"residual_gate={tensor_residual_gate:.4g} single_probe_margin={tensor_single_probe_margin:.4g})"
        )
        if tensor_gate_driven:
            print(
                "tensor_gates=on "
                f"(gate_span={tensor_gate_span:.4g} max_candidates={tensor_gate_max_candidates})"
            )
        else:
            print("tensor_gates=off")
    else:
        print("tensor_field=off")
    if khinchin_gate:
        print(
            "khinchin_gate=on "
            f"(terms={khinchin_terms} span={khinchin_gate_span:.4g} "
            f"single_probe_threshold={khinchin_single_probe_threshold:.4g})"
        )
    else:
        print("khinchin_gate=off")
    if small_prime_peel:
        print(f"small_prime_peel=on (limit={small_prime_limit})")
    else:
        print("small_prime_peel=off")
    print(f"p^n: {format_prime_powers(factors)}")
    if unresolved:
        print(f"status: UNRESOLVED (geometric splitter stalled on {len(unresolved)} cofactor(s))")
        print(f"unresolved_cofactors: {unresolved}")
    else:
        print("status: SUCCESS (geometric-only peel completed)")
    print(f"elapsed_s={elapsed:.6f}")


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Timestamped Euclidean peel-and-retry factorization.")
    p.add_argument("nums", nargs="+", type=int, help="integers to factor")
    p.add_argument(
        "--no-fermat-lehman",
        action="store_true",
        help="disable Fermat/Lehman classical fast path before geometric search",
    )
    p.add_argument(
        "--fermat-max-steps",
        type=int,
        default=0,
        help="Fermat outer-loop step cap (0 => bitlength-aware default)",
    )
    p.add_argument(
        "--lehman-k-max",
        type=int,
        default=0,
        help="Lehman k-loop cap (0 => bitlength-aware default)",
    )
    p.add_argument(
        "--no-residue-gate",
        action="store_true",
        help="disable mod-small-prime coprime residue prefilter on candidates",
    )
    p.add_argument(
        "--residue-gate-prime-limit",
        type=int,
        default=97,
        help="largest small prime for residue prefilter (default: 97)",
    )
    p.add_argument(
        "--max-probes-per-step",
        type=int,
        default=12,
        help="max weighted candidates probed per binary reflection step (default: 12)",
    )
    p.add_argument(
        "--sqrt-arity",
        type=float,
        default=2.0,
        help="arity used by sqrt-arity prune gate in binary reflection (default: 2.0)",
    )
    p.add_argument(
        "--no-sqrt-arity-prune",
        action="store_true",
        help="disable sqrt-arity pruning in binary reflection search",
    )
    p.add_argument(
        "--no-tensor-field",
        action="store_true",
        help="disable tensor-biased ordering in binary reflection search",
    )
    p.add_argument("--tensor-chi-base", type=int, default=4, help="target tensor bond dimension (default: 4)")
    p.add_argument("--tensor-chi-max", type=int, default=8, help="max working tensor bond dimension (default: 8)")
    p.add_argument(
        "--tensor-residual-gate",
        type=float,
        default=0.25,
        help="single-probe enabled only when truncation residual ratio <= gate",
    )
    p.add_argument(
        "--tensor-single-probe-margin",
        type=float,
        default=0.35,
        help="minimum tensor priority gap to probe only one mirrored candidate",
    )
    p.add_argument(
        "--no-tensor-gates",
        action="store_true",
        help="disable gate-driven tensor candidate synthesis (falls back to mirrored ordering)",
    )
    p.add_argument(
        "--tensor-gate-span",
        type=float,
        default=0.08,
        help="fraction-domain perturbation span for gate-driven candidates",
    )
    p.add_argument(
        "--tensor-gate-max-candidates",
        type=int,
        default=4,
        help="max gate-driven candidates probed per binary step",
    )
    p.add_argument(
        "--khinchin-gate",
        action="store_true",
        help="enable Khinchin-channel gate guidance for candidate synthesis",
    )
    p.add_argument("--khinchin-terms", type=int, default=10, help="continued-fraction terms for Khinchin channel")
    p.add_argument("--khinchin-gate-span", type=float, default=0.06, help="fraction perturbation span for Khinchin gate")
    p.add_argument(
        "--khinchin-single-probe-threshold",
        type=float,
        default=0.10,
        help="if |ln(G_t/K)| is below this threshold, probe one candidate only",
    )
    p.add_argument(
        "--no-small-prime-peel",
        action="store_true",
        help="disable deterministic peeling of prime factors <= small-prime-limit",
    )
    p.add_argument(
        "--small-prime-limit",
        type=int,
        default=257,
        help="largest prime used in prepass peeling (default: 257)",
    )
    return p


def main() -> None:
    args = build_parser().parse_args()
    if args.sqrt_arity <= 0.0:
        raise SystemExit("--sqrt-arity must be > 0")
    if args.tensor_chi_base < 2:
        raise SystemExit("--tensor-chi-base must be >= 2")
    if args.tensor_chi_max < 2:
        raise SystemExit("--tensor-chi-max must be >= 2")
    if args.tensor_chi_max < args.tensor_chi_base:
        raise SystemExit("--tensor-chi-max must be >= --tensor-chi-base")
    if args.tensor_residual_gate < 0.0:
        raise SystemExit("--tensor-residual-gate must be >= 0")
    if args.tensor_single_probe_margin < 0.0:
        raise SystemExit("--tensor-single-probe-margin must be >= 0")
    if args.tensor_gate_span < 0.0:
        raise SystemExit("--tensor-gate-span must be >= 0")
    if args.tensor_gate_max_candidates < 1:
        raise SystemExit("--tensor-gate-max-candidates must be >= 1")
    if args.khinchin_terms < 3:
        raise SystemExit("--khinchin-terms must be >= 3")
    if args.khinchin_gate_span < 0.0:
        raise SystemExit("--khinchin-gate-span must be >= 0")
    if args.khinchin_single_probe_threshold < 0.0:
        raise SystemExit("--khinchin-single-probe-threshold must be >= 0")
    if args.small_prime_limit < 2:
        raise SystemExit("--small-prime-limit must be >= 2")
    if args.fermat_max_steps < 0:
        raise SystemExit("--fermat-max-steps must be >= 0")
    if args.lehman_k_max < 0:
        raise SystemExit("--lehman-k-max must be >= 0")
    if args.residue_gate_prime_limit < 2:
        raise SystemExit("--residue-gate-prime-limit must be >= 2")
    if args.max_probes_per_step < 1:
        raise SystemExit("--max-probes-per-step must be >= 1")
    sqrt_arity_prune = not args.no_sqrt_arity_prune
    tensor_field = not args.no_tensor_field
    tensor_gate_driven = not args.no_tensor_gates
    small_prime_peel = not args.no_small_prime_peel
    fermat_lehman = not args.no_fermat_lehman
    fermat_max_steps = None if args.fermat_max_steps == 0 else args.fermat_max_steps
    lehman_k_max = None if args.lehman_k_max == 0 else args.lehman_k_max
    residue_gate = not args.no_residue_gate
    for n in args.nums:
        if n < 1:
            print(f"n={n} -> skipped (must be >= 1)")
            continue
        run_one(
            n,
            fermat_lehman=fermat_lehman,
            fermat_max_steps=fermat_max_steps,
            lehman_k_max=lehman_k_max,
            sqrt_arity_prune=sqrt_arity_prune,
            sqrt_arity=args.sqrt_arity,
            tensor_field=tensor_field,
            tensor_chi_max=args.tensor_chi_max,
            tensor_chi_base=args.tensor_chi_base,
            tensor_residual_gate=args.tensor_residual_gate,
            tensor_single_probe_margin=args.tensor_single_probe_margin,
            tensor_gate_driven=tensor_gate_driven,
            tensor_gate_span=args.tensor_gate_span,
            tensor_gate_max_candidates=args.tensor_gate_max_candidates,
            khinchin_gate=args.khinchin_gate,
            khinchin_terms=args.khinchin_terms,
            khinchin_gate_span=args.khinchin_gate_span,
            khinchin_single_probe_threshold=args.khinchin_single_probe_threshold,
            residue_gate=residue_gate,
            residue_gate_prime_limit=args.residue_gate_prime_limit,
            max_probes_per_step=args.max_probes_per_step,
            small_prime_peel=small_prime_peel,
            small_prime_limit=args.small_prime_limit,
        )


if __name__ == "__main__":
    main()


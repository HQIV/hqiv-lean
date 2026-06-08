#!/usr/bin/env python3
"""
Semiprime orthogonal-diagonal Shor (classical, two-channel).

Lean target: `Hqiv.Geometry.SemiprimeOrthogonalDiagonal`

For odd composite N (intended semiprime N = pq), multiplication by a coprime base a
splits across CRT into two cyclic channels. This module:

1. Finds multiplicative period r of a mod N (BSGS for large n, brute for small).
2. Builds a patch-local `SuperpositionCarrier` with slot-disjoint pivot/mirror flats:
   channel A = direct angle slot from a^k mod N; channel B = reflected slot (2#Q mirror).
3. Diagonal eigenphase weights cos²/sin²(2πk/r) at **mpmath precision scaled by N and r**.
4. Optional continued-fraction recovery of r from eigenphases (classical QFT peak readout).
5. Nominates candidates: period gcd splits, cofactor slots, mirror slots, period-selector gcds.

Soundness: only `OddCoreFactorWitness`-style divisibility certificates (same as reverse-Shor).
"""

from __future__ import annotations

import argparse
import json
import math
import time
from contextlib import contextmanager
from typing import Any, Iterator

from mpmath import mp

import hqiv_quantum_gate_alias_probe as osh
import hqiv_reverse_shor_period_selector as rss

# Re-export shared types
SuperpositionCarrier = rss.SuperpositionCarrier
PeriodMirrorWitness = rss.PeriodMirrorWitness

REFERENCE_M_DEFAULT = rss.REFERENCE_M_DEFAULT

# Use BSGS when odd core exceeds this bit length (brute below).
_BSGS_MIN_BITS = 20


# ---------------------------------------------------------------------------
# Precision (scaled by input N and period r)
# ---------------------------------------------------------------------------


def mpmath_prec_bits_for_n(n: int, *, period_r: int | None = None) -> int:
    """
    Binary precision for mpmath ``mp.prec``, tied to ``n`` and (when known) period ``r``.

    Eigenphases use θ_k = 2πk/r; resolving k/r mod 1 needs ~ bitlen(r) + bitlen(k) guard bits.
    """
    bl = max(1, abs(n).bit_length())
    rl = max(1, abs(period_r).bit_length()) if period_r and period_r > 1 else bl
    # O(orbit) trig sums: scale with shell #Q ≈ sqrt(n) as well.
    q_bits = max(1, math.isqrt(max(2, n)).bit_length())
    return min(50_000, max(128, bl * 4 + rl * 3 + q_bits * 2 + 128))


@contextmanager
def mpmath_prec_scope_for_n(n: int, *, period_r: int | None = None) -> Iterator[None]:
    """Set ``mp.prec`` from ``n`` (and optional ``r``), restore on exit."""
    old_prec, old_dps = mp.prec, mp.dps
    try:
        mp.prec = mpmath_prec_bits_for_n(n, period_r=period_r)
        yield
    finally:
        mp.prec = old_prec
        mp.dps = old_dps


# ---------------------------------------------------------------------------
# Shell maps (Lean `QuantumFactorGateFrontier`)
# ---------------------------------------------------------------------------


def reflection_mod(n: int) -> int:
    """Lean `reflectionMod n` = max 1 (2 * qSpan n)."""
    return max(1, 2 * rss.q_span(n))


def reflect_slot(n: int, slot: int) -> int:
    """Lean `reflectSlot` on doubled span."""
    m = reflection_mod(n)
    return (m - 1 - (slot % m)) % m


def cofactor_candidate_from_slot(n: int, slot: int) -> int:
    """Lean `cofactorCandidateFromSlot`."""
    q = rss.q_span(n)
    if q <= 1:
        return 2
    return 2 + (slot % (q - 1))


def angle_slot(n: int, code: int) -> int:
    """Lean `angleSlot`."""
    return code % rss.q_span(n)


def order_search_cap(n: int) -> int:
    """Maximum period length to search (no artificial 2^20 cap)."""
    return max(1, n - 1)


def _modinv(a: int, n: int) -> int | None:
    a %= n
    if math.gcd(a, n) != 1:
        return None
    t, newt = 0, 1
    r, newr = n, a
    while newr:
        q = r // newr
        t, newt = newt, t - q * newt
        r, newr = newr, r - q * newr
    if r != 1:
        return None
    return t % n


def normalize_order(a: int, n: int, r: int) -> int | None:
    """Reduce r to the minimal positive order of a mod n."""
    if r <= 0 or pow(a, r, n) != 1:
        return None
    out = r
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47):
        while out % p == 0 and pow(a, out // p, n) == 1:
            out //= p
    d = 2
    while d * d <= out:
        if out % d == 0:
            while out % d == 0 and pow(a, out // d, n) == 1:
                out //= d
        d += 1 if d == 2 else 2
    return out if out > 0 and pow(a, out, n) == 1 else None


def multiplicative_order_brute(a: int, n: int, *, max_r: int | None = None) -> int | None:
    """Smallest r > 0 with a^r ≡ 1 (mod n); linear scan."""
    if n <= 1:
        return None
    a %= n
    if math.gcd(a, n) != 1:
        return None
    cap = max_r if max_r is not None else order_search_cap(n)
    x = 1
    for r in range(1, cap + 1):
        x = (x * a) % n
        if x == 1:
            return r
    return None


def multiplicative_order_bsgs(a: int, n: int) -> int | None:
    """
    Baby-step giant-step order finder: O(√n) modular multiplies (typical).

    Finds smallest r > 0 with a^r ≡ 1 (mod n) when the scan succeeds.
    """
    if n <= 1:
        return None
    a %= n
    if math.gcd(a, n) != 1:
        return None
    if pow(a, 1, n) == 1:
        return 1

    m = int(math.isqrt(n)) + 1
    table: dict[int, int] = {}
    x = 1
    for j in range(m):
        if x == 1 and j > 0:
            return normalize_order(a, n, j)
        table[x] = j
        x = (x * a) % n

    inv = _modinv(a, n)
    if inv is None:
        return None
    gamma = pow(inv, m, n)
    y = 1
    for i in range(m + 1):
        if y in table:
            r = i * m + table[y]
            if r > 0:
                r_min = normalize_order(a, n, r)
                if r_min is not None:
                    return r_min
        y = (y * gamma) % n
    return None


def multiplicative_order(
    a: int,
    n: int,
    *,
    max_r: int | None = None,
    method: str = "auto",
) -> tuple[int | None, str]:
    """
    Order of a mod n. Returns (r, method_used).

    ``auto``: brute if n is small or max_r is tight; else BSGS then brute fallback.
    """
    cap = max_r if max_r is not None else order_search_cap(n)
    if method == "brute":
        return multiplicative_order_brute(a, n, max_r=cap), "brute"
    if method == "bsgs":
        r = multiplicative_order_bsgs(a, n)
        return r, "bsgs"

    bits = max(2, n).bit_length()
    if bits <= _BSGS_MIN_BITS or cap <= 1 << 16:
        return multiplicative_order_brute(a, n, max_r=cap), "brute"
    r = multiplicative_order_bsgs(a, n)
    if r is not None:
        return r, "bsgs"
    return multiplicative_order_brute(a, n, max_r=cap), "brute_fallback"


def _cf_convergents_unit(x: mp.mpf, *, max_terms: int = 96) -> Iterator[tuple[int, int]]:
    """Continued-fraction convergents p/q for x in (0,1)."""
    h_prev, k_prev = 0, 1
    h_curr, k_curr = 1, 0
    t = mp.mpf(x) % 1
    for _ in range(max_terms):
        if t <= mp.mpf("1e-80"):
            break
        a_i = int(mp.floor(t))
        h_new = a_i * h_curr + h_prev
        k_new = a_i * k_curr + k_prev
        if k_new > 0:
            yield h_new, k_new
        h_prev, k_prev = h_curr, k_curr
        h_curr, k_curr = h_new, k_new
        frac = t - a_i
        if frac <= mp.mpf("1e-80"):
            break
        t = 1 / frac


def recover_period_from_eigenphase(
    a: int,
    n: int,
    k: int,
    theta: mp.mpf,
    *,
    max_denom: int | None = None,
) -> int | None:
    """
    Classical QFT-style readout: θ ≈ 2πk/r (mod 2π) ⇒ recover r via convergents of θ/(2π).
    """
    if k <= 0:
        return None
    cap = max_denom if max_denom is not None else order_search_cap(n)
    with mpmath_prec_scope_for_n(n):
        frac = (mp.mpf(theta) / (2 * mp.pi)) % 1
        best: int | None = None
        tol = mp.mpf(10) ** (-(mp.prec // 8))
        for p, q in _cf_convergents_unit(frac):
            if q < 2 or q > cap:
                continue
            if abs(frac - mp.mpf(p) / q) > tol:
                continue
            if pow(a, q, n) != 1:
                continue
            r_min = normalize_order(a, n, q)
            if r_min is None:
                continue
            if best is None or r_min < best:
                best = r_min
        return best


def shor_gcd_candidates_from_period(a: int, n: int, r: int) -> list[int]:
    """Classical Shor split when period r is even: gcd(a^(r/2) ± 1, n)."""
    if r <= 0 or r % 2 == 1:
        return []
    half = r // 2
    base = pow(a, half, n)
    out: list[int] = []
    for x in (base - 1, base + 1):
        g = math.gcd(x, n)
        if 1 < g < n:
            out.append(g)
    return out


def orbit_steps_for_period(r: int, n: int) -> int:
    """How many orbit steps to materialize on the carrier (full period up to practical cap)."""
    # Full period for diagonal closure; cap only for absurd r relative to bitlen.
    hard_cap = max(512, 4 * max(1, n.bit_length()) ** 2)
    return min(r, hard_cap)


def orbit_value_slots(
    n: int,
    a: int,
    r: int,
    *,
    max_steps: int | None = None,
) -> list[tuple[int, int, int]]:
    """
    For k = 0..steps-1 return (k, slot_a, slot_b).
    """
    steps = orbit_steps_for_period(r, n) if max_steps is None else min(r, max_steps)
    rows: list[tuple[int, int, int]] = []
    for k in range(steps):
        v = pow(a, k, n)
        sa = angle_slot(n, v)
        sb = reflect_slot(n, sa)
        rows.append((k, sa, sb))
    return rows


def slot_disjoint_channels(slot_a: int, slot_b: int) -> bool:
    return slot_a != slot_b


def eigenphase_weights(
    n: int,
    r: int,
    k: int,
) -> tuple[mp.mpf, mp.mpf]:
    """Diagonal eigenphase weights (cos², sin²) at precision determined by n and r."""
    with mpmath_prec_scope_for_n(n, period_r=r):
        phase = 2 * mp.pi * mp.mpf(k) / mp.mpf(max(r, 1))
        c = mp.cos(phase)
        s = mp.sin(phase)
        return c**2, s**2


def build_diagonal_carrier(
    L: int,
    odd: int,
    a: int,
    r: int,
    *,
    max_orbit_steps: int | None = None,
) -> tuple[SuperpositionCarrier, dict[str, Any]]:
    """
    Two-channel diagonal carrier: high-precision cos²/sin² on pivot vs mirror flats.
    """
    prec_bits = mpmath_prec_bits_for_n(odd, period_r=r)
    amps: dict[int, float] = {}
    disjoint_pairs = 0
    total_pairs = 0
    peak_k = 0
    peak_weight = mp.mpf(-1)

    with mpmath_prec_scope_for_n(odd, period_r=r):
        two_pi = 2 * mp.pi
        for k, sa, sb in orbit_value_slots(odd, a, r, max_steps=max_orbit_steps):
            total_pairs += 1
            if slot_disjoint_channels(sa, sb):
                disjoint_pairs += 1
            phase = two_pi * mp.mpf(k) / mp.mpf(max(r, 1))
            w_a = mp.cos(phase) ** 2
            w_b = mp.sin(phase) ** 2
            total_w = w_a + w_b
            if total_w > peak_weight:
                peak_weight = total_w
                peak_k = k
            flat_a = osh.wrap_idx(L, sa)
            flat_b = osh.wrap_idx(L, sb)
            amps[flat_a] = amps.get(flat_a, 0.0) + float(w_a)
            amps[flat_b] = amps.get(flat_b, 0.0) + float(w_b)

        cf_period: int | None = None
        if peak_k > 0:
            theta_peak = two_pi * mp.mpf(peak_k) / mp.mpf(max(r, 1))
            cf_period = recover_period_from_eigenphase(a, odd, peak_k, theta_peak)

    support = tuple(sorted(amps.keys()))
    meta = {
        "base_a": a,
        "period_r": r,
        "mpmath_prec_bits": prec_bits,
        "peak_k": peak_k,
        "cf_period_from_peak": cf_period,
        "disjoint_slot_pairs": disjoint_pairs,
        "total_slot_pairs": total_pairs,
        "channel_orthogonality_ratio": disjoint_pairs / max(1, total_pairs),
        "orbit_steps_used": len(orbit_value_slots(odd, a, r, max_steps=max_orbit_steps)),
    }
    return SuperpositionCarrier(support=support, amps=amps), meta


def semiprime_diagonal_candidates(
    odd: int,
    a: int,
    r: int,
    carrier: SuperpositionCarrier,
    L: int,
    *,
    cf_period: int | None = None,
) -> list[int]:
    """Union of classical period gcds, slot cofactors, mirror cofactors, period-selector channels."""
    seen: set[int] = set()
    out: list[int] = []

    def add(x: int) -> None:
        if x not in seen:
            seen.add(x)
            out.append(x)

    if cf_period is not None and cf_period > 1:
        for d in shor_gcd_candidates_from_period(a, odd, cf_period):
            add(d)
            add(math.gcd(d, odd))

    for d in shor_gcd_candidates_from_period(a, odd, r):
        add(d)
        add(math.gcd(d, odd))

    for _k, sa, sb in orbit_value_slots(odd, a, r):
        for slot in (sa, sb):
            c = cofactor_candidate_from_slot(odd, slot)
            add(c)
            add(math.gcd(c, odd))

    for flat in carrier.support:
        add(rss.ket_linear_fallback_candidate(L, odd, flat))

    for w in rss.find_mirror_witnesses(L, odd, carrier):
        for d in rss.period_selector_candidates(w, odd):
            add(d)

    return out


def semiprime_orthogonal_diagonal_factor_odd(
    odd: int,
    *,
    L: int | None = None,
    bases: tuple[int, ...] | None = None,
    max_order: int | None = None,
    order_method: str = "auto",
    reference_m: int = REFERENCE_M_DEFAULT,
) -> dict[str, Any]:
    """
    Factor odd composite using semiprime two-channel diagonal + classical period gcd.
    """
    if odd <= 1:
        return {
            "odd": odd,
            "divisor": None,
            "success": odd == 1,
            "steps_used": 0,
            "pipeline": "semiprime-orthogonal-diagonal",
        }

    L_eff = rss._default_L(odd) if L is None else max(1, L)
    if bases is None:
        bases = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47)

    started = time.perf_counter()
    trace: list[dict[str, Any]] = []
    hit: int | None = None
    hit_meta: dict[str, Any] | None = None

    for a in bases:
        if math.gcd(a, odd) != 1:
            continue
        r, order_tag = multiplicative_order(a, odd, max_r=max_order, method=order_method)
        if r is None:
            trace.append(
                {
                    "base_a": a,
                    "period_r": None,
                    "order_method": order_tag,
                    "skipped": "order_not_found",
                    "order_cap": max_order if max_order is not None else order_search_cap(odd),
                }
            )
            continue

        carrier, carrier_meta = build_diagonal_carrier(L_eff, odd, a, r)
        cf_r = carrier_meta.get("cf_period_from_peak")
        candidates = semiprime_diagonal_candidates(
            odd, a, r, carrier, L_eff, cf_period=cf_r if isinstance(cf_r, int) else None
        )

        for d in candidates:
            if rss.certify_odd_core_divisor(odd, d):
                hit = d
                hit_meta = {
                    "base_a": a,
                    "period_r": r,
                    "order_method": order_tag,
                    "candidate": d,
                    "carrier_support_size": len(carrier.support),
                    **carrier_meta,
                }
                break

        trace.append(
            {
                "base_a": a,
                "period_r": r,
                "order_method": order_tag,
                "carrier_support_size": len(carrier.support),
                "candidates_tried": len(candidates),
                "factor_hit": hit,
                **carrier_meta,
            }
        )
        if hit is not None:
            break

    elapsed = time.perf_counter() - started
    return {
        "odd": odd,
        "divisor": hit,
        "cofactor": (odd // hit) if hit is not None else None,
        "success": hit is not None,
        "steps_used": len(trace),
        "elapsed_s": elapsed,
        "L": L_eff,
        "basis_card": osh.sparse_basis_card(L_eff),
        "pipeline": "semiprime-orthogonal-diagonal",
        "hit_meta": hit_meta,
        "trace": trace,
    }


def semiprime_orthogonal_diagonal_factor(
    n: int,
    *,
    L: int | None = None,
    bases: tuple[int, ...] | None = None,
    max_order: int | None = None,
    order_method: str = "auto",
    reference_m: int = REFERENCE_M_DEFAULT,
) -> dict[str, Any]:
    """Peel twos, run semiprime diagonal on odd core."""
    if n <= 1:
        return {"n": n, "factors": [1], "success": False, "pipeline": "semiprime-orthogonal-diagonal"}

    original = n
    twos: list[int] = []
    odd = n
    while odd % 2 == 0:
        twos.append(2)
        odd //= 2
    if odd == 1:
        return {
            "n": original,
            "factors": sorted(twos),
            "success": True,
            "twos_peeled": len(twos),
            "odd_core": 1,
            "pipeline": "semiprime-orthogonal-diagonal",
        }

    node = semiprime_orthogonal_diagonal_factor_odd(
        odd,
        L=L,
        bases=bases,
        max_order=max_order,
        order_method=order_method,
        reference_m=reference_m,
    )
    if not node["success"] or node["divisor"] is None:
        return {
            "n": original,
            "factors": sorted(twos + [odd]),
            "success": False,
            "twos_peeled": len(twos),
            "odd_core": odd,
            "odd_node": node,
            "pipeline": "semiprime-orthogonal-diagonal",
        }

    d = int(node["divisor"])
    q = odd // d
    factors = sorted(twos + [d, q])
    return {
        "n": original,
        "factors": factors,
        "success": math.prod(factors) == original,
        "twos_peeled": len(twos),
        "odd_core": odd,
        "odd_node": node,
        "pipeline": "semiprime-orthogonal-diagonal",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Semiprime orthogonal-diagonal factorization")
    parser.add_argument("n", type=int)
    parser.add_argument("--L", type=int, default=0, help="harmonic cutoff (0 => auto)")
    parser.add_argument(
        "--order-method",
        choices=("auto", "brute", "bsgs"),
        default="auto",
        help="period-finding method",
    )
    parser.add_argument(
        "--max-order",
        type=int,
        default=0,
        help="cap period search (0 => n-1, no fixed 2^20 ceiling)",
    )
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    L = None if args.L == 0 else args.L
    max_order = None if args.max_order == 0 else args.max_order
    result = semiprime_orthogonal_diagonal_factor(
        args.n,
        L=L,
        max_order=max_order,
        order_method=args.order_method,
    )
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print(
            f"n={result['n']} factors={result['factors']} success={result['success']} "
            f"pipeline={result['pipeline']}"
        )
        node = result.get("odd_node") or {}
        meta = node.get("hit_meta") or {}
        if meta:
            print(
                f"  period_r={meta.get('period_r')} order={meta.get('order_method')} "
                f"prec_bits={meta.get('mpmath_prec_bits')}"
            )


if __name__ == "__main__":
    main()

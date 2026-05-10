#!/usr/bin/env python3
"""
HQIV OSH Integrated Driver — Solve et Coagula

Unified system where the HQIV sparse simulation pipeline is the central engine.
Phase channel (rapidity), geometric angle registers, and reflection symmetry
are native enhancements.
"""

from __future__ import annotations

import argparse
import json
import math
import time
from dataclasses import dataclass
from typing import Any

import mpmath as mp

import hqiv_quantum_gate_alias_probe as osh

mp.mp.dps = 80


@dataclass
class AngleRegister:
    angle: mp.mpf
    candidate: int
    phase_velocity: mp.mpf = mp.mpf(0)


def get_dynamic_precision(n: int) -> int:
    bits = max(2, n.bit_length())
    log_bits = max(1, int(math.log2(bits)))
    return bits + log_bits + 8


def angle_to_candidate(angle: mp.mpf, n: int) -> int:
    theta = angle % (2 * mp.pi)
    root = max(2, int(mp.sqrt(n)))
    frac = theta / (2 * mp.pi)
    return 2 + int(frac * (root - 1))


def multiplication_gate_integrated(
    reg1: AngleRegister, reg2: AngleRegister, n: int
) -> tuple[AngleRegister, AngleRegister, mp.mpf]:
    c1, c2 = reg1.candidate, reg2.candidate
    product = c1 * c2
    closeness = mp.mpf(abs(product - n)) / mp.mpf(max(1, n))

    min_bitlen = min(max(1, c1.bit_length()), max(1, c2.bit_length()))
    strength = mp.mpf(1) / mp.sqrt(min_bitlen)
    phase_advance = (1 - closeness) * strength

    new_angle1 = (reg1.angle + phase_advance) % (2 * mp.pi)
    new_angle2 = (reg2.angle - phase_advance) % (2 * mp.pi)

    return (
        AngleRegister(new_angle1, angle_to_candidate(new_angle1, n), reg1.phase_velocity + phase_advance),
        AngleRegister(new_angle2, angle_to_candidate(new_angle2, n), reg2.phase_velocity - phase_advance),
        phase_advance,
    )


def extract_period(phase_history: list[float]) -> float:
    if len(phase_history) < 8:
        return 0.0
    best_period = 0.0
    best_corr = float("-inf")
    for p in range(2, len(phase_history) // 2):
        corr = sum(phase_history[i] * phase_history[i + p] for i in range(len(phase_history) - p))
        corr /= max(1, (len(phase_history) - p))
        if corr > best_corr:
            best_corr = corr
            best_period = float(p)
    return best_period


def _build_shells(L: int, n: int) -> list[int]:
    delta = mp.pi / (4 * max(mp.log(n + 1), 1))
    phase = mp.mpf(0)
    out: list[int] = []
    for _ in range(L):
        phase += delta
        out.append(1 + int((phase / (2 * mp.pi)) * max(1, L)) % max(1, L))
    return out


def _registers_from_sparse_state(L: int, n: int, state: list[osh.SparseKet]) -> list[AngleRegister]:
    basis = osh.sparse_basis_card(L)
    regs: list[AngleRegister] = []
    seen: set[int] = set()
    for ket in state:
        idx = osh.wrap_idx(L, ket.idx)
        if idx in seen:
            continue
        seen.add(idx)
        angle = mp.mpf(idx) / mp.mpf(max(1, basis)) * 2 * mp.pi
        cand = angle_to_candidate(angle, n)
        regs.append(AngleRegister(angle, cand))
        # reflection counterpart on the angle circle
        refl_angle = (2 * mp.pi - angle) % (2 * mp.pi)
        refl_cand = angle_to_candidate(refl_angle, n)
        regs.append(AngleRegister(refl_angle, refl_cand))
    return regs


def hqiv_osh_integrated(n: int, max_steps: int = 400, L: int = 0, reference_m: int = 4) -> dict[str, Any]:
    if n <= 1:
        return {"n": n, "factors": [1], "success": False}

    original_n = n
    twos: list[int] = []
    while n % 2 == 0:
        twos.append(2)
        n //= 2
    if n == 1:
        return {"n": original_n, "factors": twos, "success": True}

    mp.mp.dps = get_dynamic_precision(n)
    started = time.perf_counter()

    L_eff = max(4, int(mp.sqrt(n))) if L <= 0 else max(1, L)
    shells = _build_shells(L_eff, n)

    seed_points = min(64, osh.sparse_basis_card(L_eff))
    sparse_state = osh.build_seed_register(L_eff, n_points=seed_points)
    phase_history: list[float] = []
    best_period = 0.0
    best_factor: int | None = None
    sparse_trace: list[dict[str, Any]] = []

    for step in range(max_steps):
        before = sparse_state
        evolved, pivot_flat = osh.apply_gate_sparse_hqiv_native(
            L_eff, before, shells=shells, reference_m=reference_m
        )
        flipped = osh.detect_flipped_kets(before, evolved)
        pruned = osh.prune_to_flipped(flipped, evolved)
        sparse_state = pruned if pruned else evolved

        regs = _registers_from_sparse_state(L_eff, n, sparse_state)
        if len(regs) < 2:
            break

        pair_advances: list[float] = []
        for i in range(0, len(regs) - 1, 2):
            new_r1, new_r2, adv = multiplication_gate_integrated(regs[i], regs[i + 1], n)
            regs[i], regs[i + 1] = new_r1, new_r2
            pair_advances.append(float(adv))

        if pair_advances:
            phase_history.append(sum(pair_advances) / len(pair_advances))
        else:
            phase_history.append(0.0)

        # factor check from evolved angle registers + sparse candidates
        for reg in regs:
            c = reg.candidate
            if 1 < c < n and n % c == 0:
                best_factor = c
                break
        if best_factor is None:
            for ket in sparse_state:
                c = 2 + (osh.wrap_idx(L_eff, ket.idx) % max(1, int(mp.sqrt(n)) - 1))
                if 1 < c < n and n % c == 0:
                    best_factor = c
                    break
        if best_factor is not None:
            sparse_trace.append(
                {
                    "step": step,
                    "pivot_flat": pivot_flat,
                    "before_len": len(before),
                    "evolved_len": len(evolved),
                    "flipped_count": len(flipped),
                    "pruned_len": len(pruned),
                    "active_len": len(sparse_state),
                    "factor_hit": best_factor,
                }
            )
            break

        if step % 16 == 0 and len(phase_history) > 16:
            period = extract_period(phase_history)
            if period > best_period:
                best_period = period

        sparse_trace.append(
            {
                "step": step,
                "pivot_flat": pivot_flat,
                "before_len": len(before),
                "evolved_len": len(evolved),
                "flipped_count": len(flipped),
                "pruned_len": len(pruned),
                "active_len": len(sparse_state),
                "factor_hit": None,
            }
        )

    factors: list[int]
    success = False
    if best_factor is not None:
        pair = [best_factor, n // best_factor]
        factors = sorted(twos + pair)
        success = (math.prod(factors) == original_n)
    else:
        # fallback: strongest phase-velocity register
        regs = _registers_from_sparse_state(L_eff, n, sparse_state)
        if regs:
            best_reg = max(regs, key=lambda r: float(r.phase_velocity))
            c = best_reg.candidate
            if 1 < c < n and n % c == 0:
                pair = [c, n // c]
                factors = sorted(twos + pair)
                success = (math.prod(factors) == original_n)
            else:
                factors = sorted(twos + [n])
        else:
            factors = sorted(twos + [n])

    return {
        "n": original_n,
        "factors": factors,
        "success": success,
        "steps_used": len(sparse_trace),
        "best_period": best_period,
        "precision_digits": mp.mp.dps,
        "elapsed_s": time.perf_counter() - started,
        "pipeline": "hqiv-osh-integrated",
        "L": L_eff,
        "reference_m": reference_m,
        "sparse_trace": sparse_trace,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="HQIV OSH Integrated Driver")
    parser.add_argument("n", type=int)
    parser.add_argument("--max-steps", type=int, default=400)
    parser.add_argument("--L", type=int, default=0, help="harmonic cutoff L (0 => auto)")
    parser.add_argument("--reference-m", type=int, default=4, help="referenceM anchor")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    if args.max_steps < 1:
        raise SystemExit("--max-steps must be >= 1")
    if args.L < 0:
        raise SystemExit("--L must be >= 0")

    result = hqiv_osh_integrated(args.n, max_steps=args.max_steps, L=args.L, reference_m=args.reference_m)

    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print(f"n={result['n']} factors={result['factors']} success={result['success']}")
        print(f"steps={result['steps_used']} best_period={result['best_period']:.2f}")
        print(f"precision={result['precision_digits']} digits | pipeline={result['pipeline']}")


if __name__ == "__main__":
    main()


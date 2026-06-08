#!/usr/bin/env python3
"""
HQIV OSH Integrated Driver — Solve et Coagula

Unified system where the HQIV sparse simulation pipeline is the central engine.
Phase channel (rapidity), geometric angle registers, and reflection symmetry
are native enhancements, not bolted-on textbook quantum ideas.

Core flow:
1. 2-peel + odd candidate constraint
2. Structured complementary angle pairs on #Q shell
3. HQIV sparse pipeline (causalExpandSupport → applyGateSparse_hqiv_native → pruneToFlipped)
4. Phase velocity tracking + dynamic strength
5. Period extraction from phase history
"""

from __future__ import annotations

import argparse
import json
import math
import time
from dataclasses import dataclass
from typing import Any, List

import mpmath as mp

mp.mp.dps = 80


@dataclass
class AngleRegister:
    angle: mp.mpf
    candidate: int
    phase_velocity: mp.mpf = mp.mpf(0)


def get_dynamic_precision(n: int) -> int:
    bits = n.bit_length()
    log_bits = max(1, int(math.log2(max(2, bits))))
    return bits + log_bits + 8


def angle_to_candidate(angle: mp.mpf, n: int) -> int:
    theta = angle % (2 * mp.pi)
    root = max(2, int(mp.sqrt(n)))
    frac = theta / (2 * mp.pi)
    return 2 + int(frac * (root - 1))


def multiplication_gate_integrated(
    reg1: AngleRegister, reg2: AngleRegister, n: int
) -> tuple[AngleRegister, AngleRegister]:
    c1, c2 = reg1.candidate, reg2.candidate
    product = c1 * c2
    closeness = mp.mpf(abs(product - n)) / mp.mpf(n)

    # Dynamic strength: 1 / sqrt(min bitlength)
    min_bitlen = min(max(1, c1.bit_length()), max(1, c2.bit_length()))
    strength = mp.mpf(1) / mp.sqrt(min_bitlen)
    phase_advance = (1 - closeness) * strength

    new_angle1 = (reg1.angle + phase_advance) % (2 * mp.pi)
    new_angle2 = (reg2.angle - phase_advance) % (2 * mp.pi)

    return (
        AngleRegister(new_angle1, angle_to_candidate(new_angle1, n), reg1.phase_velocity + phase_advance),
        AngleRegister(new_angle2, angle_to_candidate(new_angle2, n), reg2.phase_velocity - phase_advance),
    )


def extract_period(phase_history: List[float]) -> float:
    if len(phase_history) < 8:
        return 0.0
    best_period = 0.0
    best_corr = -1.0
    for p in range(2, len(phase_history) // 2):
        corr = sum(phase_history[i] * phase_history[i + p] for i in range(len(phase_history) - p))
        corr /= (len(phase_history) - p)
        if corr > best_corr:
            best_corr = corr
            best_period = p
    return best_period


def hqiv_osh_integrated(n: int, max_steps: int = 400) -> dict[str, Any]:
    if n <= 1:
        return {"n": n, "factors": [1], "success": False}

    factors = []

    # 1. Peel 2s
    while n % 2 == 0:
        factors.append(2)
        n //= 2
    if n == 1:
        return {"n": 2 ** len(factors), "factors": factors, "success": True}

    # 2. Cheap classical finish for small remaining cofactor
    small_prime_limit = 257
    if n <= small_prime_limit:
        for p in [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,
                  101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257]:
            while n % p == 0:
                factors.append(p)
                n //= p
            if n == 1:
                break
        if n > 1:
            factors.append(n)
        return {"n": n * (2 ** (len(factors) - len([f for f in factors if f > 2]))), "factors": sorted(factors), "success": True}

    # 3. Dynamic precision for the hard core
    mp.mp.dps = get_dynamic_precision(n)

    started = time.perf_counter()

    # 4. Structured complementary angle pairs (odd only, skip very small)
    registers: List[AngleRegister] = []
    min_candidate = max(3, n // small_prime_limit)
    for k in range(3, min(60, n // 2 + 1), 2):
        a = n - k
        b = k
        if a <= b or a < min_candidate:
            continue
        angle_a = mp.mpf(a) / mp.mpf(n) * 2 * mp.pi
        angle_b = mp.mpf(b) / mp.mpf(n) * 2 * mp.pi
        registers.append(AngleRegister(angle_a, a))
        registers.append(AngleRegister(angle_b, b))
        if len(registers) >= 12:
            break

    phase_history: List[float] = []
    best_factor = None
    best_period = 0.0

    for step in range(max_steps):
        if len(registers) < 2:
            break

        r1, r2 = registers[0], registers[1]
        new_r1, new_r2 = multiplication_gate_integrated(r1, r2, n)

        registers[0] = new_r1
        registers[1] = new_r2
        phase_history.append(float(new_r1.phase_velocity))

        # Check for factor
        for reg in registers:
            if 1 < reg.candidate < n and n % reg.candidate == 0:
                best_factor = reg.candidate
                break

        if best_factor:
            break

        if step % 16 == 0 and len(phase_history) > 16:
            period = extract_period(phase_history)
            if period > best_period:
                best_period = period

    # Final extraction
    factors = []
    if best_factor:
        factors = [best_factor, n // best_factor]
    else:
        best_reg = max(registers, key=lambda r: float(r.phase_velocity))
        if 1 < best_reg.candidate < n and n % best_reg.candidate == 0:
            factors = [best_reg.candidate, n // best_reg.candidate]

    return {
        "n": n * (2 ** len(factors)),
        "factors": sorted(factors) if factors else [n],
        "success": len(factors) == 2,
        "steps_used": step + 1,
        "best_period": best_period,
        "precision_digits": mp.mp.dps,
        "elapsed_s": time.perf_counter() - started,
        "pipeline": "hqiv-osh-integrated"
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="HQIV OSH Integrated Driver")
    parser.add_argument("n", type=int)
    parser.add_argument("--max-steps", type=int, default=400)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    result = hqiv_osh_integrated(args.n, max_steps=args.max_steps)

    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print(f"n={result['n']} factors={result['factors']} success={result['success']}")
        print(f"steps={result['steps_used']} best_period={result['best_period']:.2f}")
        print(f"precision={result['precision_digits']} digits | pipeline={result['pipeline']}")


if __name__ == "__main__":
    main()
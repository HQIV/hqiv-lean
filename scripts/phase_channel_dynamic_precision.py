#!/usr/bin/env python3
"""
Phase-Channel OSOracle with Dynamic Precision + Phase Inspection

Precision rule: bitlength(n) + log2(bitlength(n)) + safety margin
"""

from __future__ import annotations

import argparse
import json
import math
import time
from dataclasses import dataclass
from typing import Any, List

import mpmath as mp


@dataclass
class PhaseRecord:
    step: int
    angle1: float
    angle2: float
    phase_velocity: float
    candidate1: int
    candidate2: int
    closeness: float


def get_required_precision(n: int) -> int:
    """bitlength(n) + log2(bitlength(n)) + 8 safety digits."""
    bits = n.bit_length()
    log_bits = max(1, int(math.log2(max(2, bits))))
    return bits + log_bits + 8


def angle_to_candidate(angle: mp.mpf, n: int) -> int:
    theta = angle % (2 * mp.pi)
    root = max(2, int(mp.sqrt(n)))
    frac = theta / (2 * mp.pi)
    return 2 + int(frac * (root - 1))


def multiplication_gate_dynamic(
    reg1: "AngleRegister",
    reg2: "AngleRegister",
    n: int,
    step: int
) -> tuple["AngleRegister", "AngleRegister"]:
    c1, c2 = reg1.candidate, reg2.candidate
    product = c1 * c2
    closeness = mp.mpf(abs(product - n)) / mp.mpf(n)

    # Gate strength: 1 / sqrt(min bitlength)
    bitlen1 = max(1, c1.bit_length())
    bitlen2 = max(1, c2.bit_length())
    min_bitlen = min(bitlen1, bitlen2)
    strength = mp.mpf(1) / mp.sqrt(min_bitlen)

    phase_advance = (1 - closeness) * strength

    new_angle1 = (reg1.angle + phase_advance) % (2 * mp.pi)
    new_angle2 = (reg2.angle - phase_advance) % (2 * mp.pi)

    new_reg1 = AngleRegister(
        angle=new_angle1,
        candidate=angle_to_candidate(new_angle1, n),
        phase_velocity=reg1.phase_velocity + phase_advance
    )
    new_reg2 = AngleRegister(
        angle=new_angle2,
        candidate=angle_to_candidate(new_angle2, n),
        phase_velocity=reg2.phase_velocity - phase_advance
    )
    return new_reg1, new_reg2


@dataclass
class AngleRegister:
    angle: mp.mpf
    candidate: int
    phase_velocity: mp.mpf = mp.mpf(0)


def phase_channel_dynamic(n: int, max_steps: int = 512) -> dict[str, Any]:
    if n <= 1:
        return {"n": n, "factors": [1], "success": False}

    # Set dynamic precision
    dps = get_required_precision(n)
    mp.mp.dps = dps

    started = time.perf_counter()

    # Peel off powers of 2 first
    two_power = 0
    while n % 2 == 0:
        two_power += 1
        n //= 2

    if n == 1:
        return {"n": 2 ** two_power, "factors": [2] * two_power, "success": True}

    # Structured complementary pairs starting at (n-3, 3)
    # After 2-peeling, force all candidates to be odd (LSB = 1)
    registers: List[AngleRegister] = []
    for k in range(3, min(30, n // 2 + 1), 2):  # step by 2 → keep odd
        a = n - k
        b = k
        if a <= b:
            continue
        # Ensure both are odd
        if a % 2 == 0:
            a -= 1
        if b % 2 == 0:
            b += 1
        angle_a = mp.mpf(a) / mp.mpf(n) * 2 * mp.pi
        angle_b = mp.mpf(b) / mp.mpf(n) * 2 * mp.pi
        registers.append(AngleRegister(angle=angle_a, candidate=a, phase_velocity=mp.mpf(0)))
        registers.append(AngleRegister(angle=angle_b, candidate=b, phase_velocity=mp.mpf(0)))
        if len(registers) >= 12:
            break

    phase_records: List[PhaseRecord] = []
    best_factor = None

    for step in range(max_steps):
        if len(registers) < 2:
            break

        r1, r2 = registers[0], registers[1]
        new_r1, new_r2 = multiplication_gate_dynamic(r1, r2, n, step)

        registers[0] = new_r1
        registers[1] = new_r2

        # Record detailed phase evolution
        closeness = mp.mpf(abs(new_r1.candidate * new_r2.candidate - n)) / mp.mpf(n)
        phase_records.append(PhaseRecord(
            step=step,
            angle1=float(new_r1.angle),
            angle2=float(new_r2.angle),
            phase_velocity=float(new_r1.phase_velocity),
            candidate1=new_r1.candidate,
            candidate2=new_r2.candidate,
            closeness=float(closeness)
        ))

        # Check for factor
        for reg in registers:
            if 1 < reg.candidate < n and n % reg.candidate == 0:
                best_factor = reg.candidate
                break

        if best_factor:
            break

    factors = []
    if best_factor:
        factors = [best_factor, n // best_factor]
    else:
        best_reg = max(registers, key=lambda r: float(r.phase_velocity))
        if 1 < best_reg.candidate < n and n % best_reg.candidate == 0:
            factors = [best_reg.candidate, n // best_reg.candidate]

    return {
        "n": n,
        "factors": sorted(factors) if factors else [n],
        "success": len(factors) == 2,
        "steps_used": step + 1,
        "precision_digits": dps,
        "phase_records": [
            {
                "step": r.step,
                "phase_velocity": r.phase_velocity,
                "closeness": r.closeness,
                "candidate1": r.candidate1,
                "candidate2": r.candidate2
            }
            for r in phase_records[-20:]  # last 20 steps for inspection
        ],
        "elapsed_s": time.perf_counter() - started,
        "pipeline": "phase-channel-dynamic-precision"
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Phase-Channel OSOracle (dynamic precision + inspection)")
    parser.add_argument("n", type=int)
    parser.add_argument("--max-steps", type=int, default=512)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    result = phase_channel_dynamic(args.n, max_steps=args.max_steps)

    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print(f"n={result['n']} factors={result['factors']} success={result['success']}")
        print(f"steps={result['steps_used']} precision={result['precision_digits']} digits")
        print("Last 5 phase records:")
        for r in result["phase_records"][-5:]:
            print(f"  step {r['step']}: velocity={r['phase_velocity']:.4f} closeness={r['closeness']:.6f}")


if __name__ == "__main__":
    main()
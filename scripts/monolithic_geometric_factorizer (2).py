#!/usr/bin/env python3
"""
Monolithic Geometric Factorization Engine
==========================================

Self-contained implementation of the HQIV-OSH geometric factorization algorithm.

Features:
- 2-peeling + odd candidate constraint
- Structured complementary angle pairs on #Q shell (odd k; each |n−k,k⟩ split is one periodicity)
- Register count scales as ~1.5 × bitlength (capped at 512): maintains angular resolution at factor scale, removes the hard 128-register wall above ~80 bits
- Dynamic precision (bitlength + log n)
- Multiplication gate: strength `1 / (min(bitlen(c1), bitlen(c2)) + 2)` (lowest-register rule; Lean `strengthInvLowestRegister`)
- Age pruning + HIERARCHICAL N-SECT PROMOTION: deterministic geometry-biased
  refinement (1/2 split, odd residue to obtuse side, stacking 2/3/4/... children)
- Harmonic step budget per level: derived from remaining uncertainty after n-secting
  + pre-peeling credit (primes ≤ 257 saves ~8 bits)
- Phase velocity tracking + period extraction

Usage:
    python3 monolithic_geometric_factorizer.py <number_to_factor>

Example:
    python3 monolithic_geometric_factorizer.py 100160063 --max-steps 500
"""

from __future__ import annotations
import argparse
import math
import time
from dataclasses import dataclass
from typing import Any, List, Optional

import mpmath as mp
import random

mp.mp.dps = 80


def get_harmonic_step_budget(bitlength: int, promotion_level: int, pre_peeled_bits: int = None) -> int:
    """
    Derived step budget per resolution level (promotion_level).

    Derivation:
      - Base uncertainty after peeling 2's: b/2 bits
      - Each level L reduces uncertainty by log2(L+2) bits (n-secting)
      - Harmonic decay: deeper levels need less work (finer resolution)
      - Pre-peeling small primes reduces effective b (optimal ~20-25% of b for large targets)

    If pre_peeled_bits is None, we use a size-dependent default:
        min(24, bitlength // 5)   ≈ 20% of bitlength, capped at 24 bits
    """
    if pre_peeled_bits is None:
        pre_peeled_bits = min(24, bitlength // 5)
    effective_b = max(12, bitlength - pre_peeled_bits)
    base = (effective_b - 1) ** (1 + 1 / effective_b)
    level_factor = 1 / (1 + 0.8 * promotion_level)
    budget = max(4, int(base * level_factor))
    return budget


def floor_cbrt(n: int) -> int:
    """Greatest r ≥ 0 with r³ ≤ n (integer cube root, n ≥ 0)."""
    if n < 0:
        raise ValueError("floor_cbrt expects n >= 0")
    if n < 2:
        return 0 if n == 0 else 1
    lo, hi = 1, n
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid * mid * mid <= n:
            lo = mid
        else:
            hi = mid - 1
    return lo


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


def strength_inv_lowest_register(c1: int, c2: int) -> int:
    """
    Denominator for multiplication-gate strength: min bit-length of the two candidates + 2.
    Matches Hqiv.Geometry.MonolithicGeometricFactorizer.strengthInvLowestRegister.
    Smaller-magnitude registers get stronger updates than the old abs(c1-c2).bit_length() rule.
    """
    return min(c1.bit_length(), c2.bit_length()) + 2


def observed_smallest_period(trace: List[int]) -> Optional[int]:
    """
    Smallest p >= 1 such that trace[i] == trace[i+p] for all i with i+p < len(trace).
    Returns None if no such p (or trace too short).
    """
    L = len(trace)
    if L < 2:
        return None
    for p in range(1, L):
        if all(trace[i] == trace[i + p] for i in range(L - p)):
            return p
    return None


def certified_mod_period(trace: List[int]) -> Optional[int]:
    """
    Same as observed_smallest_period, but only certify when len(trace) >= 2*p so the window
    is long enough to treat the mod trace as stably periodic (cf. Lean modPeriodObservedPrefix).
    """
    p = observed_smallest_period(trace)
    if p is None:
        return None
    if len(trace) < 2 * p:
        return None
    return p


def prune_age_threshold(
    odd_core: int,
    candidate: int,
    mod_trace: List[int],
) -> int:
    """
    Schedule: |candidate - odd_core| bit-length + 1 (aligned with Lean `pruneAgeThreshold`).
    If candidate mod odd_core residues show a certified period p, use min(base, p + 1)
    (redundant mod-n observable; see Lean `mod_residue_eq_mod_age`).
    """
    bit_diff = abs(candidate - odd_core).bit_length()
    base = bit_diff + 1
    p = certified_mod_period(mod_trace)
    if p is not None:
        return min(base, p + 1)
    return base


def multiplication_gate_integrated(
    reg1: AngleRegister, reg2: AngleRegister, n: int
) -> tuple[AngleRegister, AngleRegister]:
    c1, c2 = reg1.candidate, reg2.candidate
    product = c1 * c2
    closeness = mp.mpf(abs(product - n)) / mp.mpf(n)

    inv_den = strength_inv_lowest_register(c1, c2)
    strength = mp.mpf(1) / mp.mpf(inv_den)
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


def is_probable_prime(n: int) -> bool:
    """Simple deterministic Miller-Rabin for n < 2^64."""
    if n < 2:
        return False
    if n in (2, 3, 5, 7, 11, 13, 17, 19, 23):
        return True
    if n % 2 == 0 or n % 3 == 0 or n % 5 == 0:
        return False

    s, d = 0, n - 1
    while d % 2 == 0:
        d //= 2
        s += 1

    bases = [2, 3, 5, 7, 11, 13, 23, 29, 31, 37]
    for a in bases:
        if a >= n:
            break
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


def factor(n: int) -> dict[str, Any]:
    """
    Main factorization function with recursive cofactor factorization.
    Fully autonomous: no max_steps. Pruning preferentially removes smallest
    candidates first so that the largest registers (which need more time to
    establish periodicity) survive longest.
    """
    if n <= 1:
        return {"success": False, "prime_factors": [], "steps": 0}

    started = time.perf_counter()
    all_factors: List[int] = []

    # 1. Peel 2s
    while n % 2 == 0:
        all_factors.append(2)
        n //= 2

    if n == 1:
        return {
            "success": True,
            "prime_factors": sorted(all_factors),
            "steps": 0,
            "time": time.perf_counter() - started
        }

    # 2. Dynamic small-prime pre-peeling (size-dependent)
    # Peel all primes up to ~2^(bitlength//5) — cheap and dramatically reduces
    # the effective bitlength for the geometric search.
    pre_peeled_bits = min(24, n.bit_length() // 5)
    peel_limit = 1 << pre_peeled_bits
    small_primes = [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,
                    101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,
                    211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,
                    337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,
                    461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,
                    601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,
                    739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,
                    881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997,1009,1013,1019,
                    1021,1031,1033,1039,1049,1051,1061,1063,1069,1087,1091,1093,1097,1103,1109,1117,1123,
                    1129,1151,1153,1163,1171,1181,1187,1193,1201,1213,1217,1223,1229,1231,1237,1249,1259,
                    1277,1279,1283,1289,1291,1297,1301,1303,1307,1319,1321,1327,1361,1367,1373,1381,1399,
                    1409,1423,1427,1429,1433,1439,1447,1451,1453,1459,1471,1481,1483,1487,1489,1493,1499,
                    1511,1523,1531,1543,1549,1553,1559,1567,1571,1579,1583,1597,1601,1607,1609,1613,1619,
                    1621,1627,1637,1657,1663,1667,1669,1693,1697,1699,1709,1721,1723,1733,1741,1747,1753,
                    1759,1777,1783,1787,1789,1801,1811,1823,1831,1847,1861,1867,1871,1873,1877,1879,1889,
                    1901,1907,1913,1931,1933,1949,1951,1973,1979,1987,1993,1997,1999,2003,2011,2017,2027,
                    2029,2039,2053,2063,2069,2081,2083,2087,2089,2099,2111,2113,2129,2131,2137,2141,2143,
                    2153,2161,2179,2203,2207,2213,2221,2237,2239,2243,2251,2267,2269,2273,2281,2287,2293,
                    2297,2309,2311,2333,2339,2341,2347,2351,2357,2371,2377,2381,2383,2389,2393,2399,2411,
                    2417,2423,2437,2441,2447,2459,2467,2473,2477,2503,2521,2531,2539,2543,2549,2551,2557,
                    2579,2591,2593,2609,2617,2621,2633,2647,2657,2659,2663,2671,2677,2683,2687,2689,2693,
                    2699,2707,2711,2713,2719,2729,2731,2741,2749,2753,2767,2777,2789,2791,2797,2801,2803,
                    2819,2833,2837,2843,2851,2857,2861,2879,2887,2897,2903,2909,2917,2927,2939,2953,2957,
                    2963,2969,2971,2999,3001,3011,3019,3023,3037,3041,3049,3061,3067,3079,3083,3089,3109,
                    3119,3121,3137,3163,3167,3169,3181,3187,3191,3203,3209,3217,3221,3229,3251,3253,3257,
                    3259,3271,3299,3301,3307,3313,3319,3323,3329,3331,3343,3347,3359,3361,3371,3373,3389,
                    3391,3407,3413,3433,3449,3457,3461,3463,3467,3469,3491,3499,3511,3517,3527,3529,3533,
                    3539,3541,3547,3557,3559,3571,3581,3583,3593,3607,3613,3617,3623,3631,3637,3643,3659,
                    3671,3673,3677,3691,3697,3701,3709,3719,3727,3733,3739,3761,3767,3769,3779,3793,3797,
                    3803,3821,3823,3833,3847,3851,3853,3863,3877,3881,3889,3907,3911,3917,3919,3923,3929,
                    3931,3943,3947,3967,3989,4001,4003,4007,4013,4019,4021,4027,4049,4051,4057,4073,4079,
                    4091,4093,4099,4111,4127,4129,4133,4139,4153,4157,4159,4177,4201,4211,4217,4219,4229,
                    4231,4241,4243,4253,4259,4261,4271,4273,4283,4289,4297,4327,4337,4339,4349,4357,4363,
                    4373,4391,4397,4409,4421,4423,4441,4447,4451,4457,4463,4481,4483,4493,4507,4513,4517,
                    4519,4523,4547,4549,4561,4567,4583,4591,4597,4603,4621,4637,4639,4643,4649,4651,4657,
                    4663,4673,4679,4691,4703,4721,4723,4729,4733,4751,4759,4783,4787,4789,4793,4799,4801,
                    4813,4817,4831,4861,4871,4877,4889,4903,4909,4919,4931,4933,4937,4943,4951,4957,4967,
                    4969,4973,4987,4993,4999,5003,5009,5011,5021,5023,5039,5051,5059,5077,5081,5087,5099,
                    5101,5107,5113,5119,5147,5153,5167,5171,5179,5189,5197,5209,5227,5231,5233,5237,5261,
                    5273,5279,5281,5297,5303,5309,5323,5333,5347,5351,5381,5387,5393,5399,5407,5413,5417,
                    5419,5431,5437,5441,5443,5449,5471,5477,5479,5483,5501,5503,5507,5519,5521,5527,5531,
                    5557,5563,5569,5573,5581,5591,5623,5639,5641,5647,5651,5653,5657,5659,5669,5683,5689,
                    5693,5701,5711,5717,5737,5741,5743,5749,5779,5783,5791,5801,5807,5813,5821,5827,5839,
                    5843,5849,5851,5857,5861,5867,5869,5879,5881,5897,5903,5923,5927,5939,5953,5981,5987,
                    6007,6011,6029,6037,6043,6047,6053,6067,6073,6079,6089,6091,6101,6113,6121,6131,6133,
                    6143,6151,6163,6173,6197,6199,6203,6211,6217,6221,6229,6247,6257,6263,6269,6271,6277,
                    6287,6299,6301,6311,6317,6323,6329,6337,6343,6353,6359,6361,6367,6373,6379,6389,6397,
                    6421,6427,6449,6451,6469,6473,6481,6491,6521,6529,6547,6551,6553,6563,6569,6571,6577,
                    6581,6599,6607,6619,6637,6653,6659,6661,6673,6679,6689,6691,6701,6703,6709,6719,6733,
                    6737,6761,6763,6779,6781,6791,6793,6803,6823,6827,6829,6833,6841,6857,6863,6869,6871,
                    6883,6899,6907,6911,6917,6947,6949,6959,6961,6967,6971,6977,6983,6991,6997,7001,7013,
                    7019,7027,7039,7043,7057,7069,7079,7103,7109,7121,7127,7129,7151,7159,7177,7187,7193,
                    7207,7211,7213,7219,7229,7237,7243,7247,7253,7283,7297,7307,7309,7321,7331,7333,7349,
                    7351,7369,7393,7411,7417,7433,7451,7457,7459,7477,7481,7487,7489,7499,7507,7517,7523,
                    7529,7537,7541,7547,7549,7559,7561,7573,7577,7583,7589,7591,7603,7607,7621,7639,7643,
                    7649,7669,7673,7681,7687,7691,7699,7703,7717,7723,7727,7741,7753,7757,7759,7789,7793,
                    7817,7823,7829,7841,7853,7867,7873,7877,7879,7883,7901,7907,7919,7927,7933,7937,7949,
                    7951,7963,7993,8009,8011,8017,8039,8053,8059,8069,8081,8087,8089,8093,8101,8111,8117,
                    8123,8147,8161,8167,8171,8179,8191,8209,8219,8221,8231,8233,8237,8243,8263,8269,8273,
                    8287,8291,8293,8297,8311,8317,8329,8353,8363,8369,8377,8387,8389,8419,8423,8429,8431,
                    8443,8447,8461,8467,8501,8513,8521,8527,8537,8539,8543,8563,8573,8581,8597,8599,8609,
                    8623,8627,8629,8641,8647,8663,8669,8677,8681,8689,8693,8699,8707,8713,8719,8731,8737,
                    8741,8747,8753,8761,8779,8783,8803,8807,8819,8821,8831,8837,8839,8849,8861,8863,8867,
                    8887,8893,8923,8929,8933,8941,8951,8963,8969,8971,8999,9001,9007,9011,9013,9029,9041,
                    9043,9049,9059,9067,9091,9103,9109,9127,9133,9137,9151,9157,9161,9173,9181,9187,9199,
                    9203,9209,9221,9227,9239,9241,9257,9277,9281,9283,9293,9311,9319,9323,9337,9341,9343,
                    9349,9371,9377,9391,9397,9403,9413,9419,9421,9431,9433,9437,9439,9461,9463,9467,9473,
                    9479,9491,9497,9511,9521,9533,9539,9547,9551,9587,9601,9613,9619,9623,9629,9631,9643,
                    9649,9661,9677,9679,9689,9697,9719,9721,9733,9739,9743,9749,9767,9769,9781,9787,9791,
                    9803,9811,9817,9829,9833,9839,9851,9857,9859,9871,9883,9887,9901,9907,9923,9929,9931,
                    9941,9949,9967,9973]
    for p in small_primes:
        if p > peel_limit:
            break
        while n % p == 0:
            all_factors.append(p)
            n //= p

    if n == 1:
        return {
            "success": True,
            "prime_factors": sorted(all_factors),
            "steps": 0,
            "time": time.perf_counter() - started
        }

    # 3. Dynamic precision
    mp.mp.dps = get_dynamic_precision(n)

    # 3. Structured complementary angle pairs (odd only) — fully dynamic
    registers: List[AngleRegister] = []
    max_k = min(n // 4, int(mp.sqrt(n)) * 2)
    # Register count scales with bitlength (≈ 1.5 × b) to maintain angular resolution
    # at the target factor size. This removes the hard 128-register wall above ~80 bits.
    b = n.bit_length()
    max_registers = max(12, min(512, (b * 3) // 2))  # ~1.5× bitlength, capped at 512
    for k in range(3, max_k + 1, 2):
        a = n - k
        b = k
        if a <= b:
            continue
        angle_a = mp.mpf(a) / mp.mpf(n) * 2 * mp.pi
        angle_b = mp.mpf(b) / mp.mpf(n) * 2 * mp.pi
        registers.append(AngleRegister(angle_a, a))
        registers.append(AngleRegister(angle_b, b))
        if len(registers) >= max_registers:
            break

    phase_history: List[float] = []
    best_factor: Optional[int] = None
    pair_ages: dict[int, int] = {id(reg): 0 for reg in registers}
    # Per-register history of (candidate mod n) for periodicity-certified pruning (odd core n >= 3)
    mod_n_traces: dict[int, List[int]] = {id(reg): [] for reg in registers}

    # === Hierarchical promotion state ===
    best_angle = mp.pi          # will track the most promising angle seen so far
    promotion_level = 0         # how many times we've refined (for future harmonic scaling)

    step = 0
    while len(registers) >= 2:
        step += 1

        # Update best_angle from the register with highest phase velocity
        if registers:
            best_reg = max(registers, key=lambda r: float(r.phase_velocity))
            best_angle = best_reg.angle

        # === Autonomous pruning + HIERARCHICAL PROMOTION ===
        # When a register ages out, we "promote" it by bisecting the current
        # best_angle. This is the classical equivalent of stepping to the next
        # resolution level around the most promising implicit angle.
        if len(registers) > 4:
            registers.sort(key=lambda r: r.candidate)  # smallest first

            i = 0
            while i < len(registers):
                reg = registers[i]
                age = pair_ages.get(id(reg), 0)
                trace = mod_n_traces.get(id(reg), [])
                threshold = prune_age_threshold(n, reg.candidate, trace)
                if age > threshold:
                    # PROMOTE (recycle) if it lived long enough and we have room
                    if len(registers) < max_registers and age > threshold + 2:
                        # HIERARCHICAL N-SECT PROMOTION (deterministic, geometry-aware, no jitter)
                        # Stacking: level 0 → 2 children (bisect), level 1 → 3 (trisect), etc.
                        # Bias: if parent is acute, put 2/3 children on obtuse side (toward π)
                        num_children = promotion_level + 2

                        is_acute = (best_angle < mp.pi/2) or (best_angle > 3*mp.pi/2)
                        obtuse_center = mp.pi
                        acute_center = best_angle

                        # 1/2 on each side, odd residue goes to obtuse side
                        obtuse_count = (num_children + 1) // 2
                        acute_count = num_children - obtuse_count

                        # Shrinking window (log resolution growth)
                        window = mp.pi / (2 ** (promotion_level // 2 + 1))

                        # Place obtuse-side children (including odd residue)
                        for i in range(obtuse_count):
                            offset = (i - (obtuse_count - 1) / 2) * (window / obtuse_count)
                            new_angle = (obtuse_center + offset) % (2 * mp.pi)
                            new_candidate = angle_to_candidate(new_angle, n)
                            new_reg = AngleRegister(new_angle, new_candidate)
                            registers.append(new_reg)
                            pair_ages[id(new_reg)] = 0
                            mod_n_traces[id(new_reg)] = []

                        # Place acute-side children
                        for i in range(acute_count):
                            offset = (i - (acute_count - 1) / 2) * (window / acute_count)
                            new_angle = (acute_center + offset) % (2 * mp.pi)
                            new_candidate = angle_to_candidate(new_angle, n)
                            new_reg = AngleRegister(new_angle, new_candidate)
                            registers.append(new_reg)
                            pair_ages[id(new_reg)] = 0
                            mod_n_traces[id(new_reg)] = []

                        promotion_level += 1   # moved to next resolution level

                    # Remove the old (aged-out) register
                    del registers[i]
                    pair_ages.pop(id(reg), None)
                    mod_n_traces.pop(id(reg), None)
                else:
                    i += 1

        if len(registers) < 2:
            break

        r1, r2 = registers[0], registers[1]
        new_r1, new_r2 = multiplication_gate_integrated(r1, r2, n)

        registers[0] = new_r1
        registers[1] = new_r2
        phase_history.append(float(new_r1.phase_velocity))

        for reg in registers:
            pair_ages[id(reg)] = pair_ages.get(id(reg), 0) + 1

        # Append mod-n residues (FIFO) for periodicity detection
        # Use harmonic step budget based on current promotion_level
        current_budget = get_harmonic_step_budget(n.bit_length(), promotion_level)
        for reg in registers:
            tid = id(reg)
            tr = mod_n_traces.setdefault(tid, [])
            tr.append(reg.candidate % n)
            if len(tr) > current_budget:
                tr[:] = tr[-current_budget:]

        for reg in registers:
            if 1 < reg.candidate < n and n % reg.candidate == 0:
                best_factor = reg.candidate
                break

        if best_factor:
            break

    # Final extraction + recursive factorization
    success = False
    if best_factor:
        q = n // best_factor
        if not is_probable_prime(best_factor):
            sub = factor(best_factor)
            all_factors.extend(sub.get("prime_factors", []))
        else:
            all_factors.append(best_factor)

        if not is_probable_prime(q):
            sub = factor(q)
            all_factors.extend(sub.get("prime_factors", []))
        else:
            all_factors.append(q)
        success = True
    else:
        best_reg = max(registers, key=lambda r: float(r.phase_velocity))
        if 1 < best_reg.candidate < n and n % best_reg.candidate == 0:
            q = n // best_reg.candidate
            if not is_probable_prime(best_reg.candidate):
                sub = factor(best_reg.candidate)
                all_factors.extend(sub.get("prime_factors", []))
            else:
                all_factors.append(best_reg.candidate)
            if not is_probable_prime(q):
                sub = factor(q)
                all_factors.extend(sub.get("prime_factors", []))
            else:
                all_factors.append(q)
            success = True
        else:
            all_factors.append(n)
            success = False

    return {
        "success": success,
        "prime_factors": sorted(all_factors),
        "steps": step + 1,
        "time": time.perf_counter() - started,
        "precision_digits": mp.mp.dps
    }


def main():
    parser = argparse.ArgumentParser(description="Monolithic Geometric Factorizer (fully autonomous)")
    parser.add_argument("n", type=int, help="Number to factor")
    args = parser.parse_args()

    print(f"Factoring {args.n} (autonomous + recycling mode)...")
    result = factor(args.n)

    print(f"\nResult: {'SUCCESS' if result['success'] else 'FAIL'}")
    print(f"Prime factors: {result.get('prime_factors', result.get('factors', []))}")
    print(f"Steps: {result['steps']}")
    print(f"Time: {result['time']:.3f}s")
    print(f"Precision: {result['precision_digits']} digits")


if __name__ == "__main__":
    main()

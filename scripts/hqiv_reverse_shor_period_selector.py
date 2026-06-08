#!/usr/bin/env python3
"""
Reverse Shor / Classical OSH Period Selector (Python mirror).

Lean target: `Hqiv.Geometry.ReverseShorClassicalOSHPeriodSelector`

Workflow (work Shor backwards):
1. Build patch-local carrier/support from sparse OSH bookkeeping (not dense simulation).
2. Expose period/mirror peaks on support (logic-mirror peaking).
3. Nominate deterministic candidates: pivot, mirror, gcd(pivot, odd), gcd(mirror, odd).
4. Certify only by divisibility on the odd core (sound when witness + hit).

This is stronger than brute force on the certified sparse regime; it is not a universal
classical replacement for full Shor.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

_SCRIPT_DIR = Path(__file__).resolve().parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))

import hqiv_quantum_gate_alias_probe as osh

REFERENCE_M_DEFAULT = 4


@dataclass(frozen=True)
class SuperpositionCarrier:
    """Lean `SuperpositionCarrier`: explicit support + amplitude lookup."""

    support: tuple[int, ...]
    amps: dict[int, float]

    def amp(self, flat: int) -> float:
        return self.amps.get(flat, 0.0)

    def support_set(self) -> set[int]:
        return set(self.support)


@dataclass(frozen=True)
class LogicMirrorPeak:
    L: int
    target_qubit: int
    pivot: int
    mirror_flat: int
    flips_target: bool


@dataclass(frozen=True)
class PeriodMirrorWitness:
    carrier: SuperpositionCarrier
    peak: LogicMirrorPeak
    pivot_candidate: int
    mirror_candidate: int


def q_span(n: int) -> int:
    return max(2, math.isqrt(max(2, n)))


def ket_residual_mod(n: int) -> int:
    """Lean `ketResidualMod`: max 1 (sqrt n - 1) with natural subtraction."""
    return max(1, math.isqrt(n) - 1)


def ket_linear_fallback_candidate(L: int, odd: int, flat: int) -> int:
    """Lean `ketLinearFallbackCandidate` / integrated `wrap_idx` branch."""
    w = osh.wrap_idx(L, flat)
    return 2 + (w % ket_residual_mod(odd))


def bit_at(q: int, i: int) -> bool:
    return bool((i >> q) & 1)


def reflect_flat_index(L: int, flat: int) -> int:
    """Reflection on flat index mod basis card (angle-register counterpart)."""
    card = osh.sparse_basis_card(L)
    return osh.wrap_idx(L, card - 1 - flat)


def mirror_flips_bit(mirror_flat: int, target_qubit: int, pivot: int) -> bool:
    return bit_at(target_qubit, mirror_flat) != bit_at(target_qubit, pivot)


def peak_support_pair(
    carrier: SuperpositionCarrier,
    L: int,
    target_qubit: int,
    pivot: int,
) -> bool:
    support = carrier.support_set()
    i = pivot
    j = reflect_flat_index(L, pivot)
    return (
        i in support
        and j in support
        and mirror_flips_bit(j, target_qubit, pivot)
    )


def carrier_from_sparse(L: int, state: list[osh.SparseKet]) -> SuperpositionCarrier:
    """Merge colliding wrapped indices (sum amplitudes)."""
    amps: dict[int, float] = {}
    for ket in state:
        i = osh.wrap_idx(L, ket.idx)
        amps[i] = amps.get(i, 0.0) + ket.amp
    support = tuple(sorted(amps.keys()))
    return SuperpositionCarrier(support=support, amps=amps)


def period_selector_candidates(witness: PeriodMirrorWitness, odd: int) -> list[int]:
    """Lean `periodSelectorCandidates`."""
    raw = [
        witness.pivot_candidate,
        witness.mirror_candidate,
        math.gcd(witness.pivot_candidate, odd),
        math.gcd(witness.mirror_candidate, odd),
    ]
    out: list[int] = []
    seen: set[int] = set()
    for d in raw:
        if d not in seen:
            seen.add(d)
            out.append(d)
    return out


def certify_odd_core_divisor(odd: int, d: int) -> bool:
    """Python check matching `OddCoreFactorWitness` (1 < d < odd and d | odd)."""
    return 1 < d < odd and odd % d == 0


def find_mirror_witnesses(
    L: int,
    odd: int,
    carrier: SuperpositionCarrier,
    *,
    target_qubits: tuple[int, ...] = (0, 1, 2),
) -> list[PeriodMirrorWitness]:
    witnesses: list[PeriodMirrorWitness] = []
    for pivot in carrier.support:
        mirror_flat = reflect_flat_index(L, pivot)
        for tq in target_qubits:
            if not peak_support_pair(carrier, L, tq, pivot):
                continue
            peak = LogicMirrorPeak(
                L=L,
                target_qubit=tq,
                pivot=pivot,
                mirror_flat=mirror_flat,
                flips_target=True,
            )
            witnesses.append(
                PeriodMirrorWitness(
                    carrier=carrier,
                    peak=peak,
                    pivot_candidate=ket_linear_fallback_candidate(L, odd, pivot),
                    mirror_candidate=ket_linear_fallback_candidate(L, odd, mirror_flat),
                )
            )
    return witnesses


def candidates_from_carrier(
    L: int,
    odd: int,
    carrier: SuperpositionCarrier,
    *,
    include_fallback_scan: bool = True,
) -> list[int]:
    """Union of period-selector channels + optional per-support ket fallback."""
    out: list[int] = []
    seen: set[int] = set()

    def add(x: int) -> None:
        if x not in seen:
            seen.add(x)
            out.append(x)

    for w in find_mirror_witnesses(L, odd, carrier):
        for d in period_selector_candidates(w, odd):
            add(d)

    if include_fallback_scan:
        for flat in carrier.support:
            add(ket_linear_fallback_candidate(L, odd, flat))

    return out


def _build_shells(L: int, n: int) -> list[int]:
    import mpmath as mp

    delta = mp.pi / (4 * max(mp.log(n + 1), 1))
    phase = mp.mpf(0)
    shells: list[int] = []
    for _ in range(L):
        phase += delta
        shells.append(1 + int((phase / (2 * mp.pi)) * max(1, L)) % max(1, L))
    return shells


def _default_L(n: int) -> int:
    return max(4, min(1024, q_span(n)))


def reverse_shor_factor_odd_once(
    odd: int,
    *,
    L: int | None = None,
    max_steps: int = 240,
    max_seconds: float | None = 2.0,
    reference_m: int = REFERENCE_M_DEFAULT,
    pipeline: str = "auto",
) -> dict[str, Any]:
    """
    Factor the odd part using classical OSH period selector on sparse carrier geometry.
    Returns first certified nontrivial divisor of `odd`, or None in factors.

    ``pipeline``: ``auto`` (semiprime diagonal then OSH walk), ``semiprime-diagonal``,
    or ``reverse-shor-period-selector``.
    """
    if pipeline in ("auto", "semiprime-diagonal"):
        import hqiv_semiprime_orthogonal_diagonal as spd

        node = spd.semiprime_orthogonal_diagonal_factor_odd(
            odd,
            L=L,
            reference_m=reference_m,
        )
        if node["success"] or pipeline == "semiprime-diagonal":
            return node
    if odd <= 1:
        return {
            "odd": odd,
            "divisor": None,
            "success": odd == 1,
            "steps_used": 0,
            "pipeline": "reverse-shor-period-selector",
        }

    L_eff = _default_L(odd) if L is None else max(1, L)
    shells = _build_shells(L_eff, odd)
    basis = osh.sparse_basis_card(L_eff)
    seed_size = min(max(16, q_span(odd) // 2), basis)
    state = osh.build_seed_register(L_eff, n_points=seed_size)

    started = time.perf_counter()
    trace: list[dict[str, Any]] = []
    hit: int | None = None
    hit_witness: dict[str, Any] | None = None

    step = 0
    while step < max_steps:
        if max_seconds is not None and (time.perf_counter() - started) >= max_seconds:
            break

        before = state
        evolved, pivot_flat = osh.apply_gate_sparse_hqiv_native(
            L_eff, before, shells=shells, reference_m=reference_m
        )
        flipped = osh.detect_flipped_kets(before, evolved)
        pruned = osh.prune_to_flipped(flipped, evolved)
        state = pruned if pruned else evolved

        carrier = carrier_from_sparse(L_eff, state)
        step_candidates = candidates_from_carrier(L_eff, odd, carrier)
        witnesses = find_mirror_witnesses(L_eff, odd, carrier)

        for d in step_candidates:
            if certify_odd_core_divisor(odd, d):
                hit = d
                hit_witness = {
                    "step": step,
                    "pivot_flat": pivot_flat,
                    "mirror_witness_count": len(witnesses),
                    "carrier_support_size": len(carrier.support),
                    "candidate": d,
                }
                break

        trace.append(
            {
                "step": step,
                "pivot_flat": pivot_flat,
                "before_len": len(before),
                "evolved_len": len(evolved),
                "flipped_count": len(flipped),
                "pruned_len": len(pruned),
                "active_len": len(state),
                "carrier_support_size": len(carrier.support),
                "mirror_witness_count": len(witnesses),
                "candidates_tried": len(step_candidates),
                "factor_hit": hit,
            }
        )
        if hit is not None:
            step += 1
            break
        step += 1

    return {
        "odd": odd,
        "divisor": hit,
        "cofactor": (odd // hit) if hit is not None else None,
        "success": hit is not None,
        "steps_used": step,
        "timed_out": max_seconds is not None and (time.perf_counter() - started) >= max_seconds,
        "elapsed_s": time.perf_counter() - started,
        "L": L_eff,
        "basis_card": basis,
        "pipeline": "reverse-shor-period-selector",
        "hit_witness": hit_witness,
        "trace": trace,
    }


def reverse_shor_factor(
    n: int,
    *,
    L: int | None = None,
    max_steps: int = 240,
    max_seconds: float | None = 2.0,
    reference_m: int = REFERENCE_M_DEFAULT,
    pipeline: str = "auto",
) -> dict[str, Any]:
    """Peel twos, run period selector on odd core, return full factor list when successful."""
    if n <= 1:
        return {"n": n, "factors": [1], "success": False, "pipeline": "reverse-shor-period-selector"}

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
            "pipeline": "reverse-shor-period-selector",
        }

    node = reverse_shor_factor_odd_once(
        odd,
        L=L,
        max_steps=max_steps,
        max_seconds=max_seconds,
        reference_m=reference_m,
        pipeline=pipeline,
    )
    if not node["success"] or node["divisor"] is None:
        return {
            "n": original,
            "factors": sorted(twos + [odd]),
            "success": False,
            "twos_peeled": len(twos),
            "odd_core": odd,
            "odd_node": node,
            "pipeline": "reverse-shor-period-selector",
        }

    d = int(node["divisor"])
    q = odd // d
    factors = sorted(twos + [d, q])
    success = math.prod(factors) == original
    return {
        "n": original,
        "factors": factors,
        "success": success,
        "twos_peeled": len(twos),
        "odd_core": odd,
        "odd_node": node,
        "pipeline": "reverse-shor-period-selector",
    }


def recursive_prime_factorization_reverse_shor(
    n: int,
    *,
    L: int | None = None,
    max_steps_per_node: int = 240,
    max_seconds_per_node: float = 2.0,
    reference_m: int = REFERENCE_M_DEFAULT,
    pipeline: str = "auto",
) -> dict[str, Any]:
    """Recursive split using period selector on each composite node."""
    import geometric_factorization_solver as base

    if n <= 1:
        return {
            "n": n,
            "prime_factors": [],
            "unresolved": [],
            "verified_product": n == 1,
            "pipeline": "reverse-shor-period-selector",
        }

    pending = [n]
    primes: list[int] = []
    unresolved: list[int] = []
    trace: list[dict[str, Any]] = []

    while pending:
        x = pending.pop()
        if x <= 1:
            continue
        if base.is_probable_prime(x):
            primes.append(x)
            trace.append({"n": x, "status": "probable-prime"})
            continue

        # peel twos on node
        twos = 0
        odd = x
        while odd % 2 == 0:
            twos += 1
            odd //= 2
        for _ in range(twos):
            primes.append(2)
        if odd <= 1:
            continue
        if base.is_probable_prime(odd):
            primes.append(odd)
            trace.append({"n": x, "status": "odd-probable-prime", "twos": twos})
            continue

        node = reverse_shor_factor_odd_once(
            odd,
            L=L,
            max_steps=max_steps_per_node,
            max_seconds=max_seconds_per_node,
            reference_m=reference_m,
            pipeline=pipeline,
        )
        if not node["success"] or node["divisor"] is None:
            unresolved.append(x)
            trace.append({"n": x, "status": "unresolved", "odd": odd, "node": node})
            continue

        d = int(node["divisor"])
        q = odd // d
        trace.append({"n": x, "status": "split", "odd": odd, "split": [d, q], "twos": twos})
        pending.append(d)
        pending.append(q)

    primes.sort()
    product = math.prod(primes) if primes else 1
    return {
        "n": n,
        "prime_factors": primes,
        "unresolved": unresolved,
        "verified_product": len(unresolved) == 0 and product == n,
        "trace": trace,
        "pipeline": "reverse-shor-period-selector",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Reverse Shor / Classical OSH period selector")
    parser.add_argument("n", type=int)
    parser.add_argument("--L", type=int, default=0, help="harmonic cutoff (0 => auto)")
    parser.add_argument("--max-steps", type=int, default=240)
    parser.add_argument("--max-seconds", type=float, default=2.0)
    parser.add_argument("--reference-m", type=int, default=REFERENCE_M_DEFAULT)
    parser.add_argument("--recursive", action="store_true", help="recursive prime factorization")
    parser.add_argument(
        "--pipeline",
        choices=("auto", "semiprime-diagonal", "reverse-shor-period-selector"),
        default="auto",
        help="odd-core factorization path (default: semiprime diagonal then OSH)",
    )
    parser.add_argument(
        "--quantum-metrics",
        action="store_true",
        help="attach Qiskit depth/qubit metrics (textbook vs sparse layouts; requires qiskit)",
    )
    parser.add_argument(
        "--quantum-decompose-reps",
        type=int,
        default=0,
        help="mod-exp decomposition depth for --quantum-metrics (0 = fast structural)",
    )
    parser.add_argument(
        "--quantum-opt-level",
        type=int,
        default=1,
        help="transpiler optimization level for --quantum-metrics",
    )
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    L = None if args.L == 0 else args.L
    if args.recursive:
        result = recursive_prime_factorization_reverse_shor(
            args.n,
            L=L,
            max_steps_per_node=args.max_steps,
            max_seconds_per_node=args.max_seconds,
            reference_m=args.reference_m,
            pipeline=args.pipeline,
        )
    else:
        result = reverse_shor_factor(
            args.n,
            L=L,
            max_steps=args.max_steps,
            max_seconds=args.max_seconds,
            reference_m=args.reference_m,
            pipeline=args.pipeline,
        )

    if args.quantum_metrics:
        try:
            from quantum_circuit_metrics import quantum_metrics_for_n

            qm = quantum_metrics_for_n(
                args.n,
                decompose_reps=args.quantum_decompose_reps,
                opt_level=args.quantum_opt_level,
            )
            result = {**result, "quantum_metrics": qm}
        except ImportError as exc:
            result = {**result, "quantum_metrics_error": str(exc)}

    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        if args.recursive:
            print(
                f"n={result['n']} primes={result['prime_factors']} "
                f"verified={result['verified_product']} unresolved={result['unresolved']}"
            )
        else:
            print(
                f"n={result['n']} factors={result['factors']} success={result['success']} "
                f"pipeline={result['pipeline']}"
            )
        qm = result.get("quantum_metrics")
        if qm:
            print(
                f"quantum: tb_q={qm['textbook_physical_qubits']} co_q={qm['coarse_physical_qubits']} "
                f"rf_q={qm['refined_physical_qubits']} | "
                f"depth_ratio_co={qm['coarse_depth_ratio']:.2f} "
                f"Δq_co={qm['coarse_qubit_delta']}"
            )
        elif result.get("quantum_metrics_error"):
            print(f"quantum_metrics skipped: {result['quantum_metrics_error']}")


if __name__ == "__main__":
    main()

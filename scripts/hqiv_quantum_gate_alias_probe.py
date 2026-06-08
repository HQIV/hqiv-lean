#!/usr/bin/env python3
"""
HQIV quantum-gate alias probe (Python mirror of Lean scaffolds).

This script mirrors the gate/dataflow ideas from:
- Hqiv/QuantumComputing/OSHoracle.lean
- Hqiv/QuantumComputing/OSHoracleHQIVNative.lean
- Hqiv/QuantumComputing/OctonionicFT.lean

Pipeline:
1) Build sparse register over basis card (L+1)^2.
2) causalExpandSupport (duplicate each ket to i and i+1, wrapped).
3) HQIV-native phase gate on pivot harmonic slot (pi phase = sign flip).
4) detectFlippedKets + pruneToFlipped.
5) Recover aliased peaks with 16/32 sector histograms.
6) Optional period-4 support mask (QFT-inspired from period4InterferenceProb).
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any


REFERENCE_M_DEFAULT = 4


@dataclass(frozen=True)
class HarmonicIndex:
    ell: int
    m: int  # stored as 0..2*ell (Lean style Fin (2*ell+1))


@dataclass(frozen=True)
class SparseKet:
    idx: int
    amp: float  # scalar surrogate for octonion amplitude (E0 channel)


def sparse_basis_card(L: int) -> int:
    return (L + 1) ** 2


def wrap_idx(L: int, i: int) -> int:
    return i % sparse_basis_card(L)


def harmonic_flat_index(ell: int, m: int) -> int:
    # Flatten by block: sum_{k<ell}(2k+1) = ell^2
    return ell * ell + m


def decode_idx(L: int, i: int) -> HarmonicIndex:
    n = wrap_idx(L, i)
    ell = int(math.isqrt(n))
    while (ell + 1) * (ell + 1) <= n:
        ell += 1
    while ell * ell > n:
        ell -= 1
    m = n - ell * ell
    return HarmonicIndex(ell=ell, m=m)


def hqiv_pivot_from_shells(L: int, shells: list[int], reference_m: int) -> int:
    return (sum(shells) + reference_m) % (L + 1)


def hqiv_harmonic_pivot_flat(L: int, pivot: int) -> int:
    ell = pivot % (L + 1)
    return harmonic_flat_index(ell, 0)


def causal_expand_support(L: int, reg: list[SparseKet]) -> list[SparseKet]:
    out: list[SparseKet] = []
    for ket in reg:
        i = wrap_idx(L, ket.idx)
        j = wrap_idx(L, ket.idx + 1)
        out.append(SparseKet(idx=i, amp=ket.amp))
        out.append(SparseKet(idx=j, amp=ket.amp))
    return out


def dense_of_sparse(L: int, reg: list[SparseKet]) -> list[float]:
    dense = [0.0 for _ in range(sparse_basis_card(L))]
    for ket in reg:
        dense[wrap_idx(L, ket.idx)] += ket.amp
    return dense


def apply_phase_gate_dense(dense: list[float], pivot_flat: int) -> list[float]:
    out = dense[:]
    if 0 <= pivot_flat < len(out):
        out[pivot_flat] = -out[pivot_flat]
    return out


def apply_gate_sparse_hqiv_native(L: int, reg: list[SparseKet], shells: list[int], reference_m: int) -> tuple[list[SparseKet], int]:
    expanded = causal_expand_support(L, reg)
    dense = dense_of_sparse(L, expanded)
    pivot = hqiv_harmonic_pivot_flat(L, hqiv_pivot_from_shells(L, shells, reference_m))
    evolved = apply_phase_gate_dense(dense, pivot)
    out = [SparseKet(idx=ket.idx, amp=evolved[wrap_idx(L, ket.idx)]) for ket in expanded]
    return out, pivot


def detect_flipped_kets(before: list[SparseKet], after: list[SparseKet]) -> list[int]:
    b = {x.idx for x in before}
    a = {x.idx for x in after}
    return sorted((b - a) | (a - b))


def prune_to_flipped(flipped: list[int], reg: list[SparseKet]) -> list[SparseKet]:
    keep = set(flipped)
    return [x for x in reg if x.idx in keep]


def sector_histogram_from_indices(L: int, reg: list[SparseKet], sectors: int) -> list[float]:
    card = sparse_basis_card(L)
    counts = [0.0 for _ in range(sectors)]
    for ket in reg:
        j = wrap_idx(L, ket.idx)
        sec = int(math.floor((j / card) * sectors)) % sectors
        counts[sec] += abs(ket.amp)
    return counts


def local_maxima_bins(hist: list[float], min_frac: float) -> list[int]:
    if not hist:
        return []
    peak = max(hist)
    if peak <= 0.0:
        return []
    out: list[int] = []
    n = len(hist)
    for i in range(n):
        l = hist[(i - 1) % n]
        c = hist[i]
        r = hist[(i + 1) % n]
        if c >= l and c >= r and c >= min_frac * peak:
            out.append(i)
    return out


def period4_mask_indices(reg: list[SparseKet]) -> list[SparseKet]:
    return [k for k in reg if k.idx % 4 == 0]


def build_seed_register(L: int, n_points: int) -> list[SparseKet]:
    # Deterministic sparse seed, one ket per index on E0 channel.
    return [SparseKet(idx=i, amp=1.0) for i in range(min(n_points, sparse_basis_card(L)))]


def run_probe(L: int, shells: list[int], reference_m: int, n_points: int, peak_min_frac: float) -> dict[str, Any]:
    seed = build_seed_register(L, n_points=n_points)
    evolved, pivot_flat = apply_gate_sparse_hqiv_native(L, seed, shells=shells, reference_m=reference_m)
    flipped = detect_flipped_kets(seed, evolved)
    pruned = prune_to_flipped(flipped, evolved)

    h16 = sector_histogram_from_indices(L, pruned, sectors=16)
    h32 = sector_histogram_from_indices(L, pruned, sectors=32)
    peaks16 = local_maxima_bins(h16, min_frac=peak_min_frac)
    peaks32 = local_maxima_bins(h32, min_frac=peak_min_frac)

    # "Recover aliased peaks": compare 32-bin peaks against doubled 16-bin bins.
    predicted32 = sorted({(2 * p) % 32 for p in peaks16} | {(2 * p + 1) % 32 for p in peaks16})
    recovered_secondary32 = [p for p in peaks32 if p not in predicted32]

    p4 = period4_mask_indices(pruned)
    h16_p4 = sector_histogram_from_indices(L, p4, sectors=16)
    peaks16_p4 = local_maxima_bins(h16_p4, min_frac=peak_min_frac)

    return {
        "inputs": {
            "L": L,
            "shells": shells,
            "reference_m": reference_m,
            "n_points": n_points,
            "peak_min_frac": peak_min_frac,
        },
        "gate_pipeline": {
            "sparse_basis_card": sparse_basis_card(L),
            "seed_len": len(seed),
            "evolved_len": len(evolved),  # expected 2 * seed_len
            "flipped_count": len(flipped),
            "pruned_len": len(pruned),
            "hqiv_pivot_flat": pivot_flat,
            "hqiv_pivot_harmonic": decode_idx(L, pivot_flat).__dict__,
        },
        "alias_recovery": {
            "hist16": h16,
            "hist32": h32,
            "peaks16": peaks16,
            "peaks32": peaks32,
            "predicted32_from_16": predicted32,
            "recovered_secondary32": recovered_secondary32,
            "period4_peaks16": peaks16_p4,
            "interpretation": (
                "Secondary aliases are bins that appear in 32-sector peaks but are not explained "
                "by simple 16->32 splitting; period-4 mask highlights QFT-style harmonics."
            ),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="HQIV quantum-gate alias peak probe.")
    parser.add_argument("--L", type=int, default=7, help="Harmonic cutoff L (default: 7).")
    parser.add_argument(
        "--shells",
        default="1,2,3,4,5,6,7",
        help="Comma-separated shell list; length should match L (default: 1..7).",
    )
    parser.add_argument("--reference-m", type=int, default=REFERENCE_M_DEFAULT, help="referenceM anchor (default: 4).")
    parser.add_argument("--n-points", type=int, default=22, help="Sparse seed size (default: 22 for 16+6).")
    parser.add_argument("--peak-min-frac", type=float, default=0.35, help="Relative threshold for peak bins.")
    parser.add_argument("--output", default="data/hqiv_quantum_gate_alias_probe.json", help="Output JSON path.")
    args = parser.parse_args()

    shells = [int(x.strip()) for x in args.shells.split(",") if x.strip()]
    if args.L < 1:
        raise SystemExit("--L must be >= 1")
    if len(shells) != args.L:
        raise SystemExit(f"--shells length must equal L. got len={len(shells)}, L={args.L}")
    if args.n_points <= 0:
        raise SystemExit("--n-points must be positive")

    report = run_probe(
        L=args.L,
        shells=shells,
        reference_m=args.reference_m,
        n_points=args.n_points,
        peak_min_frac=args.peak_min_frac,
    )

    out = Path(args.output)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2))

    print("HQIV quantum-gate alias probe")
    print("=" * 29)
    print(f"L / basis            : {args.L} / {report['gate_pipeline']['sparse_basis_card']}")
    print(f"seed -> evolved len  : {report['gate_pipeline']['seed_len']} -> {report['gate_pipeline']['evolved_len']}")
    print(f"pivot harmonic       : {report['gate_pipeline']['hqiv_pivot_harmonic']}")
    print(f"peaks16 / peaks32    : {report['alias_recovery']['peaks16']} / {report['alias_recovery']['peaks32']}")
    print(f"secondary 32 peaks   : {report['alias_recovery']['recovered_secondary32']}")
    print(f"period4 peaks16      : {report['alias_recovery']['period4_peaks16']}")
    print(f"output               : {out}")


if __name__ == "__main__":
    main()


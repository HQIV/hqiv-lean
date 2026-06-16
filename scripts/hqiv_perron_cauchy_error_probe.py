#!/usr/bin/env python3
"""
Numerical probe for Path A relaxed Cauchy rectangle error (Lean mirror).

Formulas from `Hqiv/Story/S3GoldbachPerronContourRemainder.lean` at unit scale x = 1:

  tail_bookkeeping = 2 * B_{M,σ} / (σ * T)
  FMPlusOne(M,σ₀,T) = (B_{M,σ₀} + 1) / (σ₀ * T)
  left_edge = A₂_smoothed + 8 * FMPlusOne(M,σ₀,T)
  total = tail_bookkeeping + left_edge

Fejér hybrid left-edge (partial Path A; Lean mirror):
  a2_fejer_hybrid = fejer_coupling + a2_kernel_pairing  (Gaussian-chart Mellin slack)
  left_edge_fejer_hybrid = a2_fejer_hybrid + 8 * FMPlusOne

Coupling (structural): |∑_{1≤N≤M} K_T(N; center) · (a_N − 1)| with
  Gaussian K = exp(−(N−center)²/(2T²))
  Fejér   K = max(0, 1 − |N−center|/T)

Regime (Lean hypotheses): 1 ≤ T, 1 ≤ σ₀, σ₀ ≥ T, σ₀·T ≤ 2π, σ₀ < σ.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Literal

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUT = ROOT / "data" / "perron_cauchy_error_probe.json"
DEFAULT_SWEEP_OUT = ROOT / "data" / "perron_coupling_sweep_probe.json"

TWO_PI = 2 * math.pi
SQRT_2PI = math.sqrt(2 * math.pi)

SmootherKind = Literal["gaussian", "fejer"]


def sieve_primes(limit: int) -> list[int]:
    if limit < 2:
        return []
    is_p = [True] * (limit + 1)
    is_p[0] = is_p[1] = False
    for p in range(2, int(limit**0.5) + 1):
        if is_p[p]:
            step = p
            start = p * p
            is_p[start : limit + 1 : step] = [False] * len(is_p[start : limit + 1 : step])
    return [i for i, v in enumerate(is_p) if v]


def goldbach_midpoint_candidates(N: int, primes: set[int]) -> list[int]:
    out: list[int] = []
    for p in range(2, N + 1):
        q = 2 * N - p
        if p in primes and q in primes and p <= N <= q:
            out.append(p)
    return out


def geometric_aggregate(N: int, primes: set[int]) -> float:
    return sum(
        math.sqrt(p * (2 * N - p))
        for p in goldbach_midpoint_candidates(N, primes)
    )


def vertical_bound_B(M: int, sigma: float, primes: set[int]) -> float:
    """B_{M,σ} = ∑_{N≤M} ∑_p √{p(2N−p)} (2N)^{−σ}."""
    total = 0.0
    for N in range(1, M + 1):
        for p in goldbach_midpoint_candidates(N, primes):
            q = 2 * N - p
            total += math.sqrt(p * q) * (2 * N) ** (-sigma)
    return total


def unweighted_mass(M: int, primes: set[int]) -> float:
    """B_{M,0} = ∑_{N≤M} a_N."""
    return sum(geometric_aggregate(N, primes) for N in range(1, M + 1))


def midpoint_kernel(
    smoother: SmootherKind, scale: float, center: float, N: int
) -> float:
    """Lean: goldbachMidpointGaussianKernel / goldbachMidpointFejerKernel (scale = T)."""
    d = float(N) - center
    if smoother == "gaussian":
        return math.exp(-(d * d) / (2.0 * scale * scale))
    return max(0.0, 1.0 - abs(d) / scale)


def kernel_truncated_mass(
    M: int, scale: float, center: float, smoother: SmootherKind
) -> float:
    return sum(midpoint_kernel(smoother, scale, center, N) for N in range(1, M + 1))


def aggregate_coupling_sum(
    M: int,
    scale: float,
    center: float,
    smoother: SmootherKind,
    primes: set[int],
) -> float:
    """∑_{N≤M} K(N; center) · (a_N − 1) (signed)."""
    return sum(
        midpoint_kernel(smoother, scale, center, N) * (geometric_aggregate(N, primes) - 1.0)
        for N in range(1, M + 1)
    )


def aggregate_coupling_error(
    M: int,
    scale: float,
    center: float,
    smoother: SmootherKind,
    primes: set[int],
) -> float:
    return abs(aggregate_coupling_sum(M, scale, center, smoother, primes))


def smoothed_discrete_target(
    M: int,
    scale: float,
    center: float,
    smoother: SmootherKind,
    primes: set[int],
) -> float:
    return sum(
        midpoint_kernel(smoother, scale, center, N) * geometric_aggregate(N, primes)
        for N in range(1, M + 1)
    )


def coupling_bound_unweighted(
    M: int, scale: float, center: float, smoother: SmootherKind, primes: set[int]
) -> float:
    return unweighted_mass(M, primes) + kernel_truncated_mass(M, scale, center, smoother)


# --- Path A analytic slack (Gaussian chart only in Lean certificate) ---


def heat_full_line(T: float) -> float:
    return T * SQRT_2PI


def heat_vertical_integral(T: float) -> float:
    return T * SQRT_2PI * math.erf(math.sqrt(2))


def heat_vertical_tail_bound(T: float) -> float:
    return heat_full_line(T) - heat_vertical_integral(T)


def heat_vertical_anchor_normalized(T: float) -> float:
    return heat_vertical_integral(T) / (2 * math.pi)


def nat_prefix_sum(M: int, T: float) -> float:
    return sum(math.exp(-(n * n) / (2 * T * T)) for n in range(M))


def poisson_dual_z_sum(T: int, terms: int = 200) -> float:
    a = 2 * math.pi * math.pi * T * T
    s = 1.0
    for n in range(1, terms + 1):
        s += 2 * math.exp(-a * n * n)
    return s


def zsum_nat_tail_beyond(M: int, T: int, terms: int = 500) -> float:
    return sum(math.exp(-((n + M) ** 2) / (2 * T * T)) for n in range(terms))


def fm_plus_one(B: float, sigma0: float, T: float) -> float:
    return (B + 1.0) / (sigma0 * max(1.0, T))


def a1_poisson_error(M: int, T: int) -> float:
    mirror = nat_prefix_sum(M, float(T)) - 1.0
    tail = zsum_nat_tail_beyond(M, T)
    dual_excess = poisson_dual_z_sum(T) - 1.0
    return mirror + 2 * tail + heat_full_line(float(T)) * dual_excess


def a20_error(M: int, T: int) -> float:
    return a1_poisson_error(M, T) + heat_vertical_tail_bound(float(T))


def a2_heat_anchor_link(M: int, T: int) -> float:
    T_f = float(T)
    return (
        a20_error(M, T)
        + (1 - 1 / (2 * math.pi)) * heat_full_line(T_f)
        + heat_vertical_anchor_normalized(T_f)
    )


def a2_kernel_pairing(M: int, T: int, sigma0: float, B_sigma0: float) -> float:
    return a2_heat_anchor_link(M, T) + 4 * fm_plus_one(B_sigma0, sigma0, float(T))


def a2_smoothed_gaussian(
    M: int, T: int, sigma0: float, B_sigma0: float, primes: set[int]
) -> float:
    """Path A left-edge A₂ term uses Gaussian smoother at center = M."""
    coupling = aggregate_coupling_error(M, float(T), float(M), "gaussian", primes)
    return coupling + a2_kernel_pairing(M, T, sigma0, B_sigma0)


def a2_smoothed_fejer_hybrid(
    M: int, T: int, sigma0: float, B_sigma0: float, primes: set[int]
) -> float:
    """Fejér coupling + Gaussian-chart A₂ kernel slack (Lean hybrid budget)."""
    coupling = aggregate_coupling_error(M, float(T), float(M), "fejer", primes)
    return coupling + a2_kernel_pairing(M, T, sigma0, B_sigma0)


def left_edge_mellin_link(
    M: int, T: int, sigma0: float, B_sigma0: float, primes: set[int]
) -> float:
    return a2_smoothed_gaussian(M, T, sigma0, B_sigma0, primes) + 8 * fm_plus_one(
        B_sigma0, sigma0, float(T)
    )


def left_edge_mellin_link_fejer_hybrid(
    M: int, T: int, sigma0: float, B_sigma0: float, primes: set[int]
) -> float:
    return a2_smoothed_fejer_hybrid(M, T, sigma0, B_sigma0, primes) + 8 * fm_plus_one(
        B_sigma0, sigma0, float(T)
    )


def tail_bookkeeping(B_sigma: float, sigma: float, T: float) -> float:
    return 2 * B_sigma / (sigma * max(1.0, T))


def valid_sigma0_for_T(T: int) -> tuple[float, float]:
    lo = float(T)
    hi = TWO_PI / T
    return lo, hi


def default_center_offsets(M: int, T: int) -> list[int]:
    """Offsets Δ so center = M + Δ; span ±max(T, M/10) with step ~T/2."""
    span = max(T, M // 10, 1)
    step = max(T // 2, 1)
    offsets = list(range(-span, span + 1, step))
    if 0 not in offsets:
        offsets.append(0)
    return sorted(set(offsets))


def parse_int_list(spec: str) -> list[int]:
    return [int(x.strip()) for x in spec.split(",") if x.strip()]


@dataclass(frozen=True)
class ErrorBreakdown:
    M: int
    T: int
    sigma0: float
    sigma: float
    B_M_sigma0: float
    B_M_sigma: float
    tail_bookkeeping: float
    a2_smoothed: float
    fm_plus_one_8x: float
    left_edge_mellin: float
    total_error: float
    left_edge_fraction: float
    a2_fraction_of_left: float
    tail_fraction: float
    a2_components: dict[str, float]
    unweighted_mass_B_M_0: float
    kernel_truncated_mass: float
    coupling_bound_unweighted: float
    coupling_over_bound: float
    fejer_hybrid_a2_smoothed: float
    fejer_hybrid_left_edge_mellin: float
    fejer_hybrid_total_error: float
    fejer_hybrid_left_edge_savings: float
    fejer_hybrid_total_savings: float
    fejer_coupling: float
    fejer_coupling_vs_gaussian: float


def breakdown(M: int, T: int, sigma0: float, sigma: float, primes: set[int]) -> ErrorBreakdown:
    B_sigma0 = vertical_bound_B(M, sigma0, primes)
    B_sigma = vertical_bound_B(M, sigma, primes)
    a2 = a2_smoothed_gaussian(M, T, sigma0, B_sigma0, primes)
    a2_fejer = a2_smoothed_fejer_hybrid(M, T, sigma0, B_sigma0, primes)
    fm8 = 8 * fm_plus_one(B_sigma0, sigma0, float(T))
    left = a2 + fm8
    left_fejer = a2_fejer + fm8
    tail = tail_bookkeeping(B_sigma, sigma, float(T))
    total = tail + left
    total_fejer = tail + left_fejer
    T_f = float(T)
    coupling = aggregate_coupling_error(M, T_f, float(M), "gaussian", primes)
    fejer_cpl = aggregate_coupling_error(M, T_f, float(M), "fejer", primes)
    B0 = unweighted_mass(M, primes)
    kmass = kernel_truncated_mass(M, T_f, float(M), "gaussian")
    cbound = B0 + kmass
    return ErrorBreakdown(
        M=M,
        T=T,
        sigma0=sigma0,
        sigma=sigma,
        B_M_sigma0=B_sigma0,
        B_M_sigma=B_sigma,
        tail_bookkeeping=tail,
        a2_smoothed=a2,
        fm_plus_one_8x=fm8,
        left_edge_mellin=left,
        total_error=total,
        left_edge_fraction=left / total if total else 0.0,
        a2_fraction_of_left=a2 / left if left else 0.0,
        tail_fraction=tail / total if total else 0.0,
        a2_components={
            "aggregate_coupling": coupling,
            "a2_heat_anchor_link": a2_heat_anchor_link(M, T),
            "a2_kernel_4x_fm": 4 * fm_plus_one(B_sigma0, sigma0, T_f),
            "a1_poisson": a1_poisson_error(M, T),
            "heat_vertical_tail": heat_vertical_tail_bound(T_f),
        },
        unweighted_mass_B_M_0=B0,
        kernel_truncated_mass=kmass,
        coupling_bound_unweighted=cbound,
        coupling_over_bound=coupling / cbound if cbound else 0.0,
        fejer_hybrid_a2_smoothed=a2_fejer,
        fejer_hybrid_left_edge_mellin=left_fejer,
        fejer_hybrid_total_error=total_fejer,
        fejer_hybrid_left_edge_savings=left - left_fejer,
        fejer_hybrid_total_savings=total - total_fejer,
        fejer_coupling=fejer_cpl,
        fejer_coupling_vs_gaussian=fejer_cpl / coupling if coupling else 0.0,
    )


@dataclass(frozen=True)
class CouplingSweepRow:
    M: int
    T: int
    smoother: SmootherKind
    center_offset: int
    center: float
    aggregate_coupling: float
    aggregate_coupling_signed: float
    kernel_truncated_mass: float
    smoothed_discrete_target: float
    kernel_at_truncation_N: float
    geometric_aggregate_at_M: float
    unweighted_mass_B_M_0: float
    coupling_bound_unweighted: float
    coupling_over_bound: float
    coupling_vs_default_gaussian: float | None
    degenerate_near_zero: bool


def coupling_sweep_row(
    M: int,
    T: int,
    smoother: SmootherKind,
    center_offset: int,
    primes: set[int],
    default_gaussian_coupling: float | None = None,
) -> CouplingSweepRow:
    T_f = float(T)
    center = float(M + center_offset)
    signed = aggregate_coupling_sum(M, T_f, center, smoother, primes)
    coupling = abs(signed)
    kmass = kernel_truncated_mass(M, T_f, center, smoother)
    B0 = unweighted_mass(M, primes)
    cbound = B0 + kmass
    a_M = geometric_aggregate(M, primes)
    rel = (
        coupling / default_gaussian_coupling
        if default_gaussian_coupling and default_gaussian_coupling > 0
        else None
    )
    k_at_M = midpoint_kernel(smoother, T_f, center, M)
    degenerate = coupling < 1.0 or k_at_M < 0.05
    return CouplingSweepRow(
        M=M,
        T=T,
        smoother=smoother,
        center_offset=center_offset,
        center=center,
        aggregate_coupling=coupling,
        aggregate_coupling_signed=signed,
        kernel_truncated_mass=kmass,
        smoothed_discrete_target=smoothed_discrete_target(M, T_f, center, smoother, primes),
        kernel_at_truncation_N=k_at_M,
        geometric_aggregate_at_M=a_M,
        unweighted_mass_B_M_0=B0,
        coupling_bound_unweighted=cbound,
        coupling_over_bound=coupling / cbound if cbound else 0.0,
        coupling_vs_default_gaussian=rel,
        degenerate_near_zero=degenerate,
    )


def run_grid(M_values: list[int], T_values: list[int]) -> dict:
    prime_limit = max(M_values) * 2 + 100
    primes = set(sieve_primes(prime_limit))
    rows: list[dict] = []
    for T in T_values:
        lo, hi = valid_sigma0_for_T(T)
        for sigma0 in (lo, (lo + hi) / 2, hi):
            sigma = min(sigma0 + 0.5, sigma0 + (hi - lo) * 0.25 + 0.1)
            if sigma <= sigma0:
                sigma = sigma0 + 0.01
            for M in M_values:
                rows.append(asdict(breakdown(M, T, sigma0, sigma, primes)))
    return {
        "regime": "1≤T, 1≤σ₀, σ₀≥T, σ₀·T≤2π, σ₀<σ, x=1",
        "formula_source": "Hqiv/Story/S3GoldbachPerronContourRemainder.lean",
        "fejer_hybrid_note": (
            "Fejér hybrid left-edge = Fejér coupling + Gaussian A₂ kernel slack + 8×FMPlusOne; "
            "Lean: goldbachFejerGaussianHybridLeftEdgeMellinLinkError"
        ),
        "rows": rows,
    }


def run_coupling_sweep(
    M_values: list[int],
    T_values: list[int],
    center_offsets: list[int] | None,
    smoothers: list[SmootherKind],
) -> dict:
    prime_limit = max(M_values) * 2 + 100
    primes = set(sieve_primes(prime_limit))
    rows: list[dict] = []
    for M in M_values:
        for T in T_values:
            offsets = center_offsets if center_offsets is not None else default_center_offsets(M, T)
            default_cpl = aggregate_coupling_error(M, float(T), float(M), "gaussian", primes)
            for smoother in smoothers:
                for delta in offsets:
                    row = coupling_sweep_row(
                        M, T, smoother, delta, primes, default_gaussian_coupling=default_cpl
                    )
                    rows.append(asdict(row))
    return {
        "description": "Aggregate coupling vs smoother kind and kernel center offset",
        "formula_source": "Hqiv/Story/S3GoldbachPerronContourRemainder.lean",
        "kernels": {
            "gaussian": "exp(−(N−center)²/(2T²))",
            "fejer": "max(0, 1 − |N−center|/T)",
        },
        "truncation": "sum N = 1..M; default Lean center = M (offset 0)",
        "rows": rows,
    }


def print_path_a_summary(M_values: list[int], T_values: list[int], primes: set[int]) -> None:
    print("\nPath A summary (mid σ₀, Gaussian center=M):")
    print(
        f"{'M':>6} {'T':>3} {'total':>12} {'tail%':>7} {'A2/left%':>9} "
        f"{'coupling':>10} {'cpl/bnd':>8}"
    )
    for T in T_values:
        lo, hi = valid_sigma0_for_T(T)
        sigma0 = (lo + hi) / 2
        sigma = sigma0 + 0.5
        for M in M_values:
            b = breakdown(M, T, sigma0, sigma, primes)
            print(
                f"{M:6d} {T:3d} {b.total_error:12.4g} "
                f"{100 * b.tail_fraction:6.1f}% {100 * b.a2_fraction_of_left:8.1f}% "
                f"{b.a2_components['aggregate_coupling']:10.4g} "
                f"{b.coupling_over_bound:7.3f}"
            )

    print("\nFejér hybrid vs Gaussian left-edge (same tail; Fejér coupling + Gaussian A₂ slack):")
    print(
        f"{'M':>6} {'T':>3} {'G left':>12} {'F left':>12} {'save%':>7} "
        f"{'G total':>12} {'F total':>12} {'F/G cpl':>8}"
    )
    for T in T_values:
        lo, hi = valid_sigma0_for_T(T)
        sigma0 = (lo + hi) / 2
        sigma = sigma0 + 0.5
        for M in M_values:
            b = breakdown(M, T, sigma0, sigma, primes)
            save_pct = (
                100 * b.fejer_hybrid_left_edge_savings / b.left_edge_mellin
                if b.left_edge_mellin
                else 0.0
            )
            print(
                f"{M:6d} {T:3d} {b.left_edge_mellin:12.4g} "
                f"{b.fejer_hybrid_left_edge_mellin:12.4g} {save_pct:6.1f}% "
                f"{b.total_error:12.4g} {b.fejer_hybrid_total_error:12.4g} "
                f"{b.fejer_coupling_vs_gaussian:8.3f}"
            )


def print_coupling_sweep_summary(payload: dict) -> None:
    rows = payload["rows"]
    by_key: dict[tuple[int, int], list[dict]] = {}
    for r in rows:
        by_key.setdefault((r["M"], r["T"]), []).append(r)

    print("\nCoupling sweep — smoother comparison at center offset 0 (center = M):")
    print(
        f"{'M':>6} {'T':>3} {'smoother':>9} {'coupling':>12} {'vs G':>8} "
        f"{'kmass':>8} {'a_M':>10}"
    )
    for (M, T), group in sorted(by_key.items()):
        at_zero = [r for r in group if r["center_offset"] == 0]
        g_ref = next(
            (r["aggregate_coupling"] for r in at_zero if r["smoother"] == "gaussian"),
            None,
        )
        for r in sorted(at_zero, key=lambda x: x["smoother"]):
            vs_g = (
                r["aggregate_coupling"] / g_ref
                if g_ref and r["smoother"] != "gaussian"
                else 1.0 if r["smoother"] == "gaussian" else None
            )
            vs_s = f"{vs_g:8.3f}" if vs_g is not None else "     n/a"
            print(
                f"{M:6d} {T:3d} {r['smoother']:>9} "
                f"{r['aggregate_coupling']:12.4g} {vs_s} "
                f"{r['kernel_truncated_mass']:8.4g} {r['geometric_aggregate_at_M']:10.4g}"
            )

    print("\nBest non-degenerate coupling (|offset|≤T, center≤M, coupling≥1):")
    print(
        f"{'M':>6} {'T':>3} {'smoother':>9} {'offset':>7} {'coupling':>12} "
        f"{'vs defG':>8} {'k(M)':>8}"
    )
    for (M, T), group in sorted(by_key.items()):
        fair = [
            r
            for r in group
            if not r["degenerate_near_zero"]
            and r["center_offset"] <= 0
            and abs(r["center_offset"]) <= T
        ]
        if not fair:
            fair = [r for r in group if r["center_offset"] == 0]
        best = min(fair, key=lambda r: r["aggregate_coupling"])
        rel = best.get("coupling_vs_default_gaussian")
        rel_s = f"{rel:8.3f}" if rel is not None else "     n/a"
        print(
            f"{M:6d} {T:3d} {best['smoother']:>9} {best['center_offset']:7d} "
            f"{best['aggregate_coupling']:12.4g} {rel_s} "
            f"{best['kernel_at_truncation_N']:8.4g}"
        )

    print("\nDegenerate minima (coupling≈0 from kernel support past M — not Lean-aligned):")
    for (M, T), group in sorted(by_key.items()):
        deg = [r for r in group if r["degenerate_near_zero"]]
        if not deg:
            continue
        best = min(deg, key=lambda r: r["aggregate_coupling"])
        if best["aggregate_coupling"] < 1:
            print(
                f"  M={M} T={T}: {best['smoother']} offset={best['center_offset']} "
                f"coupling={best['aggregate_coupling']:.4g} k(M)={best['kernel_at_truncation_N']:.4g}"
            )

    print("\nCenter-offset profile (Gaussian, first grid point only):")
    print(f"{'M':>6} {'T':>3} {'offset':>7} {'center':>8} {'coupling':>12} {'vs defG':>8}")
    shown = 0
    for (M, T), group in sorted(by_key.items()):
        if shown >= 3:
            break
        gauss = [r for r in group if r["smoother"] == "gaussian"]
        gauss.sort(key=lambda r: r["center_offset"])
        for r in gauss:
            rel = r.get("coupling_vs_default_gaussian")
            rel_s = f"{rel:8.3f}" if rel is not None else "     n/a"
            print(
                f"{M:6d} {T:3d} {r['center_offset']:7d} {r['center']:8.1f} "
                f"{r['aggregate_coupling']:12.4g} {rel_s}"
            )
        shown += 1


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--M", type=int, nargs="+", default=[50, 200, 1000, 5000])
    parser.add_argument("--T", type=int, nargs="+", default=[1, 2])
    parser.add_argument("-o", "--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument(
        "--coupling-sweep",
        action="store_true",
        help="Run center-offset + smoother comparison probe",
    )
    parser.add_argument(
        "--sweep-out",
        type=Path,
        default=DEFAULT_SWEEP_OUT,
        help="JSON output for coupling sweep",
    )
    parser.add_argument(
        "--center-offsets",
        type=str,
        default="",
        help="Comma-separated Δ for center = M + Δ (default: auto span ±max(T,M/10))",
    )
    parser.add_argument(
        "--smoothers",
        type=str,
        default="gaussian,fejer",
        help="Comma-separated: gaussian, fejer",
    )
    parser.add_argument(
        "--sweep-only",
        action="store_true",
        help="Skip Path A grid; only write coupling sweep",
    )
    args = parser.parse_args()

    smoothers: list[SmootherKind] = []
    for s in args.smoothers.split(","):
        s = s.strip().lower()
        if s in ("gaussian", "fejer"):
            smoothers.append(s)  # type: ignore[arg-type]
        elif s:
            raise SystemExit(f"Unknown smoother: {s!r} (use gaussian, fejer)")

    offsets: list[int] | None = None
    if args.center_offsets.strip():
        offsets = parse_int_list(args.center_offsets)

    prime_limit = max(args.M) * 2 + 100
    primes = set(sieve_primes(prime_limit))

    if not args.sweep_only:
        payload = run_grid(args.M, args.T)
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(payload, indent=2) + "\n")
        print(f"Wrote {len(payload['rows'])} Path A rows to {args.out}")
        print_path_a_summary(args.M, args.T, primes)

    if args.coupling_sweep or args.sweep_only:
        sweep = run_coupling_sweep(args.M, args.T, offsets, smoothers)
        args.sweep_out.parent.mkdir(parents=True, exist_ok=True)
        args.sweep_out.write_text(json.dumps(sweep, indent=2) + "\n")
        print(f"Wrote {len(sweep['rows'])} coupling-sweep rows to {args.sweep_out}")
        print_coupling_sweep_summary(sweep)


if __name__ == "__main__":
    main()

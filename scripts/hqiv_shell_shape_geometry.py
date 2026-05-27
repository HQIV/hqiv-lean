#!/usr/bin/env python3
"""
How HQIV geometry forces shell_shape — continuous coordinate, not integer shells.

Lean anchors:
  • curvatureDensity(x) = (1/x)(1 + α ln x)     — OctonionicLightCone
  • shell_shape(m) = curvatureDensity(m+1)       — sample at x = m+1
  • φ(m) = 2(m+1)  ⇔  x := φ/2 = m+1 = 1/T(m)  — AuxiliaryField
  • δE/4π_geom = shell_shape × 21               — DoublePreferredAxis (norm cancels)
  • timeAngle period 2π; quarter π/2              — HQVMetric / ComptonHorizonPhase
  • 1/α_eff(φ) = 42(1 + α ln(φ+1))               — SM_GR_Unification / Action

Integer shell index m is a **readout grid**: ξ = m+1. Physics lives on ξ ∈ ℝ₊.

Run:
  python3 scripts/hqiv_shell_shape_geometry.py
  python3 scripts/hqiv_shell_shape_geometry.py --find-codata
"""

from __future__ import annotations

import argparse
import math
import sys
from dataclasses import dataclass
from pathlib import Path

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(_ROOT / "scripts"))

import cubic_phase_relax_probe as cpr  # noqa: E402

ALPHA = cpr.ALPHA
GAMMA = cpr.GAMMA
INV_ALPHA_GUT = 42.0
TWO_PI = 2.0 * math.pi
HORIZON_QUARTER = TWO_PI / 4.0
REFERENCE_M = cpr.REFERENCE_M
EM_XI = float(REFERENCE_M)  # ξ = m+1 at Gauss row
EW_XI = float(REFERENCE_M + 2)  # m=5 ⇒ ξ=6
LOCKIN_XI = float(REFERENCE_M + 1)
CODATA_INV_ALPHA = 137.035999177


def xi_from_m(m: float) -> float:
    """Continuous horizon coordinate ξ = m+1 = φ/2 = 1/T."""
    return m + 1.0


def m_from_xi(xi: float) -> float:
    return xi - 1.0


def curvature_density(xi: float) -> float:
    if xi <= 0.0:
        return float("nan")
    return (1.0 / xi) * (1.0 + ALPHA * math.log(xi))


def shell_shape_at_xi(xi: float) -> float:
    return curvature_density(xi)


def shell_shape_m(m: int) -> float:
    return shell_shape_at_xi(xi_from_m(float(m)))


def phi_of_xi(xi: float) -> float:
    return 2.0 * xi


def T_of_xi(xi: float) -> float:
    return 1.0 / xi


def one_over_alpha_eff_xi(xi: float, c: float = 1.0) -> float:
    phi = phi_of_xi(xi)
    return INV_ALPHA_GUT * (1.0 + c * ALPHA * math.log(phi + 1.0))


def detuning_rindler(xi: float) -> float:
    """1 + (γ/2)m with m = ξ-1."""
    m = m_from_xi(xi)
    return 1.0 + (GAMMA / 2.0) * m


def detuned_surface_xi(xi: float) -> float:
    """S(m)/detuning with S ~ (m+1)(m+2) = ξ(ξ+1)."""
    m = m_from_xi(xi)
    s = (m + 1.0) * (m + 2.0)
    return s / detuning_rindler(xi)


def curvature_integral_continuous(xi_max: float, steps: int = 2000) -> float:
    """∫_1^ξ_max ρ(ξ) dξ (Riemann)."""
    if xi_max <= 1.0:
        return 0.0
    a, b = 1.0, xi_max
    h = (b - a) / steps
    total = 0.0
    for i in range(steps):
        x0 = a + i * h
        x1 = x0 + h
        total += 0.5 * h * (curvature_density(x0) + curvature_density(x1))
    return total


def omega_k_continuous(xi: float, xi_ref: float) -> float:
    num = curvature_integral_continuous(xi)
    den = curvature_integral_continuous(xi_ref)
    if den <= 0.0:
        return 1.0
    return num / den


def holonomy_phase_density_xi(xi: float) -> float:
    """
    Phase advance per unit ξ from self-clock + O-Maxwell slot:
    compton ω = ξ (SurfaceWaveSelfClock), quarter = π/2/ω = π/(2ξ).
    Density ~ d(π/2)/dξ = -π/(2ξ²) — use magnitude budget at ξ.
    """
    if xi <= 0.0:
        return float("nan")
    return HORIZON_QUARTER / xi  # radians per ξ step in the natural clock


def braced_inv_alpha_xi(xi_gauss: float, xi_ew: float, c: float = 1.0) -> float:
    inv_g = one_over_alpha_eff_xi(xi_gauss, c)
    ratio = shell_shape_at_xi(xi_gauss) / shell_shape_at_xi(xi_ew)
    return inv_g * ratio


def mexican_hat_veff_xi(xi: float, lam: float = 1.0, phi: float = 0.1, t: float = 1.0) -> float:
    """V_eff ~ 1/effCorrected at global δ from lapse (schematic)."""
    m = m_from_xi(xi)
    delta = lam * (0.0 + phi * t)
    den = detuning_rindler(xi) + delta
    if den <= 0.0:
        return float("inf")
    return shell_shape_at_xi(xi) * (m + 1.0) * (m + 2.0) / den


@dataclass
class XiConstraint:
    name: str
    xi: float
    m: float
    sigma: float
    inv_alpha: float
    inv_alpha_braced: float
    omega_k_lockin: float
    holonomy_share: float


def find_xi_for_inv_alpha_braced(target: float, c: float = 1.0) -> float:
    """ξ on Gauss shell where braced readout = target (bisection; braced decreases in ξ)."""
    lo, hi = 1.5, EW_XI - 0.01
    if braced_inv_alpha_xi(lo, EW_XI, c) < target:
        return lo
    if braced_inv_alpha_xi(hi, EW_XI, c) > target:
        return hi
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        if braced_inv_alpha_xi(mid, EW_XI, c) > target:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def find_xi_for_inv_alpha_direct(target: float, c: float = 1.0) -> float:
    lo, hi = 1.01, 50.0
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        if one_over_alpha_eff_xi(mid, c) < target:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def evaluate_xi(xi: float, c: float = 1.0) -> XiConstraint:
    m = m_from_xi(xi)
    w = (int(m) % 7) % 3 + 1
    w_norm = w / 12.0
    return XiConstraint(
        name=f"ξ={xi:.4f}",
        xi=xi,
        m=m,
        sigma=shell_shape_at_xi(xi),
        inv_alpha=one_over_alpha_eff_xi(xi, c),
        inv_alpha_braced=braced_inv_alpha_xi(xi, EW_XI, c),
        omega_k_lockin=omega_k_continuous(xi, LOCKIN_XI),
        holonomy_share=TWO_PI * w_norm,
    )


def print_geometry_narrative() -> None:
    print("=" * 72)
    print("HQIV: shell_shape as forced geometry (continuous ξ, not integer m)")
    print("=" * 72)
    print()
    print("1. THE COORDINATE (one variable for everything)")
    print("   ξ := φ/2 = m+1 = T_Pl/T(m) = 1/T")
    print("   Lean: shell_shape_in_terms_of_phi, shell_shape_T_formula, phi_of_shell_closed_form")
    print()
    print("2. THE SHAPE (forced by lattice α, not fitted)")
    print("   σ(ξ) = ρ(ξ) = (1/ξ)(1 + α ln ξ)   with α = 3/5 proved")
    print("   Integer shell: σ(m) = ρ(m+1)  — just a sample point on this curve")
    print()
    print("3. CURVATURE NORM CANCELS IN GAUSS LAW (why σ survives)")
    print("   δE(ξ) = N_curv · σ(ξ)   but   δE / 4π_geom = σ(ξ) × 21")
    print("   N_curv = 6^7√3 is NOT an extra knob in the EM readout — it divides out")
    print()
    print("4. HOLONOMY (2π is the closure, not an integer shell)")
    print("   Full lapse phase period: 2π (Conservations timeAngle_zero_to_twoPi)")
    print("   Quarter turn per Compton tick: π/2 = ω·Δt with ω ~ ξ")
    print("   Seven Fano weights partition ONE 2π turn: Σ_v (2π/7)·w_v")
    print("   ⇒ coupling rows are phase-budget on σ(ξ), not 'pick m=3'")
    print()
    print("5. ACTION (same ξ in the φ slot)")
    print("   EL: α ln(φ+1)∂φ  with φ = 2ξ")
    print("   1/α_eff(ξ) = 42(1 + c·α·ln(2ξ+1))")
    print("   Same logarithm as σ(ξ) — holonomy + O-Maxwell + shell_shape are one function of ξ")
    print()
    print("6. WHY INTEGER SHELLS MISLEAD")
    print("   m ∈ ℕ is a chart for ξ; electroweak vs Gauss is TWO POINTS on the curve:")
    print(f"      ξ_Gauss = {EM_XI:.0f}  (m={REFERENCE_M-1}),  ξ_EW = {EW_XI:.0f}  (m={REFERENCE_M+1})")
    print("   CODATA α is a ratio of σ at those ξ values (brace), not a third integer.")
    print()


def print_sample_table(c: float = 1.0) -> None:
    print("Samples on the continuous curve (c_Fano = {:.4f}):".format(c))
    print(f"{'ξ':>8} {'m':>8} {'σ(ξ)':>10} {'1/α(ξ)':>10} {'1/α br→EW':>12} {'Ω_k':>8}")
    xis = [2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 9.0, 13.0, LOCKIN_XI, EM_XI, EW_XI]
    for xi in sorted(set(xis)):
        r = evaluate_xi(xi, c)
        print(
            f"{r.xi:8.3f} {r.m:8.3f} {r.sigma:10.5f} {r.inv_alpha:10.2f} "
            f"{r.inv_alpha_braced:12.2f} {r.omega_k_lockin:8.4f}"
        )
    print()


def print_codata_fit() -> None:
    print("=" * 72)
    print("Continuous ξ targets for CODATA 1/α ≈ {:.6f}".format(CODATA_INV_ALPHA))
    print()
    xi_dir = find_xi_for_inv_alpha_direct(CODATA_INV_ALPHA, 1.0)
    xi_br = find_xi_for_inv_alpha_braced(CODATA_INV_ALPHA, 1.0)
    c_dir = (CODATA_INV_ALPHA / INV_ALPHA_GUT - 1.0) / (
        ALPHA * math.log(phi_of_xi(EM_XI) + 1.0)
    )
    print(f"  Direct at ξ_Gauss={EM_XI:.0f}: need c = {c_dir:.4f} (Fano normalization)")
    print(f"  Direct 1/α at solved ξ = {xi_dir:.4f}  (m = {m_from_xi(xi_dir):.4f})")
    print(f"  Braced Gauss→EW: ξ_Gauss ≈ {xi_br:.4f}  (m ≈ {m_from_xi(xi_br):.4f})")
    print(f"    at integer ξ_Gauss={EM_XI:.0f}, braced = {braced_inv_alpha_xi(EM_XI, EW_XI, 1.0):.2f}")
    print(f"    σ ratio σ({EM_XI:.0f})/σ({EW_XI:.0f}) = {shell_shape_at_xi(EM_XI)/shell_shape_at_xi(EW_XI):.4f}")
    print()
    print("  Lock-in calibration: Ω_k(ξ, ξ_lockin)=1 at ξ_lockin =", LOCKIN_XI)
    for xi in (EM_XI, EW_XI, xi_br, xi_dir):
        print(f"    Ω_k({xi:.3f}) = {omega_k_continuous(xi, LOCKIN_XI):.4f}")
    print()
    print("  Holonomy + action consistency at ξ_Gauss (c=1):")
    r = evaluate_xi(EM_XI, 1.0)
    print(f"    σ(ξ) = {r.sigma:.5f}")
    print(f"    ln(2ξ+1) = {math.log(phi_of_xi(EM_XI)+1):.4f}")
    print(f"    holonomy share (Fano w at v=0) = {r.holonomy_share:.4f} rad")
    print(f"    1/α_eff = {r.inv_alpha:.2f}  |  braced to EW = {r.inv_alpha_braced:.2f}")
    print()


def print_forced_xi_from_constraints() -> None:
    """
    Overdetermined continuous constraints (no PDG):
      • Ω_k(ξ) = 1 at lock-in ξ₀
      • σ(ξ) matches spectral detuning slope (γ/2)
      • holonomy: k(ξ)·c = 4w/7
    Then one CODATA brace fixes c — check if ξ clusters.
    """
    print("=" * 72)
    print("Scan: where do geometry-only constraints cluster on ξ?")
    xi0 = LOCKIN_XI
    best = None
    print(f"{'ξ':>8} {'Ω_k-1':>10} {'σ-σ*':>10} {'hol-res':>10}")
    for i in range(50, 400):
        xi = 1.0 + (i / 40.0)
        ok = omega_k_continuous(xi, xi0) - 1.0
        # spectral: σ(ξ) ~ 42·rindler/ξ at leading order — use detuned proxy
        sig_star = detuned_surface_xi(xi) / (xi * (xi + 1.0))
        sig_res = shell_shape_at_xi(xi) - sig_star
        hol_res = ALPHA * math.log(phi_of_xi(xi) + 1.0) - (4.0 / 7.0) * (2.0 / 3.0)
        score = abs(ok) + abs(sig_res) + abs(hol_res)
        if best is None or score < best[0]:
            best = (score, xi, ok, sig_res, hol_res)
        if i % 40 == 0:
            print(f"{xi:8.3f} {ok:10.4f} {sig_res:10.4f} {hol_res:10.4f}")
    if best:
        print(f"\n  best cluster: ξ ≈ {best[1]:.3f}  score={best[0]:.4f}")
    print()


def main() -> None:
    p = argparse.ArgumentParser(description="shell_shape geometry forcing")
    p.add_argument("--find-codata", action="store_true")
    p.add_argument("--scan", action="store_true")
    args = p.parse_args()

    print_geometry_narrative()
    print_sample_table(1.0)
    if args.find_codata:
        print_codata_fit()
    if args.scan:
        print_forced_xi_from_constraints()


if __name__ == "__main__":
    main()

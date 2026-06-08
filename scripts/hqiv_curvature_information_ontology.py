#!/usr/bin/env python3
"""
HQIV ontology explorer: discrete information capacity ↔ curvature ↔ lapse ↔ G_eff.

Everything here is in **stasis** with respect to the formal stack: closed forms and
identities mirrored from Lean / `cubic_phase_relax_probe.py`. No PDG fits, no mass
anchors, no tunable parameters beyond choosing shell range and display conventions.

Lean / Python mirrors:
  • `Hqiv/Geometry/OctonionicLightCone` — `available_modes`, `new_modes`, `latticeAlphaRatio`,
    `cumLatticeSimplexCount`, `shell_shape`, `curvature_integral`, `omega_k_at_horizon`
  • `Hqiv/Geometry/HQVMetric` — `HQVM_lapse`, `timeAngle`, `G_eff` = φ^α, `3 - γ` = 13/5
  • `Hqiv/Geometry/SphericalHarmonicsBridge` — cumulative S² degeneracy (m+1)² vs capacity

Run:
  python3 scripts/hqiv_curvature_information_ontology.py
  python3 scripts/hqiv_curvature_information_ontology.py --m-max 12 --json
  python3 scripts/hqiv_curvature_information_ontology.py --stasis-only
  python3 scripts/hqiv_curvature_information_ontology.py --horizon 6 --phi-newton 0 --t 1
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import asdict, dataclass
from pathlib import Path

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(_ROOT / "scripts"))

import cubic_phase_relax_probe as cpr  # noqa: E402

# ---------------------------------------------------------------------------
# Constants (same as Lean / cpr)

ALPHA = cpr.ALPHA
GAMMA = cpr.GAMMA
THREE_MINUS_GAMMA = 3.0 - GAMMA  # 13/5
REFERENCE_M = cpr.REFERENCE_M
PHI_TEMPERATURE_COEFF = cpr.PHI_TEMPERATURE_COEFF
T_PL = 1.0


def lattice_simplex_count(m: int) -> int:
    return (m + 2) * (m + 1)


def cum_lattice_simplex_count(n: int) -> int:
    """`cumLatticeSimplexCount n` = (n+1)(n+2)(n+3) / 3  (integer, hockey-stick)."""
    return ((n + 1) * (n + 2) * (n + 3)) // 3


def lattice_alpha_ratio(n: int) -> float:
    """Lean `latticeAlphaRatio n` — equals α = 3/5 for every n (theorem)."""
    cum = cum_lattice_simplex_count(n)
    if cum == 0:
        return float("nan")
    return float((n + 1) * (n + 2) * (n + 3)) / (5.0 * cum)


def available_modes(m: int) -> float:
    """`available_modes m` = 4(m+2)(m+1)."""
    return 4.0 * float(lattice_simplex_count(m))


def new_modes(m: int) -> float:
    """Incremental modes at shell m (Lean `new_modes`)."""
    if m == 0:
        return available_modes(0)
    return available_modes(m) - available_modes(m - 1)


def spherical_harmonic_cumulative(m: int) -> float:
    """Cumulative S² mode count through L = m: (m+1)²."""
    return float(m + 1) ** 2


def modes_div_harmonic(m: int) -> float:
    """`available_modes m / (m+1)²` → 4 as m → ∞."""
    h = spherical_harmonic_cumulative(m)
    if h <= 0.0:
        return float("nan")
    return available_modes(m) / h


def T_m(m: int) -> float:
    """Auxiliary temperature ladder T(m) = T_Pl/(m+1), T_Pl = 1."""
    return T_PL / float(m + 1)


def phi_of_shell(m: int) -> float:
    """φ(m) = phiTemperatureCoeff * (m+1)."""
    return PHI_TEMPERATURE_COEFF * float(m + 1)


def G_eff(phi: float) -> float:
    """Homogeneous sector: G_eff(φ) = φ^α for φ ≥ 0 (Lean `G_eff_eq`)."""
    if phi < 0.0:
        raise ValueError("G_eff requires φ ≥ 0")
    return phi ** ALPHA


def hqvm_lapse(phi_newton: float, phi_aux: float, t: float) -> float:
    """ADM lapse N = 1 + Φ + φ t (Lean `HQVM_lapse`)."""
    return 1.0 + phi_newton + phi_aux * t


def time_angle(phi_aux: float, t: float) -> float:
    return phi_aux * t


@dataclass(frozen=True)
class ShellOntologyRow:
    """One shell: information capacity, curvature, relative Ω, metric proxies."""

    m: int
    T_m: float
    phi_aux: float
    new_modes: float
    available_modes: float
    spherical_harmonic_cumulative: float
    modes_over_harmonic: float
    shell_shape: float
    curvature_integral_up_to_m: float
    omega_k_vs_ref: float
    shell_shape_per_new_mode: float
    G_eff_at_phi: float
    time_angle_t_unit: float
    lapse_phi_zero_t: float


def curvature_integral_up_to(m: int) -> float:
    """Sum shell_shape(k) for k = 0 .. m-1 (same as cpr.curvature_integral(n) with n=m)."""
    return cpr.curvature_integral(m)


def omega_k(n: int, horizon: int) -> float:
    return cpr.omega_k_at_horizon(n, horizon)


def build_row(m: int, horizon: int, phi_newton: float, t_demo: float) -> ShellOntologyRow:
    phi = phi_of_shell(m)
    nm = new_modes(m)
    sh = cpr.shell_shape(m)
    ci = curvature_integral_up_to(m)
    ok = omega_k(m, horizon)
    per = sh / nm if nm > 0 else float("nan")
    return ShellOntologyRow(
        m=m,
        T_m=T_m(m),
        phi_aux=phi,
        new_modes=nm,
        available_modes=available_modes(m),
        spherical_harmonic_cumulative=spherical_harmonic_cumulative(m),
        modes_over_harmonic=modes_div_harmonic(m),
        shell_shape=sh,
        curvature_integral_up_to_m=ci,
        omega_k_vs_ref=ok,
        shell_shape_per_new_mode=per,
        G_eff_at_phi=G_eff(phi),
        time_angle_t_unit=time_angle(phi, t_demo),
        lapse_phi_zero_t=hqvm_lapse(phi_newton, phi, t_demo),
    )


def stasis_report(*, n_check: int = 30) -> dict[str, object]:
    """Numerical checks that definitions sit in equilibrium (no free knobs)."""
    errors_alpha = []
    for n in range(n_check + 1):
        r = lattice_alpha_ratio(n)
        errors_alpha.append(abs(r - ALPHA))

    lock = omega_k(REFERENCE_M, REFERENCE_M)
    monogamy = abs((ALPHA + GAMMA) - 1.0)

    return {
        "alpha_plus_gamma_minus_1": monogamy,
        "three_minus_gamma": THREE_MINUS_GAMMA,
        "omega_k_at_reference_lock": lock,
        "omega_k_lock_error": abs(lock - 1.0),
        "lattice_alpha_ratio_max_abs_err": max(errors_alpha) if errors_alpha else 0.0,
        "modes_div_harmonic_at_m_100": modes_div_harmonic(100),
        "reference_M": REFERENCE_M,
    }


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--m-min", type=int, default=0)
    p.add_argument("--m-max", type=int, default=10)
    p.add_argument("--horizon", type=int, default=REFERENCE_M, help="Ω_k denominator shell (reference pin)")
    p.add_argument("--phi-newton", type=float, default=0.0, help="Φ in N = 1 + Φ + φ t")
    p.add_argument("--t", type=float, default=1.0, help="coordinate time slice for lapse / time angle demo")
    p.add_argument("--stasis-only", action="store_true")
    p.add_argument("--json", action="store_true")
    args = p.parse_args()

    if args.m_max < args.m_min:
        p.error("--m-max must be >= --m-min")

    stasis = stasis_report()
    if args.stasis_only:
        if args.json:
            print(json.dumps({"stasis": stasis}, indent=2))
        else:
            print("HQIV stasis checks (closed-form identities, no fits)\n")
            for k, v in stasis.items():
                print(f"  {k}: {v}")
        return

    rows = [
        build_row(m, args.horizon, args.phi_newton, args.t)
        for m in range(args.m_min, args.m_max + 1)
    ]

    out: dict[str, object] = {
        "stasis": stasis,
        "horizon_for_omega_k": args.horizon,
        "phi_newton": args.phi_newton,
        "t_demo": args.t,
        "shells": [asdict(r) for r in rows],
    }

    if args.json:
        print(json.dumps(out, indent=2))
        return

    print("HQIV curvature–information ontology (stasis / derivation-only)\n")
    print("Stasis:")
    for k, v in stasis.items():
        print(f"  {k}: {v}")
    print()
    print(
        f"Columns: Ω_k = Σsh(<m)/Σsh(<h), h={args.horizon}; "
        f"G_eff = φ(m)^{ALPHA}; N = 1 + Φ + φ·t with Φ={args.phi_newton}, t={args.t}\n"
    )
    hdr = (
        f"{'m':>3} {'T(m)':>8} {'φ':>8} {'new':>8} {'avail':>8} "
        f"{'Ycum':>8} {'/Y':>8} {'shell':>10} {'Σsh<m':>10} {'Ω_k':>8} "
        f"{'sh/new':>10} {'G_eff':>10} {'δθ′':>8} {'N':>10}"
    )
    print(hdr)
    print("-" * len(hdr))
    for r in rows:
        print(
            f"{r.m:3d} {r.T_m:8.5f} {r.phi_aux:8.5f} {r.new_modes:8.1f} {r.available_modes:8.1f} "
            f"{r.spherical_harmonic_cumulative:8.1f} {r.modes_over_harmonic:8.5f} "
            f"{r.shell_shape:10.6f} {r.curvature_integral_up_to_m:10.6f} {r.omega_k_vs_ref:8.5f} "
            f"{r.shell_shape_per_new_mode:10.6f} {r.G_eff_at_phi:10.6f} {r.time_angle_t_unit:8.5f} "
            f"{r.lapse_phi_zero_t:10.6f}"
        )
    print()
    print(
        "Interpretation (ontology, not a fit):\n"
        "  • new / avail — discrete null-cone mode unlocks (information capacity).\n"
        "  • Ycum / /Y — cumulative S² harmonic degeneracy (m+1)²; /Y → 4 (octonion factor).\n"
        "  • shell / K(m) — curvature imprint sample and partial curvature channel.\n"
        "  • Ω_k — curvature ratio vs horizon shell (causal closure relative to outer pin).\n"
        "  • sh/new — imprint per newly unlocked mode at this shell (dimensionless bookkeeping).\n"
        "  • G_eff — varying gravitational coupling from φ(m) alone.\n"
        "  • δθ′, N — time angle and lapse from the informational-energy axiom.\n"
    )


if __name__ == "__main__":
    main()

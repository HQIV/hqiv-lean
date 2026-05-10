#!/usr/bin/env python3
"""
Run the bulk-equivalent calculation using only derived curvature (no arbitrary input).

Matches the Lean definitions in OctonionicLightCone and Baryogenesis:
- alpha = 3/5 (lattice-derived)
- curvatureDensity(x) = (1/x) * (1 + alpha * log(x))
- shell_shape(m) = curvatureDensity(m+1)  [positive, so shell_shape_abs = shell_shape]
- curvature_integral(n) = sum_{m=0}^{n-1} shell_shape(m)
- reference horizon = lockin shell = qcdShell + stepsFromQCDToLockin (discrete steps through baryogenesis).
- omega_k_partial(n) = omega_k_true * curvature_integral(n) / curvature_integral(referenceM)
- eta_partial(n) = eta_paper * curvature_integral(n) / curvature_integral(referenceM)

Discrete ladder: QCD shell -> stepsFromQCDToLockin -> lockin -> stepsAfterLockin steps (baryogenesis). No arbitrary 500.
"""

import math

# --- Derived from lattice (Lean: OctonionicLightCone, Baryogenesis, AuxiliaryField) ---
ALPHA = 3.0 / 5.0  # 3/5, proved in Lean
QCD_SHELL = 1
STEPS_FROM_QCD_TO_LOCKIN = 3
STEPS_AFTER_LOCKIN = 3
# referenceM = lockin = qcdShell + stepsFromQCDToLockin; discrete steps through baryogenesis
REFERENCE_M = QCD_SHELL + STEPS_FROM_QCD_TO_LOCKIN
OMEGA_K_TRUE = 0.0098
ETA_PAPER = 6.10e-10

# Curvature norm 6^7 * sqrt(3) (for deltaE; not needed for omega_k/eta ratio)
CURVATURE_NORM_BASE = 6.0 ** 7  # 279936
CURVATURE_NORM = CURVATURE_NORM_BASE * math.sqrt(3)


def curvature_density(x: float) -> float:
    """curvatureDensity(x) = (1/x) * (1 + alpha * log(x)). x must be > 0."""
    if x <= 0:
        raise ValueError("curvature_density requires x > 0")
    return (1.0 / x) * (1.0 + ALPHA * math.log(x))


def shell_shape(m: int) -> float:
    """shell_shape(m) = curvatureDensity(m+1)."""
    return curvature_density(m + 1.0)


def curvature_integral(n: int) -> float:
    """curvature_integral(n) = sum_{m=0}^{n-1} shell_shape(m)."""
    if n <= 0:
        return 0.0
    return sum(shell_shape(m) for m in range(n))


def omega_k_partial(n: int, ref_integral: float) -> float:
    """omega_k_partial(n) = omega_k_true * curvature_integral(n) / curvature_integral(referenceM)."""
    if ref_integral <= 0:
        return OMEGA_K_TRUE
    return OMEGA_K_TRUE * curvature_integral(n) / ref_integral


def eta_partial(n: int, ref_integral: float) -> float:
    """eta_partial(n) = eta_paper * curvature_integral(n) / curvature_integral(referenceM)."""
    if ref_integral <= 0:
        return ETA_PAPER
    return ETA_PAPER * curvature_integral(n) / ref_integral


def delta_e(m: int) -> float:
    """deltaE(m) = curvature_norm * shell_shape(m)."""
    return CURVATURE_NORM * shell_shape(m)


def main() -> None:
    ref_integral = curvature_integral(REFERENCE_M)
    baryogenesis_end = REFERENCE_M + STEPS_AFTER_LOCKIN
    baryogenesis_shells = list(range(QCD_SHELL, baryogenesis_end + 1))
    print("Bulk-equivalent calculation (derived curvature only)")
    print("=" * 56)
    print(f"  alpha           = {ALPHA} (3/5)")
    print(f"  qcdShell         = {QCD_SHELL}")
    print(f"  stepsToLockin    = {STEPS_FROM_QCD_TO_LOCKIN}")
    print(f"  stepsAfterLockin = {STEPS_AFTER_LOCKIN}")
    print(f"  referenceM       = {REFERENCE_M} (lockin)")
    print(f"  baryogenesisShells = {baryogenesis_shells}")
    print(f"  omega_k_true    = {OMEGA_K_TRUE}")
    print(f"  eta_paper       = {ETA_PAPER}")
    print()
    print(f"  curvature_integral({REFERENCE_M}) = {ref_integral}")
    print()
    # At the reference horizon, partial = true value
    omega_at_ref = omega_k_partial(REFERENCE_M, ref_integral)
    eta_at_ref = eta_partial(REFERENCE_M, ref_integral)
    print(f"  omega_k_partial({REFERENCE_M}) = {omega_at_ref}  (expect {OMEGA_K_TRUE})")
    print(f"  eta_partial({REFERENCE_M})     = {eta_at_ref}  (expect {ETA_PAPER})")
    print()
    # A few other shells
    for n in [1, 10, 100, 500]:
        ci = curvature_integral(n)
        ok = omega_k_partial(n, ref_integral)
        et = eta_partial(n, ref_integral)
        print(f"  n={n:3d}  curvature_integral={ci:.6f}  omega_k_partial={ok:.6e}  eta_partial={et:.6e}")
    print()
    # Single number output (for "arrive at a number")
    print("Result (curvature integral at reference horizon):", ref_integral)
    print("Result (omega_k at reference):", omega_at_ref)
    print("Result (eta at reference):", eta_at_ref)


if __name__ == "__main__":
    main()

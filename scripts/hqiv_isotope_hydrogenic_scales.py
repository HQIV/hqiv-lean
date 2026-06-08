#!/usr/bin/env python3
"""
HQIV bound-state hydrogenic scales per isotope (exploratory step).

Mirrors the Lean layer in `Hqiv/Physics/BoundStates.lean`:

  • `phi_of_shell` from `Hqiv/Geometry/AuxiliaryField.lean` (φ(m) = 2(m+1))
  • `oneOverAlphaEffAtShell`, `alphaEffAtShell` with `Hqiv.Geometry.OctonionicLightCone.alpha = 3/5`
  • `expectedGroundEnergyAtShell m Z μ` = −μ Z² α_eff(m)² / 2

Nuclear masses enter **only** through the **reduced mass** μ in atomic units (m_e = 1):
  μ = M / (M + 1),  M = m_nucleus / m_e.

We then define a **single** radial length scale (effective Bohr radius in a.u.)

  a₀^eff(m, Z, μ) = 1 / (μ Z α_eff(m))

and map it to a **representative s-Gaussian exponent** (variance matching: rms ∼ a₀)

  α_GTO ∼ 1 / (2 (a₀^eff)²)

so future minimal bases can be **fed from (m, Z, μ)** instead of tabulated STO-3G.

Mass ratios are **CODATA/NIST**-style constants (not PDG particle masses); they are the
standard bridge from isotope label → μ. Optional HQIV-derived nuclear masses could
replace M later.

Usage:
  python3 scripts/hqiv_isotope_hydrogenic_scales.py
"""

from __future__ import annotations

import math
from dataclasses import dataclass

# ---------------------------------------------------------------------------
# HQIV ladder (match Lean)


def phi_of_shell(m: int) -> float:
    """`phi_of_shell_closed_form`: φ(m) = 2(m+1)."""
    return 2.0 * (float(m) + 1.0)


ALPHA_HQIV = 3.0 / 5.0  # OctonionicLightCone.alpha
ONE_OVER_ALPHA_BARE = 42.0


def one_over_alpha_eff_at_shell(m: int, c: float = 1.0) -> float:
    ph = phi_of_shell(m)
    return ONE_OVER_ALPHA_BARE * (1.0 + c * ALPHA_HQIV * math.log(ph + 1.0))


def alpha_eff_at_shell(m: int, c: float = 1.0) -> float:
    return 1.0 / one_over_alpha_eff_at_shell(m, c)


def expected_ground_energy_at_shell(m: int, z: int, mu: float, c: float = 1.0) -> float:
    """`Hqiv.Physics.expectedGroundEnergyAtShell`: −μ Z² α_eff² / 2 (Hartree if μ in electron-mass units)."""
    ae = alpha_eff_at_shell(m, c)
    return -mu * float(z * z) * ae * ae / 2.0


# ---------------------------------------------------------------------------
# Isotope → reduced mass (electron mass = 1 a.u.)


# Nucleus mass in atomic units (m_e = 1): M = m_nucleus / m_e (approximate).
# Source order-of-magnitude: CODATA / NIST tables.
NUCLEAR_MASS_OVER_M_E = {
    "¹H": 1836.15267343,  # proton
    "²H": 3670.4829652,  # deuteron
    "³H": 5496.92129,  # triton
}


def reduced_mass_au(m_over_me: float) -> float:
    """μ = m_e M / (m_e + M) with m_e = 1 ⇒ μ = M / (M + 1)."""
    m = float(m_over_me)
    return m / (m + 1.0)


# ---------------------------------------------------------------------------
# Length scale → Gaussian width (s orbital, crude variance match)


def effective_bohr_radius_hqiv_au(m: int, z: int, mu: float, c: float = 1.0) -> float:
    """Length scale ℓ = 1 / (μ Z α_eff(m)) — follows the same α_eff as `expectedGroundEnergyAtShell`."""
    return 1.0 / (mu * float(z) * alpha_eff_at_shell(m, c))


def bohr_radius_standard_au(z: int, mu: float) -> float:
    """Textbook Bohr radius in atomic units: a₀ = 1 / (μ Z) (Coulomb −Z/r, ħ=e=m_e=1)."""
    return 1.0 / (mu * float(z))


def s_gaussian_exponent_from_length(a0: float) -> float:
    """Unnormalized primitive exp(-α r²): match rms radius ~ a₀ ⇒ α ~ 1/(2 a₀²)."""
    if a0 <= 0.0:
        raise ValueError("a0 must be positive")
    return 1.0 / (2.0 * a0 * a0)


@dataclass(frozen=True)
class IsotopeRow:
    label: str
    m_nucleus_over_me: float
    mu: float
    m_shell: int
    alpha_eff: float
    e0_hqiv_hartree: float
    e0_bohr_hartree: float
    a0_standard_au: float
    gto_alpha_from_standard_a0: float
    a0_hqiv_au: float
    gto_alpha_from_hqiv_a0: float


def row(label: str, m_shell: int, z: int = 1, c: float = 1.0) -> IsotopeRow:
    m_over = NUCLEAR_MASS_OVER_M_E[label]
    mu = reduced_mass_au(m_over)
    ae = alpha_eff_at_shell(m_shell, c)
    e_hqiv = expected_ground_energy_at_shell(m_shell, z, mu, c)
    e_bohr = -mu * float(z * z) / 2.0  # n=1 hydrogenic in Hartree a.u. (Coulomb −Z/r)
    a0_std = bohr_radius_standard_au(z, mu)
    ga_std = s_gaussian_exponent_from_length(a0_std)
    a0_hq = effective_bohr_radius_hqiv_au(m_shell, z, mu, c)
    ga_hq = s_gaussian_exponent_from_length(a0_hq)
    return IsotopeRow(
        label=label,
        m_nucleus_over_me=m_over,
        mu=mu,
        m_shell=m_shell,
        alpha_eff=ae,
        e0_hqiv_hartree=e_hqiv,
        e0_bohr_hartree=e_bohr,
        a0_standard_au=a0_std,
        gto_alpha_from_standard_a0=ga_std,
        a0_hqiv_au=a0_hq,
        gto_alpha_from_hqiv_a0=ga_hq,
    )


def main() -> None:
    # Shell m = 4 aligns with `referenceM` / lock-in story in many HQIV modules.
    shells = (0, 1, 4)
    isotopes = ("¹H", "²H", "³H")

    print("HQIV hydrogenic exploratory scales (Z=1)")
    print("  α (lattice) =", ALPHA_HQIV, "  1/α_GUT bare =", ONE_OVER_ALPHA_BARE)
    print()

    for m in shells:
        print(f"--- shell m = {m}  (φ(m) = {phi_of_shell(m):.6g}) ---")
        print(
            f"  α_eff(m) = {alpha_eff_at_shell(m):.12g}   "
            f"1/α_eff = {one_over_alpha_eff_at_shell(m):.6f}"
        )
        # Reference: pure Coulomb in a.u. with α=1 would give E = −μ Z² / 2 at n=1.
        for iso in isotopes:
            r = row(iso, m, z=1)
            print(
                f"  {iso}: μ={r.mu:.9f}  "
                f"E0(HQIV Lean)={r.e0_hqiv_hartree:.6e} Ha  "
                f"E0(Bohr)={r.e0_bohr_hartree:.8f} Ha  "
                f"a0(std)={r.a0_standard_au:.6f}  α_GTO(std)~{r.gto_alpha_from_standard_a0:.6f}"
            )
            print(
                f"        a0(HQIV)=1/(μZα_eff)={r.a0_hqiv_au:.6f}  "
                f"α_GTO(HQIV)~{r.gto_alpha_from_hqiv_a0:.6f}  (see note below)"
            )
        print()

    # Isotope shift at fixed m: ΔE between ¹H and ²H
    m_ref = 4
    h1 = row("¹H", m_ref)
    d2 = row("²H", m_ref)
    t3 = row("³H", m_ref)
    print(f"--- isotope shifts (same shell m={m_ref}, Z=1) ---")
    print(f"  ΔE Bohr:  E(²H)−E(¹H) = {d2.e0_bohr_hartree - h1.e0_bohr_hartree:.10e} Ha")
    print(f"  ΔE Bohr:  E(³H)−E(¹H) = {t3.e0_bohr_hartree - h1.e0_bohr_hartree:.10e} Ha")
    print(f"  ΔE HQIV:  E(²H)−E(¹H) = {d2.e0_hqiv_hartree - h1.e0_hqiv_hartree:.10e} Ha")
    print()
    print(
        "Interpretation:\n"
        "  • E0(Bohr) = −μ Z² / 2 is the standard Hartree-atom hydrogenic ground energy (Z=1).\n"
        "  • E0(HQIV Lean) uses `expectedGroundEnergyAtShell`: α_eff(m) is the shell-modulated\n"
        "    coupling from `BoundStates` (GUT-normalized ladder); it is **not** α≈1 in a.u.,\n"
        "    so |E0(HQIV)| is much smaller than |E0(Bohr)| unless you rescale or reinterpret.\n"
        "  • For **Gaussian/minimal-basis widths** tied to **isotope mass**, use a0(std)=1/(μZ)\n"
        "    and α_GTO(std); μ is the only isotope dependence at this crude level.\n"
        "  • a0(HQIV) shows what happens if you literally use α_eff(m) as the Coulomb strength\n"
        "    in the same length formula — useful for debugging scaling, not for STO replacement yet."
    )


if __name__ == "__main__":
    main()

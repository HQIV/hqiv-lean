"""HQIV cosmological outside-curvature lock-down: wall-clock age / T_CMB / birefringence.

This module locks the *outside-curvature* sector of HQIV (the cosmological
environment the local lattice sits inside) down to a **single external
dimensionful input** -- the FIRAS CMB temperature ``T_CMB = 2.7255 K`` -- with
everything else derived from the two HQIV axioms (discrete null lattice +
informational monogamy):

  * Planck units (T_Pl, t_Pl) from the defining SI constants (G, hbar, c, k_B).
  * The xi <-> shell map: the harmonic temperature ladder ``T(m) = T_Pl/(m+1)``
    fixes the present temperature-ladder depth ``m_T = T_Pl/T_CMB - 1``, and the
    stars-and-bars lattice count ``latticeSimplexCount(m) = (m+2)(m+1)`` gives the
    number of new Planck cells per propagation shell (``~ (T_Pl/T_CMB)^2``).
  * The integer monogamy impedance ``referenceM * q^2 = 4 * 5^2 = 100`` (the
    hadronic export pin and the alpha = 3/5 denominator), which fixes the
    present propagation-shell offset ``m_prop = 1/100`` with **zero age input**.

The cosmic-birefringence observable is ``beta = alpha * log(1 + m_prop)``.

Two independent routes to the present propagation-shell offset:

  Route A (integer impedance, no age input):  m_prop = 1/(referenceM*q^2) = 1/100
           -> beta_A = (3/5) log(1.01) = 0.342 deg
           -> *predicts* the wall-clock age by inverting the lattice count.

  Route B (HQIV-modified CLASS dynamics):      t_wall = 51.2 Gyr (background run)
           -> m_prop_B = (t_wall/t_Pl) / latticeSimplexCount(m_T) = 0.0111
           -> beta_B = (3/5) log(1.0111) = 0.379 deg.

THE LOCK: Route A predicts a wall-clock age (~46 Gyr) from T_CMB + the lattice
count alone; it agrees with the *independently computed* CLASS dynamics value
(51.2 Gyr) to ~90%, tying the birefringence sector to the universe-age sector.
Both beta values bracket the Eskilt & Komatsu 2022 PR4 measurement
(0.342 +/- 0.094 deg) within 1 sigma, while the apparent age (13.8 Gyr) gives
beta = 0.103 deg (-2.55 sigma) -- so the chain selects wall-clock over apparent
age and is not adjustable.

Honest scope: this dressing is a global multiplicative environment factor on the
*absolute* scale; it cancels in dimensionless ratios (m_p/m_e, alpha ratios,
mass ratios), so it does not move those residuals. It sharpens the cosmological
witness chain (beta, age, T_CMB) and the lab-frame environment modulator. The
local-gravity stack (galaxy/solar/Earth, ~1e-7) is recorded for completeness and
is negligible at this level.

Run with::

    python scripts/hqiv_cmb_age_lockdown.py

Writes ``data/hqiv_cmb_age_lockdown_witnesses.json``.

Lean alignment: ``Hqiv/Cosmology/CosmologicalShellLadder.lean`` and
``Hqiv/Geometry/UniverseAge.lean``.
"""

from __future__ import annotations

import json
import math
from pathlib import Path

# --------------------------------------------------------------------------
# Defining / CODATA SI constants (exact defining constants; not fitted).
# --------------------------------------------------------------------------
G = 6.67430e-11           # m^3 kg^-1 s^-2  (CODATA 2018)
HBAR = 1.054571817e-34    # J s             (from defining h)
C_LIGHT = 299792458.0     # m/s             (exact, SI definition)
K_B = 1.380649e-23        # J/K             (exact, SI definition)

# Seconds per Gyr (Julian year).
GYR_S = 3.1556952e16

# --------------------------------------------------------------------------
# Derived Planck units.
# --------------------------------------------------------------------------
T_PLANCK_K = math.sqrt(HBAR * C_LIGHT**5 / G) / K_B   # ~1.4168e32 K
T_PLANCK_S = math.sqrt(HBAR * G / C_LIGHT**5)         # ~5.391e-44 s

# --------------------------------------------------------------------------
# The single external dimensionful input.
# --------------------------------------------------------------------------
T_CMB_K = 2.7255          # FIRAS CMB monopole temperature (K)

# --------------------------------------------------------------------------
# HQIV lattice rationals (fully determined by the two axioms).
# --------------------------------------------------------------------------
ALPHA = 3.0 / 5.0         # sole curvature-imprint exponent (alpha_eq_3_5)
ALPHA_NUM = 3             # numerator of alpha = p/q
ALPHA_DENOM = 5           # denominator q of alpha = p/q
REFERENCE_M = 4           # hadronic export pin (proton-anchor shell)

# HQIV-modified CLASS background-run wall-clock and apparent ages (Gyr).
T_WALL_CLASS_GYR = 51.2
T_APPARENT_GYR = 13.8

# Eskilt & Komatsu 2022 (Planck PR4) cosmic-birefringence measurement (deg).
ESKILT_PR4_CENTRAL_DEG = 0.342
ESKILT_PR4_SIGMA_DEG = 0.094


def lattice_simplex_count(m: float) -> float:
    """``latticeSimplexCount(m) = (m+2)(m+1)`` -- stars-and-bars cell count.

    For large ``m`` this is ``~ m^2``; with ``m = m_T = T_Pl/T_CMB - 1`` it is
    the number of new Planck cells per propagation shell (``~ (T_Pl/T_CMB)^2``).
    """
    return (m + 2.0) * (m + 1.0)


def temperature_ladder_depth(t_obs_k: float = T_CMB_K) -> float:
    """Present temperature-ladder depth ``m_T = T_Pl/T_obs - 1`` (DERIVED map)."""
    return T_PLANCK_K / t_obs_k - 1.0


def cells_per_shell(t_obs_k: float = T_CMB_K) -> float:
    """Planck cells per propagation shell at the observation temperature."""
    return lattice_simplex_count(temperature_ladder_depth(t_obs_k))


def integer_monogamy_impedance() -> int:
    """``referenceM * q^2 = 4 * 25 = 100`` -- the integer monogamy impedance."""
    return REFERENCE_M * ALPHA_DENOM * ALPHA_DENOM


def beta_deg(m_prop: float) -> float:
    """Cosmic-birefringence observable ``beta = alpha * log(1 + m_prop)`` (deg)."""
    return math.degrees(ALPHA * math.log(1.0 + m_prop))


def m_prop_from_wall_clock(t_wall_gyr: float, t_obs_k: float = T_CMB_K) -> float:
    """``m_prop = (t_wall/t_Pl) / latticeSimplexCount(m_T)`` (Candidate B)."""
    t_wall_planck = t_wall_gyr * GYR_S / T_PLANCK_S
    return t_wall_planck / cells_per_shell(t_obs_k)


def wall_clock_age_from_impedance(t_obs_k: float = T_CMB_K) -> float:
    """Wall-clock age (Gyr) *predicted* by the integer impedance (Route A).

    Inverting ``m_prop = (t_wall/t_Pl) / cells_per_shell`` at the integer
    ``m_prop = 1/(referenceM*q^2)`` gives a wall-clock age from T_CMB and the
    derived lattice count alone -- no Friedmann/CLASS input.
    """
    m_prop = 1.0 / integer_monogamy_impedance()
    t_wall_planck = m_prop * cells_per_shell(t_obs_k)
    return t_wall_planck * T_PLANCK_S / GYR_S


def route_a_integer_impedance() -> dict:
    """Route A: integer monogamy impedance, zero age input."""
    m_prop = 1.0 / integer_monogamy_impedance()
    return {
        "route": "A_integer_monogamy_impedance",
        "impedance_referenceM_times_q_squared": integer_monogamy_impedance(),
        "m_prop": m_prop,
        "beta_deg": beta_deg(m_prop),
        "predicted_wall_clock_age_Gyr": wall_clock_age_from_impedance(),
        "age_input": "none (pure integers + T_CMB + lattice count)",
    }


def route_b_class_dynamics() -> dict:
    """Route B: HQIV-modified CLASS background-run wall-clock age."""
    m_prop = m_prop_from_wall_clock(T_WALL_CLASS_GYR)
    return {
        "route": "B_class_dynamics_wall_clock_age",
        "t_wall_Gyr": T_WALL_CLASS_GYR,
        "m_prop": m_prop,
        "beta_deg": beta_deg(m_prop),
        "age_input": "wall-clock age from HQIV-modified CLASS background run",
    }


def apparent_age_falsifier() -> dict:
    """The apparent age (13.8 Gyr) is the falsifier: it gives beta = 0.103 deg."""
    m_prop = m_prop_from_wall_clock(T_APPARENT_GYR)
    b = beta_deg(m_prop)
    sigma = (b - ESKILT_PR4_CENTRAL_DEG) / ESKILT_PR4_SIGMA_DEG
    return {
        "route": "falsifier_apparent_age",
        "t_apparent_Gyr": T_APPARENT_GYR,
        "m_prop": m_prop,
        "beta_deg": b,
        "deviation_sigma": sigma,
        "verdict": "REJECTED: apparent age gives -2.55 sigma; chain selects wall-clock.",
    }


def lock_summary() -> dict:
    """The cosmological lock: cross-validation of the wall-clock age + beta."""
    a = route_a_integer_impedance()
    b = route_b_class_dynamics()
    t_pred = a["predicted_wall_clock_age_Gyr"]
    deviation = abs(t_pred - T_WALL_CLASS_GYR) / T_WALL_CLASS_GYR
    lo = ESKILT_PR4_CENTRAL_DEG - ESKILT_PR4_SIGMA_DEG
    hi = ESKILT_PR4_CENTRAL_DEG + ESKILT_PR4_SIGMA_DEG
    a_in = lo <= a["beta_deg"] <= hi
    b_in = lo <= b["beta_deg"] <= hi
    return {
        "wall_clock_age_integer_route_Gyr": t_pred,
        "wall_clock_age_class_route_Gyr": T_WALL_CLASS_GYR,
        "age_agreement_fraction": 1.0 - deviation,
        "age_deviation_pct": 100.0 * deviation,
        "beta_integer_route_deg": a["beta_deg"],
        "beta_class_route_deg": b["beta_deg"],
        "eskilt_pr4_central_deg": ESKILT_PR4_CENTRAL_DEG,
        "eskilt_pr4_sigma_deg": ESKILT_PR4_SIGMA_DEG,
        "integer_route_within_1sigma": a_in,
        "class_route_within_1sigma": b_in,
        "lock": (
            "Integer monogamy impedance predicts the wall-clock age from T_CMB + "
            "lattice count alone; it agrees with the independent CLASS dynamics "
            "value to ~90%. Both beta routes bracket Eskilt PR4 within 1 sigma; "
            "the apparent age is rejected at -2.55 sigma."
        ),
    }


def local_gravity_note() -> dict:
    """Local-gravity stack (galaxy/solar/Earth): global + ~1e-7, cancels in ratios."""
    return {
        "earth_surface_phi_over_c2": 6.953e-10,
        "solar_at_1AU_phi_over_c2": 9.871e-9,
        "galactic_vc_phi_over_c2": 6.040e-7,
        "full_local_stack_phi_over_c2": 6.146e-7,
        "cmb_dipole_v_over_c": 1.234e-3,
        "scope": (
            "These dress the lab-frame outside modulator (~0.3 ppm) but are a "
            "global multiplicative factor: they cancel exactly in dimensionless "
            "ratios (m_p/m_e, alpha ratios), and are 4 orders below the ~0.2% "
            "residuals. Recorded for completeness; negligible for the cosmo lock."
        ),
    }


def build_witnesses() -> dict:
    """Assemble the full witness bundle for the cosmological lock-down."""
    return {
        "title": "HQIV cosmological outside-curvature lock-down (age / T_CMB / birefringence)",
        "single_external_dimensionful_input": {
            "name": "T_CMB",
            "value_K": T_CMB_K,
            "source": "FIRAS CMB monopole",
        },
        "derived_constants": {
            "T_Planck_K": T_PLANCK_K,
            "t_Planck_s": T_PLANCK_S,
            "alpha": ALPHA,
            "referenceM": REFERENCE_M,
            "alpha_denominator_q": ALPHA_DENOM,
        },
        "xi_to_shell_map": {
            "temperature_ladder_depth_m_T": temperature_ladder_depth(),
            "cells_per_shell_latticeSimplexCount": cells_per_shell(),
            "note": "m_T = T_Pl/T_CMB - 1; cells/shell = (m_T+2)(m_T+1) ~ (T_Pl/T_CMB)^2 (DERIVED).",
        },
        "route_A_integer_impedance": route_a_integer_impedance(),
        "route_B_class_dynamics": route_b_class_dynamics(),
        "falsifier_apparent_age": apparent_age_falsifier(),
        "lock": lock_summary(),
        "local_gravity_stack": local_gravity_note(),
    }


def _fmt(witnesses: dict) -> str:
    lock = witnesses["lock"]
    a = witnesses["route_A_integer_impedance"]
    b = witnesses["route_B_class_dynamics"]
    f = witnesses["falsifier_apparent_age"]
    xi = witnesses["xi_to_shell_map"]
    lines = [
        "HQIV cosmological outside-curvature lock-down",
        "=" * 60,
        f"Single external input : T_CMB = {T_CMB_K} K (FIRAS)",
        f"Derived Planck units  : T_Pl = {T_PLANCK_K:.4e} K, t_Pl = {T_PLANCK_S:.4e} s",
        "",
        "xi <-> shell map (DERIVED from the lattice axiom):",
        f"  m_T (ladder depth)  = {xi['temperature_ladder_depth_m_T']:.4e}",
        f"  cells / shell       = {xi['cells_per_shell_latticeSimplexCount']:.4e}",
        "",
        "Route A  (integer impedance referenceM*q^2 = 100, NO age input):",
        f"  m_prop = {a['m_prop']:.5f}   beta = {a['beta_deg']:.4f} deg",
        f"  -> predicted wall-clock age = {a['predicted_wall_clock_age_Gyr']:.2f} Gyr",
        "",
        "Route B  (HQIV-modified CLASS dynamics, t_wall = 51.2 Gyr):",
        f"  m_prop = {b['m_prop']:.5f}   beta = {b['beta_deg']:.4f} deg",
        "",
        f"Falsifier (apparent age 13.8 Gyr): beta = {f['beta_deg']:.4f} deg "
        f"({f['deviation_sigma']:.2f} sigma) -> REJECTED",
        "",
        "LOCK:",
        f"  wall-clock age: integer route {lock['wall_clock_age_integer_route_Gyr']:.1f} Gyr "
        f"vs CLASS {lock['wall_clock_age_class_route_Gyr']:.1f} Gyr "
        f"({lock['age_agreement_fraction']*100:.1f}% agreement)",
        f"  Eskilt PR4 = {lock['eskilt_pr4_central_deg']} +/- {lock['eskilt_pr4_sigma_deg']} deg; "
        f"both routes within 1 sigma: "
        f"A={lock['integer_route_within_1sigma']}, B={lock['class_route_within_1sigma']}",
    ]
    return "\n".join(lines)


def main() -> None:
    witnesses = build_witnesses()
    print(_fmt(witnesses))
    out = Path(__file__).resolve().parents[1] / "data" / "hqiv_cmb_age_lockdown_witnesses.json"
    out.write_text(json.dumps(witnesses, indent=2))
    print(f"\nWrote {out}")


if __name__ == "__main__":
    main()

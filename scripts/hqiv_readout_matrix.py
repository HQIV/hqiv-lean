#!/usr/bin/env python3
"""
HQIV readout matrix — the bra/ket substrate of the diatomic spectroscopy sector.

Companion to ``papers/readout_matrices/`` and the molecular-spectroscopy engine
``hqiv_molecular_spectroscopy``.  The thesis is structural, not a new number:

  * The conserved object is the lattice-simplex mode-state |ψ⟩ (the contact
    shell triplet / accumulated curvature), shared with the finite-mode
    Kirchhoff blackbody.
  * Each geometric-core readout is a *bra* ⟨r_O| and the observable is the
    matrix element ⟨r_O|ψ⟩.  In log-space the rovibrational SI constants are
    an exact integer/half-integer TRANSFER MATRIX T over four log-primaries
    (Ceff, r_e, D_e, μ).
  * The substrate is LOSSLESS: T is invertible on its rank, so HQIV's
    primaries can be read straight back out of a measured spectrum.
  * The LEFT-null space of T gives parameter-free, geometry-independent
    "conservation laws" (Kirchhoff loop laws) the observables must satisfy.

Everything below is *derived from / verified against* the engine's own outputs;
no constant is fitted.  Run as a script for the audit table, or import the
functions.  Reproduces the Tables of ``hqiv_physical_readouts_as_matrices.tex``.
"""
from __future__ import annotations

import math
from dataclasses import dataclass

import numpy as np

import hqiv_molecular_spectroscopy as ms

# Physical constants (SI), only for the rotational inversion B_e -> r_e.
_HBAR = 1.054571817e-34
_C_CM = 2.99792458e10
_AMU = 1.66053907e-27
_CM1_PER_EV = 8065.543937

# ---------------------------------------------------------------------------
# The transfer matrix T (rows = observables, cols = log-primaries).
# ---------------------------------------------------------------------------
PRIMARIES = ("log Ceff", "log r_e", "log D_e", "log mu")
TRANSFER_MATRIX: dict[str, tuple[float, float, float, float]] = {
    #            log Ceff  log r_e  log D_e  log mu
    "a*r_e":      (1.0,    0.0,     0.0,    0.0),
    "omega_e":    (1.0,   -1.0,     0.5,   -0.5),
    "B_e":        (0.0,   -2.0,     0.0,   -1.0),
    "omega_e*x_e":(2.0,   -2.0,     0.0,   -1.0),
    "D_J":        (-2.0,  -4.0,    -1.0,   -2.0),
}

# Integer left-null vectors of T: combinations of observable rows that depend on
# NO primary, i.e. the parameter-free conservation ("loop") laws.  Each maps an
# observable name to its integer exponent; the relation is  ∏ obs^exp = const.
CONSERVATION_LAWS: dict[str, dict[str, int]] = {
    # Kratzer: D_J = 4 B_e^3 / omega_e^2  (const = 4)
    "kratzer": {"D_J": 1, "B_e": -3, "omega_e": 2},
    # Morse loop: omega_e*x_e = B_e * (a*r_e)^2  (const = 1)
    "morse_loop": {"omega_e*x_e": 1, "B_e": -1, "a*r_e": -2},
}


@dataclass(frozen=True)
class ReadoutBundle:
    """Engine outputs for one molecule, in the (observable, primary) basis."""

    name: str
    primaries: dict[str, float]   # Ceff, r_e, D_e, mu (linear, not log)
    observables: dict[str, float]  # a*r_e, omega_e, B_e, omega_e*x_e, D_J


def _engine_rows() -> list[ReadoutBundle]:
    out: list[ReadoutBundle] = []
    for bench in ms.diatomic_benchmarks():
        r = ms.evaluate_diatomic(bench)
        if r.omega_e_curvature_cm1 <= 0:
            continue
        out.append(
            ReadoutBundle(
                name=r.name,
                primaries={
                    "Ceff": r.contact_curvature_effective,
                    "r_e": r.r_e_angstrom,
                    "D_e": r.D_e_ev,
                    "mu": r.reduced_mass_amu,
                },
                observables={
                    "a*r_e": r.morse_a_re,
                    "omega_e": r.omega_e_cm1,
                    "B_e": r.B_e_cm1,
                    "omega_e*x_e": r.omega_e_xe_cm1,
                    "D_J": r.D_J_cm1,
                },
            )
        )
    return out


def recover_transfer_matrix() -> dict[str, np.ndarray]:
    """Least-squares recover T from the engine's outputs alone (black-box check).

    Returns {observable: coefficient row over PRIMARIES}; should equal
    ``TRANSFER_MATRIX`` to machine precision.
    """
    rows = _engine_rows()
    design = np.array(
        [[math.log(b.primaries[p.split()[1]]) for p in PRIMARIES] + [1.0] for b in rows]
    )
    recovered: dict[str, np.ndarray] = {}
    for obs in TRANSFER_MATRIX:
        y = np.array([math.log(b.observables[obs]) for b in rows])
        coef, *_ = np.linalg.lstsq(design, y, rcond=None)
        recovered[obs] = coef[:4]
    return recovered


def conservation_law_constants() -> dict[str, dict[str, float]]:
    """Evaluate each conservation law across the suite; the value must be constant."""
    rows = _engine_rows()
    out: dict[str, dict[str, float]] = {}
    for law_name, law in CONSERVATION_LAWS.items():
        vals = []
        for b in rows:
            s = sum(exp * math.log(b.observables[k]) for k, exp in law.items())
            vals.append(math.exp(s))
        arr = np.array(vals)
        out[law_name] = {
            "const": float(arr.mean()),
            "relative_spread": float(arr.std() / arr.mean()),
        }
    return out


def r_e_from_B_e(b_e_cm1: float, reduced_mass_amu: float) -> float:
    """Lossless rotational inversion: B_e = ħ/(4π c μ r_e²)  ->  r_e [Å]."""
    return math.sqrt(_HBAR / (4 * math.pi * _C_CM * b_e_cm1 * reduced_mass_amu * _AMU)) * 1e10


def morse_range_from_spectrum(omega_e_xe_cm1: float, b_e_cm1: float) -> float:
    """Lossless anharmonic inversion via the Morse loop law: a·r_e = √(ω_e x_e / B_e)."""
    return math.sqrt(omega_e_xe_cm1 / b_e_cm1)


def well_depth_from_spectrum(omega_e_cm1: float, omega_e_xe_cm1: float) -> float:
    """Lossless binding inversion (Morse): D_e = ω_e² / (4 ω_e x_e) [eV]."""
    return (omega_e_cm1 ** 2 / (4.0 * omega_e_xe_cm1)) / _CM1_PER_EV


def lossless_inversion_table() -> list[dict[str, float]]:
    """Read HQIV primaries back out of measured (NIST) spectra and compare."""
    rows = _engine_rows()
    table: list[dict[str, float]] = []
    for b in rows:
        e = ms.NIST_COMPARISON.get(b.name)
        if not e:
            continue
        mu = b.primaries["mu"]
        table.append(
            {
                "name": b.name,
                "r_e_nist": e["r_e"],
                "r_e_from_Be": r_e_from_B_e(e["B_e"], mu),
                "r_e_hqiv": b.primaries["r_e"],
                "are_from_spec": morse_range_from_spectrum(e["omega_e_xe"], e["B_e"]),
                "are_hqiv": b.observables["a*r_e"],
                "De_nist": e["D_e"],
                "De_from_spec": well_depth_from_spectrum(e["omega_e"], e["omega_e_xe"]),
                "De_hqiv": b.primaries["D_e"],
            }
        )
    return table


def _main() -> None:
    print("HQIV READOUT MATRIX  —  bra/ket substrate of diatomic spectroscopy\n")

    print("Transfer matrix T (claimed vs least-squares recovered from engine):")
    print(f"  {'observable':12s}  {'claimed':>22s}   max|recovered-claimed|")
    rec = recover_transfer_matrix()
    worst = 0.0
    for obs, row in TRANSFER_MATRIX.items():
        d = float(np.max(np.abs(rec[obs] - np.array(row))))
        worst = max(worst, d)
        print(f"  {obs:12s}  {str([round(x,3) for x in row]):>22s}   {d:.2e}")
    print(f"  -> overall recovery residual: {worst:.2e}\n")

    print("Conservation (Kirchhoff loop) laws — left-null space of T:")
    for name, info in conservation_law_constants().items():
        print(f"  {name:11s}: const = {info['const']:.6g}  "
              f"(relative spread {info['relative_spread']:.1e})")
    print()

    print("Lossless inversion — HQIV primaries recovered from measured spectra:")
    print(f"  {'mol':5s} | {'r_e  NIST  spec  HQIV':24s} | "
          f"{'a*r_e spec  HQIV':16s} | {'D_e[eV] NIST spec HQIV':24s}")
    for t in lossless_inversion_table():
        print(f"  {t['name']:5s} | "
              f"{t['r_e_nist']:7.3f}{t['r_e_from_Be']:6.3f}{t['r_e_hqiv']:6.3f}{'':5s}| "
              f"{t['are_from_spec']:7.3f}{t['are_hqiv']:7.3f}{'':2s} | "
              f"{t['De_nist']:7.2f}{t['De_from_spec']:7.2f}{t['De_hqiv']:7.2f}")


if __name__ == "__main__":
    _main()

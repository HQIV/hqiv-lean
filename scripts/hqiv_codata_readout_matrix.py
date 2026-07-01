#!/usr/bin/env python3
"""
HQIV CODATA readout matrix — the atomic fundamental-constant web as ONE
integer-power linear map, the fundamental-constant analogue of the diatomic
readout matrix (``hqiv_readout_matrix``, ``papers/readout_matrices/``).

Thesis (same as the molecular sector, lifted to CODATA): a physical readout is
a row of a matrix on a conserved state.  Here the "state" is the log of a tiny
physical core

      |psi> = ( log alpha , log m_e , log c , log hbar , log e ),

of which only TWO entries are genuine measured/derived physics — the
fine-structure constant ``alpha`` and the electron mass ``m_e`` — because
c, hbar (h), e are *exact* SI defining constants since 2019.  Every standard
atomic CODATA constant (Bohr radius, Compton wavelength, classical electron
radius, Rydberg constant, Hartree energy, Bohr magneton, Thomson cross
section, ...) is then an exact INTEGER-POWER monomial in these primaries:

      log(const) = T_row . |psi> + log(prefactor),

with the prefactor only ever 1, 2*pi, 1/(4*pi), 1/2, or 8*pi/3.  The matrix
reproduces CODATA to the precision of the typed reference values (~1e-9), and
its LEFT-null space is the famous dimensionless ladder

      lambdabar_C / a0 = alpha,   r_e / a0 = alpha^2,   r_e * R_inf = alpha^3/(4 pi),
      sigma_T / r_e^2 = 8 pi / 3   (a PURE number — no physical input at all).

HQIV consequence: the entire atomic-constant web is *forced* once HQIV supplies
its two inputs.  The three alpha-power ratios above need ONLY alpha, so HQIV's
own alpha(0) readout (the IR/Thomson running endpoint ~1/136.8) predicts them
directly, with no mass anchor; sigma_T/r_e^2 needs nothing.  What HQIV does NOT
yet close (m_e from first principles, exact alpha = 1/137.036) is exactly the
non-prefactor content of the two load-bearing primaries — the matrix makes the
location of the genuine physics input unambiguous.
"""
from __future__ import annotations

import math
from dataclasses import dataclass

import numpy as np

# --- physical core (primaries).  c, hbar(h), e are EXACT 2019-SI defining
#     constants; only alpha and m_e carry measured/derived physics. -----------
ALPHA_CODATA = 7.2973525693e-3        # fine-structure constant (dimensionless)
M_E_CODATA = 9.1093837015e-31         # electron mass (kg)
C_SI = 299792458.0                    # speed of light (m/s), exact
HBAR_SI = 1.054571817e-34             # reduced Planck (J s)  (h exact)
E_SI = 1.602176634e-19                # elementary charge (C), exact

PRIMARIES = ("alpha", "m_e", "c", "hbar", "e")

# Each readout: integer powers over PRIMARIES, plus an analytic prefactor.
READOUT_MATRIX: dict[str, tuple[tuple[int, int, int, int, int], float, str]] = {
    #              alpha m_e  c  hbar e   prefactor          unit
    "a0":         ((-1, -1, -1,  1, 0), 1.0,                "m"),
    "lambdabar_C":((0, -1, -1,  1, 0), 1.0,                 "m"),
    "lambda_C":   ((0, -1, -1,  1, 0), 2 * math.pi,         "m"),
    "r_e":        ((1, -1, -1,  1, 0), 1.0,                 "m"),
    "R_inf":      ((2,  1,  1, -1, 0), 1.0 / (4 * math.pi), "1/m"),
    "nu_Ry":      ((2,  1,  2, -1, 0), 1.0 / (4 * math.pi), "Hz"),
    "E_h":        ((2,  1,  2,  0, 0), 1.0,                 "J"),
    "E_h_eV":     ((2,  1,  2,  0, -1), 1.0,                "eV"),
    "mu_B":       ((0, -1,  0,  1, 1), 0.5,                 "J/T"),
    "sigma_T":    ((2, -2, -2,  2, 0), 8 * math.pi / 3.0,   "m^2"),
}

# CODATA reference values (for verification only — never an input).
CODATA_REFERENCE: dict[str, float] = {
    "a0": 5.29177210903e-11,
    "lambdabar_C": 3.8615926796e-13,
    "lambda_C": 2.42631023867e-12,
    "r_e": 2.8179403262e-15,
    "R_inf": 10973731.568160,
    "nu_Ry": 3.2898419602508e15,
    "E_h": 4.3597447222071e-18,
    "E_h_eV": 27.211386245988,
    "mu_B": 9.2740100783e-24,
    "sigma_T": 6.6524587321e-29,
}

# Dimensionless loop laws = left-null combinations of the readout rows.
# value of each combination is a pure prefactor (no primary dependence at all
# beyond the stated alpha power).
LOOP_LAWS: dict[str, dict[str, int]] = {
    "lambdabar_C/a0 = alpha":   {"lambdabar_C": 1, "a0": -1},   # -> alpha^1
    "r_e/a0 = alpha^2":         {"r_e": 1, "a0": -1},           # -> alpha^2
    "r_e*R_inf = alpha^3/(4pi)":{"r_e": 1, "R_inf": 1},         # -> alpha^3 (prefactor 1/4pi)
    "sigma_T/r_e^2 = 8pi/3":    {"sigma_T": 1, "r_e": -2},      # -> pure number
}


def _state(alpha: float = ALPHA_CODATA, m_e: float = M_E_CODATA) -> np.ndarray:
    return np.array([math.log(alpha), math.log(m_e),
                     math.log(C_SI), math.log(HBAR_SI), math.log(E_SI)])


def readout(name: str, alpha: float = ALPHA_CODATA, m_e: float = M_E_CODATA) -> float:
    """Evaluate one CODATA constant as prefactor * exp(row . state)."""
    exps, pref, _unit = READOUT_MATRIX[name]
    return pref * math.exp(float(np.dot(exps, _state(alpha, m_e))))


def reproduce_codata() -> dict[str, dict[str, float]]:
    """Every constant from the matrix vs CODATA reference (rel. error)."""
    out: dict[str, dict[str, float]] = {}
    for name in READOUT_MATRIX:
        val = readout(name)
        ref = CODATA_REFERENCE[name]
        out[name] = {"matrix": val, "codata": ref, "rel_err": abs(val - ref) / ref}
    return out


def loop_law_residual(law: dict[str, int]) -> np.ndarray:
    """Net primary-exponent vector of a loop-law combination (should be alpha-only)."""
    v = np.zeros(len(PRIMARIES))
    for name, k in law.items():
        v = v + k * np.array(READOUT_MATRIX[name][0], float)
    return v


def matrix_rank() -> int:
    mat = np.array([READOUT_MATRIX[n][0] for n in READOUT_MATRIX], float)
    return int(np.linalg.matrix_rank(mat, tol=1e-9))


@dataclass(frozen=True)
class AlphaForcedRatio:
    name: str
    alpha_power: int
    prefactor: float
    codata: float


# The three ratios that depend on alpha ALONE (no mass anchor): HQIV's alpha
# readout predicts these directly.
ALPHA_FORCED_RATIOS: tuple[AlphaForcedRatio, ...] = (
    AlphaForcedRatio("lambdabar_C/a0", 1, 1.0, ALPHA_CODATA),
    AlphaForcedRatio("r_e/a0", 2, 1.0, ALPHA_CODATA ** 2),
    AlphaForcedRatio("r_e*R_inf", 3, 1.0 / (4 * math.pi), ALPHA_CODATA ** 3 / (4 * math.pi)),
)


def alpha_forced_from_hqiv(inv_alpha_hqiv: float) -> list[dict[str, float]]:
    """Predict the alpha-only CODATA ratios from an HQIV 1/alpha readout."""
    a = 1.0 / inv_alpha_hqiv
    rows: list[dict[str, float]] = []
    for r in ALPHA_FORCED_RATIOS:
        pred = r.prefactor * a ** r.alpha_power
        rows.append({
            "name": r.name,
            "alpha_power": r.alpha_power,
            "hqiv": pred,
            "codata": r.codata,
            "rel_err": abs(pred - r.codata) / r.codata,
        })
    return rows


def _main() -> None:
    print("HQIV CODATA READOUT MATRIX — atomic constants as one integer-power map\n")
    print("Two physical inputs: alpha, m_e.  c, hbar, e are exact SI definitions.\n")

    print(f"{'constant':12s}{'matrix':>16s}{'CODATA':>16s}{'rel err':>11s}  unit")
    worst = 0.0
    for name, info in reproduce_codata().items():
        worst = max(worst, info["rel_err"])
        unit = READOUT_MATRIX[name][2]
        print(f"{name:12s}{info['matrix']:16.6e}{info['codata']:16.6e}"
              f"{info['rel_err']:11.1e}  {unit}")
    print(f"  -> worst rel err (typed-reference limited): {worst:.1e}")
    print(f"  -> matrix rank {matrix_rank()} over {len(PRIMARIES)} primaries"
          f" => {len(READOUT_MATRIX) - matrix_rank()} loop laws\n")

    print("Loop laws (left-null space) — net primary exponents [alpha,m_e,c,hbar,e]:")
    for desc, law in LOOP_LAWS.items():
        print(f"  {desc:30s} -> {loop_law_residual(law).astype(int).tolist()}")
    print()

    try:
        import hqiv_alpha_ir_running as ir
        inv_ew = ir.ew_brace_inv_alpha()
        inv_thom = ir.bare_inv_alpha_at_shell(20)
        print("alpha-FORCED CODATA ratios from HQIV's own alpha readout "
              "(no mass anchor):")
        for label, inv in (("EW brace 1/a=%.2f" % inv_ew, inv_ew),
                           ("IR/Thomson 1/a=%.2f" % inv_thom, inv_thom)):
            print(f"  [{label}]")
            for row in alpha_forced_from_hqiv(inv):
                print(f"    {row['name']:14s} (a^{row['alpha_power']}): "
                      f"HQIV={row['hqiv']:.6e}  CODATA={row['codata']:.6e}  "
                      f"rel={row['rel_err']:.2%}")
    except Exception as exc:  # pragma: no cover - alpha module optional
        print(f"(HQIV alpha readout unavailable: {exc})")


if __name__ == "__main__":
    _main()

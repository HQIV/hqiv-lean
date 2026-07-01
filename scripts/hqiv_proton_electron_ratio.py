#!/usr/bin/env python3
"""
HQIV proton-to-electron mass ratio as a DERIVED readout (no CODATA 1836 injected).

Background.  The atom pipeline historically hard-coded the CODATA ratio
``1836.15267343`` as a "charge-ratio bridge" to get the electron mass from the
proton lock-in.  That is the one place the atomic sector smuggled in an external
constant.  This module replaces it with a genuine HQIV readout: the ratio of two
masses that the framework itself charts, with NO PDG lepton mass and NO CODATA
ratio anywhere in the formula.

Construction (both masses are HQIV outputs):

  * Proton  m_p  — the proton lock-in scale witness at referenceM=4
                   (938.272 MeV; the framework's single hadronic anchor).
  * Electron m_e — the TUFT winding-n=1 sector-determinant on the vev->T8 chart,
                   `leptonMassSpectrum_at_xi_from_vev_T8_MeV` evaluated at the
                   lock-in coordinate ξ=5.  This is the geometric lepton scalar
                       M_n = (n+1)·exp(a·n − ζ(3)·n²)·exp(n·α/6)   (n=1)
                   times the Hopf spectral scale √(2π)·v·κ₆, with α the *derived*
                   O–Maxwell brace constant.  No PDG electron mass enters.

      m_p / m_e  =  938.272 / 0.5099  =  1840.13   (CODATA 1836.15267, +0.22%).

Honesty / scope.  This is a TWO-witness readout: the proton lock-in (MeV) and the
electroweak vev (MeV) are independent dimensionful anchors, so the ratio is not
yet a *single-anchor*, pure-geometry number — collapsing the two anchors (deriving
the vev↔proton scale ratio from the lattice) remains the open problem.  But it is
a real, falsifiable HQIV prediction of a dimensionless constant, and it removes the
only hard-coded CODATA value in the atomic sector.  The +0.22% residual is exactly
the TUFT electron's 0.99784× ratio to the PDG electron mass.
"""
from __future__ import annotations

from dataclasses import dataclass

import hqiv_scale_witness as sw

# CODATA value — comparison guardrail only, NEVER used in a derivation here.
CODATA_PROTON_ELECTRON_RATIO = 1836.15267343
CODATA_ELECTRON_MASS_MEV = 0.51099895000


def derived_electron_mass_mev() -> float:
    """Electron mass from the TUFT vev->T8 winding-n=1 chart (PDG-free)."""
    import hqiv_tuft_mass_spectrum_pdg_eval as tuft

    # (τ, μ, e) at the lock-in coordinate; electron is the n=1 (last) entry.
    return tuft.lepton_mass_spectrum_at_xi_mev(tuft.XI_LOCKIN)[2]


def proton_mass_mev(proton_mev: float | None = None) -> float:
    if proton_mev is None:
        proton_mev = sw.load_witness_bundle().derived_proton_mass_mev
    return proton_mev


def derived_proton_to_electron_ratio(proton_mev: float | None = None) -> float:
    """m_p / m_e from two HQIV charts (proton lock-in / TUFT lepton vev->T8)."""
    return proton_mass_mev(proton_mev) / derived_electron_mass_mev()


@dataclass(frozen=True)
class ProtonElectronReadout:
    proton_mev: float
    electron_mev: float
    ratio: float
    codata_ratio: float
    codata_electron_mev: float

    @property
    def ratio_rel_err(self) -> float:
        return abs(self.ratio - self.codata_ratio) / self.codata_ratio

    @property
    def electron_rel_err(self) -> float:
        return abs(self.electron_mev - self.codata_electron_mev) / self.codata_electron_mev


def readout(proton_mev: float | None = None) -> ProtonElectronReadout:
    p = proton_mass_mev(proton_mev)
    e = derived_electron_mass_mev()
    return ProtonElectronReadout(
        proton_mev=p,
        electron_mev=e,
        ratio=p / e,
        codata_ratio=CODATA_PROTON_ELECTRON_RATIO,
        codata_electron_mev=CODATA_ELECTRON_MASS_MEV,
    )


def _main() -> None:
    r = readout()
    print("HQIV proton-to-electron mass ratio — derived readout (no CODATA 1836)\n")
    print(f"  proton   m_p = {r.proton_mev:.5f} MeV   (lock-in scale witness, referenceM=4)")
    print(f"  electron m_e = {r.electron_mev:.6f} MeV   (TUFT vev->T8, winding n=1)")
    print(f"               PDG {r.codata_electron_mev:.6f} MeV  "
          f"(ratio {r.electron_mev / r.codata_electron_mev:.5f}, "
          f"{r.electron_rel_err:.3%})\n")
    print(f"  m_p / m_e (HQIV)   = {r.ratio:.5f}")
    print(f"  m_p / m_e (CODATA) = {r.codata_ratio:.5f}")
    print(f"  relative error     = {r.ratio_rel_err:.3%}")
    print("\n  note: two-witness readout (proton MeV + EW vev); single-anchor"
          "\n        (proton-only) closed form is the open target.")


if __name__ == "__main__":
    _main()

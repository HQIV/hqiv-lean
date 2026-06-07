#!/usr/bin/env python3
"""
Electroweak boson readout on the TUFT dynamic chart.

Mirrors `Hqiv/Physics/TuftElectroweakBosonReadout.lean`:
  • W  — M_W_closure × √(v_lock/v_gauge) × heavy-gap scale (primary; Lean `tuftMW_atXi_GeV`)
  • Z  — W / cos θ_W with geometric sin²θ_W (weak vs EM Gauss shells)
  • H  — √(2λ) v(ξ) + γ·(1/Θ_local) with derived quartic λ

Run:
  python3 scripts/hqiv_tuft_electroweak_boson_readout.py
"""

from __future__ import annotations

import math
from dataclasses import dataclass

import cubic_phase_relax_probe as cpr

ALPHA = cpr.ALPHA
GAMMA = cpr.GAMMA
REFERENCE_M = cpr.REFERENCE_M
EM_GAUSS_SHELL = REFERENCE_M - 1
EW_PHI_SHELL = REFERENCE_M + 1
XI_LOCKIN = 5.0
ELECTROWEAK_VEV_GEV = 246_219.65 / 1000.0

# Lean `boson_witness_*` closed forms (GeV)
M_W_DERIVED_GEV = 392.0 / 5.0
M_Z_NAIVE_GEV = 2744.0 / 25.0
M_H_DERIVED_GEV = 588.0 / 5.0
GAUGE_VEV_AT_LOCKIN_GEV = M_W_DERIVED_GEV / (1.0 / 3.0)  # tuftGaugeVevAtLockin_GeV = 1176/5

PDG_GEV = {
    "W": 80.379,
    "Z": 91.1876,
    "H": 125.11,
}


def sin2_theta_w_triality() -> float:
    g2 = 1.0 / 3.0
    g1 = GAMMA / 3.0
    return (g1 * g1) / (g1 * g1 + g2 * g2)


def sin2_theta_w_geometric_lockin() -> float:
    """Lean `sin2ThetaWGeometricLockin`."""
    imprint = cpr.geometric_resonance_step(EW_PHI_SHELL, EM_GAUSS_SHELL)
    return sin2_theta_w_triality() * imprint


def cos_theta_w_geometric_lockin() -> float:
    s2 = sin2_theta_w_geometric_lockin()
    if s2 >= 1.0:
        raise ValueError(f"sin²θ_W must be < 1, got {s2}")
    return math.sqrt(1.0 - s2)


def tuft_electroweak_scale_at_xi(xi: float) -> float:
    """Lean `tuftElectroweakScaleAtXi`."""
    import hqiv_tuft_mass_spectrum_pdg_eval as tmse

    gap = tmse.heavy_lepton_gap_at_xi(xi)
    gap_lock = tmse.heavy_lepton_gap_at_xi(XI_LOCKIN)
    return gap / gap_lock


def tuft_vev_at_xi_gev(xi: float = XI_LOCKIN) -> float:
    import hqiv_tuft_mass_spectrum_pdg_eval as tmse

    return tmse.tuft_vev_at_xi_mev(xi) / 1000.0


def higgs_quartic_lambda_gauge_witness() -> float:
    """Lean `higgsQuarticLambdaGaugeWitness`."""
    return M_H_DERIVED_GEV**2 / (2.0 * GAUGE_VEV_AT_LOCKIN_GEV**2)


def tuft_vev_sqrt_bridge_lockin() -> float:
    """Lean `tuftVevSqrtBridgeLockin`: sqrt(v_lock / v_gauge)."""
    return math.sqrt(ELECTROWEAK_VEV_GEV / GAUGE_VEV_AT_LOCKIN_GEV)


def tuft_mw_pinned_at_xi_gev(xi: float = XI_LOCKIN) -> float:
    """Lean `tuftMW_pinnedAtXi_GeV`: g_SU2 * v(ξ)."""
    return (1.0 / 3.0) * tuft_vev_at_xi_gev(xi)


def tuft_mh_scalar_monogamy_localization_gev() -> float:
    """Lean `tuftMH_scalarMonogamyLocalization_GeV`: γ · (1/Θ_local)."""
    return GAMMA * 6.0  # bosonLocalizationEnergyLowerBound = 6 GeV


def tuft_mw_at_xi_gev(xi: float = XI_LOCKIN) -> float:
    """Lean `tuftMW_atXi_GeV`: M_W_closure × scale × √(v_lock/v_gauge)."""
    return (
        M_W_DERIVED_GEV
        * tuft_electroweak_scale_at_xi(xi)
        * tuft_vev_sqrt_bridge_lockin()
    )


def tuft_mz_at_xi_gev(xi: float = XI_LOCKIN) -> float:
    return tuft_mw_at_xi_gev(xi) / cos_theta_w_geometric_lockin()


def tuft_mh_scalar_closure_at_xi_gev(xi: float = XI_LOCKIN) -> float:
    """Lean `tuftMH_scalarClosure_atXi_GeV` (diagnostic)."""
    return M_H_DERIVED_GEV * tuft_electroweak_scale_at_xi(xi)


def tuft_mh_at_xi_gev(xi: float = XI_LOCKIN) -> float:
    """Lean `tuftMH_atXi_GeV`: √(2λ) v + γ·(1/Θ_local)."""
    lam = higgs_quartic_lambda_gauge_witness()
    v = tuft_vev_at_xi_gev(xi)
    return math.sqrt(2.0 * lam) * v + tuft_mh_scalar_monogamy_localization_gev()


@dataclass(frozen=True)
class BosonReadoutRow:
    name: str
    model_gev: float
    pdg_gev: float
    lean_anchor: str

    @property
    def ratio(self) -> float:
        return self.model_gev / self.pdg_gev


def boson_readout_at_xi(xi: float = XI_LOCKIN) -> list[BosonReadoutRow]:
    return [
        BosonReadoutRow("W", tuft_mw_at_xi_gev(xi), PDG_GEV["W"], "tuftMW_atXi_GeV"),
        BosonReadoutRow("Z", tuft_mz_at_xi_gev(xi), PDG_GEV["Z"], "tuftMZ_atXi_GeV"),
        BosonReadoutRow("H", tuft_mh_at_xi_gev(xi), PDG_GEV["H"], "tuftMH_atXi_GeV"),
    ]


def main() -> None:
    s2 = sin2_theta_w_geometric_lockin()
    print(f"Electroweak boson readout @ ξ_lock = {XI_LOCKIN:g}")
    print(f"  sin²θ_W geometric (EW shell {EW_PHI_SHELL}, EM Gauss {EM_GAUSS_SHELL}): {s2:.6f}")
    print(f"  sin²θ_W PDG: {0.23122:.6f}")
    print(f"  M_Z naive (g_SU2+g_U1): {M_Z_NAIVE_GEV:.3f} GeV  ratio {M_Z_NAIVE_GEV/PDG_GEV['Z']:.4f}")
    print(
        f"  H scalar closure (diagnostic): {tuft_mh_scalar_closure_at_xi_gev():.3f} GeV  "
        f"ratio {tuft_mh_scalar_closure_at_xi_gev()/PDG_GEV['H']:.4f}"
    )
    print()
    print(f"  {'boson':6} {'model [GeV]':>12} {'PDG [GeV]':>12} {'ratio':>8}")
    for row in boson_readout_at_xi():
        print(f"  {row.name:6} {row.model_gev:12.3f} {row.pdg_gev:12.3f} {row.ratio:8.4f}")
        print(f"         Lean: {row.lean_anchor}")


if __name__ == "__main__":
    main()

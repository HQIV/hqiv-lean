#!/usr/bin/env python3
"""
Single-scale witness bundle for HQIV Python pipelines.

Default witness: proton_lockin — derived proton/neutron/boson masses from
`data/hqiv_witnesses.json` (Lean `export_witnesses.lean`). CODATA α and CMB
horizon quantities are comparison targets, not simultaneous solve anchors.

Run:
  python3 scripts/hqiv_scale_witness.py
  python3 scripts/hqiv_scale_witness.py --witness codata_alpha
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal

ScaleWitness = Literal["proton_lockin", "codata_alpha", "cmb_now"]
DEFAULT_SCALE_WITNESS: ScaleWitness = "proton_lockin"

_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_WITNESS_JSON = _ROOT / "data" / "hqiv_witnesses.json"

# Comparison layer (not active anchors under proton_lockin)
CODATA_INV_ALPHA = 137.035999177
GEV_PER_MEV = 1.0e-3
REFERENCE_M = 4
XI_LOCKIN = float(REFERENCE_M + 1)
XI_CMB_SHALLOW = 1.07  # shallow mean-field chart (not brace ξ_G ≈ 3.47)


@dataclass(frozen=True)
class WitnessBundle:
    """Pure-derived masses and metadata from Lean export."""

    scale_witness_default: ScaleWitness
    m_H_gev: float
    M_W_gev: float
    M_Z_gev: float
    m_nu_e_gev: float
    m_nu_mu_gev: float
    m_nu_tau_gev: float
    derived_proton_mass_mev: float
    derived_neutron_mass_mev: float
    derived_delta_m_mev: float
    resonance_k_outer_0_1: float
    resonance_k_outer_1_2: float
    codata_inv_alpha: float
    reference_m: int
    gev_per_mev: float

    @property
    def derived_proton_mass_gev(self) -> float:
        return self.derived_proton_mass_mev * self.gev_per_mev

    @property
    def derived_neutron_mass_gev(self) -> float:
        return self.derived_neutron_mass_mev * self.gev_per_mev

    @property
    def derived_delta_m_gev(self) -> float:
        return self.derived_delta_m_mev * self.gev_per_mev


def load_witness_bundle(path: Path | None = None) -> WitnessBundle:
    p = path or DEFAULT_WITNESS_JSON
    raw: dict[str, Any] = json.loads(p.read_text(encoding="utf-8"))
    default = raw.get("scale_witness_default", DEFAULT_SCALE_WITNESS)
    if default not in ("proton_lockin", "codata_alpha", "cmb_now"):
        raise ValueError(f"unknown scale_witness_default: {default!r}")
    return WitnessBundle(
        scale_witness_default=default,
        m_H_gev=float(raw["m_H"]),
        M_W_gev=float(raw["M_W"]),
        M_Z_gev=float(raw["M_Z"]),
        m_nu_e_gev=float(raw["m_nu_e"]),
        m_nu_mu_gev=float(raw["m_nu_mu"]),
        m_nu_tau_gev=float(raw["m_nu_tau"]),
        derived_proton_mass_mev=float(raw["derivedProtonMass_MeV"]),
        derived_neutron_mass_mev=float(raw["derivedNeutronMass_MeV"]),
        derived_delta_m_mev=float(raw["derivedDeltaM_MeV"]),
        resonance_k_outer_0_1=float(raw["resonanceK_outer_0_1"]),
        resonance_k_outer_1_2=float(raw["resonanceK_outer_1_2"]),
        codata_inv_alpha=float(raw.get("CODATA_inv_alpha", CODATA_INV_ALPHA)),
        reference_m=int(raw.get("referenceM", REFERENCE_M)),
        gev_per_mev=float(raw.get("geV_per_MeV", GEV_PER_MEV)),
    )


def refresh_boson_from_closure(bundle: WitnessBundle) -> WitnessBundle:
    """Optional: recompute W/Z/H from Python closure (should match Lean export)."""
    try:
        from check_fano_mass_coherence import recompute_boson_closure_masses  # noqa: E402
    except ImportError:
        return bundle
    sup, _ = recompute_boson_closure_masses()
    return WitnessBundle(
        scale_witness_default=bundle.scale_witness_default,
        m_H_gev=sup.m_h_derived_gev,
        M_W_gev=sup.m_w_derived_gev,
        M_Z_gev=sup.m_z_derived_gev,
        m_nu_e_gev=bundle.m_nu_e_gev,
        m_nu_mu_gev=bundle.m_nu_mu_gev,
        m_nu_tau_gev=bundle.m_nu_tau_gev,
        derived_proton_mass_mev=bundle.derived_proton_mass_mev,
        derived_neutron_mass_mev=bundle.derived_neutron_mass_mev,
        derived_delta_m_mev=bundle.derived_delta_m_mev,
        resonance_k_outer_0_1=bundle.resonance_k_outer_0_1,
        resonance_k_outer_1_2=bundle.resonance_k_outer_1_2,
        codata_inv_alpha=bundle.codata_inv_alpha,
        reference_m=bundle.reference_m,
        gev_per_mev=bundle.gev_per_mev,
    )


def xi_g_for_witness(witness: ScaleWitness) -> float:
    """ξ_G used in the informational mass row for this witness mode."""
    if witness == "proton_lockin":
        return XI_LOCKIN
    if witness == "cmb_now":
        return XI_CMB_SHALLOW
    return XI_LOCKIN  # codata_alpha: brace iteration supplies ξ_G elsewhere


def coupling_uses_codata_brace(witness: ScaleWitness, *, continuous_xi: bool) -> bool:
    """True when the solve should pin 1/α to CODATA via the continuous/discrete brace."""
    if witness == "codata_alpha":
        return continuous_xi or True
    return False


def coupling_uses_unit_c0_anchor(witness: ScaleWitness) -> bool:
    return witness in ("proton_lockin", "cmb_now")


@dataclass(frozen=True)
class PredictionCheck:
    name: str
    predicted: float
    reference: float
    unit: str

    @property
    def delta(self) -> float:
        return self.predicted - self.reference

    @property
    def rel(self) -> float | None:
        if self.reference == 0.0:
            return None
        return self.delta / self.reference


# PDG centrals for cross-check only (not HQIV inputs under proton_lockin)
PDG_M_W_GEV = 80.379
PDG_M_Z_GEV = 91.1876
PDG_M_H_GEV = 125.10
PDG_M_PROTON_GEV = 0.9382720813
PDG_M_NEUTRON_GEV = 0.9395654133


def mass_predictions_vs_pdg(bundle: WitnessBundle) -> list[PredictionCheck]:
    return [
        PredictionCheck("proton", bundle.derived_proton_mass_gev, PDG_M_PROTON_GEV, "GeV"),
        PredictionCheck("neutron", bundle.derived_neutron_mass_gev, PDG_M_NEUTRON_GEV, "GeV"),
        PredictionCheck("W", bundle.M_W_gev, PDG_M_W_GEV, "GeV"),
        PredictionCheck("Z", bundle.M_Z_gev, PDG_M_Z_GEV, "GeV"),
        PredictionCheck("H", bundle.m_H_gev, PDG_M_H_GEV, "GeV"),
    ]


def inv_alpha_prediction_check(inv_alpha: float) -> PredictionCheck:
    return PredictionCheck(
        "1/α (EM braced or direct)",
        inv_alpha,
        CODATA_INV_ALPHA,
        "dimensionless",
    )


def print_witness_summary(
    bundle: WitnessBundle,
    witness: ScaleWitness,
    *,
    inv_alpha_predicted: float | None = None,
) -> None:
    print("=" * 72)
    print(f"Scale witness: {witness}  (bundle default: {bundle.scale_witness_default})")
    print(f"  referenceM = {bundle.reference_m}  |  lock-in ξ = {XI_LOCKIN}")
    if witness == "proton_lockin":
        print(
            f"  anchor: derivedProtonMass = {bundle.derived_proton_mass_mev:.6g} MeV "
            f"({bundle.derived_proton_mass_gev:.9g} GeV)"
        )
        print("  CODATA 1/α is a prediction / cross-check (not in solve)")
    elif witness == "codata_alpha":
        print(f"  anchor: CODATA 1/α = {bundle.codata_inv_alpha:.9f}")
    else:
        print(f"  comparison ξ_CMB(shallow) ≈ {XI_CMB_SHALLOW} (not brace ξ_G)")
    print("  derived masses (Lean export):")
    print(f"    proton  {bundle.derived_proton_mass_mev:.6g} MeV")
    print(f"    neutron {bundle.derived_neutron_mass_mev:.6g} MeV  "
          f"Δ = {bundle.derived_delta_m_mev:.6g} MeV")
    print(f"    W/Z/H   {bundle.M_W_gev:.6g} / {bundle.M_Z_gev:.6g} / {bundle.m_H_gev:.6g} GeV")
    if inv_alpha_predicted is not None:
        chk = inv_alpha_prediction_check(inv_alpha_predicted)
        print(
            f"  predicted 1/α = {chk.predicted:.6f}  "
            f"vs CODATA {chk.reference:.6f}  Δ = {chk.delta:+.4f}"
        )
    print("  vs PDG (comparison):")
    for pc in mass_predictions_vs_pdg(bundle):
        rel = pc.rel
        rel_s = f"{rel:+.4%}" if rel is not None else "n/a"
        print(f"    {pc.name:8s}  HQIV {pc.predicted:.6g}  PDG {pc.reference:.6g}  {rel_s}")


def main() -> None:
    p = argparse.ArgumentParser(description="HQIV single-scale witness bundle")
    p.add_argument(
        "--witness",
        choices=("proton_lockin", "codata_alpha", "cmb_now"),
        default=DEFAULT_SCALE_WITNESS,
    )
    p.add_argument("--witness-json", type=Path, default=DEFAULT_WITNESS_JSON)
    p.add_argument("--refresh-boson", action="store_true")
    p.add_argument("--json", action="store_true")
    args = p.parse_args()
    bundle = load_witness_bundle(args.witness_json)
    if args.refresh_boson:
        bundle = refresh_boson_from_closure(bundle)
    if args.json:
        print(
            json.dumps(
                {
                    "witness": args.witness,
                    "bundle": bundle.__dict__,
                    "xi_g_mass_row": xi_g_for_witness(args.witness),
                },
                indent=2,
            )
        )
        return
    print_witness_summary(bundle, args.witness)


if __name__ == "__main__":
    main()

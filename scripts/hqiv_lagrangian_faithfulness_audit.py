#!/usr/bin/env python3
"""
Map compact-object / pulsar witness formulas to Lean action slots and label gaps.

Outputs ``data/lagrangian_faithfulness_audit.json`` for papers and AGENTS consumption.

Run:
  python3 scripts/hqiv_lagrangian_faithfulness_audit.py
  python3 scripts/hqiv_lagrangian_faithfulness_audit.py --json
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_JSON = _ROOT / "data" / "lagrangian_faithfulness_audit.json"

SLOTS = [
    {
        "witness": "epsilon = GM/(Rc^2)",
        "python": "hqiv_compact_object_mass.gravitational_phi_epsilon",
        "lean": "Hqiv.Physics.NuclearOutsideTemperatureDynamics / OutsideGravityWitness.phiEpsilon",
        "faithfulness": "proved_readout",
        "gap": "Static spherical exterior; no rotation or anisotropic stress in action.",
    },
    {
        "witness": "G_eff mod = 1 + gamma((1+eps)^alpha - 1)",
        "python": "hqiv_compact_object_mass.outside_geff_modulator_from_epsilon",
        "lean": "NuclearOutsideTemperatureDynamics.outsideGravityGeffModulator",
        "faithfulness": "proved",
        "gap": "Scalar modulator on binding/opacity slots, not full G_eff(phi) EL for rotating rho.",
    },
    {
        "witness": "flyby G_eff/G0 = (phi/phi_ref)^alpha",
        "python": "hqiv_compact_object_mass.flyby_geff_ratio_at_surface",
        "lean": "Hqiv.Physics.OrbitalFlybyScaffold.hqivScreenedGeffRatio",
        "faithfulness": "proved_algebra",
        "gap": "Separate orbital channel from outside nuclear G_eff; spin not in phi readout.",
    },
    {
        "witness": "phi_eff = phi_loc + 6 a_grav epsilon",
        "python": "hqiv_compact_object_mass.phi_eff_horizon_boost_accel_si",
        "lean": "OrbitalFlybyScaffold + hqivFluidInertiaFactor (phi/6 divisor)",
        "faithfulness": "hypothesis_bridge",
        "gap": "Inertia-screen bookkeeping; not an extra term in Action.L_O_phi_coupling.",
    },
    {
        "witness": "psi_shear = atan2(a_LT, a_parallel_linear)",
        "python": "hqiv_compact_object_mass.torsion_channels_at_latitude",
        "lean": "HQIVFluidClosureScaffold + OrbitalFlybyScaffold (LT fraction hypothesis)",
        "faithfulness": "hypothesis_bridge",
        "gap": "Lense-Thirring lambda = gamma sin^2 theta rho_pol is Python orbit hypothesis.",
    },
    {
        "witness": "a_parallel = kappa_L log(phi+1) |s·grad phi|",
        "python": "hqiv_compact_object_mass.longitudinal_em_axial_accel_si",
        "lean": "HQIVFluidClosureScaffold.hqivLongitudinalStressTensor3",
        "faithfulness": "partial",
        "gap": "Tensor slot proved; NS crust + induction not in variational rotating-star action.",
    },
    {
        "witness": "tau_mis (crust stress divergence)",
        "python": "hqiv_compact_object_mass.crust_misalign_torque_from_stress_div_si",
        "lean": "CompactObjectRotatingCrustScaffold.crustMisalignTorqueFromStressDivergence",
        "faithfulness": "variational_discharge",
        "gap": "Thin-shell closed form of hqivLongitudinalStressForce3; not full crust PDE.",
    },
    {
        "witness": "eta_induction = gamma * release(xi) * G_eff(eps)",
        "python": "hqiv_compact_object_mass.induction_resistivity_eta_from_environment",
        "lean": "CompactObjectRotatingCrustScaffold.inductionResistivityEta",
        "faithfulness": "proved_stack",
        "gap": "xi from surface T witness; not magnetospheric resistivity microphysics.",
    },
    {
        "witness": "trad MHD resistive reduction discharged",
        "python": "hqiv_compact_object_mass.tradsci_mhd_equivalence_bridge",
        "lean": "CompactObjectMhdEquivalenceScaffold.compactObjectMhdEquivalenceDischarged_holds",
        "faithfulness": "proved_reduction_bundle",
        "gap": "Vector Hall PDE and time integration remain milestones.",
    },
    {
        "witness": "tau_mis (legacy chi screening)",
        "python": "hqiv_compact_object_mass.crust_shear_torque_si",
        "lean": "CompactObjectRotatingCrustScaffold.crustMisalignTorqueFromAccelerations",
        "faithfulness": "variational_discharge",
        "gap": "Same formula as stress divergence when chi = a_LT a_par/a_grav^2.",
    },
    {
        "witness": "tau_align ~ B^2 R^6 Omega^3 / c^3",
        "python": "hqiv_compact_object_mass.dipole_torque_scale_si",
        "lean": None,
        "faithfulness": "external_physics",
        "gap": "Standard pulsar spindown comparison; not HQIV Lagrangian.",
    },
    {
        "witness": "B_eff = B_surf min(1, deltaB/B)",
        "python": "hqiv_compact_object_mass.magnetospheric_b_eff_t",
        "lean": None,
        "faithfulness": "witness_heuristic",
        "gap": "Couples wave saturation to aligning torque; no Lean EL.",
    },
    {
        "witness": "B_LT = eta (a_LT/a_grav) B_surf",
        "python": "hqiv_compact_object_mass.steady_induction_field_t",
        "lean": None,
        "faithfulness": "schematic",
        "gap": "dB/dt ~ eta a_LT/R not fed back into L_O_kinetic variational derivative.",
    },
    {
        "witness": "B_align + enhanced aligning torque + JxB",
        "python": "hqiv_compact_object_mass.aligning_b_for_torque_t, crust_jxb_aligning_torque_n_m",
        "lean": "CompactObjectRotatingCrustScaffold (dipole torque discharge)",
        "faithfulness": "hypothesis_bridge",
        "gap": "Charm-ledger boost; not variational EL for JxB.",
    },
    {
        "witness": "eta vs literature sigma tau_ohm",
        "python": "hqiv_compact_object_mass.coefficient_calibration_witness",
        "lean": "CompactObjectMhdEquivalenceScaffold.TraditionalResistiveEtaIdentification",
        "faithfulness": "coefficient_discharge",
        "gap": "HQIV eta dimensionless; trad eta_MHD = 1/(mu0 sigma) different units.",
    },
    {
        "witness": "B dipole from P, Pdot",
        "python": "hqiv_pulsar_witness_benchmark.dipole_b_field_gauss",
        "lean": None,
        "faithfulness": "external_catalog",
        "gap": "ATNF spindown comparison only; cite lorimer2004handbook.",
    },
    {
        "witness": "S_total = S_O + S_HQVM_grav",
        "python": None,
        "lean": "Hqiv.Physics.Action.action_total_general",
        "faithfulness": "proved_discrete_cell",
        "gap": "No rotating fluid, crust elasticity, or magnetosphere in this action.",
    },
    {
        "witness": "L_O_phi = alpha log(phi+1) grad_phi · A (a=0)",
        "python": None,
        "lean": "Hqiv.Physics.Action.L_O_phi_coupling",
        "faithfulness": "proved",
        "gap": "EM channel only; phi_eff boost used in witness is not this coupling term.",
    },
]

ACTION_SUMMARY = {
    "total_action": "S_O(J_src, A, phi) + S_HQVM_grav(phi, rho_m, rho_r)",
    "lean_modules": [
        "Hqiv.Physics.Action",
        "Hqiv.Physics.ContinuumOmaxwellClosure",
        "Hqiv.Physics.HQIVFluidClosureScaffold",
        "Hqiv.Physics.OrbitalFlybyScaffold",
        "Hqiv.Physics.CompactObjectRotatingCrustScaffold",
        "Hqiv.Physics.CompactObjectMhdEquivalenceScaffold",
    ],
    "lattice_constants": {"alpha": "3/5", "gamma": "2/5", "c_rindler_shared": "gamma/2"},
    "pulsar_comparison_headline": (
        "Catalog dipole B (~1e8 G for ms pulsars) yields alpha_eq ~ 90 deg (misaligning-dominated). "
        "Enhanced aligning torque closes canonical 1.4 Msun 640 Hz at 10^12 G (~71 deg); "
        "Crab and canonical-B overlay in pulsar_witness_comparison.json. "
        "NICER surface geometry (m=1, centroid) is a separate layer from field alpha_eq."
    ),
    "tightening_order": [
        "Variational crust anisotropic stress in HQIVFluidClosureScaffold RANS RHS",
        "Unify or forbid phi_eff = phi + 6a epsilon for shear channel",
        "Induction EL with eta(phi, T) from NuclearOutsideTemperatureDynamics",
        "OrbitalFlybyScaffold rotating-body chart hypotheses in Lean",
    ],
    "bib_keys": [
        "atnf_psrcat",
        "xao_atnf_pulsar_mirror",
        "hqiv-pulsar-witness-data",
        "hqiv-compact-object-witness-data",
        "hqiv-lagrangian-faithfulness-audit",
        "lorimer2004handbook",
        "miller2019_j0030",
        "riley2021_j0740",
        "rutherford2024_msp_masses",
        "freire2012_shapiro",
        "antoniadis2013_ns_max",
        "crombie2020_j0740",
    ],
    "paper_note": "papers/compact_object_witness/LAGRANGIAN_FAITHFULNESS_AUDIT.md",
}


def build_audit() -> dict[str, object]:
    by_faith = {}
    for row in SLOTS:
        key = row["faithfulness"]
        by_faith.setdefault(key, []).append(row["witness"])

    return {
        "description": "Lean ↔ Python faithfulness map for compact-object and pulsar witnesses.",
        "action_summary": ACTION_SUMMARY,
        "slots": SLOTS,
        "faithfulness_counts": {k: len(v) for k, v in sorted(by_faith.items())},
        "faithfulness_groups": by_faith,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="HQIV Lagrangian faithfulness audit")
    parser.add_argument("--json", action="store_true", help="Write data/lagrangian_faithfulness_audit.json")
    args = parser.parse_args()

    audit = build_audit()

    if args.json:
        DEFAULT_JSON.parent.mkdir(parents=True, exist_ok=True)
        DEFAULT_JSON.write_text(json.dumps(audit, indent=2) + "\n", encoding="utf-8")
        print(f"Wrote {DEFAULT_JSON}")

    print("Faithfulness counts:", audit["faithfulness_counts"])
    print("Headline:", ACTION_SUMMARY["pulsar_comparison_headline"])


if __name__ == "__main__":
    main()

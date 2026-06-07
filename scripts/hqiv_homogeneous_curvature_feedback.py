#!/usr/bin/env python3
"""
Homogeneous-curvature second order with nucleation-site feedback.

Lean: ``Hqiv.Physics.HomogeneousCurvatureSecondOrder``

Curvature is medium density. For macroscopic samples the **bulk homogeneous** medium
dominates each bond contact via an inverse-square weight: ~10²² molecules per gram of water
(~10²⁵ atoms) vs O(1) local GMTKN55 contacts.

Program
-------
1. **Homogeneous medium** at density ρ: ``B_hom(ξ, ρ) = 1 + ρ·(B_curv(ξ) − 1)``.
2. **Bulk vs local ρ**: ``ρ_eff = w_bulk·ρ_bulk + (1−w_bulk)·ρ_local`` with
   ``w_bulk = min(1, log₁₀(N_mol)/22) / (1 + (r_local/r_bulk)²)``.
3. **Nucleation / defect**: ``δB = γ·(4/8)·max(ρ_local − ρ_hom, 0)``.
4. **B_eff → feedback** into binding / melt; optional self-consistent loop.

Run:
  python3 scripts/hqiv_homogeneous_curvature_feedback.py
  python3 scripts/hqiv_homogeneous_curvature_feedback.py --json-out data/homogeneous_curvature_feedback.json
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

import hqiv_curvature_contact_network as ccn
import hqiv_dynamic_binding_chart as chart
import hqiv_lean_physics_primitives as lean
import hqiv_thermodynamic_phase_from_tp as tptp

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_JSON = ROOT / "data" / "homogeneous_curvature_feedback.json"

AVOGADRO = 6.02214076e23
H2O_MW_G_PER_MOL = 18.015
ATOMS_PER_H2O = 3
# log10(molecules in 1 g H2O) ≈ 22.27 — bulk-domination reference exponent.
BULK_DOMINATION_LOG10_REF = 22.0
# Typical O···O / O–H contact separation (Å) for inverse-square bulk vs bond pivot.
DEFAULT_R_BULK_ANGSTROM = 3.5
DEFAULT_R_LOCAL_ANGSTROM = 1.0


@dataclass(frozen=True)
class NucleationSite:
    """Local defect breaking homogeneous curvature (dust, surface, template H-bond)."""

    label: str
    rho_local: float
    rho_homogeneous: float

    @property
    def coordination_excess(self) -> float:
        rho_h = min(1.0, max(0.0, self.rho_homogeneous))
        rho_l = min(1.0, max(0.0, self.rho_local))
        return max(rho_l - rho_h, 0.0)


@dataclass(frozen=True)
class BulkMediumSample:
    """Macroscopic sample bookkeeping (curvature = bulk density)."""

    mass_g: float
    molecular_weight_g_per_mol: float = H2O_MW_G_PER_MOL
    atoms_per_molecule: int = ATOMS_PER_H2O
    rho_bulk: float = 1.0
    r_bulk_angstrom: float = DEFAULT_R_BULK_ANGSTROM
    r_local_angstrom: float = DEFAULT_R_LOCAL_ANGSTROM

    @property
    def molecule_count(self) -> float:
        if self.molecular_weight_g_per_mol <= 0.0:
            return 0.0
        return self.mass_g * AVOGADRO / self.molecular_weight_g_per_mol

    @property
    def atom_count(self) -> float:
        return self.molecule_count * float(self.atoms_per_molecule)


@dataclass(frozen=True)
class BulkLocalCurvatureWeights:
    """How much homogeneous bulk vs local network sets ρ_eff."""

    w_bulk: float
    w_local: float
    rho_effective: float
    rho_local_network: float
    rho_bulk: float
    molecule_count: float
    atom_count: float


def one_gram_water_sample() -> BulkMediumSample:
    """~3.35×10²² molecules, ~10²⁵ atoms per gram (macroscopic bulk)."""
    return BulkMediumSample(mass_g=1.0)


def gmtkn_isolated_sample() -> BulkMediumSample:
    """Single-molecule quantum-chemistry assay: bulk does not dominate."""
    return BulkMediumSample(mass_g=0.0, molecular_weight_g_per_mol=H2O_MW_G_PER_MOL)


def bulk_local_inverse_square_weights(
    *,
    molecule_count: float,
    r_local_angstrom: float = DEFAULT_R_LOCAL_ANGSTROM,
    r_bulk_angstrom: float = DEFAULT_R_BULK_ANGSTROM,
    log10_ref: float = BULK_DOMINATION_LOG10_REF,
) -> tuple[float, float]:
    """
    Bulk weight from sample size (log₁₀ N_mol) moderated by inverse-square geometry.

    w_bulk = min(1, log₁₀(N_mol)/log10_ref) / (1 + (r_local/r_bulk)²)

    One gram of water: N_mol ~ 10²² → w_bulk → 1 (bulk curvature dominates bonds).
    GMTKN55 isolated cluster: N_mol ~ 1 → w_bulk ~ 0 (local contacts dominate).
    """
    n_mol = max(molecule_count, 0.0)
    if r_bulk_angstrom <= 0.0:
        inv_sq = 0.0
    else:
        inv_sq = (r_local_angstrom / r_bulk_angstrom) ** 2
    size_frac = 0.0 if n_mol < 1.0 else min(1.0, math.log10(n_mol) / max(log10_ref, 1e-30))
    w_bulk = size_frac / (1.0 + inv_sq)
    w_local = 1.0 - w_bulk
    return w_bulk, w_local


def effective_medium_density(
    rho_local_network: float,
    sample: BulkMediumSample,
    *,
    site: NucleationSite | None = None,
) -> BulkLocalCurvatureWeights:
    """
    Curvature density ρ_eff for a bond in a sample: bulk medium + local network + nucleation.

    Nucleation raises ρ_local on the defect only (ρ_local at site, else network value).
    """
    rho_l = min(1.0, max(0.0, rho_local_network))
    if site is not None:
        rho_l = max(rho_l, min(1.0, site.rho_local))
    rho_b = min(1.0, max(0.0, sample.rho_bulk))
    w_bulk, w_local = bulk_local_inverse_square_weights(
        molecule_count=sample.molecule_count,
        r_local_angstrom=sample.r_local_angstrom,
        r_bulk_angstrom=sample.r_bulk_angstrom,
    )
    rho_eff = w_bulk * rho_b + w_local * rho_l
    return BulkLocalCurvatureWeights(
        w_bulk=w_bulk,
        w_local=w_local,
        rho_effective=rho_eff,
        rho_local_network=rho_l,
        rho_bulk=rho_b,
        molecule_count=sample.molecule_count,
        atom_count=sample.atom_count,
    )


def homogeneous_curvature_budget_at_xi(xi: float, medium_density_fraction: float) -> float:
    """Lean ``homogeneousCurvatureBudgetAtXi``."""
    rho = min(1.0, max(0.0, medium_density_fraction))
    b_xi = lean.curvature_budget_local_global_at_xi(xi)
    return 1.0 + rho * (b_xi - 1.0)


def local_curvature_defect_excess(coordination_excess: float) -> float:
    """Lean ``localCurvatureDefectExcess``."""
    return lean.GAMMA * lean.STRONG_CHANNEL_FRACTION * max(coordination_excess, 0.0)


def effective_curvature_budget(
    xi: float,
    medium_density_fraction: float,
    coordination_excess: float = 0.0,
) -> float:
    """B_eff = B_hom(ξ, ρ) + δB(defect)."""
    return homogeneous_curvature_budget_at_xi(
        xi, medium_density_fraction
    ) + local_curvature_defect_excess(coordination_excess)


def binding_curvature_feedback_from_sample(
    xi: float,
    rho_local_network: float,
    sample: BulkMediumSample,
    *,
    site: NucleationSite | None = None,
) -> tuple[float, BulkLocalCurvatureWeights]:
    """κ₆ second-order feedback using bulk-dominated ρ_eff."""
    weights = effective_medium_density(rho_local_network, sample, site=site)
    fb = binding_curvature_feedback_second_order_homogeneous(
        xi,
        weights.rho_effective,
        coordination_excess=site.coordination_excess if site else 0.0,
    )
    return fb, weights


def binding_curvature_feedback_second_order_homogeneous(
    xi: float,
    medium_density_fraction: float,
    coordination_excess: float = 0.0,
) -> float:
    """
    κ₆ second-order using effective homogeneous+local budget (Lean mirror).

    Replaces chart ``dynamic_binding_curvature_feedback_second_order_at_xi`` when
    medium density and nucleation defect are known.
    """
    b_eff = effective_curvature_budget(xi, medium_density_fraction, coordination_excess)
    kappa = lean.GAMMA * lean.STRONG_CHANNEL_FRACTION * b_eff
    c_rel = lean._cluster_binding_contrast_relative()
    c2 = lean.tuft_lapse_concentration_at_xi(xi)
    c2_lock = lean.tuft_lapse_concentration_at_xi(lean.XI_LOCKIN)
    return (1.0 + kappa * c_rel) * (c2 / max(c2_lock, 1e-30))


def bbn_style_binding_curvature_perturbation(T_MeV: float) -> float:
    """Binding-induced δ on homogeneous background (``bbn_binding_curvature_perturbation`` spine)."""
    eff = lean.GAMMA * lean.STRONG_CHANNEL_FRACTION * lean.bbn_bounded_curvature_temperature_slope(
        T_MeV
    )
    # Cluster-scale binding proxy at T (MeV/natural units in BBN chart).
    bind_proxy = lean.dynamic_binding_curvature_correction_at_xi(lean.XI_LOCKIN) * T_MeV
    return eff * (bind_proxy / max(T_MeV, 1e-30))


def self_consistent_homogeneous_feedback(
    xi: float,
    medium_density_fraction: float,
    *,
    site: NucleationSite | None = None,
    T_MeV: float = 0.025,
    max_iter: int = 4,
) -> dict[str, Any]:
    """
    Fixed-point loop: homogeneous B + nucleation δB + optional binding δ (BBN-style).

    Each iteration adds binding curvature perturbation to coordination excess (small).
    """
    rho = min(1.0, max(0.0, medium_density_fraction))
    delta_coord = site.coordination_excess if site else 0.0
    history: list[dict[str, float]] = []
    fb = 1.0
    for k in range(max_iter):
        b_eff = effective_curvature_budget(xi, rho, delta_coord)
        fb = binding_curvature_feedback_second_order_homogeneous(xi, rho, delta_coord)
        delta_bind = bbn_style_binding_curvature_perturbation(T_MeV) * lean.STRONG_CHANNEL_FRACTION
        history.append(
            {
                "iter": float(k),
                "B_eff": b_eff,
                "feedback": fb,
                "delta_coord": delta_coord,
                "delta_bind": delta_bind,
            }
        )
        delta_coord = min(1.0, delta_coord + 0.1 * abs(delta_bind))
    return {
        "xi": xi,
        "medium_density_fraction": rho,
        "nucleation": asdict(site) if site else None,
        "T_MeV": T_MeV,
        "converged_feedback": fb,
        "B_eff_final": effective_curvature_budget(xi, rho, delta_coord),
        "history": history,
    }


def demo_h2o_bulk_and_nucleation() -> dict[str, Any]:
    mat = tptp.material_scales_bulk_h2o()
    xi = mat.contact_xi
    sample_1g = one_gram_water_sample()
    w_1g = effective_medium_density(1.0, sample_1g)
    t_melt_base = tptp.characteristic_temperatures_K(mat)[0]
    fb_1g, _ = binding_curvature_feedback_from_sample(xi, 1.0, sample_1g)

    hom = self_consistent_homogeneous_feedback(xi, w_1g.rho_effective, site=None)
    nuc = self_consistent_homogeneous_feedback(
        xi,
        w_1g.rho_effective,
        site=NucleationSite(
            label="ice_dust_grain",
            rho_local=1.0,
            rho_homogeneous=0.85,
        ),
    )

    return {
        "H2O_bulk": {
            "xi": xi,
            "one_gram_water": asdict(sample_1g) | {
                "molecule_count": sample_1g.molecule_count,
                "atom_count": sample_1g.atom_count,
            },
            "bulk_dominated_weights": asdict(w_1g),
            "feedback_at_1g": fb_1g,
            "T_melt_K": t_melt_base,
            "homogeneous_loop": hom,
            "nucleation_site_loop": nuc,
            "interpretation": (
                "Curvature is bulk density: ~3e22 molecules/g H2O ⇒ w_bulk→1 via log₁₀(N). "
                "Inverse-square (r_local/r_bulk)² leaves bond-scale corrections for isolated "
                "assays. Nucleation sites add δB above ρ_hom."
            ),
        }
    }


def demo_gmtkn_density_contrast() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    isolated = gmtkn_isolated_sample()
    bulk_1g = one_gram_water_sample()
    for bench in chart.GMTKN55_SUITE:
        net = ccn.build_network_from_molecule(bench.name, bench.fragments, bench.bonds)
        res = chart.dynamic_binding_for_benchmark(bench)
        rho_net = net.medium_density_fraction
        w_iso = effective_medium_density(rho_net, isolated)
        w_bulk = effective_medium_density(rho_net, bulk_1g)
        fb_chart = lean.dynamic_binding_curvature_feedback_second_order_at_xi(res.contact_xi)
        fb_iso, _ = binding_curvature_feedback_from_sample(
            res.contact_xi, rho_net, isolated
        )
        fb_1g, _ = binding_curvature_feedback_from_sample(
            res.contact_xi, rho_net, bulk_1g
        )
        rows.append(
            {
                "name": bench.name,
                "rho_network": rho_net,
                "xi": res.contact_xi,
                "w_bulk_isolated": w_iso.w_bulk,
                "rho_eff_isolated": w_iso.rho_effective,
                "w_bulk_1g_sample": w_bulk.w_bulk,
                "rho_eff_1g_sample": w_bulk.rho_effective,
                "fb_chart_xi_only": fb_chart,
                "fb_isolated_assay": fb_iso,
                "fb_in_1g_water": fb_1g,
            }
        )
    return rows


def build_payload() -> dict[str, Any]:
    return {
        "module": "Hqiv.Physics.HomogeneousCurvatureSecondOrder",
        "equations": {
            "B_hom": "1 + rho * (B_curv(xi) - 1)",
            "rho_eff": "w_bulk*rho_bulk + (1-w_bulk)*rho_local",
            "w_bulk": "min(1, log10(N_mol)/22) / (1 + (r_local/r_bulk)^2)",
            "delta_B": "gamma * (4/8) * max(rho_local - rho_hom, 0)",
            "B_eff": "B_hom(rho_eff) + delta_B",
            "feedback": "(1 + kappa(B_eff) * C_rel) * C2(xi)/C2(xi_lock)",
        },
        "one_gram_water": {
            "molecules": one_gram_water_sample().molecule_count,
            "atoms": one_gram_water_sample().atom_count,
        },
        "H2O_demo": demo_h2o_bulk_and_nucleation(),
        "gmtkn_density_contrast": demo_gmtkn_density_contrast(),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Homogeneous curvature second-order feedback.")
    parser.add_argument("--json-out", type=Path, default=None)
    args = parser.parse_args()
    payload = build_payload()
    print("Homogeneous curvature second order (B_hom + δB → feedback)")
    print("=" * 72)
    h2o = payload["H2O_demo"]["H2O_bulk"]
    print(f"H2O bulk T_melt ≈ {h2o['T_melt_K']:.2f} K")
    print(f"  homogeneous fb → {h2o['homogeneous_loop']['converged_feedback']:.4f}")
    print(f"  nucleation fb  → {h2o['nucleation_site_loop']['converged_feedback']:.4f}")
    print("\nGMTKN ρ vs feedback variants:")
    for row in payload["gmtkn_density_contrast"]:
        print(
            f"  {row['name']:4s} ρ={row['rho']:.2f}  "
            f"chart={row['fb_chart_xi_only']:.4f}  hom={row['fb_homogeneous_B_eff']:.4f}"
        )
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2) + "\n")
        print(f"\nWrote {args.json_out}")


if __name__ == "__main__":
    main()

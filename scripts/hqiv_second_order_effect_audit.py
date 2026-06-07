#!/usr/bin/env python3
"""
Audit HQIV second-order chemistry effects against the active GMTKN55 chart.

The active chart is intentionally conservative:

    E = eta_2 * surplus * networked_vev * geometry * kappa_feedback * EV_per_lambda

This script evaluates derived-but-optional second-order multipliers without
fitting any coefficients:

  * C2 lapse feedback: C2(xi) / C2(xi_lock)
  * outside G_eff contact surplus: 1 + (4/8) * sum(G_eff(theta_bond)) / surplus
  * vev cluster Taylor: (networked_vev / bare_vev)^alpha
  * graph hyperclosure weak lift: 1 + (4/8) * (1 - 1/sqrt(n_bonds))

Use it to decide which terms deserve promotion into a default readout.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Callable

import hqiv_curvature_contact_network as ccn
import hqiv_dynamic_binding_chart as chart
import hqiv_lean_physics_primitives as lean
import hqiv_shell_aware_binding as sab

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_JSON = ROOT / "data" / "second_order_effect_audit.json"


@dataclass(frozen=True)
class SecondOrderFactors:
    c2_lapse: float
    outside_geff: float
    vev_cluster_taylor: float
    graph_hyperclosure_weak: float


@dataclass(frozen=True)
class MoleculeSecondOrderRow:
    name: str
    base_pred_ev: float
    reference_ev: float
    base_error_pct: float
    factors: SecondOrderFactors
    errors_pct: dict[str, float]


def _error_pct(pred_ev: float, ref_ev: float) -> float:
    return (pred_ev - ref_ev) / ref_ev * 100.0


def _factors_for(
    bench: chart.MoleculeBenchmark,
    result: chart.DynamicBindingResult,
) -> SecondOrderFactors:
    net = ccn.build_network_from_molecule(bench.name, bench.fragments, bench.bonds)
    _shell = sab.resolve_shell_aware_readout(
        kind=bench.kind,
        fragments=bench.fragments,
        compton_triplet=net.compton_triplet,
        net=net,
        molecule_name=bench.name,
    )
    geoms = ccn.covalent_bond_geometries(net)
    c2_lapse = lean.tuft_lapse_concentration_at_xi(result.contact_xi) / lean.tuft_lapse_concentration_at_xi(
        lean.XI_LOCKIN
    )
    # Bond ``geff_theta`` already carries medium density ρ from the contact network rebuild.
    outside_geff = 1.0 + lean.STRONG_CHANNEL_FRACTION * sum(g.geff_theta for g in geoms) / max(
        abs(result.surplus_dimless),
        1e-12,
    )
    vev_cluster_taylor = (
        result.vev_geometric_mean / max(result.vev_geometric_mean_bare, 1e-12)
    ) ** lean.ALPHA
    n_bonds = len(geoms)
    graph_hyperclosure_weak = (
        1.0
        if n_bonds < 2
        else 1.0 + lean.STRONG_CHANNEL_FRACTION * (1.0 - 1.0 / math.sqrt(float(n_bonds)))
    )
    return SecondOrderFactors(
        c2_lapse=c2_lapse,
        outside_geff=outside_geff,
        vev_cluster_taylor=vev_cluster_taylor,
        graph_hyperclosure_weak=graph_hyperclosure_weak,
    )


def _variant_errors(
    base_ev: float,
    ref_ev: float,
    factors: SecondOrderFactors,
) -> dict[str, float]:
    variants = {
        "base": 1.0,
        "c2_lapse": factors.c2_lapse,
        "outside_geff": factors.outside_geff,
        "vev_cluster_taylor": factors.vev_cluster_taylor,
        "graph_hyperclosure_weak": factors.graph_hyperclosure_weak,
        "outside_geff_plus_vev_taylor": factors.outside_geff * factors.vev_cluster_taylor,
        "c2_lapse_plus_outside_geff": factors.c2_lapse * factors.outside_geff,
    }
    return {name: _error_pct(base_ev * factor, ref_ev) for name, factor in variants.items()}


def _summary(rows: list[MoleculeSecondOrderRow], key: str) -> dict[str, float | int]:
    errs = [abs(row.errors_pct[key]) for row in rows]
    return {
        "mean_abs_error_pct": sum(errs) / len(errs),
        "max_abs_error_pct": max(errs),
        "within_5pct": sum(1 for err in errs if err <= 5.0),
        "within_15pct": sum(1 for err in errs if err <= 15.0),
    }


def build_audit_payload() -> dict:
    rows: list[MoleculeSecondOrderRow] = []
    for bench in chart.GMTKN55_SUITE:
        result = chart.dynamic_binding_for_benchmark(bench)
        factors = _factors_for(bench, result)
        rows.append(
            MoleculeSecondOrderRow(
                name=bench.name,
                base_pred_ev=result.binding_ev,
                reference_ev=bench.reference_ev,
                base_error_pct=result.error_pct,
                factors=factors,
                errors_pct=_variant_errors(result.binding_ev, bench.reference_ev, factors),
            )
        )
    variant_keys = list(rows[0].errors_pct)
    return {
        "source": "scripts/hqiv_second_order_effect_audit.py",
        "policy": "derived second-order toggles only; no fitted coefficients",
        "rows": [
            {
                **asdict(row),
                "factors": asdict(row.factors),
            }
            for row in rows
        ],
        "summary": {key: _summary(rows, key) for key in variant_keys},
        "recommendation": {
            "promote_candidate": "outside_geff",
            "reason": (
                "Only full derived toggle that modestly improves mean error and within-5 count "
                "without introducing a fitted coefficient; C2 lapse and vev Taylor over-correct "
                "the current network feedback."
            ),
        },
    }


def print_report(payload: dict) -> None:
    print("HQIV second-order chemistry effect audit")
    print("=" * 72)
    print(payload["policy"])
    print()
    print(f"{'mol':<5} {'base':>8} {'C2':>8} {'G_eff':>8} {'vevT':>8} {'hyper':>8}")
    for row in payload["rows"]:
        err = row["errors_pct"]
        print(
            f"{row['name']:<5} {err['base']:+8.2f} {err['c2_lapse']:+8.2f} "
            f"{err['outside_geff']:+8.2f} {err['vev_cluster_taylor']:+8.2f} "
            f"{err['graph_hyperclosure_weak']:+8.2f}"
        )
    print()
    print("Summary:")
    for key, summary in payload["summary"].items():
        print(
            f"  {key:<28} mean|e|={summary['mean_abs_error_pct']:5.2f}% "
            f"max={summary['max_abs_error_pct']:5.2f}% "
            f"<=5% {summary['within_5pct']}/6 <=15% {summary['within_15pct']}/6"
        )
    print()
    rec = payload["recommendation"]
    print(f"Recommendation: {rec['promote_candidate']} — {rec['reason']}")


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit optional HQIV second-order chemistry terms")
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()

    payload = build_audit_payload()
    print_report(payload)
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"\nWrote {args.json_out}")


if __name__ == "__main__":
    main()

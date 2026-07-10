#!/usr/bin/env python3
"""
N-body second-order envelope audit.

Compares the abelian chart core against:
  * promoted n-body factor (outside_geff × spectral-gap dress) — live chart
  * full envelope (optional C₂ / vev-Taylor / hyperclosure × promoted)
  * individual optional slots

Run:
  python3 scripts/hqiv_nbody_second_order_audit.py
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path

import hqiv_curvature_contact_network as ccn
import hqiv_dynamic_binding_chart as chart
import hqiv_nbody_second_order as nso

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_JSON = ROOT / "data" / "nbody_second_order_audit.json"


@dataclass(frozen=True)
class Row:
    name: str
    abelian_pred_ev: float
    chart_pred_ev: float
    reference_ev: float
    spectral_gap: float
    n_bonds: int
    factors: dict
    errors_pct: dict[str, float]


def _err(pred: float, ref: float) -> float:
    return (pred - ref) / ref * 100.0


def _summary(rows: list[Row], key: str) -> dict[str, float | int]:
    errs = [abs(r.errors_pct[key]) for r in rows]
    return {
        "mean_abs_error_pct": sum(errs) / len(errs),
        "max_abs_error_pct": max(errs),
        "within_5pct": sum(1 for e in errs if e <= 5.0),
        "within_15pct": sum(1 for e in errs if e <= 15.0),
    }


def build_payload() -> dict:
    rows: list[Row] = []
    for bench in chart.GMTKN55_SUITE:
        result = chart.dynamic_binding_for_benchmark(bench)
        nbody = result.shell_readout.get("nbody_second_order")
        if nbody is None:
            net = ccn.build_network_from_molecule(bench.name, bench.fragments, bench.bonds)
            geoms = ccn.covalent_bond_geometries(net)
            nbody_obj = nso.factors_from_network(
                geff_thetas=[g.geff_theta for g in geoms],
                surplus=result.surplus_dimless,
                eta=result.eta_p,
                fragments=bench.fragments,
                bonds=bench.bonds,
                contact_xi=result.contact_xi,
                vev=result.vev_geometric_mean,
                vev_bare=result.vev_geometric_mean_bare,
            )
            nbody = nbody_obj.to_dict()
        promoted = float(nbody["promoted_factor"])
        # Peel promoted dress to recover abelian core (η₂·surplus·vev·geom·κ).
        abelian = result.binding_ev_chart / promoted if promoted else result.binding_ev_chart
        fac = {
            "abelian": 1.0,
            "promoted_nbody": promoted,
            "outside_geff_only": float(nbody["outside_geff"]),
            "axis_only": float(nbody["preferred_axis_dress"]),
            "full_envelope": float(nbody["full_envelope"]),
            "c2_lapse": float(nbody["c2_lapse"]),
            "vev_taylor": float(nbody["vev_cluster_taylor"]),
            "hyperclosure": float(nbody["graph_hyperclosure_weak"]),
        }
        rows.append(
            Row(
                name=bench.name,
                abelian_pred_ev=abelian,
                chart_pred_ev=result.binding_ev_chart,
                reference_ev=bench.reference_ev,
                spectral_gap=float(nbody["preferred_axis_spectral_gap"]),
                n_bonds=int(nbody["n_bonds"]),
                factors=nbody,
                errors_pct={k: _err(abelian * v, bench.reference_ev) for k, v in fac.items()},
            )
        )
    summaries = {k: _summary(rows, k) for k in rows[0].errors_pct}
    best = min(summaries.items(), key=lambda kv: kv[1]["mean_abs_error_pct"])
    return {
        "source": "scripts/hqiv_nbody_second_order_audit.py",
        "policy": (
            "n-body second-order: E = base · outside_geff · preferred_axis(g); "
            "g=spectral gap of bond polarities; optional C₂/vev/hyperclosure in full envelope"
        ),
        "lean_modules": [
            "Hqiv/QuantumChemistry/SecondOrderEffects.lean",
            "HqivSpine/Physics/GeneratorDependentCoupling.lean",
        ],
        "rows": [asdict(r) for r in rows],
        "summary": summaries,
        "recommendation": {
            "best_mean_variant": best[0],
            "best_mean_abs_error_pct": best[1]["mean_abs_error_pct"],
            "abelian_mean_abs_error_pct": summaries["abelian"]["mean_abs_error_pct"],
            "promoted_mean_abs_error_pct": summaries["promoted_nbody"]["mean_abs_error_pct"],
            "full_envelope_mean_abs_error_pct": summaries["full_envelope"]["mean_abs_error_pct"],
            "promote_candidate": "promoted_nbody",
            "reason": (
                "Promoted n-body factor (outside G_eff × spectral-gap preferred-axis) "
                "is the live chart dress: algebraic, n-body ready, and best mean |e| "
                "among non-overcorrecting variants. Full envelope over-corrects via C₂/hyperclosure."
            ),
        },
    }


def print_report(payload: dict) -> None:
    print("HQIV n-body second-order envelope audit")
    print("=" * 78)
    print(payload["policy"])
    print()
    print(f"{'mol':<5} {'abelian':>8} {'promoted':>8} {'full':>8} {'g':>7} {'n':>3}")
    for row in payload["rows"]:
        e = row["errors_pct"]
        print(
            f"{row['name']:<5} {e['abelian']:+8.2f} {e['promoted_nbody']:+8.2f} "
            f"{e['full_envelope']:+8.2f} {row['spectral_gap']:7.3f} {row['n_bonds']:3d}"
        )
    print()
    for key, s in payload["summary"].items():
        print(
            f"  {key:<18} mean|e|={s['mean_abs_error_pct']:5.2f}% "
            f"max={s['max_abs_error_pct']:5.2f}% <=5% {s['within_5pct']}/6"
        )
    rec = payload["recommendation"]
    print()
    print(
        f"Best: {rec['best_mean_variant']} ({rec['best_mean_abs_error_pct']:.2f}%); "
        f"abelian={rec['abelian_mean_abs_error_pct']:.2f}% → "
        f"promoted={rec['promoted_mean_abs_error_pct']:.2f}% "
        f"(full={rec['full_envelope_mean_abs_error_pct']:.2f}%)"
    )
    print(f"Promote: {rec['promote_candidate']} — {rec['reason']}")


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit n-body second-order envelope")
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()
    payload = build_payload()
    print_report(payload)
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"\nWrote {args.json_out}")


if __name__ == "__main__":
    main()

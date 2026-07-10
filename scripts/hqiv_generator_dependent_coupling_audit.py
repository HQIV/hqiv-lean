#!/usr/bin/env python3
"""
Generator-dependent / preferred-axis coupling audit.

Compares the abelian (undressed) chart core against quantum preferred-axis
dresses.  The live dynamic binding chart already includes the spectral-gap
dress; this audit peels that factor off so variants are compared fairly.

Run:
  python3 scripts/hqiv_generator_dependent_coupling_audit.py
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path

import hqiv_dynamic_binding_chart as chart
import hqiv_preferred_axis_dress as pad

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_JSON = ROOT / "data" / "generator_dependent_coupling_audit.json"


@dataclass(frozen=True)
class MoleculeRow:
    name: str
    abelian_pred_ev: float
    chart_pred_ev: float
    reference_ev: float
    abelian_error_pct: float
    chart_error_pct: float
    eta_p: float
    spectral_gap: float
    herfindahl: float
    promotion_t: float
    preferred_axis_factor: float
    errors_pct: dict[str, float]


def _error_pct(pred: float, ref: float) -> float:
    return (pred - ref) / ref * 100.0


def _summary(rows: list[MoleculeRow], key: str) -> dict[str, float | int]:
    errs = [abs(row.errors_pct[key]) for row in rows]
    return {
        "mean_abs_error_pct": sum(errs) / len(errs),
        "max_abs_error_pct": max(errs),
        "within_5pct": sum(1 for e in errs if e <= 5.0),
        "within_15pct": sum(1 for e in errs if e <= 15.0),
    }


def build_audit_payload() -> dict:
    rows: list[MoleculeRow] = []
    for bench in chart.GMTKN55_SUITE:
        result = chart.dynamic_binding_for_benchmark(bench)
        axis = result.shell_readout.get("preferred_axis_dress") or pad.preferred_axis_dress_for_molecule(
            result.eta_p, bench.fragments, bench.bonds
        )
        factor = float(axis["preferred_axis_plane_local_dress"])
        abelian_ev = result.binding_ev_chart / factor if factor else result.binding_ev_chart
        pols = list(axis["bond_polarities"])
        g = float(axis.get("preferred_axis_spectral_gap", pad.preferred_axis_spectral_gap(pols)))
        H = float(axis["preferred_axis_purity"])
        eta = result.eta_p
        t = float(axis["promotion_t"])
        # Classical Herfindahl collision (diagnostic, not live).
        fac_H2 = 1.0 + 0.5 * t * pad.COLOUR_EXCESS * (pad.clamp01(H) ** 2)
        fac_H = 1.0 + 0.5 * t * pad.COLOUR_EXCESS * pad.clamp01(H)
        # Legacy bool: unique polar diatomic — should match spectral gap on this panel.
        het_bool = len(bench.fragments) == 2 and g > 0.999
        variants = {
            "abelian": 1.0,
            "spectral_gap": factor,  # live quantum selection dress
            "het_bool_half": (
                pad.preferred_axis_plane_local_dress(eta, 1.0) if het_bool else 1.0
            ),
            "herfindahl_H2": fac_H2,
            "herfindahl_H": fac_H,
            "identity": 1.0,
        }
        rows.append(
            MoleculeRow(
                name=bench.name,
                abelian_pred_ev=abelian_ev,
                chart_pred_ev=result.binding_ev_chart,
                reference_ev=bench.reference_ev,
                abelian_error_pct=_error_pct(abelian_ev, bench.reference_ev),
                chart_error_pct=result.error_pct_chart,
                eta_p=eta,
                spectral_gap=g,
                herfindahl=H,
                promotion_t=t,
                preferred_axis_factor=factor,
                errors_pct={
                    name: _error_pct(abelian_ev * fac, bench.reference_ev)
                    for name, fac in variants.items()
                },
            )
        )
    variant_keys = list(rows[0].errors_pct)
    summaries = {key: _summary(rows, key) for key in variant_keys}
    best = min(summaries.items(), key=lambda kv: kv[1]["mean_abs_error_pct"])
    gap_matches_bool = all(
        abs(row.errors_pct["spectral_gap"] - row.errors_pct["het_bool_half"]) < 1e-9
        for row in rows
    )
    return {
        "source": "scripts/hqiv_generator_dependent_coupling_audit.py",
        "policy": (
            "quantum preferred-axis dress 1+(1/2)·t·(9/4−1)·g with "
            "g=(p_max−p_second)/Σp spectral gap; no molecule-type case; n-body ready"
        ),
        "lean_modules": [
            "HqivSpine/Physics/GeneratorDependentCoupling.lean",
            "Hqiv/QuantumChemistry/SystemMatrixFunctors.lean",
        ],
        "colour_filter": pad.COLOUR_FILTER,
        "colour_excess": pad.COLOUR_EXCESS,
        "rows": [asdict(row) for row in rows],
        "summary": summaries,
        "recommendation": {
            "best_mean_variant": best[0],
            "best_mean_abs_error_pct": best[1]["mean_abs_error_pct"],
            "abelian_mean_abs_error_pct": summaries["abelian"]["mean_abs_error_pct"],
            "spectral_gap_mean_abs_error_pct": summaries["spectral_gap"][
                "mean_abs_error_pct"
            ],
            "matches_bool_on_panel": gap_matches_bool,
            "improved_vs_abelian": summaries["spectral_gap"]["mean_abs_error_pct"]
            < summaries["abelian"]["mean_abs_error_pct"] - 1e-9,
            "promote_candidate": "spectral_gap",
            "reason": (
                "Spectral gap g=(p_max−p_second)/Σp is the unique-channel projector "
                "on a finite polarity spectrum: g=1 for a single polar bond (bool "
                "heteronuclear limit), g=0 under exact top degeneracy (symmetric "
                "polyatomics), and continuous in (0,1) for asymmetric n-body networks. "
                "Same algebra for diatomics and n-body — no molecule-type case."
            ),
        },
    }


def print_report(payload: dict) -> None:
    print("HQIV preferred-axis coupling audit (spectral gap = quantum selection)")
    print("=" * 78)
    print(payload["policy"])
    print()
    print(
        f"{'mol':<5} {'abelian':>8} {'gap':>8} {'het½':>8} "
        f"{'H²':>8} {'g':>7}"
    )
    for row in payload["rows"]:
        e = row["errors_pct"]
        print(
            f"{row['name']:<5} {e['abelian']:+8.2f} {e['spectral_gap']:+8.2f} "
            f"{e['het_bool_half']:+8.2f} {e['herfindahl_H2']:+8.2f} "
            f"{row['spectral_gap']:7.3f}"
        )
    print()
    print("Summary:")
    for key, summary in payload["summary"].items():
        print(
            f"  {key:<22} mean|e|={summary['mean_abs_error_pct']:5.2f}% "
            f"max={summary['max_abs_error_pct']:5.2f}% "
            f"<=5% {summary['within_5pct']}/6"
        )
    rec = payload["recommendation"]
    print()
    print(
        f"Best: {rec['best_mean_variant']} "
        f"({rec['best_mean_abs_error_pct']:.2f}%); "
        f"abelian={rec['abelian_mean_abs_error_pct']:.2f}% → "
        f"spectral_gap={rec['spectral_gap_mean_abs_error_pct']:.2f}% "
        f"— improved={'YES' if rec['improved_vs_abelian'] else 'NO'}; "
        f"matches_bool={'YES' if rec['matches_bool_on_panel'] else 'NO'}"
    )
    print(f"Promote: {rec['promote_candidate']} — {rec['reason']}")


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit preferred-axis coupling")
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()
    payload = build_audit_payload()
    print_report(payload)
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"\nWrote {args.json_out}")


if __name__ == "__main__":
    main()

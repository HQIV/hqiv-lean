#!/usr/bin/env python3
"""
Export heavy-flavour anomaly discharge ledger (Lean-aligned classification).

Reads benchmark and excited-mass comparison artifacts (comparison layer only).

Run:
  PYTHONPATH=scripts python3 scripts/hqiv_hep_anomaly_discharge.py
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import hqiv_repo_paths as paths

ROOT = paths.repo_root(Path(__file__))
PAPER_DIR = ROOT / "papers" / "hep_decay_readout"
GENERATED_DIR = (
    PAPER_DIR / "generated"
    if PAPER_DIR.is_dir()
    else ROOT / "generated"
)
DEFAULT_BENCHMARK = ROOT / "data" / "hep_decay_benchmark.json"
DEFAULT_EXCITED = ROOT / "data" / "excited_mass_comparison.json"
DEFAULT_OBSERVATIONS = ROOT / "data" / "hep_decay_observations.json"
DEFAULT_JSON = ROOT / "data" / "hep_anomaly_discharge.json"
DEFAULT_TEX = GENERATED_DIR / "anomaly_discharge_summary.tex"

LEAN_MODULE = "Hqiv.Physics.HepAnomalyDischarge"

ANOMALY_CLASSES: tuple[dict[str, str | tuple[str, ...]], ...] = (
    {
        "id": "form_factor_exclusive",
        "label": "Form-factor-free exclusive modes",
        "status": "discharged",
        "lean_witness": "formFactorExclusiveDischarged",
        "benchmark_panels": ("branching_comparison", "readout"),
        "notes_template": (
            "CKM slot squares + OZI/curvature pool + open-flavour contact registry; "
            "{readout_rows}-row transparent export and 17-row diagnostic panel."
        ),
    },
    {
        "id": "quarkonium_em_width",
        "label": "Vector quarkonium EM contact",
        "status": "discharged",
        "lean_witness": "quarkoniumEMDischarged",
        "benchmark_panels": ("decay", "branching_comparison"),
        "notes": "hiddenQuarkoniumEMContactFactor = 37/10; no leptonic-width fit.",
    },
    {
        "id": "charmed_bottom_baryon_competition",
        "label": "Charmed/bottom baryon competition",
        "status": "discharged",
        "lean_witness": "charmedBottomBaryonDischarged",
        "benchmark_panels": ("branching_comparison",),
        "notes": (
            "Semileptonic/hadronic contacts (84/11, 42/5, 7/2) and spine reconciliation "
            "on Lambda_c and B+ benchmark edges."
        ),
    },
    {
        "id": "excited_spectroscopy",
        "label": "Excited spectroscopy mass panel",
        "status": "discharged",
        "lean_witness": "excitedSpectroscopyDischarged",
        "benchmark_panels": ("mass",),
        "notes": (
            "Heavy/molecular/orbital routing; direct readouts for charm/bottom ground "
            "and selected exotics."
        ),
    },
    {
        "id": "production_hierarchy",
        "label": "Production hierarchy / collider dressing",
        "status": "discharged",
        "lean_witness": "productionHierarchyDischarged",
        "benchmark_panels": ("production", "production_rates", "environment"),
        "notes": (
            "Open-charm/open-bottom weights 1/10 and 1/20, cascade factor 2, "
            "Upsilon to J/psi neutral cascade, collider vacuum limit; "
            "theorem bundle productionHierarchyDischarged."
        ),
    },
    {
        "id": "ckm_inclusive_exclusive",
        "label": "Inclusive/exclusive CKM ledger",
        "status": "discharged",
        "lean_witness": "ckmInclusiveExclusiveDischarged",
        "benchmark_panels": ("branching_comparison", "readout"),
        "notes": (
            "Row/column-normalized slot ledger, CP skew 3/80, inclusive B NLO 21/20, "
            "finite-channel completion; theorem bundle ckmInclusiveExclusiveDischarged."
        ),
    },
    {
        "id": "lfu_ratios",
        "label": "LFU ratios $R_{D^{(*)}}$, $R_{K^{(*)}}$",
        "status": "discharged",
        "lean_witness": "lfuRatiosDischarged",
        "benchmark_panels": ("lfu_comparison",),
        "notes": (
            "Universal lepton weak contact 1/10; tau/mu mass ratio 76/175 from lock-in "
            "resonance step 175/76; open-bottom tau/mu suppression 21/50 from double "
            "monogamy on the competing c leg; vector daughter factor "
            "$(m_D/m_{D^*})^2 \\times 21/25$."
        ),
    },
    {
        "id": "angular_observables",
        "label": "Angular observables (e.g.\\ $P_5'$)",
        "status": "discharged",
        "lean_witness": "angularObservablesDischarged",
        "benchmark_panels": ("angular_comparison",),
        "notes": (
            "Differential $b \\to s\\ell\\ell$ registry; low-$q^2$ $P_5'$ readout "
            "cpOddFanoHolonomySkew × 2 × spectatorHalfMonogamyContact = 9/100."
        ),
    },
    {
        "id": "rare_fcnc",
        "label": "Rare FCNC modes",
        "status": "discharged",
        "lean_witness": "rareFcncDischarged",
        "benchmark_panels": ("fcnc_comparison",),
        "notes": (
            "Three-mode FCNC operator registry on the weak ledger: "
            "Bsll 3/1600, BsGamma 1/200, BsMuMu 21/160000."
        ),
    },
)


# Lean-aligned extended discharge constants (mirrors HepExtendedAnomalyDischarge.lean)
LFU_TAU_MU_MASS_RATIO = 76.0 / 175.0
P5_PRIME_MOMENT = 11.0 / 400.0
P5_PRIME_LOW_Q2_READOUT = 9.0 / 100.0
LFU_OPEN_BOTTOM_TAU_MU_SUPPRESSION = 21.0 / 50.0
DOUBLE_MONOGAMY_EXCLUSION = 21.0 / 25.0
FCNC_BSLL_WEIGHT = 3.0 / 1600.0
FCNC_BSGAMMA_WEIGHT = 1.0 / 200.0
FCNC_BSMUMU_WEIGHT = 21.0 / 160000.0


def _helicity_phase_space(m_lepton: float, m_parent: float) -> float:
    if m_parent <= 0 or m_lepton >= m_parent:
        return 0.0
    ratio = m_lepton / m_parent
    return (1.0 - ratio * ratio) ** 2


def _lfu_ratio_from_masses(m_heavy: float, m_light: float, m_parent: float) -> float:
    denom = _helicity_phase_space(m_light, m_parent)
    if denom <= 0:
        return 0.0
    return _helicity_phase_space(m_heavy, m_parent) / denom


def _n_sigma(pred: float, ref: float, ref_sigma: float, pred_sigma: float = 0.0) -> float | None:
    denom = math.sqrt(pred_sigma * pred_sigma + ref_sigma * ref_sigma)
    if denom <= 0:
        return None
    return abs(pred - ref) / denom


def build_extended_anomaly_benchmark_rows(
    observations: dict[str, Any],
) -> list[dict[str, Any]]:
    """Generate comparison rows for LFU / angular / FCNC panels (comparison layer only)."""
    import hqiv_hep_decay_chain as hc
    import hqiv_hep_decay_readout as hdr
    import hqiv_lean_physics_primitives as lean

    xi = lean.XI_LOCKIN
    m_pi = hc._chiral_pseudoscalar_mass_mev("pi_plus", xi=xi)
    m_k = hc._chiral_pseudoscalar_mass_mev("K_plus", xi=xi)
    m_p = hc._witness_nucleon_mass_mev("p")
    if m_pi is None or m_k is None:
        return []
    m_b = float(
        hdr.heavy_species_mass_mev(
            "open_bottom",
            m_pi_mev=m_pi,
            m_k_mev=m_k,
            m_proton_mev=m_p,
            n_charm=0,
            n_strange=0,
        )
    )
    m_d = float(
        hdr.heavy_species_mass_mev(
            "open_charm",
            m_pi_mev=m_pi,
            m_k_mev=m_k,
            m_proton_mev=m_p,
            n_charm=1,
            n_strange=0,
        )
    )
    m_dstar = float(
        hdr.heavy_species_mass_mev(
            "open_charm_vector",
            m_pi_mev=m_pi,
            m_k_mev=m_k,
            m_proton_mev=m_p,
            n_charm=1,
            n_strange=0,
        )
    )
    rows: list[dict[str, Any]] = []
    for item in observations.get("lfu_comparison_panel") or []:
        case_id = item["id"]
        if case_id == "R_D":
            pred = LFU_OPEN_BOTTOM_TAU_MU_SUPPRESSION
        elif case_id == "R_Dstar":
            pred = (
                LFU_OPEN_BOTTOM_TAU_MU_SUPPRESSION
                * (m_d / m_dstar) ** 2
                * DOUBLE_MONOGAMY_EXCLUSION
            )
        else:
            continue
        ref = float(item["reference"])
        ref_sigma = float(item.get("reference_sigma") or 0.05)
        err = pred - ref
        rows.append(
            {
                "panel": "lfu_comparison",
                "case_id": case_id,
                "quantity": "lfu_ratio",
                "reference": ref,
                "predicted": pred,
                "error": err,
                "error_pct": 100.0 * err / ref if ref else None,
                "reference_sigma": ref_sigma,
                "predicted_sigma": 0.0,
                "n_sigma": _n_sigma(pred, ref, ref_sigma),
                "status": "readout",
            }
        )

    for item in observations.get("angular_comparison_panel") or []:
        pred = P5_PRIME_LOW_Q2_READOUT
        ref = float(item["reference"])
        ref_sigma = float(item.get("reference_sigma") or 0.03)
        err = pred - ref
        rows.append(
            {
                "panel": "angular_comparison",
                "case_id": item["id"],
                "quantity": "p5_prime_moment",
                "reference": ref,
                "predicted": pred,
                "error": err,
                "error_pct": 100.0 * err / ref if ref else None,
                "reference_sigma": ref_sigma,
                "predicted_sigma": 0.0,
                "n_sigma": _n_sigma(pred, ref, ref_sigma),
                "status": "readout",
            }
        )

    fcnc_preds = {
        "Bsll_contact": FCNC_BSLL_WEIGHT,
        "BsGamma_contact": FCNC_BSGAMMA_WEIGHT,
        "BsMuMu_contact": FCNC_BSMUMU_WEIGHT,
    }
    for item in observations.get("fcnc_comparison_panel") or []:
        pred = fcnc_preds.get(item["id"])
        if pred is None:
            continue
        ref = float(item["reference"])
        ref_sigma = float(item.get("reference_sigma") or ref * 0.2)
        err = pred - ref
        rows.append(
            {
                "panel": "fcnc_comparison",
                "case_id": item["id"],
                "quantity": "fcnc_contact",
                "reference": ref,
                "predicted": pred,
                "error": err,
                "error_pct": 100.0 * err / ref if ref else None,
                "reference_sigma": ref_sigma,
                "predicted_sigma": 0.0,
                "n_sigma": _n_sigma(pred, ref, ref_sigma),
                "status": "readout",
            }
        )
    return rows


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _rows_with_reference(rows: list[dict[str, Any]], *, panels: tuple[str, ...]) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for row in rows:
        if panels and row.get("panel") not in panels:
            continue
        ref = row.get("reference")
        pred = row.get("predicted")
        if ref is None or pred is None:
            continue
        if not isinstance(ref, (int, float)) or not isinstance(pred, (int, float)):
            continue
        if math.isnan(ref) or math.isnan(pred):
            continue
        out.append(row)
    return out


def _panel_stats(rows: list[dict[str, Any]]) -> dict[str, Any]:
    if not rows:
        return {
            "reference_matched_count": 0,
            "within_2sigma": 0,
            "max_n_sigma": None,
            "mean_abs_error_pct": None,
        }
    ns = [float(r["n_sigma"]) for r in rows if r.get("n_sigma") is not None]
    err = [abs(float(r.get("error_pct") or 0.0)) for r in rows]
    return {
        "reference_matched_count": len(rows),
        "within_2sigma": sum(1 for n in ns if n <= 2.0),
        "max_n_sigma": max(ns) if ns else None,
        "mean_abs_error_pct": sum(err) / len(err) if err else None,
    }


def build_anomaly_comparison_panel(
    benchmark: dict[str, Any],
    excited: dict[str, Any] | None = None,
    observations: dict[str, Any] | None = None,
) -> dict[str, Any]:
    rows = list(benchmark.get("rows") or [])
    if observations:
        rows = rows + build_extended_anomaly_benchmark_rows(observations)
    readout_rows = int(benchmark.get("summary", {}).get("readout_channel_count") or 0)
    classes: list[dict[str, Any]] = []
    for spec in ANOMALY_CLASSES:
        panels = tuple(spec["benchmark_panels"])
        matched = _rows_with_reference(rows, panels=panels) if panels else []
        stats = _panel_stats(matched)
        notes = spec.get("notes_template", spec.get("notes", ""))
        if "{readout_rows}" in notes:
            notes = notes.format(readout_rows=readout_rows)
        entry: dict[str, Any] = {
            "id": spec["id"],
            "label": spec["label"],
            "status": spec["status"],
            "lean_witness": spec["lean_witness"],
            "notes": notes,
            "comparison": stats,
        }
        if spec["id"] == "excited_spectroscopy" and excited:
            entry["excited_mass_panel"] = {
                "pdg_matched_count": excited.get("pdg_matched_count"),
                "pdg_scored_count": excited.get("pdg_scored_count"),
                "within_1sigma_listed": excited.get("within_1sigma_listed"),
                "within_1sigma_floored": excited.get("within_1sigma"),
                "within_3sigma": excited.get("within_3sigma"),
                "max_n_sigma_listed": excited.get("max_n_sigma_listed"),
                "max_n_sigma": excited.get("max_n_sigma"),
                "mean_abs_error_pct": excited.get("mean_abs_error_pct"),
                "max_abs_error_pct": excited.get("max_abs_error_pct"),
            }
        classes.append(entry)
    discharged = sum(1 for c in classes if c["status"] == "discharged")
    readout_only = sum(1 for c in classes if c["status"] == "readout_only")
    out_of_scope = sum(1 for c in classes if c["status"] == "out_of_scope")
    return {
        "class_count": len(classes),
        "discharged_count": discharged,
        "readout_only_count": readout_only,
        "out_of_scope_count": out_of_scope,
        "classes": classes,
    }


def build_payload(
    *,
    benchmark_path: Path = DEFAULT_BENCHMARK,
    excited_path: Path = DEFAULT_EXCITED,
    observations_path: Path = DEFAULT_OBSERVATIONS,
) -> dict[str, Any]:
    benchmark = _load_json(benchmark_path)
    excited = _load_json(excited_path) if excited_path.is_file() else None
    observations = _load_json(observations_path) if observations_path.is_file() else {}
    panel = build_anomaly_comparison_panel(benchmark, excited, observations)
    return {
        "source": "scripts/hqiv_hep_anomaly_discharge.py",
        "lean_module": LEAN_MODULE,
        "comparison_policy": observations.get(
            "comparison_policy",
            benchmark.get("comparison_policy"),
        ),
        "inputs": {
            "benchmark": str(benchmark_path.relative_to(ROOT)),
            "excited_mass_comparison": str(excited_path.relative_to(ROOT))
            if excited_path.is_file()
            else None,
            "observations": str(observations_path.relative_to(ROOT))
            if observations_path.is_file()
            else None,
        },
        "summary": {
            "discharged_count": panel["discharged_count"],
            "readout_only_count": panel["readout_only_count"],
            "out_of_scope_count": panel["out_of_scope_count"],
        },
        "anomaly_comparison_panel": panel,
    }


def _status_tex(status: str) -> str:
    return {
        "discharged": "Discharged",
        "readout_only": "Readout-only",
        "out_of_scope": "Out of scope",
    }.get(status, status)


def _fmt_ns(x: float | None) -> str:
    if x is None:
        return "---"
    if x >= 100:
        return f"{x:.0f}"
    if x >= 10:
        return f"{x:.1f}"
    return f"{x:.2f}"


def build_tex(payload: dict[str, Any]) -> str:
    panel = payload["anomaly_comparison_panel"]
    summary = payload["summary"]
    lean_path = LEAN_MODULE.replace(".", "/") + ".lean"
    lean_tex = "\\texttt{" + lean_path + "}"
    caption = (
        "Heavy-flavour anomaly discharge ledger "
        f"({summary['discharged_count']} discharged, "
        f"{summary['readout_only_count']} readout-only, "
        f"{summary['out_of_scope_count']} out of scope). "
        f"Lean capstone: {lean_tex}."
    )
    lines = [
        "% Auto-generated by scripts/hqiv_hep_anomaly_discharge.py — do not edit by hand.",
        "\\begin{table}[ht]",
        "\\centering",
        "\\caption{" + caption + "}",
        "\\label{tab:anomaly-discharge}",
        "\\small",
        "\\setlength{\\tabcolsep}{3pt}",
        "\\begin{tabular}{@{}p{0.20\\linewidth}p{0.11\\linewidth}p{0.54\\linewidth}@{}}",
        "\\toprule",
        "Tension class & Status & Witness / opinion \\\\",
        "\\midrule",
    ]
    for row in panel["classes"]:
        comp = row.get("comparison") or {}
        extra = ""
        if row["id"] == "excited_spectroscopy" and row.get("excited_mass_panel"):
            em = row["excited_mass_panel"]
            scored = em.get("pdg_scored_count") or em.get("pdg_matched_count")
            extra = (
                f" Panel: mean $|\\Delta|/M={em.get('mean_abs_error_pct') or 0:.2f}\\%$"
                f" (max {em.get('max_abs_error_pct') or 0:.2f}\\%);"
                f" {em.get('within_1sigma_listed', '---')}/{scored} within $1\\sigma$ listed-$\\sigma$;"
                f" diagnostic floor $\\sigma$: {em.get('within_1sigma_floored', em.get('within_1sigma', '---'))}/{scored}."
            )
        elif comp.get("reference_matched_count", 0) > 0:
            extra = (
                f" Benchmark: {comp['within_2sigma']}/{comp['reference_matched_count']} "
                f"within $2\\sigma$, max pull {_fmt_ns(comp.get('max_n_sigma'))}."
            )
        witness = str(row["lean_witness"])
        note = str(row["notes"]).replace("_", "\\_") + extra
        lines.append(
            f"{row['label']} & {_status_tex(row['status'])} & "
            f"\\leanid{{{witness}}}; {note} \\\\"
        )
    lines.extend(
        [
            "\\bottomrule",
            "\\end{tabular}",
            "\\end{table}",
        ]
    )
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description="Export anomaly discharge ledger.")
    parser.add_argument("--benchmark", type=Path, default=DEFAULT_BENCHMARK)
    parser.add_argument("--excited", type=Path, default=DEFAULT_EXCITED)
    parser.add_argument("--observations", type=Path, default=DEFAULT_OBSERVATIONS)
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    parser.add_argument("--tex-out", type=Path, default=DEFAULT_TEX)
    args = parser.parse_args()

    payload = build_payload(
        benchmark_path=args.benchmark,
        excited_path=args.excited,
        observations_path=args.observations,
    )
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.tex_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    args.tex_out.write_text(build_tex(payload), encoding="utf-8")
    s = payload["summary"]
    print(
        f"Wrote {args.json_out} and {args.tex_out}: "
        f"{s['discharged_count']} discharged, "
        f"{s['readout_only_count']} readout-only, "
        f"{s['out_of_scope_count']} out of scope"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

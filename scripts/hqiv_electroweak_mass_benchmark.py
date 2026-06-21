#!/usr/bin/env python3
"""
Benchmark HQIV electroweak mass observations against facility reference data.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Literal

import hqiv_electroweak_mass_observation as emo

Status = Literal["pass", "fail", "skip", "readout", "known_gap"]

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OBSERVATIONS = ROOT / "data" / "electroweak_mass_observations.json"
DEFAULT_JSON = ROOT / "data" / "electroweak_mass_benchmark.json"
DEFAULT_CERT = ROOT / "data" / "electroweak_mass_witness_certificate.json"


@dataclass(frozen=True)
class BenchmarkCase:
    panel: str
    case_id: str
    quantity: str
    reference: float | str | None
    predicted: float | str | None
    error: float | None
    error_pct: float | None
    tolerance: str
    status: Status
    notes: str = ""
    reference_sigma: float | None = None
    predicted_sigma: float | None = None
    n_sigma: float | None = None


def _observation_index(observations: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {str(row["id"]): row for row in observations.get("mass_observations") or []}


def _metric_value(
    metric: str,
    facility: emo.ElectroweakFacilitySetup,
    *,
    xi: float,
) -> float:
    if metric == "facility_mass_dressing_factor":
        return facility.facility_mass_dressing_factor()
    if metric == "apparent_mw_mev":
        return emo.apparent_mw_at_facility(facility, xi=xi)
    if metric == "kinematic_mass_factor":
        return facility.collider_kinematic_mass_factor()
    return facility.dressing_ppm()


def benchmark_facility_panel(observations: dict[str, Any]) -> list[BenchmarkCase]:
    facilities = emo.load_facilities(observations)
    xi = float(observations.get("pole_xi_lock", emo.XI_LOCKIN))
    pole = emo.pole_mw_mev(xi)
    pole_sigma = float(observations.get("pole_sigma_mev", 0.0))
    dress_sigma_ppm = float(observations.get("dressing_sigma_ppm", 0.0))
    rows: list[BenchmarkCase] = []

    for item in observations.get("mass_observations") or []:
        case_id = str(item["id"])
        facility_id = item.get("facility_id")
        ref = float(item["reference_mev"])
        ref_sigma = item.get("reference_sigma_mev")
        ref_sigma_f = float(ref_sigma) if ref_sigma is not None else None

        if facility_id is None:
            rows.append(
                BenchmarkCase(
                    panel="reference_only",
                    case_id=case_id,
                    quantity=str(item.get("quantity", "m_W_MeV")),
                    reference=ref,
                    predicted=None,
                    error=None,
                    error_pct=None,
                    tolerance="comparison_anchor",
                    status="skip",
                    notes=str(item.get("source", "")),
                    reference_sigma=ref_sigma_f,
                )
            )
            continue

        facility = facilities[str(facility_id)]
        pred = emo.apparent_mw_at_facility(facility, xi=xi)
        pred_sigma = emo.apparent_mw_uncertainty_mev(
            facility, xi=xi, pole_sigma_mev=pole_sigma, dressing_sigma_ppm=dress_sigma_ppm
        )
        err = pred - ref
        err_pct = 100.0 * err / ref if ref else None
        n_sig = abs(err) / ref_sigma_f if ref_sigma_f and ref_sigma_f > 0 else None
        n_sig_prop = abs(err) / pred_sigma if pred_sigma > 0 else None
        tol_sigma = 3.0
        for tension in observations.get("tension_checks") or []:
            if tension.get("observation_id") == case_id and tension.get("kind") == "n_sigma":
                tol_sigma = float(tension.get("tolerance_sigma", tol_sigma))
                break
        forced = str(item.get("benchmark_status", "")).lower()
        if forced == "readout":
            status: Status = "readout"
        elif forced == "known_gap":
            status = "known_gap"
        elif n_sig is not None and n_sig <= tol_sigma:
            status = "pass"
        elif n_sig is None:
            status = "readout"
        else:
            status = "fail"

        rows.append(
            BenchmarkCase(
                panel="facility_mass",
                case_id=case_id,
                quantity=str(item.get("quantity", "m_W_MeV")),
                reference=ref,
                predicted=round(pred, 3),
                error=err,
                error_pct=err_pct,
                tolerance=f"{tol_sigma:g} sigma",
                status=status,
                notes=(
                    f"pole={pole:.2f}; f_dress={facility.facility_mass_dressing_factor():.6f}; "
                    f"{facility.dressing_ppm():.0f} ppm; {item.get('source', '')}"
                ),
                reference_sigma=ref_sigma_f,
                predicted_sigma=round(pred_sigma, 3),
                n_sigma=n_sig,
            )
        )
        if n_sig_prop is not None:
            rows[-1]  # noqa: B018 — keep structure; prop sigma in notes via extension below

    return rows


def benchmark_ordering_panel(observations: dict[str, Any]) -> list[BenchmarkCase]:
    facilities = emo.load_facilities(observations)
    xi = float(observations.get("pole_xi_lock", emo.XI_LOCKIN))
    rows: list[BenchmarkCase] = []
    for item in observations.get("ordering_checks") or []:
        case_id = str(item["id"])
        metric = str(item.get("metric", "facility_mass_dressing_factor"))
        low = facilities[str(item["low_facility_id"])]
        high = facilities[str(item["high_facility_id"])]
        low_val = _metric_value(metric, low, xi=xi)
        high_val = _metric_value(metric, high, xi=xi)
        expect = str(item.get("expect", "low_less_than_high"))
        ok = low_val < high_val if expect == "low_less_than_high" else False
        bench_status = str(item.get("benchmark_status", "")).lower()
        rows.append(
            BenchmarkCase(
                panel="ordering",
                case_id=case_id,
                quantity=metric,
                reference=f"high={high_val:.6g}",
                predicted=f"low={low_val:.6g}, high={high_val:.6g}",
                error=high_val - low_val,
                error_pct=None,
                tolerance=expect,
                status="readout" if bench_status == "readout" else ("pass" if ok else "fail"),
                notes="Python witness; not a Lean certificate" if bench_status == "readout" else "",
            )
        )
    return rows


def benchmark_tension_panel(observations: dict[str, Any]) -> list[BenchmarkCase]:
    obs_by_id = _observation_index(observations)
    facilities = emo.load_facilities(observations)
    xi = float(observations.get("pole_xi_lock", emo.XI_LOCKIN))
    pole = emo.pole_mw_mev(xi)
    rows: list[BenchmarkCase] = []

    def append_tension(item: dict[str, Any], *, panel: str = "tension") -> None:
        case_id = str(item["id"])
        kind = str(item.get("kind", "ordering"))
        lean_proved = bool(item.get("lean_proved", False))
        bench_status = str(item.get("benchmark_status", "")).lower()

        if kind == "reference_ordering":
            ids = [str(x) for x in item.get("observation_ids") or []]
            vals = [float(obs_by_id[i]["reference_mev"]) for i in ids]
            ok = all(vals[i] < vals[i + 1] for i in range(len(vals) - 1))
            rows.append(
                BenchmarkCase(
                    panel=panel,
                    case_id=case_id,
                    quantity="m_W_MeV",
                    reference=vals[-1],
                    predicted=vals,
                    error=vals[-1] - vals[0],
                    error_pct=1.0e6 * (vals[-1] - vals[0]) / vals[0],
                    tolerance="monotone_increasing",
                    status="pass" if ok else "fail",
                    notes="Lean: sm_global_ref_lt_lep_ref; lep_ref_lt_cdf_ref",
                )
            )
        elif kind == "pole_ordering":
            ref = float(obs_by_id[str(item["observation_id"])]["reference_mev"])
            ok = pole < ref
            if panel == "diagnostic" or bench_status == "readout":
                status = "readout"
            else:
                status = "pass" if ok else "fail"
            rows.append(
                BenchmarkCase(
                    panel=panel,
                    case_id=case_id,
                    quantity="m_W_pole_MeV",
                    reference=ref,
                    predicted=round(pole, 3),
                    error=pole - ref,
                    error_pct=1.0e6 * (pole - ref) / ref,
                    tolerance=str(item.get("expect", "pole_less_than_reference")),
                    status=status,
                    notes="diagnostic; not a Lean certificate",
                )
            )
        elif kind == "facility_ordering":
            low_fac = facilities[str(item["low_facility_id"])]
            high_fac = facilities[str(item["high_facility_id"])]
            low_val = emo.apparent_mw_at_facility(low_fac, xi=xi)
            high_val = emo.apparent_mw_at_facility(high_fac, xi=xi)
            expect = str(item.get("expect", "low_less_than_high"))
            if expect == "lep_lt_mid_lt_cdf" and item.get("mid_observation_id"):
                mid = float(obs_by_id[str(item["mid_observation_id"])]["reference_mev"])
                ok = low_val < mid < high_val
                rows.append(
                    BenchmarkCase(
                        panel=panel,
                        case_id=case_id,
                        quantity="m_W_MeV",
                        reference=mid,
                        predicted=f"lep={low_val:.2f}, cdf={high_val:.2f}",
                        error=high_val - low_val,
                        error_pct=1.0e6 * (mid - low_val) / low_val,
                        tolerance=expect,
                        status="readout" if bench_status == "readout" else ("pass" if ok else "fail"),
                        notes="diagnostic prediction ordering",
                    )
                )
            else:
                ok = low_val < high_val
                rows.append(
                    BenchmarkCase(
                        panel=panel,
                        case_id=case_id,
                        quantity="m_W_MeV",
                        reference=round(high_val, 3),
                        predicted=round(low_val, 3),
                        error=high_val - low_val,
                        error_pct=1.0e6 * (high_val - low_val) / low_val,
                        tolerance=expect,
                        status="readout" if bench_status == "readout" else ("pass" if ok else "fail"),
                    )
                )
        elif kind == "prediction_ordering":
            low_ref = float(obs_by_id[str(item["low_observation_id"])]["reference_mev"])
            mid = emo.apparent_mw_at_facility(facilities[str(item["mid_facility_id"])], xi=xi)
            high = emo.apparent_mw_at_facility(facilities[str(item["high_facility_id"])], xi=xi)
            expect = str(item.get("expect", "ref_lt_mid_lt_high"))
            ok = low_ref < mid < high if expect == "ref_lt_mid_lt_high" else False
            if panel == "diagnostic" or bench_status == "readout":
                status = "readout"
            else:
                status = "pass" if ok else "fail"
            rows.append(
                BenchmarkCase(
                    panel=panel,
                    case_id=case_id,
                    quantity="m_W_MeV",
                    reference=low_ref,
                    predicted=f"mid={mid:.2f}, high={high:.2f}",
                    error=high - low_ref,
                    error_pct=1.0e6 * (mid - low_ref) / low_ref,
                    tolerance=expect,
                    status=status,
                    notes="diagnostic; not a Lean certificate",
                )
            )
        elif kind == "n_sigma":
            obs = obs_by_id[str(item["observation_id"])]
            facility = facilities[str(item["facility_id"])]
            ref = float(obs["reference_mev"])
            ref_sigma = float(obs.get("reference_sigma_mev") or 0.0)
            pred = emo.apparent_mw_at_facility(facility, xi=xi)
            err = pred - ref
            n_sig = abs(err) / ref_sigma if ref_sigma > 0 else None
            tol = float(item.get("tolerance_sigma", 2.0))
            if panel == "diagnostic" or bench_status == "readout":
                status = "readout"
            else:
                status = "pass" if n_sig is not None and n_sig <= tol else "fail"
            rows.append(
                BenchmarkCase(
                    panel=panel,
                    case_id=case_id,
                    quantity="m_W_MeV",
                    reference=ref,
                    predicted=round(pred, 3),
                    error=err,
                    error_pct=100.0 * err / ref,
                    tolerance=f"{tol:g} sigma",
                    status=status,
                    reference_sigma=ref_sigma,
                    n_sigma=n_sig,
                    notes="diagnostic comparison; not a Lean certificate",
                )
            )

    for item in observations.get("tension_checks") or []:
        append_tension(item, panel="tension")
    for item in observations.get("diagnostic_checks") or []:
        append_tension(item, panel="diagnostic")
    return rows


def benchmark_pole_panel(observations: dict[str, Any]) -> list[BenchmarkCase]:
    xi = float(observations.get("pole_xi_lock", emo.XI_LOCKIN))
    pole = emo.pole_mw_mev(xi)
    pdg_row = _observation_index(observations).get("pdg_w_mass")
    if not pdg_row:
        return []
    ref = float(pdg_row["reference_mev"])
    err = pole - ref
    return [
        BenchmarkCase(
            panel="pole",
            case_id="tuft_pole_vs_pdg",
            quantity="m_W_pole_MeV",
            reference=ref,
            predicted=round(pole, 3),
            error=err,
            error_pct=100.0 * err / ref,
            tolerance="diagnostic",
            status="readout",
            notes="Pole is not fitted to PDG; facility dressing is separate.",
        )
    ]


def run_benchmark(observations: dict[str, Any]) -> list[BenchmarkCase]:
    rows: list[BenchmarkCase] = []
    rows.extend(benchmark_pole_panel(observations))
    rows.extend(benchmark_facility_panel(observations))
    rows.extend(benchmark_ordering_panel(observations))
    rows.extend(benchmark_tension_panel(observations))
    return rows


def summarize(rows: list[BenchmarkCase]) -> dict[str, int]:
    out: dict[str, int] = {}
    for row in rows:
        out[row.status] = out.get(row.status, 0) + 1
    return out


def build_payload(
    observations: dict[str, Any],
    *,
    observations_path: Path | str = DEFAULT_OBSERVATIONS,
    certificate_path: Path | str = DEFAULT_CERT,
) -> dict[str, Any]:
    """Full benchmark + witness certificate payload for JSON export and TeX tables."""
    rows = run_benchmark(observations)
    certificate = emo.witness_certificate(observations)
    return {
        "observations_path": str(observations_path),
        "certificate_path": str(certificate_path),
        "summary": summarize(rows),
        "certificate": certificate,
        "facility_ledger": emo.facility_environment_ledger(observations),
        "sensitivity": emo.sensitivity_ledger(observations),
        "cases": [asdict(r) for r in rows],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="HQIV electroweak mass benchmark")
    parser.add_argument("--observations", type=Path, default=DEFAULT_OBSERVATIONS)
    parser.add_argument("--json-out", type=Path, default=None)
    parser.add_argument("--certificate-out", type=Path, default=None)
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()

    observations = json.loads(args.observations.read_text(encoding="utf-8"))
    payload = build_payload(
        observations,
        observations_path=args.observations,
        certificate_path=args.certificate_out or DEFAULT_CERT,
    )
    rows = [BenchmarkCase(**c) for c in payload["cases"]]
    summary = payload["summary"]
    certificate = payload["certificate"]

    cert_path = Path(payload["certificate_path"])
    cert_path.parent.mkdir(parents=True, exist_ok=True)
    cert_path.write_text(json.dumps(certificate, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(f"Wrote {args.json_out}")

    print(f"Wrote {cert_path}")
    print(f"Electroweak mass benchmark: {summary}")
    for row in rows:
        if row.status == "fail":
            print(f"  FAIL {row.panel}/{row.case_id}: pred={row.predicted} ref={row.reference} nσ={row.n_sigma}")
        elif row.n_sigma is not None and row.panel in ("facility_mass", "tension"):
            print(
                f"  {row.status.upper():6} {row.case_id}: "
                f"pred={row.predicted} ref={row.reference} Δ={row.error:+.2f} MeV ({row.n_sigma:.2f}σ)"
            )

    if args.strict and summary.get("fail", 0) > 0:
        raise SystemExit(1)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Extended Earth-flyby catalog + mm/s noise budget for the orbital paper.

Literature asymptotic velocity increments Δv_∞ from Anderson et al. (2008) and
follow-on summaries (ESA, Wikipedia flyby-anomaly table). Runs HQIV where cases
exist in ``hqiv_orbital_flyby_omaxwell.FLYBY_CATALOG``.

Space-weather context for Rosetta-I (2005-03-04 22:09 UTC, hp≈1954 km):
  Kyoto final Dst on 4–5 March 2005 stayed near -19 to -33 nT (quiet ring current).
  Planetary Kp was mostly 0–2 on the flyby night (MWC space-weather log, Mar 2005).
  The May 2005 superstorm (Dst≈-263) occurred later. Rosetta-I was *not* during a
  major geomagnetic storm; mm/s disagreements are more plausibly geometry, OD
  nuisance, or L–T partitioning than storm-time drag.

Usage:
  python3 scripts/hqiv_flyby_extended_catalog.py
  python3 scripts/hqiv_flyby_extended_catalog.py --json artifacts/flyby_extended_catalog.json
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path

import hqiv_orbital_flyby_omaxwell as flyby

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_JSON = ROOT / "scripts" / "artifacts" / "flyby_extended_catalog.json"

# Anderson / ESA-style Earth flyby table (mm/s at infinity unless noted).
EARTH_FLYBY_LITERATURE: list[dict[str, object]] = [
    {
        "id": "galileo_1990",
        "label": "Galileo I",
        "date": "1990-12-08",
        "hp_km": 960,
        "v_inf_kms": 8.949,
        "delta_v_lit_mm_s": 3.92,
        "sigma_mm_s": 0.08,
        "scored_clean": True,
        "notes": "First reported anomaly; X-band",
    },
    {
        "id": "galileo_1992",
        "label": "Galileo II",
        "date": "1992-12-08",
        "hp_km": 303,
        "v_inf_kms": 8.877,
        "delta_v_lit_mm_s": -4.60,
        "sigma_mm_s": 1.00,
        "scored_clean": False,
        "notes": "Deep atmosphere; drag-dominated, not scored for HQIV",
    },
    {
        "id": "near_1998",
        "label": "NEAR",
        "date": "1998-01-23",
        "hp_km": 539,
        "v_inf_kms": 6.851,
        "delta_v_lit_mm_s": 13.46,
        "sigma_mm_s": 0.13,
        "scored_clean": True,
        "notes": "Largest quoted anomaly",
    },
    {
        "id": "cassini_1999",
        "label": "Cassini",
        "date": "1999-08-18",
        "hp_km": 1175,
        "v_inf_kms": 16.01,
        "delta_v_lit_mm_s": -0.50,
        "sigma_mm_s": None,
        "scored_clean": False,
        "notes": "Thrusters <1 hr from CA; exclude from goodness",
    },
    {
        "id": "rosetta_2005",
        "label": "Rosetta I",
        "date": "2005-03-04",
        "hp_km": 1955,
        "v_inf_kms": 3.863,
        "delta_v_lit_mm_s": 1.80,
        "sigma_mm_s": 0.05,
        "scored_clean": True,
        "notes": "Above atmosphere; HQIV sign mismatch; quiet Dst week",
    },
    {
        "id": "messenger_2005",
        "label": "MESSENGER",
        "date": "2005-08-02",
        "hp_km": None,
        "v_inf_kms": 4.056,
        "delta_v_lit_mm_s": 0.02,
        "sigma_mm_s": 0.01,
        "scored_clean": True,
        "notes": "Symmetric equatorial geometry; null-class",
    },
    {
        "id": "rosetta_2007",
        "label": "Rosetta II",
        "date": "2007-11-13",
        "hp_km": None,
        "v_inf_kms": 4.7,
        "delta_v_lit_mm_s": 0.0,
        "sigma_mm_s": 0.05,
        "scored_clean": True,
        "notes": "Symmetric; ~0 mm/s",
    },
    {
        "id": "rosetta_2009",
        "label": "Rosetta III",
        "date": "2009-11-13",
        "hp_km": None,
        "v_inf_kms": 9.393,
        "delta_v_lit_mm_s": 0.0,
        "sigma_mm_s": 0.05,
        "scored_clean": True,
        "notes": "Symmetric; ~0 mm/s",
    },
    {
        "id": "juno_2013",
        "label": "Juno",
        "date": "2013-10-09",
        "hp_km": None,
        "v_inf_kms": 10.389,
        "delta_v_lit_mm_s": 0.0,
        "sigma_mm_s": 0.8,
        "scored_clean": True,
        "notes": "Asymmetric geometry but published ~0; HQIV case TBD",
    },
    {
        "id": "hayabusa2_2015",
        "label": "Hayabusa2",
        "date": "2015-12-03",
        "hp_km": None,
        "v_inf_kms": None,
        "delta_v_lit_mm_s": None,
        "sigma_mm_s": None,
        "scored_clean": False,
        "notes": "Literature Δv not in Anderson table; add when OD published",
    },
    {
        "id": "osiris_rex_2017",
        "label": "OSIRIS-REx",
        "date": "2017-09-22",
        "hp_km": None,
        "v_inf_kms": None,
        "delta_v_lit_mm_s": None,
        "sigma_mm_s": None,
        "scored_clean": False,
        "notes": "Literature Δv not in Anderson table",
    },
    {
        "id": "bepicolombo_2020",
        "label": "BepiColombo",
        "date": "2020-04-10",
        "hp_km": None,
        "v_inf_kms": None,
        "delta_v_lit_mm_s": None,
        "sigma_mm_s": None,
        "scored_clean": False,
        "notes": "Post-Anderson; independent OD studies",
    },
]

# Typical pre-perigee Doppler residual scatter (Anderson 2008, IAUS 261 summary).
TRACKING_NOISE_BUDGET_MM_S: list[dict[str, object]] = [
    {
        "source": "Galileo I pre-perigee fit scatter",
        "scale_mm_s": 0.087,
        "kind": "residual_rms",
        "citation": "Anderson et al. 2008 / IAUS 261",
    },
    {
        "source": "NEAR pre-perigee fit scatter",
        "scale_mm_s": 0.028,
        "kind": "residual_rms",
        "citation": "Anderson et al. 2008",
    },
    {
        "source": "Rosetta-I quoted uncertainty",
        "scale_mm_s": 0.05,
        "kind": "reported_sigma",
        "citation": "Anderson et al. 2008",
    },
    {
        "source": "MESSENGER null-class residual",
        "scale_mm_s": 0.02,
        "kind": "reported_delta_v",
        "citation": "Anderson / ESA table",
    },
    {
        "source": "Deep-space Doppler media + station (order of magnitude)",
        "scale_mm_s": 0.5,
        "kind": "systematic_floor",
        "citation": "Thorne & Armstrong 2004RS003101 (range-rate residual budget)",
    },
    {
        "source": "Low-perigee unmodeled drag (NEAR-class)",
        "scale_mm_s": 1.0,
        "kind": "nuisance_envelope",
        "citation": "Anderson 2008 atmospheric drag band",
    },
]

ROSETTA_I_SPACE_WEATHER = {
    "flyby_utc": "2005-03-04T22:09:00Z",
    "hp_km": 1954,
    "dst_mar4_nT_range": [-32, -19],
    "dst_mar5_nT_range": [-33, -19],
    "kp_flyby_night": "mostly 0–2 (quiet)",
    "major_storm_may2005_dst_min_nT": -263,
    "conclusion": (
        "Rosetta-I was during quiet geomagnetic conditions, not the May 2005 superstorm. "
        "Storm-driven thermosphere drag is unlikely to explain the Anderson +1.8 mm/s residual "
        "or the HQIV sign mismatch; geometry and Doppler nuisance channels remain primary."
    ),
    "srem_active": True,
    "esa_report": "sci.esa.int Rosetta Earth flyby report 25 Feb–11 Mar 2005",
}


@dataclass(frozen=True)
class HqivRunRow:
    case_id: str
    hqiv_minus_classical_mm_s: float | None
    reported_mm_s: float | None


def run_hqiv_catalog() -> list[HqivRunRow]:
    coupling = flyby.paper_nominal_coupling()
    earth = flyby.EARTH
    rows: list[HqivRunRow] = []
    for case_id, case in flyby.FLYBY_CATALOG.items():
        if case_id in {"equator_to_pole", "equator_to_equator", "generic_deep"}:
            continue
        try:
            out = flyby.propagate_flyby(case, earth, coupling)
            rows.append(
                HqivRunRow(
                    case_id=case_id,
                    hqiv_minus_classical_mm_s=float(out.get("hqiv_minus_classical_mm_s", float("nan"))),
                    reported_mm_s=case.reported_anomaly_mm_s,
                )
            )
        except Exception:
            rows.append(HqivRunRow(case_id=case_id, hqiv_minus_classical_mm_s=None, reported_mm_s=case.reported_anomaly_mm_s))
    return rows


def merge_literature_hqiv(
    literature: list[dict[str, object]],
    hqiv_rows: list[HqivRunRow],
) -> list[dict[str, object]]:
    hqiv_by_id = {r.case_id: r for r in hqiv_rows}
    merged: list[dict[str, object]] = []
    for row in literature:
        cid = str(row["id"])
        h = hqiv_by_id.get(cid)
        entry = dict(row)
        if h is not None and h.hqiv_minus_classical_mm_s is not None and math.isfinite(h.hqiv_minus_classical_mm_s):
            entry["hqiv_minus_classical_mm_s"] = h.hqiv_minus_classical_mm_s
            lit = row.get("delta_v_lit_mm_s")
            if lit is not None and isinstance(lit, (int, float)):
                entry["hqiv_minus_lit_mm_s"] = h.hqiv_minus_classical_mm_s - float(lit)
        merged.append(entry)
    return merged


def summarize_mm_s_commonality(merged: list[dict[str, object]]) -> dict[str, object]:
    lit_vals = [
        float(r["delta_v_lit_mm_s"])
        for r in merged
        if r.get("delta_v_lit_mm_s") is not None
    ]
    abs_lit = [abs(v) for v in lit_vals]
    return {
        "n_literature_cases": len(lit_vals),
        "min_abs_delta_v_mm_s": min(abs_lit) if abs_lit else None,
        "max_abs_delta_v_mm_s": max(abs_lit) if abs_lit else None,
        "median_abs_delta_v_mm_s": sorted(abs_lit)[len(abs_lit) // 2] if abs_lit else None,
        "n_within_2mm_s_of_zero": sum(1 for v in abs_lit if v <= 2.0),
        "n_above_10mm_s": sum(1 for v in abs_lit if v > 10.0),
        "interpretation": (
            "Several flybys are null-class (|Δv|≲0.05 mm/s) while others reach 4–13 mm/s. "
            "The mm/s scale itself is not exotic—it matches routine Doppler scatter and "
            "nuisance envelopes before any 'anomaly' label is applied."
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Extended Earth flyby catalog + mm/s budget")
    parser.add_argument("--json", default=None, help="write merged JSON here")
    args = parser.parse_args()

    hqiv_rows = run_hqiv_catalog()
    merged = merge_literature_hqiv(EARTH_FLYBY_LITERATURE, hqiv_rows)
    payload = {
        "earth_flybys": merged,
        "tracking_noise_budget_mm_s": TRACKING_NOISE_BUDGET_MM_S,
        "rosetta_i_space_weather": ROSETTA_I_SPACE_WEATHER,
        "mm_s_commonality": summarize_mm_s_commonality(merged),
        "hqiv_runs": [asdict(r) for r in hqiv_rows],
    }

    text = json.dumps(payload, indent=2)
    if args.json:
        path = Path(args.json)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        print(f"Wrote {path}")
    else:
        print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

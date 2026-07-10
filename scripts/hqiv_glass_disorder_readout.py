#!/usr/bin/env python3
"""
Glass / amorphous branch from packing disorder score.

Lean-aligned formula (HQIV rationals only):

  S = γ · [(1 − w_periodic) + Var(CN)/⟨CN⟩ + open²]

Prefer the amorphous packing template when ``S > α``; otherwise keep the
ordered Bravais family (Ih / Ic / FCC / …).

No fitted glass-transition tables; NIST T_g is quarantine only.

Run:
  PYTHONPATH=.:scripts python3 scripts/hqiv_glass_disorder_readout.py
  PYTHONPATH=.:scripts python3 scripts/hqiv_glass_disorder_readout.py \\
    --json-out data/glass_disorder_audit.json
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path
from typing import Any

_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

import hqiv_lean_physics_primitives as lean
from hqiv_lab.allotrope import derive_allotropes, packing_disorder_score
from hqiv_lab.coordination import infer_monomer_geometry
from hqiv_lab.packing import BravaisTopology, templates_for_motif
from hqiv_lab.spec import MoleculeSpec

DEFAULT_JSON = _REPO_ROOT / "data" / "glass_disorder_audit.json"
STRONG = lean.STRONG_CHANNEL_FRACTION
ALPHA = lean.ALPHA
GAMMA = lean.GAMMA

# Quarantine-only handbook glass / amorphous markers — never inputs.
NIST_GLASS: dict[str, dict[str, Any]] = {
    "H2O": {"notes": "LDA/HDA ice; amorphous preferred only under high disorder"},
    "SiO2": {"notes": "network glass former (engineering; not in molecular panel)"},
}


def open_fraction_from_template(label: str, a_factor: float) -> float:
    """Openness proxy: excess cell scale above identity (GENERIC / amorphous)."""
    if label == "amorphous":
        return max(0.0, a_factor - 1.0)
    if label == "Ic":
        return max(0.0, a_factor - 1.0) * GAMMA
    return 0.0


def disorder_row_for_spec(
    name: str,
    *,
    temperature_k: float,
    periodic_weight: float,
    cn_mean: float,
    cn_var: float,
) -> dict[str, Any]:
    spec = MoleculeSpec.from_chart_name(name)
    mono = infer_monomer_geometry(spec)
    templates = templates_for_motif(mono.motif, spec=spec)
    template_rows: list[dict[str, Any]] = []
    for tmpl in templates:
        open_f = open_fraction_from_template(tmpl.label, tmpl.a_factor)
        # Ordered lattices keep full periodic weight; amorphous loses it.
        w_per = (
            periodic_weight * GAMMA
            if tmpl.topology == BravaisTopology.GENERIC_CUBIC
            else periodic_weight
        )
        # Amorphous: inflate CN variance (disordered tetrahedral shell).
        var = cn_var
        if tmpl.label == "amorphous":
            var = max(cn_var, cn_mean * STRONG)
        s = packing_disorder_score(
            periodic_weight=w_per,
            mean_coordination=cn_mean,
            coordination_variance=var,
            open_fraction=open_f,
        )
        template_rows.append(
            {
                "label": tmpl.label,
                "topology": tmpl.topology.value,
                "open_fraction": open_f,
                "periodic_weight_used": w_per,
                "coordination_variance_used": var,
                "disorder_score": s,
                "prefer_amorphous_gate": s > ALPHA,
            }
        )

    cands = derive_allotropes(spec, temperature_k=temperature_k)
    preferred = cands[0] if cands else None
    # Solid-ordered reference: high periodic weight, zero open, zero CN variance.
    s_ordered = packing_disorder_score(
        periodic_weight=1.0,
        mean_coordination=cn_mean,
        coordination_variance=0.0,
        open_fraction=0.0,
    )
    s_disordered = packing_disorder_score(
        periodic_weight=0.0,
        mean_coordination=cn_mean,
        coordination_variance=cn_mean * STRONG,
        open_fraction=ALPHA + GAMMA,
    )
    row: dict[str, Any] = {
        "name": name,
        "motif": mono.motif.value,
        "intermolecular_contacts": mono.intermolecular_contacts,
        "temperature_k": temperature_k,
        "mean_coordination": cn_mean,
        "templates": template_rows,
        "preferred_allotrope": preferred.label if preferred else None,
        "preferred_score": preferred.score if preferred else None,
        "disorder_ordered_reference": s_ordered,
        "disorder_fully_disordered_reference": s_disordered,
        "amorphous_gate_alpha": ALPHA,
        "formula": "S=γ·[(1−w_per)+Var(CN)/⟨CN⟩+open²]; prefer amorphous if S>α",
    }
    if name in NIST_GLASS:
        row["nist_comparison_quarantine"] = dict(NIST_GLASS[name])
    return row


def build_glass_disorder_audit() -> dict[str, Any]:
    # H2O: tetrahedral CN=4; ordered ice vs quenched amorphous probe.
    rows = [
        disorder_row_for_spec(
            "H2O",
            temperature_k=273.15,
            periodic_weight=1.0,
            cn_mean=4.0,
            cn_var=0.0,
        ),
        disorder_row_for_spec(
            "H2O",
            temperature_k=140.0,
            periodic_weight=0.0,
            cn_mean=4.0,
            cn_var=4.0 * STRONG,
        ),
        disorder_row_for_spec(
            "CH4",
            temperature_k=90.0,
            periodic_weight=1.0,
            cn_mean=12.0,
            cn_var=0.0,
        ),
        disorder_row_for_spec(
            "NH3",
            temperature_k=195.8,
            periodic_weight=1.0,
            cn_mean=6.0,
            cn_var=0.0,
        ),
    ]
    # Identity: ordered ice S ≤ α; fully disordered S > α.
    s0 = packing_disorder_score(
        periodic_weight=1.0, mean_coordination=4.0, coordination_variance=0.0, open_fraction=0.0
    )
    s1 = packing_disorder_score(
        periodic_weight=0.0,
        mean_coordination=4.0,
        coordination_variance=4.0 * STRONG,
        open_fraction=ALPHA + GAMMA,
    )
    identity = {
        "ordered_below_alpha": s0 <= ALPHA,
        "disordered_above_alpha": s1 > ALPHA,
        "score_nonneg": s0 >= 0.0 and s1 >= 0.0,
        "h2o_has_amorphous_template": any(
            t["label"] == "amorphous" for t in rows[0]["templates"]
        ),
        "gamma_prefactor": abs(GAMMA - 0.4) < 1e-15,
    }
    return {
        "source": "scripts/hqiv_glass_disorder_readout.py",
        "lean_modules": ["Hqiv.QuantumChemistry.PhaseElasticity"],
        "formula": {
            "disorder_score": "S = γ · [(1−w_periodic) + Var(CN)/⟨CN⟩ + open²]",
            "amorphous_gate": "prefer amorphous template when S > α",
        },
        "identity_checks": identity,
        "all_identity_checks_pass": all(identity.values()),
        "rows": rows,
        "comparison_policy": "NIST/handbook glass markers are quarantine only",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()
    audit = build_glass_disorder_audit()
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(audit, indent=2) + "\n")
    print(f"wrote {args.json_out}")
    print(f"identity_ok={audit['all_identity_checks_pass']}")
    for r in audit["rows"]:
        am = next((t for t in r["templates"] if t["label"] == "amorphous"), None)
        am_s = f"  amorphous S={am['disorder_score']:.4f}" if am else ""
        print(
            f"  {r['name']:4} T={r['temperature_k']:.1f}  "
            f"pref={r['preferred_allotrope']}{am_s}"
        )


if __name__ == "__main__":
    main()

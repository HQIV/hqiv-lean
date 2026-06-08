#!/usr/bin/env python3
"""
Batch benchmark: HQIV mass-spectrum calculator (witness / coupling / informational-energy)
vs published (PDG) masses.

Uses scripts/hqiv_mass_calculator_core.py (same stack as web calculator after fix).
Run: python3 scripts/benchmark_mass_calculator_vs_pdg.py
"""

from __future__ import annotations

import json
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import hqiv_mass_calculator_core as mcc  # noqa: E402
import hqiv_scale_witness as sw  # noqa: E402
import informational_energy_mass as iem  # noqa: E402


@dataclass
class Row:
    config_id: str
    name: str
    structure: str
    variety: str
    note: str
    pipeline: str
    pub_mev: float | None
    hqiv_mev: float
    rel_pct: float | None
    sigma_pull: float | None
    category: str


def main() -> None:
    bundle = sw.load_witness_bundle()
    report = mcc.run_coupling_stack("proton_lockin", mass_row=True)
    qm = mcc.derived_quark_gev()
    catalog = mcc.parse_hadron_catalog()
    pub = json.loads((ROOT / "data/hadron_published_masses.json").read_text())
    by_cid = pub["by_config_id"]
    by_key = pub["by_key"]

    im = report.informational_mass
    print("=" * 72)
    print("HQIV mass calculator vs PDG")
    print("Pipeline: Fano coupling + informational mass row + multiplicative hadron readout")
    print(f"Catalog configurations: {len(catalog)}")
    print(f"Coupling residual ||Ac-b|| = {report.residual:.6g}")
    if im is not None:
        print(
            f"Mass row: c₀+loc = {im.row_lhs_e_tot:.6g}  budget 2π·Ω_k = {im.row_rhs_budget:.6g}  "
            f"residual = {im.row_residual:.6g}"
        )
    print(
        f"Quark ladder (GeV): u={qm['u']:.4f} d={qm['d']:.4f} s={qm['s']:.4f} "
        f"c={qm['c']:.2f} b={qm['b']:.2f}"
    )
    print("=" * 72)

    # Particle stack (p, n, W, Z, H)
    print("\n--- Particle stack (coupling ξ_v + informational readout) ---")
    parts = mcc.particle_rows_from_stack(report, bundle)
    for r in parts:
        primary = r.mass_additive if r.gauge_primary == iem.MassReadoutGauge.ADDITIVE.value else r.mass_multiplicative_rest
        err = r.rel_err_primary
        err_s = f"{err * 100:+.2f}%" if err is not None else "—"
        print(
            f"  {r.label:22s}  primary={primary:.4f} GeV  witness={r.witness_gev:.4f} GeV  Δ={err_s}"
        )

    rows: list[Row] = []
    for c in catalog:
        hres = mcc.hadron_mass_from_stack(c, report=report, bundle=bundle, qm=qm)
        rec = by_cid.get(c["config_id"]) or by_key.get(c["pdgName"])
        pub_m = rec["mass_MeV"] if rec else None
        rel = None
        pull = None
        if pub_m and pub_m > 0:
            rel = 100.0 * (hres.m_mev - pub_m) / pub_m
            if rec and rec.get("uncertainty_MeV", 0) > 0:
                pull = (hres.m_mev - pub_m) / rec["uncertainty_MeV"]
        rows.append(
            Row(
                c["config_id"],
                c["label"],
                c["structure"],
                c["variety_id"],
                c.get("note") or "",
                hres.pipeline,
                pub_m,
                hres.m_mev,
                rel,
                pull,
                rec["category"] if rec else "no_pdg_link",
            )
        )

    linked = [r for r in rows if r.pub_mev is not None]
    by_struct: dict[str, list[Row]] = {}
    for r in linked:
        by_struct.setdefault(r.structure, []).append(r)

    def stats(group: list[Row], label: str) -> None:
        rels = [r.rel_pct for r in group if r.rel_pct is not None]
        if not rels:
            return
        abs_rels = [abs(x) for x in rels]
        print(f"\n{label} (n={len(rels)})")
        print(f"  median |Δ%| = {sorted(abs_rels)[len(abs_rels) // 2]:.1f}%")
        print(f"  mean |Δ%|   = {sum(abs_rels) / len(abs_rels):.1f}%")
        within_15 = sum(1 for x in abs_rels if x <= 15)
        within_50 = sum(1 for x in abs_rels if x <= 50)
        print(f"  within 15%: {within_15}/{len(rels)}")
        print(f"  within 50%: {within_50}/{len(rels)}")
        ranked = [r for r in group if r.rel_pct is not None]
        worst = sorted(ranked, key=lambda r: abs(r.rel_pct), reverse=True)[:5]
        best = sorted(ranked, key=lambda r: abs(r.rel_pct))[:3]
        print("  best:", ", ".join(f"{r.name} ({r.rel_pct:+.1f}%)" for r in best))
        print("  worst:", ", ".join(f"{r.name} ({r.rel_pct:+.1f}%)" for r in worst))

    print("\n--- Hadron catalog (full stack) ---")
    stats(linked, "All PDG-linked hadrons")
    for st in ("baryon", "meson", "tetraquark", "pentaquark"):
        stats(by_struct.get(st, []), f"Structure: {st}")

    ground = [r for r in linked if r.note not in ("decuplet", "vector")]
    excited_dec = [r for r in linked if r.note == "decuplet"]
    excited_vec = [r for r in linked if r.note == "vector"]
    print("\n--- Excited-state tags ---")
    print(f"Ground-like (no decuplet/vector note): {len(ground)}")
    stats(ground, "Ground-like")
    print(f"Decuplet-tagged (+ radial excitation): {len(excited_dec)}")
    if excited_dec:
        stats(excited_dec, "Decuplet tag")
    print(f"Vector-tagged (+ vector excitation): {len(excited_vec)}")
    if excited_vec:
        stats(excited_vec, "Vector tag")

    p = next((r for r in rows if r.config_id == "p"), None)
    if p and p.pub_mev:
        print("\n--- Proton (witness vertex) ---")
        print(f"  p: HQIV {p.hqiv_mev:.3f} MeV  PDG {p.pub_mev:.3f}  Δ={p.rel_pct:+.2f}%  [{p.pipeline}]")

    print("\n--- Not in PDG table ---")
    for r in rows:
        if r.pub_mev is None:
            print(f"  {r.config_id}: HQIV {r.hqiv_mev:.1f} MeV [{r.pipeline}]")

    summary = {
        "pipeline": "coupling+informational_energy+witness_scale",
        "n_catalog": len(rows),
        "n_linked": len(linked),
        "coupling_residual": report.residual,
        "mass_row_residual": im.row_residual if im else None,
        "median_abs_rel_pct_all": (
            sorted([abs(r.rel_pct) for r in linked if r.rel_pct is not None])[len(linked) // 2]
            if linked
            else None
        ),
    }
    out_path = ROOT / "data" / "mass_calculator_benchmark_summary.json"
    out_path.write_text(json.dumps(summary, indent=2) + "\n")
    print(f"\nWrote {out_path.relative_to(ROOT)}")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()

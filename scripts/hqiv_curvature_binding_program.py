#!/usr/bin/env python3
"""
Curvature-first nuclear binding program — G_eff does the coupling work.

Lean spine (``NuclearCurvatureBinding``):

  B_in  = A × trace(m) × Δ(metaHorizonTrappedInsideRatio)
  B_out = G_eff(θ/θ₀) × trace(m) × contact_curvature_ledger(A,Z)
  B_tot = B_in + B_out

For A > 4 the contact ledger is the post-α sphere-touch stack expressed in
curvature contact units (deepening + γ-network − relaxation), still multiplied
by ``G_eff × trace`` — no separate phenomenological MeV ladder.

Witness columns (not merged into the spine):
  • horizon-scale overlap ``γ·modes/R_m`` per valley contact
  • legacy caustic stack and constructive ladder for comparison

Run:
  python3 scripts/hqiv_curvature_binding_program.py
  python3 scripts/hqiv_curvature_binding_program.py --json data/curvature_binding_program.json
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path

import hqiv_binding_energy_program as bep
import hqiv_curvature_binding_core as cbc
import hqiv_excited_states as hes
import hqiv_lean_physics_primitives as lean
import hqiv_nuclear_curvature_binding as ncur
import hqiv_nuclear_outside_temperature_dynamics as notd

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_JSON = ROOT / "data" / "curvature_binding_program.json"
M_SHELL = hes.REFERENCE_M
XI_LOCKIN = lean.XI_LOCKIN
PDG_BINDING_MEV = bep.PDG_BINDING_MEV
DEFAULT_PANEL = bep.DEFAULT_PANEL


@dataclass(frozen=True)
class CurvatureBindingRow:
    label: str
    A: int
    Z: int
    m: int
    m_cluster: int
    theta_rad: float
    eta: float
    g_eff_contact: float
    trace_mev: float
    contact_units: float
    intrinsic_well_deepening: float
    mass_deficit_factor: float
    outside_ladder_mev: float
    outside_gamma_network_mev: float
    outside_tetra_closure_mev: float
    outside_post_alpha_mev: float
    inside_mev: float
    outside_mev: float
    total_curvature_mev: float
    outside_mev_chart: float
    total_curvature_mev_chart: float
    outside_closure_k_mass_chart: float | None
    be_per_a_curvature: float
    horizon_scale_witness_mev: float
    binding_constructive_ladder_mev: float
    binding_caustic_curvature_mev: float
    pdg_binding_total_mev: float | None
    pdg_be_per_a_mev: float | None
    curvature_total_error_pct: float | None
    notes: str


def _pct_error(pred: float, ref: float) -> float | None:
    if ref == 0.0:
        return None
    return (pred - ref) / ref * 100.0


def build_curvature_row(
    A: int,
    Z: int,
    label: str,
    *,
    m_shell: int = M_SHELL,
    c: float = 1.0,
    xi: float | None = None,
    earth_mass_chart: bool = True,
    lab_env: notd.LabOutsideEnvironment | None = None,
) -> CurvatureBindingRow:
    m_cluster = m_shell if A <= 1 else ncur.nucleus_curvature_shell(A)
    k_mass: float | None = None
    if earth_mass_chart:
        env = lab_env or notd.LabOutsideEnvironment(gravity_tier="full")
        k_mass = env.outside_closure_k_mass_chart()
    bd = cbc.curvature_binding_breakdown(
        m_shell, A, Z, m_cluster=m_cluster, c=c, xi=xi, outside_closure_k=k_mass
    )

    caustic_total, _, _ = bep.cluster_binding_caustic_curvature(
        m_shell, A, c=c, m_cluster=m_cluster
    )
    ladder = bep.constructive_ladder_binding_mev(m_shell, A, Z, c=c)

    pdg_b = PDG_BINDING_MEV.get((A, Z))
    pdg_be_a = bep.binding_per_nucleon_mev(pdg_b, A) if pdg_b is not None else None

    notes: list[str] = []
    notes.append(
        f"network: ladder+γ+tetra+postα; D_intr={bd.intrinsic_well_deepening:.3f} "
        f"mass×{bd.mass_deficit_factor:.4f}."
    )
    if xi is not None:
        notes.append(f"ξ={xi:.3g} outside modulator.")
    if k_mass is not None:
        notes.append(f"K_mass_chart={k_mass:.9f} on outside ledger (Earth gravity well).")

    outside_chart = bd.outside_mev_chart if bd.outside_mev_chart is not None else bd.outside_mev
    total_chart = bd.total_mev_chart if bd.total_mev_chart is not None else bd.total_mev

    return CurvatureBindingRow(
        label=label,
        A=A,
        Z=Z,
        m=m_shell,
        m_cluster=m_cluster,
        theta_rad=bd.theta_rad,
        eta=bd.eta,
        g_eff_contact=bd.g_eff_contact,
        trace_mev=bd.trace_mev,
        contact_units=bd.contact_units,
        intrinsic_well_deepening=bd.intrinsic_well_deepening,
        mass_deficit_factor=bd.mass_deficit_factor,
        outside_ladder_mev=bd.outside_ladder_mev,
        outside_gamma_network_mev=bd.outside_gamma_network_mev,
        outside_tetra_closure_mev=bd.outside_tetra_closure_mev,
        outside_post_alpha_mev=bd.outside_post_alpha_mev,
        inside_mev=bd.inside_mev,
        outside_mev=bd.outside_mev,
        total_curvature_mev=bd.total_mev,
        outside_mev_chart=outside_chart,
        total_curvature_mev_chart=total_chart,
        outside_closure_k_mass_chart=k_mass,
        be_per_a_curvature=bep.binding_per_nucleon_mev(bd.total_mev, A),
        horizon_scale_witness_mev=bd.horizon_scale_outside_witness_mev,
        binding_constructive_ladder_mev=ladder,
        binding_caustic_curvature_mev=caustic_total,
        pdg_binding_total_mev=pdg_b,
        pdg_be_per_a_mev=pdg_be_a,
        curvature_total_error_pct=_pct_error(bd.total_mev, pdg_b) if pdg_b else None,
        notes=" ".join(notes),
    )


def build_panel(
    nuclei: tuple[tuple[int, int, str], ...] | None = None,
    *,
    m_shell: int = M_SHELL,
    c: float = 1.0,
    xi: float | None = None,
    earth_mass_chart: bool = True,
    lab_env: notd.LabOutsideEnvironment | None = None,
) -> list[CurvatureBindingRow]:
    panel = nuclei if nuclei is not None else DEFAULT_PANEL
    return [
        build_curvature_row(
            A, Z, label,
            m_shell=m_shell, c=c, xi=xi,
            earth_mass_chart=earth_mass_chart, lab_env=lab_env,
        )
        for A, Z, label in panel
    ]


def panel_error_summary(rows: list[CurvatureBindingRow]) -> dict[str, float | None]:
    def mean_abs(field: str) -> float | None:
        vals: list[float] = []
        for row in rows:
            err = getattr(row, field)
            if err is not None and math.isfinite(err):
                vals.append(abs(err))
        return sum(vals) / len(vals) if vals else None

    import hqiv_isotope_pdg_benchmark as bench

    light = bench.build_payload()["summary"]["mean_abs_mass_error_pct"]
    return {
        "mean_abs_mass_error_pct_light_panel": light,
        "mean_abs_curvature_total_error_pct_vs_pdg_b": mean_abs(
            "curvature_total_error_pct"
        ),
    }


def program_summary(
    rows: list[CurvatureBindingRow], *, m_shell: int = M_SHELL
) -> dict:
    he4 = next((r for r in rows if r.A == 4 and r.Z == 2), None)
    d2 = next((r for r in rows if r.A == 2 and r.Z == 1), None)
    k_row = next((r.outside_closure_k_mass_chart for r in rows if r.outside_closure_k_mass_chart), None)
    return {
        "policy": (
            "Authoritative witness: curvature + G_eff mass ledger "
            "(cluster_binding_canonical_mev; light panel |ΔM|/M ≈ 0.003%). "
            "Outside ledger includes Earth K_mass_chart = B_curv(ξ_lock)·f_g(ε) "
            "(gravity well at ξ_lock; unity B_curv). "
            "PDG total B columns are comparison-only (reference nucleon masses)."
        ),
        "binding_shell_m": m_shell,
        "alpha": lean.ALPHA,
        "outside_closure_K_mass_chart": k_row,
        "earth_outside_closure": notd.earth_outside_closure_k(
            notd.LabOutsideEnvironment(gravity_tier="full")
        ).to_dict()
        if k_row is not None
        else None,
        "formula": {
            "inside": "A × trace × Δ(metaHorizonTrappedInsideRatio)",
            "outside": "contact_units × G_eff(θ/θ₀) × trace × K_mass_chart",
            "lean_module": "Hqiv.Physics.NuclearCurvatureBinding",
        },
        "panel_error_summary": panel_error_summary(rows),
        "he4_reference": {
            "pdg_total_MeV": he4.pdg_binding_total_mev if he4 else None,
            "curvature_MeV": he4.total_curvature_mev if he4 else None,
            "inside_MeV": he4.inside_mev if he4 else None,
            "outside_MeV": he4.outside_mev if he4 else None,
            "G_eff": he4.g_eff_contact if he4 else None,
            "horizon_scale_witness_MeV": he4.horizon_scale_witness_mev if he4 else None,
            "caustic_MeV": he4.binding_caustic_curvature_mev if he4 else None,
        },
        "deuteron_reference": {
            "pdg_total_MeV": d2.pdg_binding_total_mev if d2 else None,
            "curvature_MeV": d2.total_curvature_mev if d2 else None,
            "horizon_scale_witness_MeV": d2.horizon_scale_witness_mev if d2 else None,
        },
        "network_spine": (
            "shared-well: G_eff×trace×A×(1+vc/6)×D_intr + γ-network + barbell + tetra "
            "+ post-α; mass-deficit FP; spin–magnetic residual on outside"
        ),
        "spin_magnetic_residual": (
            "γ·(4/8)·(γ²·vc/(cap·R_m) + spinStab·|A−2Z|/A·vc/cap) — Lean "
            "nuclearSpinMagneticResidualParticipation"
        ),
    }


def export_witness(
    rows: list[CurvatureBindingRow], *, m_shell: int = M_SHELL
) -> dict:
    return {
        "source": "scripts/hqiv_curvature_binding_program.py",
        "summary": program_summary(rows, m_shell=m_shell),
        "rows": [asdict(r) for r in rows],
    }


def print_panel(rows: list[CurvatureBindingRow], *, m_shell: int = M_SHELL) -> None:
    print("HQIV curvature binding program (G_eff + shared-well network)")
    print("=" * 72)
    print(
        f"Shell m={m_shell}  α={lean.ALPHA}  "
        f"B_out = ladder + γ-network + tetra + post-α (mass-deficit FP)"
    )
    print()
    header = (
        f"{'Nucl':<6} {'G_eff':>6} {'D_w':>5} {'B_in':>7} {'B_out':>7} "
        f"{'B_net':>8} {'γ_net':>6} {'PDG_B':>8} {'Δtot%':>7}"
    )
    print(header)
    print("-" * len(header))
    for row in rows:
        pdg_b = (
            f"{row.pdg_binding_total_mev:8.2f}"
            if row.pdg_binding_total_mev
            else "       —"
        )
        d_tot = (
            f"{row.curvature_total_error_pct:+7.1f}"
            if row.curvature_total_error_pct is not None
            else "      —"
        )
        print(
            f"{row.label:<6} {row.g_eff_contact:6.3f} {row.intrinsic_well_deepening:5.2f} "
            f"{row.inside_mev:7.2f} {row.outside_mev:7.2f} "
            f"{row.total_curvature_mev:8.2f} {row.outside_gamma_network_mev:6.2f} "
            f"{pdg_b} {d_tot}"
        )
    stats = panel_error_summary(rows)
    print()
    val_mass = stats.get("mean_abs_mass_error_pct_light_panel")
    val_b = stats.get("mean_abs_curvature_total_error_pct_vs_pdg_b")
    if val_mass is not None:
        print(f"Light-panel |ΔM|/M (mass ledger, authoritative): {val_mass:.3f}%")
    if val_b is not None:
        print(f"Mean |ΔB|/B_PDG (comparison-only): {val_b:.1f}%")
    print()
    print("D_w = intrinsic well deepening from valley occupancy; γ_net = network term")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, default=None, help="Write witness JSON")
    parser.add_argument("--shell", type=int, default=M_SHELL, help="Binding shell m")
    parser.add_argument(
        "--xi",
        type=float,
        default=None,
        help="Optional ξ for outside curvature modulator (BBN / lab)",
    )
    parser.add_argument(
        "--no-earth-k",
        action="store_true",
        help="Disable Earth K_mass_chart on the outside ledger (vacuum chart only)",
    )
    args = parser.parse_args()

    rows = build_panel(m_shell=args.shell, xi=args.xi, earth_mass_chart=not args.no_earth_k)
    print_panel(rows, m_shell=args.shell)

    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(
            json.dumps(export_witness(rows, m_shell=args.shell), indent=2) + "\n"
        )
        print(f"\nWrote {args.json}")


if __name__ == "__main__":
    main()

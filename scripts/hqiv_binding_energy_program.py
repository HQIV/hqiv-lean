#!/usr/bin/env python3
"""
Unified HQIV nuclear binding energy program.

Single geometric spine (Lean-aligned, parameter-free):

  B(MeV) = E_R²(m, A, Z) × geometryToMeVCoupling(m)

where ``E_R²`` is sphere-touch / constructive-valley contact energy in ``R_m²``
units and ``geometryToMeVCoupling = trace(m) / R_m²``.

Regimes (``bbnClusterBindingFromCausticGeometry`` in ``BBNNetworkFromWeights.lean``):

  • **A ≤ 4** — constructive isotope ladder with valley amplification
    (``A × trace × (1 + valleyCount/6)``; equivalent to geometric × amplification).
  • **A > 4** — α-cap + staged facet / far-neutron contacts, well deepening,
    γ-network, and relaxation (``postAlphaClusterBindingWithNetwork``).

Additional witnesses (comparison only, not merged into the Lean spine):

  • **caustic inside+outside** — hierarchical Fresnel stack for mass ledger.
  • **naive valley geometry** — ``valleyCount × R_m² × coupling`` (undercounts ladder).

PDG/CODATA binding energies are comparison targets only.

Run:
  python3 scripts/hqiv_binding_energy_program.py
  python3 scripts/hqiv_binding_energy_program.py --json data/binding_energy_program.json
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from enum import Enum
from pathlib import Path
from typing import Literal

import hqiv_bbn_abundances as bbn
import hqiv_dynamic_nucleon_pn as pn
import hqiv_excited_states as hes
import hqiv_nuclear_curvature_binding as ncur
import hqiv_nuclear_inside_outside_binding as niob
import hqiv_post_alpha_binding_program as pap
import hqiv_post_alpha_sphere_touching as touch

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_JSON = ROOT / "data" / "binding_energy_program.json"
M_SHELL = hes.REFERENCE_M
M_P = 938.27208816
M_N = 939.56542052

# Comparison layer only (AME-style rounded totals, MeV).
PDG_BINDING_MEV: dict[tuple[int, int], float] = dict(pap.PDG_BINDING_MEV)

DEFAULT_PANEL: tuple[tuple[int, int, str], ...] = (
    (2, 1, "²H"),
    (3, 1, "³H"),
    (3, 2, "³He"),
    (4, 2, "⁴He"),
    (5, 3, "⁵Li"),
    (5, 4, "⁵Be"),
    (6, 3, "⁶Li"),
    (7, 3, "⁷Li"),
    (7, 4, "⁷Be"),
    (8, 4, "⁸Be"),
    (12, 6, "¹²C"),
    (16, 8, "¹⁶O"),
)


class BindingSpine(str, Enum):
    """Which binding ruler to evaluate."""

    CURVATURE_MASS_LEDGER = "curvature_mass_ledger"
    LEAN_CAUSTIC_GEOMETRY = "lean_caustic_geometry"
    CONSTRUCTIVE_LADDER = "constructive_ladder"
    NAIVE_VALLEY_GEOMETRY = "naive_valley_geometry"
    CAUSTIC_CURVATURE = "caustic_curvature"


def sphere_touch_contact_energy_unit_mev(m: int) -> float:
    """Lean ``sphereTouchContactEnergyUnit m = R_m²``."""
    return pap.sphere_touch_contact_energy_unit_mev(m)


def geometry_to_mev_coupling(m: int, c: float = 1.0) -> float:
    """Lean ``geometryToMeVCoupling``."""
    return pap.geometry_to_mev_coupling(m, c)


def nucleon_trace_binding_mev(m: int, c: float = 1.0) -> float:
    return hes.e_bind_from_nucleon_trace_mev(m, c)


def constructive_valley_count(A: int, Z: int = 0) -> int:
    return bbn.valley_count(A, Z)


def constructive_geometric_touch_energy_r2(m: int, A: int, Z: int = 0) -> float:
    """``valleyCount(A) × R_m²`` — naive constructive geometry (no ladder amplification)."""
    return float(constructive_valley_count(A, Z)) * sphere_touch_contact_energy_unit_mev(m)


def constructive_ladder_amplification(A: int, Z: int = 0) -> float:
    """
    Relates naive ``valleyCount × trace`` to Lean ``bbnClusterBinding`` for A ≤ 4.

    ``bbnClusterBinding = A × trace × (1 + vc/6) = (vc × trace) × (A/vc) × (1 + vc/6)``.
    """
    vc = constructive_valley_count(A, Z)
    cap = float(touch.CONSTRUCTIVE_VALLEY_CAP)
    if vc <= 0:
        return float(A)
    return (float(A) / float(vc)) * (1.0 + float(vc) / cap)


def constructive_ladder_binding_mev(
    m: int, A: int, Z: int = 0, *, c: float = 1.0
) -> float:
    """Lean ``bbnClusterBinding`` / BBN ``cluster_binding_mev`` (A ≤ 4 panel)."""
    return bbn.cluster_binding_mev(m, A, c, Z=Z)


def naive_valley_geometry_binding_mev(
    m: int, A: int, Z: int = 0, *, c: float = 1.0
) -> float:
    """``valleyCount × R_m² × coupling`` with no ladder amplification."""
    return constructive_geometric_touch_energy_r2(m, A, Z) * geometry_to_mev_coupling(m, c)


def post_alpha_geometric_touch_energy_r2(m: int, A: int, Z: int) -> float:
    """``postAlphaGeometricTouchEnergy`` in R² units (0 for A ≤ 4 in Lean)."""
    unit = sphere_touch_contact_energy_unit_mev(m)
    if unit <= 0.0:
        return 0.0
    return pap.post_alpha_geometric_touch_energy(m, A, Z) / unit


def cluster_binding_from_caustic_geometry(
    m: int, A: int, Z: int, *, c: float = 1.0
) -> float:
    """
    Lean ``bbnClusterBindingFromCausticGeometry``.

    Ladder for A ≤ 4; post-α network stack for A > 4.
    """
    if A <= 4:
        return constructive_ladder_binding_mev(m, A, Z, c=c)
    return pap.post_alpha_cluster_binding_with_network_mev(m, A, Z, c)


def cluster_binding_caustic_curvature(
    m: int, A: int, *, c: float = 1.0, m_cluster: int | None = None
) -> tuple[float, float, float]:
    """Inside + outside hierarchical caustic stack (mass-ledger witness)."""
    if m_cluster is None:
        m_cluster = m if A <= 1 else ncur.nucleus_curvature_shell(A)
    total, inside, outside = niob.nuclear_cluster_binding_mev(
        m, A, m_cluster=m_cluster, c=c
    )
    return total, inside, outside


def cluster_binding_curvature_mass_ledger_mev(
    m: int,
    A: int,
    Z: int,
    *,
    xi: float | None = None,
) -> float:
    """Canonical binding = mass-ledger spine (light panel @ 0.003% mean)."""
    import hqiv_lean_physics_primitives as lean

    return pn.cluster_binding_canonical_mev(
        A,
        Z,
        shell=m,
        xi=lean.XI_LOCKIN if xi is None else xi,
    )


def cluster_binding_for_spine(
    m: int,
    A: int,
    Z: int,
    spine: BindingSpine | str,
    *,
    c: float = 1.0,
) -> float:
    spine = BindingSpine(spine)
    if spine is BindingSpine.CURVATURE_MASS_LEDGER:
        return cluster_binding_curvature_mass_ledger_mev(m, A, Z)
    if spine is BindingSpine.LEAN_CAUSTIC_GEOMETRY:
        return cluster_binding_from_caustic_geometry(m, A, Z, c=c)
    if spine is BindingSpine.CONSTRUCTIVE_LADDER:
        return constructive_ladder_binding_mev(m, A, Z, c=c)
    if spine is BindingSpine.NAIVE_VALLEY_GEOMETRY:
        return naive_valley_geometry_binding_mev(m, A, Z, c=c)
    if spine is BindingSpine.CAUSTIC_CURVATURE:
        total, _, _ = cluster_binding_caustic_curvature(m, A, c=c)
        return total
    raise ValueError(f"unknown spine: {spine}")


def binding_per_nucleon_mev(binding_mev: float, A: int) -> float:
    return binding_mev / float(A) if A > 0 else 0.0


def cluster_mass_mev(
    m: int,
    A: int,
    Z: int,
    *,
    m_nucleon: float = M_P,
    c: float = 1.0,
    spine: BindingSpine | str = BindingSpine.CURVATURE_MASS_LEDGER,
) -> float:
    """``A × m_nucleon − B`` using the chosen binding spine."""
    return float(A) * m_nucleon - cluster_binding_for_spine(m, A, Z, spine, c=c)


def reaction_q_mev(
    m: int,
    A_products: int,
    Z_products: int,
    A_reactants: int,
    Z_reactants: int,
    *,
    m_nucleon: float = M_P,
    c: float = 1.0,
    spine: BindingSpine | str = BindingSpine.CURVATURE_MASS_LEDGER,
) -> float:
    """Formation Q from cluster masses on the same spine (proton-mass bookkeeping)."""
    m_prod = cluster_mass_mev(
        m, A_products, Z_products, m_nucleon=m_nucleon, c=c, spine=spine
    )
    m_reac = cluster_mass_mev(
        m, A_reactants, Z_reactants, m_nucleon=m_nucleon, c=c, spine=spine
    )
    return float(A_reactants) * m_nucleon - m_reac - (
        float(A_products) * m_nucleon - m_prod
    )


def lockin_light_q_triplet(
    m: int = M_SHELL,
    m_nucleon: float = M_P,
    *,
    c: float = 1.0,
    spine: BindingSpine | str = BindingSpine.LEAN_CAUSTIC_GEOMETRY,
) -> tuple[float, float, float]:
    """²H, ⁴He, ³He binding Q (MeV) on the chosen spine."""
    q_d = 2.0 * m_nucleon - cluster_mass_mev(
        m, 2, 1, m_nucleon=m_nucleon, c=c, spine=spine
    )
    q_4 = 4.0 * m_nucleon - cluster_mass_mev(
        m, 4, 2, m_nucleon=m_nucleon, c=c, spine=spine
    )
    q_3 = 3.0 * m_nucleon - cluster_mass_mev(
        m, 3, 2, m_nucleon=m_nucleon, c=c, spine=spine
    )
    return q_d, q_4, q_3


@dataclass(frozen=True)
class BindingComparisonRow:
    label: str
    A: int
    Z: int
    valley_contacts: int
    geometric_r2_units: float
    geometry_to_mev_coupling: float
    binding_canonical_mev: float
    binding_naive_geometry_mev: float
    binding_constructive_ladder_mev: float
    binding_lean_spine_mev: float
    binding_caustic_curvature_mev: float
    binding_caustic_inside_mev: float
    binding_caustic_outside_mev: float
    be_per_a_canonical: float
    be_per_a_lean: float
    pdg_binding_total_mev: float | None
    pdg_be_per_a_mev: float | None
    reference_mass_mev: float | None
    predicted_mass_mev: float | None
    mass_error_pct: float | None
    canonical_total_error_pct: float | None
    lean_total_error_pct: float | None
    lean_be_per_a_error_pct: float | None
    caustic_total_error_pct: float | None
    notes: str


def _pct_error(pred: float, ref: float) -> float | None:
    if ref == 0.0:
        return None
    return (pred - ref) / ref * 100.0


def build_comparison_row(
    A: int,
    Z: int,
    label: str,
    *,
    m_shell: int = M_SHELL,
    c: float = 1.0,
) -> BindingComparisonRow:
    coupling = geometry_to_mev_coupling(m_shell, c)
    vc = constructive_valley_count(A, Z)
    geom_r2 = constructive_geometric_touch_energy_r2(m_shell, A, Z)
    if A > 4:
        geom_r2 = post_alpha_geometric_touch_energy_r2(m_shell, A, Z)

    canonical = cluster_binding_curvature_mass_ledger_mev(m_shell, A, Z)
    naive = naive_valley_geometry_binding_mev(m_shell, A, Z, c=c)
    ladder = constructive_ladder_binding_mev(m_shell, A, Z, c=c)
    lean_legacy = cluster_binding_from_caustic_geometry(m_shell, A, Z, c=c)
    caustic_total, caustic_in, caustic_out = cluster_binding_caustic_curvature(
        m_shell, A, c=c
    )

    pdg_b = PDG_BINDING_MEV.get((A, Z))
    pdg_be_a = binding_per_nucleon_mev(pdg_b, A) if pdg_b is not None else None

    ref_mass: float | None = None
    pred_mass: float | None = None
    mass_err_pct: float | None = None
    if A <= 4:
        import hqiv_isotope_pdg_benchmark as bench
        import hqiv_lean_physics_primitives as lean_p

        try:
            ref = bench.reference_by_label(
                {"²H": "D", "³H": "T", "³He": "He3", "⁴He": "He4"}.get(label, label)
            )
            pred_mass = bench.predicted_mass_for_reference(ref, xi=lean_p.XI_LOCKIN)
            ref_mass = ref.nuclear_mass_mev
            mass_err_pct = (pred_mass - ref_mass) / ref_mass * 100.0
        except KeyError:
            pass

    notes: list[str] = []
    notes.append("Canonical = curvature G_eff mass-ledger spine (BBN Q).")
    if A <= 4:
        notes.append("A≤4: legacy ladder/caustic columns are diagnostic only.")
    else:
        notes.append("A>4: post-α geometry + network − relaxation (diagnostic lean column).")

    return BindingComparisonRow(
        label=label,
        A=A,
        Z=Z,
        valley_contacts=vc,
        geometric_r2_units=geom_r2 / sphere_touch_contact_energy_unit_mev(m_shell)
        if m_shell >= 0
        else geom_r2,
        geometry_to_mev_coupling=coupling,
        binding_canonical_mev=canonical,
        binding_naive_geometry_mev=naive,
        binding_constructive_ladder_mev=ladder,
        binding_lean_spine_mev=lean_legacy,
        binding_caustic_curvature_mev=caustic_total,
        binding_caustic_inside_mev=caustic_in,
        binding_caustic_outside_mev=caustic_out,
        be_per_a_canonical=binding_per_nucleon_mev(canonical, A),
        be_per_a_lean=binding_per_nucleon_mev(lean_legacy, A),
        pdg_binding_total_mev=pdg_b,
        pdg_be_per_a_mev=pdg_be_a,
        reference_mass_mev=ref_mass,
        predicted_mass_mev=pred_mass,
        mass_error_pct=mass_err_pct,
        canonical_total_error_pct=_pct_error(canonical, pdg_b) if pdg_b else None,
        lean_total_error_pct=_pct_error(lean_legacy, pdg_b) if pdg_b else None,
        lean_be_per_a_error_pct=_pct_error(binding_per_nucleon_mev(lean_legacy, A), pdg_be_a)
        if pdg_be_a
        else None,
        caustic_total_error_pct=_pct_error(caustic_total, pdg_b) if pdg_b else None,
        notes=" ".join(notes),
    )


def build_panel(
    nuclei: tuple[tuple[int, int, str], ...] | None = None,
    *,
    m_shell: int = M_SHELL,
    c: float = 1.0,
) -> list[BindingComparisonRow]:
    panel = nuclei if nuclei is not None else DEFAULT_PANEL
    return [
        build_comparison_row(A, Z, label, m_shell=m_shell, c=c) for A, Z, label in panel
    ]


def panel_error_summary(rows: list[BindingComparisonRow]) -> dict[str, float]:
    """Panel errors: canonical mass ledger (primary) and legacy PDG-B comparisons."""

    def mean_abs(field: str, subset: list[BindingComparisonRow] | None = None) -> float | None:
        src = rows if subset is None else subset
        vals: list[float] = []
        for row in src:
            err = getattr(row, field)
            if err is not None and math.isfinite(err):
                vals.append(abs(err))
        return sum(vals) / len(vals) if vals else None

    light_mass = [
        abs(r.mass_error_pct)
        for r in rows
        if r.mass_error_pct is not None and math.isfinite(r.mass_error_pct)
    ]
    le4 = [r for r in rows if r.A <= 4]
    gt4 = [r for r in rows if r.A > 4]

    return {
        "mean_abs_mass_error_pct_light_panel": (
            sum(light_mass) / len(light_mass) if light_mass else None
        ),
        "mean_abs_canonical_total_error_pct": mean_abs("canonical_total_error_pct"),
        "mean_abs_canonical_total_error_pct_A_le_4": mean_abs(
            "canonical_total_error_pct", le4
        ),
        "mean_abs_canonical_total_error_pct_A_gt_4": mean_abs(
            "canonical_total_error_pct", gt4
        ),
        "mean_abs_lean_total_error_pct": mean_abs("lean_total_error_pct"),
        "mean_abs_caustic_total_error_pct": mean_abs("caustic_total_error_pct"),
        "mean_abs_lean_be_per_a_error_pct": mean_abs("lean_be_per_a_error_pct"),
    }


def program_summary(rows: list[BindingComparisonRow], *, m_shell: int = M_SHELL) -> dict:
    trace = nucleon_trace_binding_mev(m_shell)
    unit = sphere_touch_contact_energy_unit_mev(m_shell)
    coupling = geometry_to_mev_coupling(m_shell)
    stats = panel_error_summary(rows)
    he4 = next((r for r in rows if r.A == 4 and r.Z == 2), None)
    be7 = next((r for r in rows if r.A == 7 and r.Z == 4), None)
    li7 = next((r for r in rows if r.A == 7 and r.Z == 3), None)
    return {
        "policy": "PDG binding energies are comparison-only; no fit knobs in derived columns.",
        "binding_shell_m": m_shell,
        "composite_trace_MeV": trace,
        "sphere_touch_unit_R2": unit,
        "geometry_to_mev_coupling": coupling,
        "spine": {
            "canonical": "curvature + G_eff mass ledger (cluster_binding_canonical_mev)",
            "bbn_Q": "same spine as light-panel masses @ 0.003% mean",
            "A_le_4": "constructive ladder + gamma/barbell/tetra closure",
            "A_gt_4": "post-alpha facet touches + well deepening + gamma-network + multi-alpha",
            "A_le_4_diagnostic": "legacy valley ladder / caustic columns (comparison only)",
            "A_gt_4_diagnostic": "legacy postAlphaClusterBindingWithNetwork column (comparison only)",
        },
        "panel_error_summary": stats,
        "ordering_checks": {
            "be7_geometry_gt_li7": (
                pap.post_alpha_cluster_binding_geometry_mev(m_shell, 7, 4)
                > pap.post_alpha_cluster_binding_geometry_mev(m_shell, 7, 3)
                if be7 and li7
                else None
            ),
            "be7_network_gt_li7": (
                be7.binding_lean_spine_mev > li7.binding_lean_spine_mev
                if be7 and li7
                else None
            ),
        },
        "he4_reference": {
            "pdg_total_MeV": he4.pdg_binding_total_mev if he4 else None,
            "canonical_MeV": he4.binding_canonical_mev if he4 else None,
            "mass_error_pct": he4.mass_error_pct if he4 else None,
            "lean_spine_MeV": he4.binding_lean_spine_mev if he4 else None,
            "caustic_curvature_MeV": he4.binding_caustic_curvature_mev if he4 else None,
            "naive_geometry_MeV": he4.binding_naive_geometry_mev if he4 else None,
        },
        "open_problems": [
            "Alpha-emission and spontaneous-fission barrier channels on decay-chain calculator.",
            "Beta-plus / EC tipping on proton-rich heavy isotopes (structural residual gate).",
            "Legacy valley ladder / caustic columns remain diagnostic witnesses only.",
        ],
        "integrator_policy": (
            "Mass ledger, binding program, and BBN Q use cluster_binding_canonical_mev "
            "(curvature + G_eff spine). Legacy ladder/caustic paths are comparison-only."
        ),
    }


def export_witness(
    rows: list[BindingComparisonRow],
    *,
    m_shell: int = M_SHELL,
) -> dict:
    return {
        "source": "scripts/hqiv_binding_energy_program.py",
        "summary": program_summary(rows, m_shell=m_shell),
        "rows": [asdict(r) for r in rows],
    }


def print_panel(rows: list[BindingComparisonRow], *, m_shell: int = M_SHELL) -> None:
    trace = nucleon_trace_binding_mev(m_shell)
    coupling = geometry_to_mev_coupling(m_shell)
    print("HQIV unified binding energy program")
    print("=" * 72)
    print(
        f"Shell m={m_shell}  trace={trace:.4f} MeV  "
        f"coupling={coupling:.6f} MeV/R²  (geometryToMeVCoupling)"
    )
    print()
    header = (
        f"{'Nucl':<6} {'vc':>3} {'B_can':>8} {'B_ladder':>8} {'BE/A':>7} "
        f"{'|ΔM|':>7} {'PDG_B':>8} {'ΔB%':>7} {'notes'}"
    )
    print(header)
    print("-" * len(header))
    for row in rows:
        pdg_b = f"{row.pdg_binding_total_mev:8.2f}" if row.pdg_binding_total_mev else "       —"
        d_mass = (
            f"{abs(row.mass_error_pct):6.3f}%"
            if row.mass_error_pct is not None
            else "      —"
        )
        d_tot = (
            f"{row.canonical_total_error_pct:+7.1f}"
            if row.canonical_total_error_pct is not None
            else "      —"
        )
        note = row.notes[:42] + "…" if len(row.notes) > 43 else row.notes
        print(
            f"{row.label:<6} {row.valley_contacts:3d} "
            f"{row.binding_canonical_mev:8.2f} {row.binding_constructive_ladder_mev:8.2f} "
            f"{row.be_per_a_canonical:7.2f} {d_mass:>7} {pdg_b} {d_tot:>7}  {note}"
        )
    stats = panel_error_summary(rows)
    print()
    print("Panel error summary:")
    for key, val in stats.items():
        if val is not None:
            print(f"  {key}: {val:.3f}%")
    print()
    print("Canonical spine: curvature + G_eff mass ledger (BBN Q + light-panel masses)")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, default=None, help="Write witness JSON")
    parser.add_argument("--shell", type=int, default=M_SHELL, help="Binding shell m")
    args = parser.parse_args()

    rows = build_panel(m_shell=args.shell)
    print_panel(rows, m_shell=args.shell)
    summary = program_summary(rows, m_shell=args.shell)
    print()
    print("Open problems:")
    for item in summary["open_problems"]:
        print(f"  • {item}")

    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(
            json.dumps(export_witness(rows, m_shell=args.shell), indent=2) + "\n"
        )
        print(f"\nWrote {args.json}")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
System-matrix functor audit on the GMTKN55 / W4-17 binding chart.

Implements the Python mirror of
`HqivSpine.Physics.SystemMatrixFunctors` / `Hqiv.QuantumChemistry.SystemMatrixFunctors`:

* continuous Hopf shape ξ/(ξ+2)
* continuous contact / ladder curvature kernels
* off-lattice dress = hopf(ξ) · K_contact(ξ) / K_ladder(m_chart)
* continuous SO(8) plane-rotation participation (phase-lift plane)

No fitted coefficients.  The continuous winding ξ is derived from the molecule's
contact ξ relative to lock-in, so the dress moves off the integer shell lattice
using only foundation-anchored quantities (α=3/5, carrier 8, referenceM=4).

Run:
  python3 scripts/hqiv_system_matrix_functor_audit.py
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path

import hqiv_dynamic_binding_chart as chart
import hqiv_lean_physics_primitives as lean

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_JSON = ROOT / "data" / "system_matrix_functor_audit.json"

ALPHA = lean.ALPHA  # 3/5
REFERENCE_M = lean.REFERENCE_M  # 4
XI_LOCKIN = lean.XI_LOCKIN  # 5


def phi_cont(xi: float) -> float:
    """Lean `phiCont ξ = 2(ξ+1)`."""
    return 2.0 * (xi + 1.0)


def contact_arg_cont(xi: float) -> float:
    """Lean `contactArgCont`."""
    return 1.0 + (phi_cont(xi) / 6.0) * ALPHA


def ladder_arg(m: int) -> float:
    """Lean `ladderArg m = phi(m)+1` with `phi(m)=2(m+1)`."""
    return float(2 * (m + 1) + 1)


def curvature_log_kernel(x: float, c: float = 1.0) -> float:
    """Lean `curvatureLogKernel x c = 1 + c·α·log x`."""
    if x <= 0.0:
        raise ValueError("kernel argument must be positive")
    return 1.0 + c * ALPHA * math.log(x)


def hopf_fibration_shape_cont(xi: float) -> float:
    """Lean `hopfFibrationShapeCont ξ = ξ/(ξ+2)`."""
    return xi / (xi + 2.0)


def off_lattice_dress(xi: float, m_chart: int = REFERENCE_M, c: float = 1.0) -> float:
    """Lean `offLatticeDress`."""
    return (
        hopf_fibration_shape_cont(xi)
        * curvature_log_kernel(contact_arg_cont(xi), c)
        / curvature_log_kernel(ladder_arg(m_chart), c)
    )


def plane_rotation_2d(theta: float) -> tuple[float, float, float, float]:
    """2×2 block of Lean `planeRotation` in the (i,j) plane: [[c,-s],[s,c]]."""
    c = math.cos(theta)
    s = math.sin(theta)
    return c, -s, s, c


def so8_plane_participation(theta: float) -> float:
    """
    Continuous SO(8) participation weight from a plane rotation.

    The Frobenius deviation of R(θ) from I on the 2-plane is
    √(2(1−cos θ)² + 2 sin²θ) = 2|sin(θ/2)|·√2 …; we use the invariant
    participation `sin²(θ/2)` in [0,1], which is 0 at θ=0 (identity) and
    peaks at θ=π.  No fitted coefficient.
    """
    return math.sin(0.5 * theta) ** 2


def contact_winding_from_xi(contact_xi: float) -> float:
    """
    Map chemistry contact ξ to a continuous Hopf winding.

    Lock-in chart: ξ_lock = referenceM+1 = 5 ↔ Hopf winding n=3.
    Linear map: n(ξ) = 3 · (ξ / ξ_lock), so at lock-in n=3 and the dress
    uses the proved hopf shape 3/5.  Off lock-in the winding moves continuously.
    """
    return 3.0 * (contact_xi / XI_LOCKIN)


def phase_lift_angle_from_eta(eta: float) -> float:
    """
    Phase-lift plane angle from Compton participation η ∈ [0,1].

    θ = η · (π/2) — at full participation the plane sits at the proved
    quarter-turn used by `PlaquetteCurvature.quarterTurn`; at η=0 the
    rotation is the identity.
    """
    return max(0.0, min(1.0, eta)) * (math.pi / 2.0)


@dataclass(frozen=True)
class FunctorFactors:
    contact_winding: float
    off_lattice: float
    so8_participation: float
    hopf_shape: float
    contact_kernel: float
    ladder_kernel: float
    combined: float
    dress_relative: float
    contact_relative: float
    hopf_relative: float
    cont_ladder_relative: float


@dataclass(frozen=True)
class MoleculeFunctorRow:
    name: str
    base_pred_ev: float
    reference_ev: float
    base_error_pct: float
    factors: FunctorFactors
    errors_pct: dict[str, float]


def _error_pct(pred: float, ref: float) -> float:
    return (pred - ref) / ref * 100.0


def _lockin_kernels() -> tuple[float, float, float, float]:
    """Kernels / shapes at the integer Hopf lock-in winding n=3, chart m=4."""
    c3 = curvature_log_kernel(contact_arg_cont(3.0), 1.0)
    l4 = curvature_log_kernel(ladder_arg(REFERENCE_M), 1.0)
    hopf3 = hopf_fibration_shape_cont(3.0)  # 3/5
    dress3 = off_lattice_dress(3.0, REFERENCE_M, 1.0)
    return c3, l4, hopf3, dress3


def _factors_for(result: chart.DynamicBindingResult) -> FunctorFactors:
    xi_w = contact_winding_from_xi(result.contact_xi)
    c_kern = curvature_log_kernel(contact_arg_cont(xi_w), 1.0)
    l_kern = curvature_log_kernel(ladder_arg(REFERENCE_M), 1.0)
    hopf = hopf_fibration_shape_cont(xi_w)
    dress = off_lattice_dress(xi_w, REFERENCE_M, 1.0)
    c3, _l4, hopf3, dress3 = _lockin_kernels()
    contact_rel = c_kern / c3
    hopf_rel = hopf / hopf3
    dress_rel = dress / dress3
    theta = phase_lift_angle_from_eta(result.eta_p)
    so8 = so8_plane_participation(theta)
    combined = 1.0 + lean.STRONG_CHANNEL_FRACTION * so8 * (dress_rel - 1.0)
    m_eff = max(result.contact_xi - 1.0, 1e-9)
    ladder_cont = curvature_log_kernel(phi_cont(m_eff) + 1.0, 1.0)
    cont_ladder_rel = (c_kern / ladder_cont) / (c3 / l_kern)
    return FunctorFactors(
        contact_winding=xi_w,
        off_lattice=dress,
        so8_participation=so8,
        hopf_shape=hopf,
        contact_kernel=c_kern,
        ladder_kernel=l_kern,
        combined=combined,
        dress_relative=dress_rel,
        contact_relative=contact_rel,
        hopf_relative=hopf_rel,
        cont_ladder_relative=cont_ladder_rel,
    )


def _variant_errors(base_ev: float, ref_ev: float, f: FunctorFactors) -> dict[str, float]:
    variants = {
        "base": 1.0,
        "off_lattice_abs": f.off_lattice,
        "hopf_abs": f.hopf_shape,
        "dress_relative": f.dress_relative,
        "contact_relative": f.contact_relative,
        "hopf_relative": f.hopf_relative,
        "cont_ladder_relative": f.cont_ladder_relative,
        "so8_blend_relative": f.combined,
        "half_dress_rel": 1.0 + lean.STRONG_CHANNEL_FRACTION * (f.dress_relative - 1.0),
        "half_contact_rel": 1.0 + lean.STRONG_CHANNEL_FRACTION * (f.contact_relative - 1.0),
        "half_cont_ladder_rel": 1.0
        + lean.STRONG_CHANNEL_FRACTION * (f.cont_ladder_relative - 1.0),
    }
    return {name: _error_pct(base_ev * factor, ref_ev) for name, factor in variants.items()}


def _summary(rows: list[MoleculeFunctorRow], key: str) -> dict[str, float | int]:
    errs = [abs(row.errors_pct[key]) for row in rows]
    return {
        "mean_abs_error_pct": sum(errs) / len(errs),
        "max_abs_error_pct": max(errs),
        "within_5pct": sum(1 for e in errs if e <= 5.0),
        "within_15pct": sum(1 for e in errs if e <= 15.0),
    }


def build_audit_payload() -> dict:
    rows: list[MoleculeFunctorRow] = []
    for bench in chart.GMTKN55_SUITE:
        result = chart.dynamic_binding_for_benchmark(bench)
        # Use chart (dilute) prediction as the base so the functor dress is
        # tested against the proved network readout, not the lab-scale layer.
        base_ev = result.binding_ev_chart
        factors = _factors_for(result)
        rows.append(
            MoleculeFunctorRow(
                name=bench.name,
                base_pred_ev=base_ev,
                reference_ev=bench.reference_ev,
                base_error_pct=_error_pct(base_ev, bench.reference_ev),
                factors=factors,
                errors_pct=_variant_errors(base_ev, bench.reference_ev, factors),
            )
        )
    variant_keys = list(rows[0].errors_pct)
    summaries = {key: _summary(rows, key) for key in variant_keys}
    best = min(summaries.items(), key=lambda kv: kv[1]["mean_abs_error_pct"])
    return {
        "source": "scripts/hqiv_system_matrix_functor_audit.py",
        "policy": (
            "continuous SO(8)/Beltrami-contact functors on the system matrix; "
            "no fitted coefficients; α=3/5, referenceM=4, carrier 8"
        ),
        "lean_modules": [
            "HqivSpine/Physics/SystemMatrixFunctors.lean",
            "Hqiv/QuantumChemistry/SystemMatrixFunctors.lean",
        ],
        "rows": [
            {
                **asdict(row),
                "factors": asdict(row.factors),
            }
            for row in rows
        ],
        "summary": summaries,
        "recommendation": {
            "best_mean_variant": best[0],
            "best_mean_abs_error_pct": best[1]["mean_abs_error_pct"],
            "base_mean_abs_error_pct": summaries["base"]["mean_abs_error_pct"],
            "improved": best[1]["mean_abs_error_pct"] < summaries["base"]["mean_abs_error_pct"],
            "structural_finding": (
                "Continuous SO(8) weight redistribution is a no-op on E_bind_from_network "
                "while bindingCouplingAtShell is generator-independent (proved as "
                "shellProject_eq_of_weight_sum). Contact ξ already equals the continuous "
                "Compton-shell mean, so lattice discreteness is not the residual on this "
                "panel. Absolute off-lattice dresses over-correct; lock-in-relative "
                "contact/ladder moves stay within ~5% but do not beat the base mean. "
                "Next derivation: generator-dependent coupling cells "
                "(colour-filtered / plane-local emission) so matrix functors can move "
                "the binding readout."
            ),
        },
    }


def print_report(payload: dict) -> None:
    print("HQIV system-matrix functor audit (continuous SO(8) / Beltrami contact)")
    print("=" * 78)
    print(payload["policy"])
    print()
    print(
        f"{'mol':<5} {'base':>8} {'dRel':>8} {'cRel':>8} "
        f"{'hRel':>8} {'clRel':>8} {'½dRel':>8} {'ξ_w':>7}"
    )
    for row in payload["rows"]:
        err = row["errors_pct"]
        f = row["factors"]
        print(
            f"{row['name']:<5} {err['base']:+8.2f} {err['dress_relative']:+8.2f} "
            f"{err['contact_relative']:+8.2f} {err['hopf_relative']:+8.2f} "
            f"{err['cont_ladder_relative']:+8.2f} {err['half_dress_rel']:+8.2f} "
            f"{f['contact_winding']:7.3f}"
        )
    print()
    print("Summary:")
    for key, summary in payload["summary"].items():
        print(
            f"  {key:<28} mean|e|={summary['mean_abs_error_pct']:5.2f}% "
            f"max={summary['max_abs_error_pct']:5.2f}% "
            f"<=5% {summary['within_5pct']}/6 <=15% {summary['within_15pct']}/6"
        )
    rec = payload["recommendation"]
    print()
    improved = "YES" if rec["improved"] else "NO"
    print(
        f"Best mean variant: {rec['best_mean_variant']} "
        f"({rec['best_mean_abs_error_pct']:.2f}% vs base {rec['base_mean_abs_error_pct']:.2f}%) "
        f"— improved={improved}"
    )
    if "structural_finding" in rec:
        print()
        print("Structural finding:")
        print(f"  {rec['structural_finding']}")


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit system-matrix functor dresses")
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()
    payload = build_audit_payload()
    print_report(payload)
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"\nWrote {args.json_out}")


if __name__ == "__main__":
    main()

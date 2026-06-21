#!/usr/bin/env python3
"""
HQIV outside-curvature overlay calculator (portable reader tool).

Combines Earth-surface gravity / temperature / CMB dipole closure with optional
collider or line-shape facility dressing so comparisons to PDG (or a local
measurement) can use matched outside charts and honest σ metadata.

Lean alignment:
  Hqiv.Physics.HepDecayReadout (colliderCurvatureWidthFactor)
  Hqiv.Physics.ElectroweakMassObservation (facility charts)
  Hqiv.Physics.AcceleratorOutsideDressing (apparent mass)
  Hqiv.Physics.NuclearOutsideTemperatureDynamics (K_mass_chart)

Examples:
  PYTHONPATH=scripts python3 scripts/hqiv_outside_curvature_calculator.py dressing \\
    --magnetic-field-tesla 3.8 --stream-fraction 0.12 --chart collider_native

  PYTHONPATH=scripts python3 scripts/hqiv_outside_curvature_calculator.py compare \\
    --hqiv-mev 2286.46 --reference-mev 2286.46 --sigma-mev 0.14 \\
    --magnetic-field-tesla 3.8 --stream-fraction 0.12

  PYTHONPATH=scripts python3 scripts/hqiv_outside_curvature_calculator.py panel \\
    --magnetic-field-tesla 3.8 --stream-fraction 0.12 --json-out /tmp/panel.json

  PYTHONPATH=scripts python3 scripts/hqiv_outside_curvature_calculator.py batch \\
    --input data/outside_curvature_calculator_example.json
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Literal

import hqiv_electroweak_mass_observation as emo
import hqiv_hep_decay_readout as hdr
import hqiv_nuclear_outside_temperature_dynamics as notd

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_EXAMPLE = ROOT / "data" / "outside_curvature_calculator_example.json"
C_LIGHT_M_S = 299_792_458.0

DressingChart = Literal["line_shape", "collider_universal", "collider_native"]
ComparisonFrame = Literal["earth_tabulated", "facility_apparent"]
GravityTier = Literal["none", "earth", "solar_system", "full"]


@dataclass(frozen=True)
class OutsideEnvironmentOverlay:
    """
    Reader-supplied laboratory + facility parameters.

    Collider stream density uses ``effective_stream_fraction`` =
    ``sqrt(f_stream² + (v_beam/c)²)`` when ``beam_velocity_m_s`` is set.
    """

    magnetic_field_tesla: float = 0.0
    collider_reference_tesla: float = 4.0
    comoving_stream_fraction: float = 0.0
    line_shape_stream_fraction: float = 0.0
    dressing_chart: DressingChart = "collider_universal"
    kinematic_coupling_exponent: float | None = None
    lab_temperature_K: float = notd.LAB_ROOM_TEMPERATURE_K
    gravity_tier: GravityTier = "full"
    cmb_dipole_velocity_m_s: float = notd.CMB_DIPOLE_V_M_S
    beam_velocity_m_s: float | None = None
    facility_id: str = "custom"

    def effective_stream_fraction(self) -> float:
        base = max(self.comoving_stream_fraction, 0.0)
        if self.beam_velocity_m_s is None or self.beam_velocity_m_s <= 0:
            return base
        beta = min(self.beam_velocity_m_s / C_LIGHT_M_S, 0.999999)
        return math.sqrt(base * base + beta * beta)

    def lab_environment(self) -> notd.LabOutsideEnvironment:
        return notd.LabOutsideEnvironment(
            lab_temperature_K=self.lab_temperature_K,
            gravity_tier=self.gravity_tier,
            cmb_dipole_velocity_m_s=self.cmb_dipole_velocity_m_s,
        )

    def k_mass_chart(self) -> float:
        return notd.earth_outside_closure_k(self.lab_environment()).K_mass_chart

    def electroweak_facility(self) -> emo.ElectroweakFacilitySetup:
        exp = self.kinematic_coupling_exponent
        if exp is None:
            if self.dressing_chart == "line_shape":
                exp = 1.0
            elif self.dressing_chart == "collider_native":
                exp = emo.KINEMATIC_COUPLING_EXPONENT_LHC
            else:
                exp = 1.0
        return emo.ElectroweakFacilitySetup(
            id=self.facility_id,
            method="lhc_kinematic" if self.dressing_chart != "line_shape" else "lep_line_shape",
            dressing_chart=self.dressing_chart,
            magnetic_field_tesla=max(self.magnetic_field_tesla, 0.0),
            collider_reference_tesla=max(self.collider_reference_tesla, 1e-9),
            comoving_stream_fraction=self.effective_stream_fraction(),
            line_shape_stream_fraction=max(self.line_shape_stream_fraction, 0.0),
            kinematic_coupling_exponent=float(exp),
        )

    def k_facility(self) -> float:
        if self.dressing_chart == "line_shape" and self.magnetic_field_tesla <= 0:
            return self.electroweak_facility().facility_mass_dressing_factor()
        if (
            self.magnetic_field_tesla <= 0
            and self.effective_stream_fraction() <= 0
            and self.dressing_chart != "line_shape"
        ):
            return 1.0
        return self.electroweak_facility().facility_mass_dressing_factor()

    def k_total(self) -> float:
        return self.k_mass_chart() * self.k_facility()

    def collider_width_factor(self) -> float:
        return self.electroweak_facility().collider_width_factor()

    def dressing_ppm(self) -> float:
        return 1.0e6 * (self.k_facility() - 1.0)


@dataclass(frozen=True)
class DressingUncertainty:
    """Default 1σ relative uncertainty on K_facility from B and stream overlays."""

    sigma_b_fraction: float = 0.05
    sigma_stream_fraction: float = 0.10

    def sigma_k_facility_relative(self, overlay: OutsideEnvironmentOverlay) -> float:
        fac = overlay.electroweak_facility()
        b = max(fac.magnetic_field_tesla, 0.0)
        b_ref = max(fac.effective_collider_reference_tesla(), 1e-9)
        stream = overlay.effective_stream_fraction()
        width = fac.collider_width_factor()
        if overlay.dressing_chart == "line_shape":
            return self.sigma_stream_fraction * 0.5
        if width <= 1.0:
            return 0.0
        n = fac.kinematic_coupling_exponent
        rho_b = hdr.collider_field_curvature_density(b, b_ref)
        rho_s = hdr.comoving_stream_curvature_density(stream)
        denom = max(rho_b + rho_s, 1e-12)
        w_b = 2.0 * rho_b / denom
        w_s = 2.0 * rho_s / denom
        rel_width = math.sqrt(
            (w_b * self.sigma_b_fraction) ** 2 + (w_s * self.sigma_stream_fraction) ** 2
        )
        return n * (width - 1.0) / max(width, 1e-12) * rel_width


@dataclass(frozen=True)
class MassComparisonResult:
    m_hqiv_pole_mev: float
    m_hqiv_apparent_mev: float
    m_reference_mev: float
    delta_mev: float
    abs_error_pct: float
    sigma_reference_mev: float
    sigma_hqiv_pole_mev: float
    sigma_dressing_mev: float
    sigma_combined_mev: float
    n_sigma_combined: float
    comparison_frame: ComparisonFrame
    overlay: OutsideEnvironmentOverlay
    k_mass_chart: float
    k_facility: float
    k_total: float
    delta_lab_mev: float
    delta_accelerator_mev: float

    def as_dict(self) -> dict[str, Any]:
        payload = asdict(self)
        payload["overlay"] = overlay_to_dict(self.overlay)
        return payload


def overlay_from_dict(row: dict[str, Any]) -> OutsideEnvironmentOverlay:
    return OutsideEnvironmentOverlay(
        magnetic_field_tesla=float(row.get("magnetic_field_tesla", 0.0)),
        collider_reference_tesla=float(row.get("collider_reference_tesla", 4.0)),
        comoving_stream_fraction=float(row.get("comoving_stream_fraction", 0.0)),
        line_shape_stream_fraction=float(row.get("line_shape_stream_fraction", 0.0)),
        dressing_chart=row.get("dressing_chart", "collider_universal"),  # type: ignore[arg-type]
        kinematic_coupling_exponent=(
            float(row["kinematic_coupling_exponent"])
            if row.get("kinematic_coupling_exponent") is not None
            else None
        ),
        lab_temperature_K=float(row.get("lab_temperature_K", notd.LAB_ROOM_TEMPERATURE_K)),
        gravity_tier=row.get("gravity_tier", "full"),  # type: ignore[arg-type]
        cmb_dipole_velocity_m_s=float(
            row.get("cmb_dipole_velocity_m_s", notd.CMB_DIPOLE_V_M_S)
        ),
        beam_velocity_m_s=(
            float(row["beam_velocity_m_s"]) if row.get("beam_velocity_m_s") is not None else None
        ),
        facility_id=str(row.get("facility_id", row.get("id", "custom"))),
    )


def overlay_to_dict(overlay: OutsideEnvironmentOverlay) -> dict[str, Any]:
    return {
        "facility_id": overlay.facility_id,
        "magnetic_field_tesla": overlay.magnetic_field_tesla,
        "collider_reference_tesla": overlay.collider_reference_tesla,
        "comoving_stream_fraction": overlay.comoving_stream_fraction,
        "effective_stream_fraction": overlay.effective_stream_fraction(),
        "line_shape_stream_fraction": overlay.line_shape_stream_fraction,
        "dressing_chart": overlay.dressing_chart,
        "kinematic_coupling_exponent": overlay.kinematic_coupling_exponent,
        "lab_temperature_K": overlay.lab_temperature_K,
        "gravity_tier": overlay.gravity_tier,
        "cmb_dipole_velocity_m_s": overlay.cmb_dipole_velocity_m_s,
        "beam_velocity_m_s": overlay.beam_velocity_m_s,
    }


def preset_overlay(name: str) -> OutsideEnvironmentOverlay:
    """Named presets from electroweak / accelerator witness bundles."""
    presets: dict[str, dict[str, Any]] = {
        "earth_lab": {
            "facility_id": "earth_lab",
            "magnetic_field_tesla": 0.0,
            "comoving_stream_fraction": 0.0,
            "dressing_chart": "collider_universal",
        },
        **emo.LEAN_FACILITY_PRESETS,
    }
    if name not in presets:
        raise KeyError(f"unknown preset {name!r}; choose from {sorted(presets)}")
    row = dict(presets[name])
    row["facility_id"] = name
    if row.get("dressing_chart") == "line_shape":
        row.setdefault("magnetic_field_tesla", 0.0)
    return overlay_from_dict(row)


def compare_mass_readout(
    m_hqiv_pole_mev: float,
    m_reference_mev: float,
    sigma_reference_mev: float,
    overlay: OutsideEnvironmentOverlay,
    *,
    comparison_frame: ComparisonFrame = "facility_apparent",
    sigma_hqiv_pole_mev: float = 0.0,
    sigma_dressing_ppm: float | None = None,
    dressing_uncertainty: DressingUncertainty | None = None,
) -> MassComparisonResult:
    """
    Apples-to-apples σ pull vs a reference mass.

    * ``earth_tabulated`` — compare reference to HQIV pole (PDG table at lab).
    * ``facility_apparent`` — compare reference to ``m_pole × K_mass × K_facility``.
    """
    unc = dressing_uncertainty or DressingUncertainty()
    k_lab = overlay.k_mass_chart()
    k_fac = overlay.k_facility()
    k_tot = k_lab * k_fac
    m_apparent = m_hqiv_pole_mev * k_tot
    m_compare = m_hqiv_pole_mev if comparison_frame == "earth_tabulated" else m_apparent
    delta = m_reference_mev - m_compare
    abs_pct = abs(delta) / m_reference_mev * 100.0 if m_reference_mev else 0.0
    if sigma_dressing_ppm is None:
        rel_k = unc.sigma_k_facility_relative(overlay)
        sigma_dress = m_apparent * rel_k if comparison_frame == "facility_apparent" else 0.0
    else:
        sigma_dress = m_apparent * sigma_dressing_ppm / 1.0e6
    sigma_combined = math.sqrt(
        sigma_reference_mev ** 2 + sigma_hqiv_pole_mev ** 2 + sigma_dress ** 2
    )
    n_sigma = abs(delta) / sigma_combined if sigma_combined > 0 else float("inf")
    return MassComparisonResult(
        m_hqiv_pole_mev=m_hqiv_pole_mev,
        m_hqiv_apparent_mev=m_apparent,
        m_reference_mev=m_reference_mev,
        delta_mev=delta,
        abs_error_pct=abs_pct,
        sigma_reference_mev=sigma_reference_mev,
        sigma_hqiv_pole_mev=sigma_hqiv_pole_mev,
        sigma_dressing_mev=sigma_dress,
        sigma_combined_mev=sigma_combined,
        n_sigma_combined=n_sigma,
        comparison_frame=comparison_frame,
        overlay=overlay,
        k_mass_chart=k_lab,
        k_facility=k_fac,
        k_total=k_tot,
        delta_lab_mev=m_hqiv_pole_mev * (k_lab - 1.0),
        delta_accelerator_mev=m_hqiv_pole_mev * (k_fac - 1.0),
    )


def dressing_report(overlay: OutsideEnvironmentOverlay) -> dict[str, Any]:
    fac = overlay.electroweak_facility()
    env = overlay.lab_environment()
    closure = notd.earth_outside_closure_k(env)
    return {
        "overlay": overlay_to_dict(overlay),
        "k_mass_chart": overlay.k_mass_chart(),
        "k_facility": overlay.k_facility(),
        "k_total": overlay.k_total(),
        "dressing_ppm": overlay.dressing_ppm(),
        "collider_width_factor": overlay.collider_width_factor(),
        "facility_mass_dressing_factor": fac.facility_mass_dressing_factor(),
        "gravity_phi_epsilon": env.gravity_phi_epsilon,
        "cmb_proper_motion_v_over_c": env.cmb_proper_motion_v_over_c,
        "earth_closure": {
            "f_gravity": closure.f_gravity,
            "f_kinetic": closure.f_kinetic,
            "increment_vs_anchor_ppm": closure.increment_vs_anchor * 1.0e6,
        },
        "formulas": {
            "k_total": "K_mass_chart * K_facility",
            "k_facility_collider": "(1 + gamma * S_weak * ((B/B_ref)^2 + f_stream^2))^n_kin",
            "k_facility_line_shape": "lineShapeMassFactor(f_line)",
            "m_apparent_mev": "m_pole_mev * k_total",
        },
    }


def score_excited_panel(
    overlay: OutsideEnvironmentOverlay,
    *,
    xi: float | None = None,
) -> list[dict[str, Any]]:
    """Re-score the 85-row excited panel with a custom facility overlay."""
    import hqiv_tuft_mass_spectrum_pdg_eval as tmse
    import export_excited_mass_table as emt

    xi_val = tmse.XI_LOCKIN if xi is None else xi
    rows = emt.build_rows(xi_val)
    unc = DressingUncertainty()
    out: list[dict[str, Any]] = []
    for r in rows:
        if r.hqiv_only or r.pdg_mev is None:
            continue
        earth = compare_mass_readout(
            r.hqiv_mev,
            r.pdg_mev,
            float(r.sigma_mev or 0.01 * r.pdg_mev),
            preset_overlay("earth_lab"),
            comparison_frame="earth_tabulated",
            sigma_hqiv_pole_mev=0.0,
        )
        fac = compare_mass_readout(
            r.hqiv_mev,
            r.pdg_mev,
            float(r.sigma_mev or 0.01 * r.pdg_mev),
            overlay,
            comparison_frame="facility_apparent",
            sigma_hqiv_pole_mev=0.0,
            dressing_uncertainty=unc,
        )
        listed_sigma = float(r.sigma_mev) if r.sigma_mev and r.sigma_mev > 0 else None
        out.append(
            {
                "pdg_key": r.pdg_key,
                "name": r.name,
                "category": r.category,
                "hqiv_pole_mev": r.hqiv_mev,
                "pdg_mev": r.pdg_mev,
                "listed_sigma_mev": listed_sigma,
                "n_sigma_earth_pole": earth.n_sigma_combined,
                "n_sigma_facility_apparent": fac.n_sigma_combined,
                "abs_error_pct_earth": earth.abs_error_pct,
                "abs_error_pct_facility": fac.abs_error_pct,
                "m_hqiv_apparent_mev": fac.m_hqiv_apparent_mev,
                "sigma_combined_facility_mev": fac.sigma_combined_mev,
                "delta_facility_mev": fac.delta_mev,
                "discharge_match": r.match,
            }
        )
    return out


def panel_summary(scored: list[dict[str, Any]]) -> dict[str, Any]:
    if not scored:
        return {}
    earth_ns = [r["n_sigma_earth_pole"] for r in scored]
    fac_ns = [r["n_sigma_facility_apparent"] for r in scored]
    return {
        "row_count": len(scored),
        "within_1sigma_earth": sum(1 for x in earth_ns if x <= 1.0),
        "within_1sigma_facility": sum(1 for x in fac_ns if x <= 1.0),
        "within_2sigma_earth": sum(1 for x in earth_ns if x <= 2.0),
        "within_2sigma_facility": sum(1 for x in fac_ns if x <= 2.0),
        "mean_n_sigma_earth": sum(earth_ns) / len(earth_ns),
        "mean_n_sigma_facility": sum(fac_ns) / len(fac_ns),
        "max_n_sigma_earth": max(earth_ns),
        "max_n_sigma_facility": max(fac_ns),
    }


def run_batch(payload: dict[str, Any]) -> dict[str, Any]:
    overlay = overlay_from_dict(payload.get("overlay") or payload.get("environment") or {})
    results: list[dict[str, Any]] = []
    for row in payload.get("comparisons") or []:
        cmp = compare_mass_readout(
            float(row["hqiv_pole_mev"]),
            float(row["reference_mev"]),
            float(row.get("sigma_reference_mev", row.get("sigma_mev", 0.0))),
            overlay,
            comparison_frame=row.get("comparison_frame", "facility_apparent"),  # type: ignore[arg-type]
            sigma_hqiv_pole_mev=float(row.get("sigma_hqiv_pole_mev", 0.0)),
            sigma_dressing_ppm=(
                float(row["sigma_dressing_ppm"])
                if row.get("sigma_dressing_ppm") is not None
                else None
            ),
        )
        results.append({"label": row.get("label"), **cmp.as_dict()})
    out: dict[str, Any] = {
        "source": "scripts/hqiv_outside_curvature_calculator.py",
        "dressing": dressing_report(overlay),
        "comparisons": results,
    }
    if payload.get("include_panel"):
        scored = score_excited_panel(overlay)
        out["excited_panel"] = scored
        out["excited_panel_summary"] = panel_summary(scored)
    return out


def _add_overlay_args(p: argparse.ArgumentParser) -> None:
    p.add_argument("--preset", type=str, default=None, help="Named facility preset")
    p.add_argument("--magnetic-field-tesla", type=float, default=None, dest="b_tesla")
    p.add_argument("--reference-tesla", type=float, default=4.0, dest="b_ref")
    p.add_argument("--stream-fraction", type=float, default=0.0, dest="stream")
    p.add_argument(
        "--line-shape-stream-fraction", type=float, default=0.0, dest="line_stream"
    )
    p.add_argument(
        "--chart",
        choices=("collider_universal", "collider_native", "line_shape"),
        default=None,
    )
    p.add_argument("--kinematic-exponent", type=float, default=None, dest="kin_exp")
    p.add_argument("--lab-temperature-k", type=float, default=notd.LAB_ROOM_TEMPERATURE_K)
    p.add_argument(
        "--gravity-tier",
        choices=("none", "earth", "solar_system", "full"),
        default="full",
    )
    p.add_argument("--beam-velocity-m-s", type=float, default=None, dest="beam_v")
    p.add_argument("--facility-id", type=str, default="custom")


def _overlay_from_args(args: argparse.Namespace) -> OutsideEnvironmentOverlay:
    if args.preset:
        overlay = preset_overlay(args.preset)
    else:
        overlay = OutsideEnvironmentOverlay(facility_id=args.facility_id)
    if args.b_tesla is not None:
        overlay = OutsideEnvironmentOverlay(
            **{
                **asdict(overlay),
                "magnetic_field_tesla": args.b_tesla,
            }
        )
    updates: dict[str, Any] = {}
    if args.b_ref != 4.0:
        updates["collider_reference_tesla"] = args.b_ref
    if args.stream:
        updates["comoving_stream_fraction"] = args.stream
    if args.line_stream:
        updates["line_shape_stream_fraction"] = args.line_stream
    if args.chart:
        updates["dressing_chart"] = args.chart
    if args.kin_exp is not None:
        updates["kinematic_coupling_exponent"] = args.kin_exp
    if args.lab_temperature_k != notd.LAB_ROOM_TEMPERATURE_K:
        updates["lab_temperature_K"] = args.lab_temperature_k
    if args.gravity_tier != "full":
        updates["gravity_tier"] = args.gravity_tier
    if args.beam_v is not None:
        updates["beam_velocity_m_s"] = args.beam_v
    if updates:
        overlay = OutsideEnvironmentOverlay(**{**asdict(overlay), **updates})
    return overlay


def _print_dressing(report: dict[str, Any]) -> None:
    ov = report["overlay"]
    print("HQIV outside-curvature dressing")
    print("=" * 60)
    print(f"Facility id:           {ov['facility_id']}")
    print(f"B field (T):           {ov['magnetic_field_tesla']:.4g}")
    print(f"B_ref (T):             {ov['collider_reference_tesla']:.4g}")
    print(f"Stream fraction:       {ov['comoving_stream_fraction']:.4g}")
    print(f"Effective stream:      {ov['effective_stream_fraction']:.4g}")
    print(f"Chart:                 {ov['dressing_chart']}")
    print(f"Lab T (K):             {ov['lab_temperature_K']:.4g}")
    print(f"Gravity tier:          {ov['gravity_tier']}")
    print("-" * 60)
    print(f"K_mass_chart:          {report['k_mass_chart']:.9f}")
    print(f"K_facility:            {report['k_facility']:.9f}  ({report['dressing_ppm']:.1f} ppm)")
    print(f"K_total:               {report['k_total']:.9f}")
    print(f"F_collider (width):    {report['collider_width_factor']:.6f}")
    print(f"Gravity ε_φ:           {report['gravity_phi_epsilon']:.3e}")
    print(f"CMB dipole v/c:        {report['cmb_proper_motion_v_over_c']:.6f}")


def _print_comparison(c: MassComparisonResult) -> None:
    print("Mass comparison (apples-to-apples σ)")
    print("=" * 60)
    print(f"Frame:                 {c.comparison_frame}")
    print(f"HQIV pole (MeV):       {c.m_hqiv_pole_mev:.4f}")
    print(f"HQIV apparent (MeV):   {c.m_hqiv_apparent_mev:.4f}")
    print(f"Reference (MeV):       {c.m_reference_mev:.4f}")
    print(f"Δ (MeV):               {c.delta_mev:+.4f}  ({c.abs_error_pct:.4f}%)")
    print("-" * 60)
    print(f"σ_reference:           {c.sigma_reference_mev:.4g} MeV")
    print(f"σ_HQIV pole:           {c.sigma_hqiv_pole_mev:.4g} MeV")
    print(f"σ_dressing (fac.):     {c.sigma_dressing_mev:.4g} MeV")
    print(f"σ_combined:            {c.sigma_combined_mev:.4g} MeV")
    print(f"n_σ (combined):        {c.n_sigma_combined:.3f}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="HQIV outside-curvature overlay calculator (portable reader tool)."
    )
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_dress = sub.add_parser("dressing", help="Compute K factors from environment inputs")
    _add_overlay_args(p_dress)
    p_dress.add_argument("--json-out", type=Path, default=None)

    p_cmp = sub.add_parser("compare", help="σ pull vs reference with matched outside chart")
    _add_overlay_args(p_cmp)
    p_cmp.add_argument("--hqiv-mev", type=float, required=True, dest="hqiv")
    p_cmp.add_argument("--reference-mev", type=float, required=True, dest="ref")
    p_cmp.add_argument("--sigma-mev", type=float, default=0.0)
    p_cmp.add_argument("--sigma-hqiv-mev", type=float, default=0.0)
    p_cmp.add_argument(
        "--frame",
        choices=("earth_tabulated", "facility_apparent"),
        default="facility_apparent",
    )
    p_cmp.add_argument("--json-out", type=Path, default=None)

    p_panel = sub.add_parser(
        "panel", help="Re-score excited mass panel (85 PDG rows) with your overlay"
    )
    _add_overlay_args(p_panel)
    p_panel.add_argument("--json-out", type=Path, default=None)
    p_panel.add_argument("--csv-out", type=Path, default=None)

    p_batch = sub.add_parser("batch", help="Run comparisons from JSON input file")
    p_batch.add_argument("--input", type=Path, default=DEFAULT_EXAMPLE)
    p_batch.add_argument("--json-out", type=Path, default=None)

    sub.add_parser("presets", help="List named facility presets")

    args = parser.parse_args(argv)

    if args.cmd == "presets":
        names = sorted(set(emo.LEAN_FACILITY_PRESETS) | {"earth_lab"})
        for name in names:
            ov = preset_overlay(name)
            print(f"{name:18} K_fac={ov.k_facility():.6f}  B={ov.magnetic_field_tesla} T")
        return 0

    if args.cmd == "dressing":
        report = dressing_report(_overlay_from_args(args))
        _print_dressing(report)
        if args.json_out:
            args.json_out.parent.mkdir(parents=True, exist_ok=True)
            args.json_out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
            print(f"\nWrote {args.json_out}")
        return 0

    if args.cmd == "compare":
        overlay = _overlay_from_args(args)
        result = compare_mass_readout(
            args.hqiv,
            args.ref,
            args.sigma_mev,
            overlay,
            comparison_frame=args.frame,  # type: ignore[arg-type]
            sigma_hqiv_pole_mev=args.sigma_hqiv_mev,
        )
        _print_comparison(result)
        if args.json_out:
            args.json_out.parent.mkdir(parents=True, exist_ok=True)
            args.json_out.write_text(
                json.dumps(result.as_dict(), indent=2) + "\n", encoding="utf-8"
            )
            print(f"\nWrote {args.json_out}")
        return 0

    if args.cmd == "panel":
        overlay = _overlay_from_args(args)
        scored = score_excited_panel(overlay)
        summary = panel_summary(scored)
        print("Excited mass panel — facility overlay σ summary")
        print("=" * 60)
        for k, v in summary.items():
            print(f"{k}: {v}")
        payload = {
            "source": "scripts/hqiv_outside_curvature_calculator.py",
            "dressing": dressing_report(overlay),
            "summary": summary,
            "rows": scored,
        }
        if args.json_out:
            args.json_out.parent.mkdir(parents=True, exist_ok=True)
            args.json_out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
            print(f"\nWrote {args.json_out}")
        if args.csv_out:
            import csv

            fields = list(scored[0].keys()) if scored else []
            args.csv_out.parent.mkdir(parents=True, exist_ok=True)
            with args.csv_out.open("w", encoding="utf-8", newline="") as fh:
                w = csv.DictWriter(fh, fieldnames=fields)
                w.writeheader()
                w.writerows(scored)
            print(f"Wrote {args.csv_out}")
        return 0

    if args.cmd == "batch":
        payload = json.loads(args.input.read_text(encoding="utf-8"))
        out = run_batch(payload)
        if args.json_out:
            args.json_out.parent.mkdir(parents=True, exist_ok=True)
            args.json_out.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
            print(f"Wrote {args.json_out}")
        else:
            print(json.dumps(out, indent=2))
        return 0

    return 1


if __name__ == "__main__":
    sys.exit(main())

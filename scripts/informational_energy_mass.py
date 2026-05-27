#!/usr/bin/env python3
"""
Informational energy → mass readout (Lean mirror).

Natural units (c = ħ = T_Pl = 1):
  E_tot(m, ξ) = m + 1/Θ_local(ξ)     with Θ_local(ξ) = 1/ξ
  localization(ξ) = ξ

Readout gauges (see `Hqiv/Physics/InformationalEnergyMass.lean`):
  • additiveLocalization   — boson-style: return full E_tot (rest + 1/Θ)
  • multiplicativeLapse    — hadron-style: rest slot only, ÷ N_lapse
  • hybrid                 — (E_tot additive) then ÷ N_lapse (not lapse-then-add loc)

Gauge transformation (Lean `gauge_transformation_localization_to_lapse`):
  m_rest + loc = m_rest / N  ⟺  m_rest = loc·N / (1 - N)  for N ≠ 0, 1.

Run:
  python3 scripts/informational_energy_mass.py
  python3 scripts/informational_energy_mass.py --solve
  python3 scripts/informational_energy_mass.py --from-coupling --mass-row
  python3 scripts/informational_energy_mass.py --solve --continuous-xi --mixing-rows
  python3 scripts/informational_energy_mass.py --json

Coupling mass row (Lean `informationalEnergyMassRow`): c₀ + loc(ξ_G) = 2π·Ω_k(ξ_G).

Particle mode (--from-coupling): attach HQIV-derived rest masses (GeV) at Fano vertices,
use solved ξ_v from the coupling script, and report additive vs multiplicative gauges.

Run:
  python3 scripts/informational_energy_mass.py --from-coupling --mass-row --particles
  python3 scripts/informational_energy_mass.py --solve --particles all --phi 0.02 --t 0.1
  python3 scripts/informational_energy_mass.py --solve --mass-row --mass-row-weight-scan --scale-witness codata_alpha
  python3 scripts/informational_energy_mass.py --solve --mass-row --nucleon-lapse-scan
  python3 scripts/hqiv_excited_states.py --table
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import asdict, dataclass
from enum import Enum
from pathlib import Path
from typing import Any, Literal

MassSource = Literal["lean", "pdg"]

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(_ROOT / "scripts"))

import cubic_phase_relax_probe as cpr  # noqa: E402
import hqiv_scale_witness as sw  # noqa: E402

T_PL = 1.0
PHI_COEFF = cpr.PHI_TEMPERATURE_COEFF
REFERENCE_M = cpr.REFERENCE_M
XI_LOCKIN = sw.XI_LOCKIN
BOSON_CLOSURE_SHELL = REFERENCE_M + 1
XI_BOSON = float(BOSON_CLOSURE_SHELL + 1)
TWO_PI = 2.0 * math.pi
DEFAULT_WITNESS_JSON = sw.DEFAULT_WITNESS_JSON


class MassReadoutGauge(str, Enum):
    ADDITIVE = "additiveLocalization"
    MULTIPLICATIVE = "multiplicativeLapse"
    HYBRID = "hybrid"


def theta_local_xi(xi: float) -> float:
    """Θ_local(ξ) = T_Pl / ξ (Lean `thetaLocal_xi` / `T_xi`)."""
    if xi == 0.0:
        raise ValueError("ξ must be nonzero for Θ_local")
    return T_PL / xi


def localization_energy(xi: float) -> float:
    """1 / Θ_local(ξ) = ξ when T_Pl = 1."""
    return 1.0 / theta_local_xi(xi)


def informational_energy_total(m_rest: float, xi: float) -> float:
    """E_tot = m + 1/Θ at ξ."""
    return m_rest + localization_energy(xi)


def informational_energy_total_si(m_kg: float, c: float, hbar: float, delta_x: float) -> float:
    return m_kg * c**2 + hbar * c / delta_x


def shell_lapse_xi(xi: float, phi: float = 0.0, t: float = 0.0) -> float:
    """N = 1 + Φ + φ(ξ)·t with φ(ξ) = 2/Θ = 2ξ."""
    phi_xi = PHI_COEFF / theta_local_xi(xi)
    return 1.0 + phi + phi_xi * t


def m_rest_gauge_calibration(loc: float, lapse: float) -> float:
    """Rest mass calibrating additive vs multiplicative readouts (Lean `m_rest_gauge_calibration`)."""
    if lapse in (0.0, 1.0):
        raise ValueError("gauge calibration requires lapse ∉ {0, 1}")
    return loc * lapse / (1.0 - lapse)


def gauge_additive_equals_multiplicative(loc: float, lapse: float, tol: float = 1e-9) -> bool:
    """Check m_rest + loc = m_rest / lapse at calibrated m_rest."""
    m = m_rest_gauge_calibration(loc, lapse)
    return abs((m + loc) - (m / lapse)) <= tol * max(1.0, abs(m + loc))


def mass_from_informational_energy(
    e_tot: float, gauge: MassReadoutGauge, lapse: float = 1.0
) -> float:
    if gauge == MassReadoutGauge.ADDITIVE:
        return e_tot
    if gauge == MassReadoutGauge.MULTIPLICATIVE:
        return e_tot / lapse
    if gauge == MassReadoutGauge.HYBRID:
        return mass_from_informational_energy(
            mass_from_informational_energy(e_tot, MassReadoutGauge.ADDITIVE, 1.0),
            MassReadoutGauge.MULTIPLICATIVE,
            lapse,
        )
    raise ValueError(gauge)


def mass_from_xi(
    m_raw: float,
    xi_p: float,
    gauge: MassReadoutGauge,
    phi: float = 0.0,
    t: float = 0.0,
) -> float:
    e_tot = informational_energy_total(m_raw, xi_p)
    lapse = shell_lapse_xi(xi_p, phi=phi, t=t)
    return mass_from_informational_energy(e_tot, gauge, lapse)


def hadron_mass_from_xi(m_raw: float, xi_p: float, phi: float = 0.0, t: float = 0.0) -> float:
    """Rest slot only; localization in lapse (Lean `hadronMassFromXi`)."""
    lapse = shell_lapse_xi(xi_p, phi=phi, t=t)
    return mass_from_informational_energy(m_raw, MassReadoutGauge.MULTIPLICATIVE, lapse)


def hybrid_mass_from_xi(m_raw: float, xi_p: float, phi: float = 0.0, t: float = 0.0) -> float:
    """Additive E_tot first, then ÷ N (Lean `hybrid`; not lapse-then-localize)."""
    e_tot = informational_energy_total(m_raw, xi_p)
    lapse = shell_lapse_xi(xi_p, phi=phi, t=t)
    return mass_from_informational_energy(e_tot, MassReadoutGauge.HYBRID, lapse)


def lapse_then_localization_mass(m_raw: float, xi_p: float, phi: float = 0.0, t: float = 0.0) -> float:
    """Alternate order (not default hybrid): m_raw/N + loc."""
    lapse = shell_lapse_xi(xi_p, phi=phi, t=t)
    return m_raw / lapse + localization_energy(xi_p)


@dataclass(frozen=True)
class ParticleSpec:
    """Fano vertex + rest mass for informational-energy readout."""

    key: str
    label: str
    vertex: int
    gauge_primary: MassReadoutGauge
    lean_mass_gev: float
    pdg_mass_gev: float


DEFAULT_PARTICLES: tuple[str, ...] = ("proton", "neutron", "w", "z", "h")


def particle_catalog(bundle: sw.WitnessBundle | None = None) -> dict[str, ParticleSpec]:
    b = bundle or sw.load_witness_bundle()
    return {
        "proton": ParticleSpec(
            "proton",
            "proton (lock-in v1, uud)",
            vertex=1,
            gauge_primary=MassReadoutGauge.MULTIPLICATIVE,
            lean_mass_gev=b.derived_proton_mass_gev,
            pdg_mass_gev=sw.PDG_M_PROTON_GEV,
        ),
        "neutron": ParticleSpec(
            "neutron",
            "neutron (lock-in v1, udd)",
            vertex=1,
            gauge_primary=MassReadoutGauge.MULTIPLICATIVE,
            lean_mass_gev=b.derived_neutron_mass_gev,
            pdg_mass_gev=sw.PDG_M_NEUTRON_GEV,
        ),
        "w": ParticleSpec(
            "w",
            "W (up g1 v2)",
            vertex=2,
            gauge_primary=MassReadoutGauge.ADDITIVE,
            lean_mass_gev=b.M_W_gev,
            pdg_mass_gev=sw.PDG_M_W_GEV,
        ),
        "z": ParticleSpec(
            "z",
            "Z (up g2 v3)",
            vertex=3,
            gauge_primary=MassReadoutGauge.ADDITIVE,
            lean_mass_gev=b.M_Z_gev,
            pdg_mass_gev=sw.PDG_M_Z_GEV,
        ),
        "h": ParticleSpec(
            "h",
            "Higgs (v6)",
            vertex=6,
            gauge_primary=MassReadoutGauge.ADDITIVE,
            lean_mass_gev=b.m_H_gev,
            pdg_mass_gev=sw.PDG_M_H_GEV,
        ),
    }


def parse_particle_keys(raw: str | None, bundle: sw.WitnessBundle | None = None) -> list[str]:
    if raw is None or raw.strip().lower() in ("all", "*"):
        return list(DEFAULT_PARTICLES)
    keys = [k.strip().lower() for k in raw.split(",") if k.strip()]
    catalog = particle_catalog(bundle)
    unknown = [k for k in keys if k not in catalog]
    if unknown:
        raise ValueError(f"unknown particles {unknown}; choose from {sorted(catalog)}")
    return keys


def witness_mass_gev(spec: ParticleSpec, source: MassSource) -> float:
    return spec.pdg_mass_gev if source == "pdg" else spec.lean_mass_gev


def rel_error(predicted: float, target: float) -> float | None:
    if target == 0.0:
        return None
    return (predicted - target) / target


@dataclass
class ParticleMassRow:
    particle_key: str
    label: str
    vertex: int
    xi: float
    m_rest_gev: float
    witness_gev: float
    mass_source: str
    gauge_primary: str
    e_tot: float
    localization: float
    lapse: float
    mass_additive: float
    mass_multiplicative_rest: float
    mass_hybrid: float
    rel_err_additive: float | None
    rel_err_multiplicative: float | None
    rel_err_primary: float | None

    @property
    def m_raw(self) -> float:
        """Alias for JSON consumers expecting `m_raw`."""
        return self.m_rest_gev


def build_particle_row(
    spec: ParticleSpec,
    xi: float,
    *,
    mass_source: MassSource = "lean",
    phi: float = 0.0,
    t: float = 0.0,
) -> ParticleMassRow:
    m_rest = witness_mass_gev(spec, mass_source)
    loc = localization_energy(xi)
    e_tot = informational_energy_total(m_rest, xi)
    lapse = shell_lapse_xi(xi, phi=phi, t=t)
    m_add = mass_from_xi(m_rest, xi, MassReadoutGauge.ADDITIVE, phi=phi, t=t)
    m_mult = hadron_mass_from_xi(m_rest, xi, phi=phi, t=t)
    m_hyb = hybrid_mass_from_xi(m_rest, xi, phi=phi, t=t)
    witness = witness_mass_gev(spec, mass_source)
    primary = m_add if spec.gauge_primary == MassReadoutGauge.ADDITIVE else m_mult
    return ParticleMassRow(
        particle_key=spec.key,
        label=spec.label,
        vertex=spec.vertex,
        xi=xi,
        m_rest_gev=m_rest,
        witness_gev=witness,
        mass_source=mass_source,
        gauge_primary=spec.gauge_primary.value,
        e_tot=e_tot,
        localization=loc,
        lapse=lapse,
        mass_additive=m_add,
        mass_multiplicative_rest=m_mult,
        mass_hybrid=m_hyb,
        rel_err_additive=rel_error(m_add, witness),
        rel_err_multiplicative=rel_error(m_mult, witness),
        rel_err_primary=rel_error(primary, witness),
    )


def rows_from_coupling_particles(
    report: Any,
    particle_keys: list[str],
    *,
    bundle: sw.WitnessBundle | None = None,
    mass_source: MassSource = "lean",
    phi: float = 0.0,
    t: float = 0.0,
) -> list[ParticleMassRow]:
    """Predictions at solved ξ_v with HQIV/PDG rest masses (GeV chart)."""
    xis = report.holonomy_xi_vertices
    if xis is None:
        xis = [float(s + 1) for s in report.shells]
    catalog = particle_catalog(bundle)
    rows: list[ParticleMassRow] = []
    for key in particle_keys:
        spec = catalog[key]
        if spec.vertex < 0 or spec.vertex >= len(xis):
            raise IndexError(f"vertex {spec.vertex} out of range for ξ list len={len(xis)}")
        rows.append(
            build_particle_row(
                spec,
                float(xis[spec.vertex]),
                mass_source=mass_source,
                phi=phi,
                t=t,
            )
        )
    return rows


def example_rows(bundle: sw.WitnessBundle | None = None) -> list[ParticleMassRow]:
    """Static ξ placeholders when coupling solve is not run."""
    catalog = particle_catalog(bundle)
    xi_by_vertex = {
        0: float(REFERENCE_M),
        1: float(REFERENCE_M + 1),
        2: float(REFERENCE_M + 1),
        3: float(REFERENCE_M + 2),
        6: XI_BOSON,
    }
    return [
        build_particle_row(catalog[key], xi_by_vertex[catalog[key].vertex])
        for key in DEFAULT_PARTICLES
    ]


def omega_k_at_xi(xi: float, xi_lock: float = XI_LOCKIN) -> float:
    """Ω_k(ξ) = I(ξ)/I(ξ_lock); mirrors `hqiv_coupling_linear_system.omega_k_at_xi`."""
    import hqiv_shell_shape_geometry as ssg  # noqa: E402

    return ssg.omega_k_continuous(xi, xi_lock)


def mass_row_budget_two_pi_omega(xi_g: float, xi_lock: float = XI_LOCKIN) -> float:
    """Lean informationalEnergyMassRow budget: 2π·Ω_k(ξ_G)."""
    return TWO_PI * omega_k_at_xi(xi_g, xi_lock)


def print_informational_mass_row(report: Any) -> None:
    """Print 2π·Ω_k row check when present on a coherence report."""
    im = getattr(report, "informational_mass", None)
    if im is None:
        return
    print()
    print("Informational mass row (2π·Ω_k budget, Lean informationalEnergyMassRow):")
    print(f"  ξ_G = {im.xi_g:.4f}   Ω_k = {im.omega_k:.4f}   loc = {im.localization:.4f}")
    print(
        f"  E_tot = c₀+loc = {im.row_lhs_e_tot:.6g}   "
        f"budget 2π·Ω_k = {im.row_rhs_budget:.6g}   "
        f"residual = {im.row_residual:.6g}"
    )
    if im.row_rhs_budget != 0:
        ratio = im.row_lhs_e_tot / im.row_rhs_budget
        print(f"  E_tot / (2π·Ω_k) = {ratio:.6f}   (≈ 1 when row closes)")


@dataclass
class VertexCouplingRow:
    """Per-vertex coupling coefficients (c_v proxy), for diagnostics."""

    label: str
    vertex: int
    xi: float
    c_v: float
    m_rest_gev: float
    e_tot: float
    localization: float
    lapse: float
    mass_additive: float
    mass_multiplicative_rest: float
    mass_hybrid: float


def rows_from_coupling_vertices(report: Any, phi: float = 0.0, t: float = 0.0) -> list[VertexCouplingRow]:
    """One row per Fano vertex using solver ξ_v and c_v as dimensionless rest proxies."""
    import hqiv_coupling_linear_system as hcls  # noqa: E402

    xis = report.holonomy_xi_vertices
    if xis is None:
        xis = [float(s + 1) for s in report.shells]
    rows: list[VertexCouplingRow] = []
    for v, (xi, c_v, name) in enumerate(
        zip(xis, report.c, hcls.VERTEX_NAMES, strict=True)
    ):
        m_raw = max(c_v, 1e-6)
        loc = localization_energy(xi)
        e_tot = informational_energy_total(m_raw, xi)
        lapse = shell_lapse_xi(xi, phi=phi, t=t)
        rows.append(
            VertexCouplingRow(
                label=f"v={v} {name}",
                vertex=v,
                xi=xi,
                c_v=c_v,
                m_rest_gev=m_raw,
                e_tot=e_tot,
                localization=loc,
                lapse=lapse,
                mass_additive=mass_from_xi(m_raw, xi, MassReadoutGauge.ADDITIVE, phi=phi, t=t),
                mass_multiplicative_rest=hadron_mass_from_xi(m_raw, xi, phi=phi, t=t),
                mass_hybrid=hybrid_mass_from_xi(m_raw, xi, phi=phi, t=t),
            )
        )
    return rows


def print_boson_additive_summary(rows: list[ParticleMassRow], *, compare_pdg: bool) -> None:
    """W, Z, H at solved ξ_v with additive gauge (rest + loc)."""
    boson_keys = ("w", "z", "h")
    sub = [r for r in rows if r.particle_key in boson_keys]
    if not sub:
        return
    print()
    print("Boson sector (additive gauge, solved ξ_v, rest + localization):")
    catalog = particle_catalog()
    print(f"  {'boson':6} {'v':>2} {'ξ':>7} {'m_rest':>9} {'additive':>10} {'witness':>9} {'Δ':>9}")
    for r in sub:
        w = catalog[r.particle_key].pdg_mass_gev if compare_pdg else r.witness_gev
        d = rel_error(r.mass_additive, w)
        d_s = f"{d:+.4f}" if d is not None else "—"
        print(
            f"  {r.particle_key:6} {r.vertex:2d} {r.xi:7.4f} {r.m_rest_gev:9.4f} "
            f"{r.mass_additive:10.4f} {w:9.4f} {d_s:>9}"
        )
        print(f"    E_tot={r.e_tot:.4f}  loc={r.localization:.4f}  N={r.lapse:.4f}")


def print_particle_predictions(rows: list[ParticleMassRow], *, compare_pdg: bool) -> None:
    print()
    print("Particle predictions (solved ξ_v, rest mass + informational readout):")
    print(
        "  Units: GeV on the mass chart (loc = ξ in natural T_Pl=1 chart). "
        "Bosons: additive; nucleons: multiplicative (rest ÷ N), same ξ at lock-in v1."
    )
    hdr = (
        f"  {'particle':22s} {'v':>2s} {'ξ':>7s} {'m_rest':>9s} "
        f"{'additive':>10s} {'mult/N':>10s} {'primary':>10s} {'Δ_prim':>9s}"
    )
    print(hdr)
    for r in rows:
        d = r.rel_err_primary
        d_str = f"{d:+.4f}" if d is not None else "—"
        print(
            f"  {r.label:22s} {r.vertex:2d} {r.xi:7.4f} {r.m_rest_gev:9.4f} "
            f"{r.mass_additive:10.4f} {r.mass_multiplicative_rest:10.4f} "
            f"{(r.mass_additive if r.gauge_primary == MassReadoutGauge.ADDITIVE.value else r.mass_multiplicative_rest):10.4f} "
            f"{d_str:>9s}"
        )
        print(
            f"    E_tot={r.e_tot:.4f}  loc={r.localization:.4f}  N={r.lapse:.4f}  "
            f"witness({r.mass_source})={r.witness_gev:.4f} GeV"
        )
    print_nucleon_pair_summary(rows)
    print_boson_additive_summary(rows, compare_pdg=compare_pdg)
    if compare_pdg and rows:
        print()
        print(f"  Gauge readouts vs PDG (rest masses from {rows[0].mass_source}):")
        catalog = particle_catalog()
        for r in rows:
            spec = catalog[r.particle_key]
            for gauge_name, pred in (
                ("additive", r.mass_additive),
                ("mult/N", r.mass_multiplicative_rest),
            ):
                err = rel_error(pred, spec.pdg_mass_gev)
                if err is not None:
                    print(f"    {r.label:22s} {gauge_name:8s} vs PDG: {err:+.4f}")


@dataclass(frozen=True)
class NucleonLapsePoint:
    """Proton + neutron at shared ξ with HQVM lapse N = 1 + Φ + 2ξ·t."""

    phi: float
    t: float
    xi: float
    lapse: float
    phi_xi: float
    proton_mult_gev: float
    neutron_mult_gev: float
    proton_additive_gev: float
    neutron_additive_gev: float
    delta_mult_mev: float
    delta_additive_mev: float
    delta_mult_vs_flat_mev: float
    delta_additive_vs_flat_mev: float


def build_nucleon_lapse_point(
    report: Any,
    *,
    bundle: sw.WitnessBundle | None = None,
    mass_source: MassSource = "lean",
    phi: float = 0.0,
    t: float = 0.0,
) -> NucleonLapsePoint:
    """Both nucleons at solved ξ_v (vertex 1) with the same lapse factor."""
    rows = rows_from_coupling_particles(
        report,
        ["proton", "neutron"],
        bundle=bundle,
        mass_source=mass_source,
        phi=phi,
        t=t,
    )
    by_key = {r.particle_key: r for r in rows}
    p, n = by_key["proton"], by_key["neutron"]
    flat_p = build_particle_row(
        particle_catalog(bundle)["proton"],
        p.xi,
        mass_source=mass_source,
        phi=0.0,
        t=0.0,
    )
    flat_n = build_particle_row(
        particle_catalog(bundle)["neutron"],
        n.xi,
        mass_source=mass_source,
        phi=0.0,
        t=0.0,
    )
    phi_xi = PHI_COEFF / theta_local_xi(p.xi)
    return NucleonLapsePoint(
        phi=phi,
        t=t,
        xi=p.xi,
        lapse=p.lapse,
        phi_xi=phi_xi,
        proton_mult_gev=p.mass_multiplicative_rest,
        neutron_mult_gev=n.mass_multiplicative_rest,
        proton_additive_gev=p.mass_additive,
        neutron_additive_gev=n.mass_additive,
        delta_mult_mev=(n.mass_multiplicative_rest - p.mass_multiplicative_rest) * 1000.0,
        delta_additive_mev=(n.mass_additive - p.mass_additive) * 1000.0,
        delta_mult_vs_flat_mev=(
            (n.mass_multiplicative_rest - p.mass_multiplicative_rest)
            - (flat_n.mass_multiplicative_rest - flat_p.mass_multiplicative_rest)
        )
        * 1000.0,
        delta_additive_vs_flat_mev=(
            (n.mass_additive - p.mass_additive)
            - (flat_n.mass_additive - flat_p.mass_additive)
        )
        * 1000.0,
    )


def print_nucleon_lapse_scan(
    points: list[NucleonLapsePoint],
    *,
    bundle: sw.WitnessBundle | None = None,
) -> None:
    """How N(Φ, t) pulls proton and neutron together at fixed ξ."""
    b = bundle or sw.load_witness_bundle()
    dm_witness = (b.derived_neutron_mass_gev - b.derived_proton_mass_gev) * 1000.0
    print()
    print("Nucleon pair lapse scan (shared ξ, same gauge; Lean multiplicative hadron readout):")
    print(f"  witness Δm_n−p = {dm_witness:.4f} MeV  (flat N=1 mult should match)")
    print(
        f"  {'Φ':>8} {'t':>8} {'ξ':>7} {'N':>8} {'m_p/N':>10} {'m_n/N':>10} "
        f"{'Δ mult':>9} {'Δ vs N=1':>10} {'Δ add':>9}"
    )
    for pt in points:
        print(
            f"  {pt.phi:8.4f} {pt.t:8.4f} {pt.xi:7.4f} {pt.lapse:8.5f} "
            f"{pt.proton_mult_gev:10.4f} {pt.neutron_mult_gev:10.4f} "
            f"{pt.delta_mult_mev:9.4f} {pt.delta_mult_vs_flat_mev:10.4f} "
            f"{pt.delta_additive_mev:9.4f}"
        )
    print("  Δ mult vs N=1: change in n−p gap from lapse (0 = binding-only split at N=1).")


@dataclass(frozen=True)
class MassRowWeightScanRow:
    weight: float
    residual: float
    mass_row_residual: float | None
    mass_row_ratio: float | None
    brace_rel_err: float
    max_readout_spread: float
    xi_lockin: float | None


def brace_rel_err_from_report(report: Any) -> float:
    """Fractional EM-Gauss 1/α error vs CODATA (primary brace readout)."""
    import hqiv_coupling_linear_system as hcls  # noqa: E402

    if report.continuous_xi is not None:
        return abs(report.continuous_xi.residual_brace_vs_codata)
    for r in report.readouts:
        if "Gauss" in r.name and r.vertex == 0:
            return (r.inv_alpha_predicted - hcls.CODATA_INV_ALPHA) / hcls.CODATA_INV_ALPHA
    return float("nan")


def scan_mass_row_weight(
    weights: list[float],
    *,
    witness: sw.ScaleWitness = sw.DEFAULT_SCALE_WITNESS,
    mass_row_kind: str = "informational",
    phi: float = 0.0,
    t: float = 0.0,
    continuous_xi: bool = True,
    mixing_rows: bool = False,
) -> list[MassRowWeightScanRow]:
    import hqiv_coupling_linear_system as hcls  # noqa: E402

    use_codata = witness == "codata_alpha"
    out: list[MassRowWeightScanRow] = []
    for w in weights:
        report = hcls.run_coherence(
            "sector",
            REFERENCE_M,
            "codata_vertex0_gauss",
            scale_witness=witness,
            use_brace_instead_of_setter=use_codata,
            continuous_xi=use_codata and continuous_xi,
            density_holonomy=continuous_xi,
            mass_row=True,
            mass_row_kind=mass_row_kind,  # type: ignore[arg-type]
            mass_row_weight=w,
            mass_row_phi=phi,
            mass_row_t=t,
            mixing_rows=mixing_rows,
            include_two_objective=False,
        )
        im = report.informational_mass
        mr = im.row_residual if im is not None else None
        ratio = (
            im.row_lhs_e_tot / im.row_rhs_budget
            if im is not None and im.row_rhs_budget not in (0.0, float("nan"))
            else None
        )
        xi_v1 = (
            float(report.holonomy_xi_vertices[1])
            if report.holonomy_xi_vertices and len(report.holonomy_xi_vertices) > 1
            else None
        )
        out.append(
            MassRowWeightScanRow(
                weight=w,
                residual=report.residual,
                mass_row_residual=mr,
                mass_row_ratio=ratio,
                brace_rel_err=brace_rel_err_from_report(report),
                max_readout_spread=report.max_rel_spread_vs_codata,
                xi_lockin=xi_v1,
            )
        )
    return out


def print_mass_row_weight_scan(rows: list[MassRowWeightScanRow]) -> None:
    print()
    print("Mass-row weight scan (informational row: c₀ + loc = 2π·Ω_k):")
    print(
        f"  {'w':>8} {'‖res‖':>12} {'row res':>12} {'E/2πΩ':>8} "
        f"{'brace err':>10} {'readout spr':>11} {'ξ_v1':>8}"
    )
    for r in rows:
        ratio_s = f"{r.mass_row_ratio:.5f}" if r.mass_row_ratio is not None else "—"
        mr_s = f"{r.mass_row_residual:.4e}" if r.mass_row_residual is not None else "—"
        xi_s = f"{r.xi_lockin:.4f}" if r.xi_lockin is not None else "—"
        print(
            f"  {r.weight:8.3f} {r.residual:12.4e} {mr_s:>12} {ratio_s:>8} "
            f"{r.brace_rel_err:10.4e} {r.max_readout_spread:11.4e} {xi_s:>8}"
        )


DEFAULT_MASS_ROW_WEIGHTS = (0.0, 0.25, 0.5, 1.0, 2.0, 5.0, 10.0, 25.0, 50.0)


def print_nucleon_pair_summary(rows: list[ParticleMassRow]) -> None:
    """n−p gaps at shared ξ (binding cancels; difference is constituent udd vs uud)."""
    by_key = {r.particle_key: r for r in rows}
    if "proton" not in by_key or "neutron" not in by_key:
        return
    p, n = by_key["proton"], by_key["neutron"]
    if abs(p.xi - n.xi) > 1e-9:
        print()
        print(f"  Warning: proton ξ={p.xi:.4f} ≠ neutron ξ={n.xi:.4f}")
        return
    print()
    print(f"  Nucleon pair @ ξ={p.xi:.4f} (Lean: shared binding cancels in m_n−m_p):")
    dm_rest = n.m_rest_gev - p.m_rest_gev
    dm_add = n.mass_additive - p.mass_additive
    dm_mult = n.mass_multiplicative_rest - p.mass_multiplicative_rest
    dm_e = n.e_tot - p.e_tot
    witness_dm_mev = dm_rest * 1000.0
    print(f"    Δm_rest     = {witness_dm_mev:.4f} MeV  (bundle derivedDeltaM)")
    print(f"    ΔE_tot      = {dm_e*1000:.4f} MeV  (= Δm_rest when ξ shared)")
    print(f"    Δ additive  = {dm_add*1000:.4f} MeV")
    print(f"    Δ mult/N    = {dm_mult*1000:.4f} MeV  (primary hadron gauge)")
    if abs(p.lapse - 1.0) > 1e-6:
        phi_xi = PHI_COEFF / theta_local_xi(p.xi)
        print(f"    N = {p.lapse:.5f}  (φ(ξ)=2ξ={phi_xi:.4f}; hadron readout m_rest/N)")
        print(
            f"    m_p: {p.m_rest_gev:.4f} → {p.mass_multiplicative_rest:.4f} GeV  "
            f"m_n: {n.m_rest_gev:.4f} → {n.mass_multiplicative_rest:.4f} GeV"
        )


def print_vertex_coupling_rows(rows: list[VertexCouplingRow]) -> None:
    print()
    print("Per-vertex coupling proxies (m_rest = c_v, dimensionless):")
    for r in rows:
        print(
            f"  {r.label}: ξ={r.xi:.4f} c_v={r.c_v:.4g} "
            f"E_tot={r.e_tot:.4g} add={r.mass_additive:.4g} mult={r.mass_multiplicative_rest:.4g}"
        )


def main() -> None:
    p = argparse.ArgumentParser(description="HQIV informational energy mass readout")
    p.add_argument("--json", action="store_true")
    p.add_argument(
        "--solve",
        action="store_true",
        help="run coupling coherence solve with informational mass row (implies --from-coupling)",
    )
    p.add_argument(
        "--from-coupling",
        action="store_true",
        help="run Fano coupling solver and use ξ_v, c_v per vertex",
    )
    p.add_argument("--continuous-xi", action="store_true")
    p.add_argument("--mixing-rows", action="store_true")
    p.add_argument(
        "--mass-row",
        action="store_true",
        help="include informational mass row in coupling solve (--from-coupling / --solve)",
    )
    p.add_argument(
        "--mass-row-weight",
        type=float,
        default=1.0,
        help="weight for mass row in coupling solve (default 1)",
    )
    p.add_argument(
        "--mass-row-kind",
        choices=("informational", "omega_k"),
        default="informational",
    )
    p.add_argument("--phi", type=float, default=0.0, help="HQVM Φ for lapse")
    p.add_argument("--t", type=float, default=0.0, help="coordinate time for lapse")
    p.add_argument(
        "--particles",
        nargs="?",
        const="all",
        default=None,
        metavar="LIST",
        help="comma-separated: proton,neutron,w,z,h (or 'all'); requires --from-coupling / --solve",
    )
    p.add_argument(
        "--mass-source",
        choices=("lean", "pdg"),
        default="lean",
        help="rest-mass input: lean witnesses or PDG centrals (GeV)",
    )
    p.add_argument(
        "--compare-pdg",
        action="store_true",
        help="also print fractional error vs PDG for each gauge",
    )
    p.add_argument(
        "--scale-witness",
        choices=("proton_lockin", "codata_alpha", "cmb_now"),
        default=sw.DEFAULT_SCALE_WITNESS,
        help="single active scale witness (default proton_lockin)",
    )
    p.add_argument(
        "--witness-json",
        type=Path,
        default=DEFAULT_WITNESS_JSON,
        help="Lean-exported witness bundle (data/hqiv_witnesses.json)",
    )
    p.add_argument(
        "--vertex-proxies",
        action="store_true",
        help="with --particles, also print per-vertex c_v proxy rows",
    )
    p.add_argument(
        "--mass-row-weight-scan",
        action="store_true",
        help="sweep --mass-row-weight values (requires --solve or --from-coupling with --mass-row)",
    )
    p.add_argument(
        "--mass-row-weights",
        type=str,
        default=None,
        help="comma-separated weights for scan (default preset grid)",
    )
    p.add_argument(
        "--nucleon-lapse-scan",
        action="store_true",
        help="grid of (Φ, t) for proton+neutron at shared ξ (requires --solve)",
    )
    p.add_argument(
        "--lapse-phi-grid",
        type=str,
        default="0,0.01,0.02,0.05",
        help="comma-separated Φ values for --nucleon-lapse-scan",
    )
    p.add_argument(
        "--lapse-t-grid",
        type=str,
        default="0,0.05,0.1,0.2",
        help="comma-separated t values for --nucleon-lapse-scan",
    )
    args = p.parse_args()
    witness: sw.ScaleWitness = args.scale_witness
    bundle = sw.load_witness_bundle(args.witness_json)

    particle_keys: list[str] | None = None
    if args.particles is not None:
        if not (args.from_coupling or args.solve):
            p.error("--particles requires --from-coupling or --solve")
        particle_keys = parse_particle_keys(args.particles, bundle)

    report = None
    rows: list[ParticleMassRow] = []
    vertex_rows: list[VertexCouplingRow] | None = None
    coupling_meta: dict[str, Any] | None = None

    if args.mass_row_weight_scan and not (args.solve or args.from_coupling):
        p.error("--mass-row-weight-scan requires --solve or --from-coupling")
    if args.nucleon_lapse_scan and not args.solve:
        p.error("--nucleon-lapse-scan requires --solve (solved ξ_v)")

    if args.mass_row_weight_scan:
        weights = (
            [float(x.strip()) for x in args.mass_row_weights.split(",") if x.strip()]
            if args.mass_row_weights
            else list(DEFAULT_MASS_ROW_WEIGHTS)
        )
        scan_rows = scan_mass_row_weight(
            weights,
            witness=witness,
            mass_row_kind=args.mass_row_kind,
            phi=args.phi,
            t=args.t,
            continuous_xi=True,
            mixing_rows=args.mixing_rows,
        )
        if args.json:
            print(json.dumps([asdict(r) for r in scan_rows], indent=2))
            return
        print_mass_row_weight_scan(scan_rows)
        if not (args.solve or args.from_coupling) and not args.nucleon_lapse_scan:
            return

    if args.solve or args.from_coupling:
        import hqiv_coupling_linear_system as hcls  # noqa: E402

        use_codata = witness == "codata_alpha"
        report = hcls.run_coherence(
            "sector",
            REFERENCE_M,
            "codata_vertex0_gauss",
            scale_witness=witness,
            use_brace_instead_of_setter=use_codata,
            continuous_xi=use_codata and (args.continuous_xi or True),
            density_holonomy=args.continuous_xi or True,
            mass_row=args.mass_row or args.solve,
            mass_row_kind=args.mass_row_kind,
            mass_row_weight=args.mass_row_weight,
            mass_row_phi=args.phi,
            mass_row_t=args.t,
            mixing_rows=args.mixing_rows,
        )
        vertex_rows = rows_from_coupling_vertices(report, phi=args.phi, t=args.t)
        if particle_keys is not None:
            rows = rows_from_coupling_particles(
                report,
                particle_keys,
                bundle=bundle,
                mass_source=args.mass_source,
                phi=args.phi,
                t=args.t,
            )
        coupling_meta = {
            "scale_witness": witness,
            "residual": report.residual,
            "c_v": report.c,
            "holonomy_xi_vertices": report.holonomy_xi_vertices,
            "informational_mass": (
                asdict(report.informational_mass)
                if report.informational_mass is not None
                else None
            ),
            "vertex_proxies": [asdict(r) for r in vertex_rows],
        }

    if args.nucleon_lapse_scan:
        assert report is not None
        phi_grid = [float(x.strip()) for x in args.lapse_phi_grid.split(",") if x.strip()]
        t_grid = [float(x.strip()) for x in args.lapse_t_grid.split(",") if x.strip()]
        lapse_points = [
            build_nucleon_lapse_point(
                report,
                bundle=bundle,
                mass_source=args.mass_source,
                phi=phi_v,
                t=t_v,
            )
            for phi_v in phi_grid
            for t_v in t_grid
        ]
        if args.json:
            print(json.dumps([asdict(pt) for pt in lapse_points], indent=2))
            return
        print_nucleon_lapse_scan(lapse_points, bundle=bundle)

    if args.solve:
        assert report is not None
        import hqiv_coupling_linear_system as hcls  # noqa: E402

        if args.json:
            payload: dict[str, Any] = {
                "coherence_residual": report.residual,
                "c_v": report.c,
                "holonomy_xi_vertices": report.holonomy_xi_vertices,
                "informational_mass": coupling_meta["informational_mass"]
                if coupling_meta
                else None,
                "vertex_proxies": coupling_meta["vertex_proxies"] if coupling_meta else None,
            }
            if rows:
                payload["particles"] = [asdict(r) for r in rows]
            print(json.dumps(payload, indent=2))
            return
        sw.print_witness_summary(bundle, witness)
        hcls.print_coherence(report)
        print_informational_mass_row(report)
        if rows:
            print_particle_predictions(rows, compare_pdg=args.compare_pdg)
        if vertex_rows and (args.vertex_proxies or not rows):
            print_vertex_coupling_rows(vertex_rows)
        return

    if args.from_coupling:
        assert coupling_meta is not None
    else:
        rows = example_rows(bundle)

    out = {
        "scale_witness": witness,
        "natural_units": True,
        "mass_chart": "GeV_rest_with_xi_loc_natural",
        "xi_boson_closure": XI_BOSON,
        "boson_localization_lower_bound": localization_energy(XI_BOSON),
        "coupling": coupling_meta,
        "particles": [asdict(r) for r in rows],
    }

    if args.json:
        print(json.dumps(out, indent=2))
        return

    print("HQIV informational energy → mass readout")
    print(f"  scale witness: {witness}")
    sw.print_witness_summary(bundle, witness)
    print("  E_tot = m_rest + 1/Θ_local(ξ)   (ξ = loc in T_Pl=1 chart)")
    print("  hybrid order: (m_rest + loc) / N   |  alternate: m_rest/N + loc")
    if coupling_meta:
        print(f"  coupling residual = {coupling_meta['residual']:.6e}")
        print(f"  c_v = {[round(x, 4) for x in coupling_meta['c_v']]}")
        if coupling_meta.get("holonomy_xi_vertices"):
            print(f"  ξ_v = {[round(x, 4) for x in coupling_meta['holonomy_xi_vertices']]}")
        if coupling_meta.get("informational_mass"):
            im = coupling_meta["informational_mass"]
            print(
                f"  mass row: E_tot={im['row_lhs_e_tot']:.4g}  "
                f"2π·Ω_k={im['row_rhs_budget']:.4g}  "
                f"residual={im['row_residual']:.4g}"
            )
    if rows:
        print_particle_predictions(rows, compare_pdg=args.compare_pdg)
    elif vertex_rows:
        print_vertex_coupling_rows(vertex_rows)
    else:
        print()
        for r in rows:
            print(f"  {r.label}")
            print(f"    ξ = {r.xi:.4f}   m_rest = {r.m_rest_gev:.6g} GeV   E_tot = {r.e_tot:.6g}")
            print(f"    loc = {r.localization:.4f}   lapse N = {r.lapse:.4f}")
            print(
                f"    mass additive = {r.mass_additive:.6g}  "
                f"mult(rest) = {r.mass_multiplicative_rest:.6g}  "
                f"hybrid = {r.mass_hybrid:.6g}"
            )
            print()

    if vertex_rows and rows and args.vertex_proxies:
        print_vertex_coupling_rows(vertex_rows)


if __name__ == "__main__":
    main()

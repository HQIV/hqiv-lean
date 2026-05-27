#!/usr/bin/env python3
"""
Shared mass-spectrum calculator core: Fano coupling + informational-energy readout.

Mirrors `Hqiv/Physics/HadronMassReadout.lean`, `InformationalEnergyMass.lean`,
`MetaHorizonExcitedStates.lean`, and `scripts/hqiv_excited_states.py`.
"""

from __future__ import annotations

import math
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal

import cubic_phase_relax_probe as cpr
import hqiv_coupling_linear_system as hcls
import hqiv_excited_states as hes
import hqiv_scale_witness as sw
import informational_energy_mass as iem

ROOT = Path(__file__).resolve().parents[1]
REFERENCE_M = cpr.REFERENCE_M
XI_LOCKIN = sw.XI_LOCKIN
L_COLOR_COMPOSED = 3
L_CHARGE_DECORATED = 2
# Lean `hadronIntrinsicScale_meson_eq_four_ninths`
MESON_INTRINSIC_SCALE = (L_CHARGE_DECORATED / L_COLOR_COMPOSED) ** 2

HadronStructure = Literal["baryon", "meson", "tetraquark", "pentaquark"]

QUARK_VERTEX: dict[str, int] = {
    "u": 1,
    "c": 2,
    "t": 3,
    "d": 4,
    "s": 5,
    "b": 6,
}


def intrinsic_scale_for_structure(structure: HadronStructure) -> float:
    if structure == "meson":
        return MESON_INTRINSIC_SCALE
    return 1.0


def eff_corrected(delta: float, m: int) -> float:
    return cpr.eff_corrected(delta, float(m))


def mass_scaling_ansatz(l: int, delta: float, m: int, k: float = 1.0) -> float:
    return k * float(l * l) * eff_corrected(delta, m)


def derived_quark_gev() -> dict[str, float]:
    s_top = cpr.TOP_ANCHOR_COORD
    c_s7_up = cpr.complexity_threshold_from_geometry("s7", 2, 2)
    c_s7_down = cpr.complexity_threshold_from_geometry("s7", 2, 1)
    c_s3 = cpr.complexity_threshold_from_geometry("s3", 2, 1)

    def first_below(from_s: float, ratio: float) -> float:
        if ratio <= 1:
            return from_s
        lo, hi = 0.0, from_s
        for _ in range(100):
            mid = 0.5 * (lo + hi)
            if cpr.geometric_resonance_step(from_s, mid) >= ratio:
                lo = mid
            else:
                hi = mid
        return lo

    s_bottom = first_below(s_top, c_s7_up / max(c_s7_down, 1e-9))
    s_charm = first_below(s_top, c_s7_up)
    s_up = first_below(s_charm, c_s3)
    s_strange = first_below(s_bottom, c_s7_down)
    s_down = first_below(s_strange, c_s3)
    k_tc = cpr.geometric_resonance_step(s_top, s_charm)
    k_cu = cpr.geometric_resonance_step(s_charm, s_up)
    k_bs = cpr.geometric_resonance_step(s_bottom, s_strange)
    k_sd = cpr.geometric_resonance_step(s_strange, s_down)
    return {
        "u": cpr.M_TOP_GEV / k_tc / k_cu,
        "d": (cpr.M_BOTTOM_GEV / k_bs) / k_sd,
        "s": cpr.M_BOTTOM_GEV / k_bs,
        "c": cpr.M_TOP_GEV / k_tc,
        "b": cpr.M_BOTTOM_GEV,
        "t": cpr.M_TOP_GEV,
    }


def parse_hadron_catalog(catalog_path: Path | None = None) -> list[dict[str, Any]]:
    text = (catalog_path or ROOT / "web/hqiv-mass-spectrum-calculator/hadron-catalog.js").read_text()
    out: list[dict[str, Any]] = []
    structure: HadronStructure = "baryon"
    variety_id = "unknown"
    config_re = re.compile(
        r'\{\s*id:\s*"([^"]+)",\s*label:\s*"([^"]+)",\s*pdgName:\s*"([^"]+)"[^[]*valence:\s*\[([^\]]+)\]'
        r'(?:,\s*note:\s*"([^"]*)")?\s*\}',
    )
    for line in text.splitlines():
        vm = re.search(r'\bid:\s*"([^"]+)"', line)
        if vm and "HADRON_VARIETIES" not in line and "structure:" in line:
            variety_id = vm.group(1)
        sm = re.search(r'structure:\s*"([^"]+)"', line)
        if sm and "valenceCount" in line:
            structure = sm.group(1)  # type: ignore[assignment]
        for cm in config_re.finditer(line):
            cid, label, pdg, val_raw, note = (
                cm.group(1),
                cm.group(2),
                cm.group(3),
                cm.group(4),
                cm.group(5) or "",
            )
            valence = [
                (vm2.group(1), vm2.group(2))
                for vm2 in re.finditer(r'v\("([^"]+)",\s*"([^"]+)"\)', val_raw)
            ]
            if not valence:
                continue
            out.append(
                {
                    "variety_id": variety_id,
                    "config_id": cid,
                    "label": label,
                    "pdgName": pdg,
                    "structure": structure,
                    "valence": valence,
                    "note": note,
                }
            )
    seen: set[str] = set()
    deduped: list[dict[str, Any]] = []
    for row in out:
        if row["config_id"] in seen:
            continue
        seen.add(row["config_id"])
        deduped.append(row)
    return deduped


def mean_xi_for_valence(valence: list[tuple[str, str]], xis: list[float]) -> float:
    verts = {QUARK_VERTEX[f] for f, _ in valence if f in QUARK_VERTEX}
    if not verts:
        return float(XI_LOCKIN)
    return sum(float(xis[v]) for v in verts) / len(verts)


def valence_quark_count(valence: list[tuple[str, str]]) -> int:
    return sum(1 for _, role in valence if role == "quark")


def constituent_sum_gev(valence: list[tuple[str, str]], qm: dict[str, float]) -> float:
    return sum(qm[f] for f, role in valence if role == "quark")


def proton_uud_constituent_gev(qm: dict[str, float]) -> float:
    return 2.0 * qm["u"] + qm["d"]


def readout_shell_from_xi(xi: float) -> int:
    return max(0, min(int(round(xi - 1.0)), REFERENCE_M + 2))


def hadron_ground_mev(
    *,
    structure: HadronStructure,
    valence: list[tuple[str, str]],
    constituent_mev: float,
    m_shell: int = REFERENCE_M,
) -> float:
    """
    Lean `hadronGroundMassMeV`: (constituent − scaled E_bind) × intrinsicScale.
    """
    n = valence_quark_count(valence)
    bind = hes.e_bind_from_nucleon_trace_mev(m_shell) * (n / 3.0)
    ground = (constituent_mev - bind) * intrinsic_scale_for_structure(structure)
    return ground


def run_coupling_stack(
    scale_witness: sw.ScaleWitness = "proton_lockin",
    *,
    mass_row: bool = True,
    phi: float = 0.0,
    t: float = 0.0,
) -> hcls.CoherenceReport:
    use_codata = scale_witness == "codata_alpha"
    return hcls.run_coherence(
        "sector",
        REFERENCE_M,
        "codata_vertex0_gauss",
        scale_witness=scale_witness,
        use_brace_instead_of_setter=use_codata,
        continuous_xi=use_codata,
        density_holonomy=use_codata,
        mass_row=mass_row,
        mass_row_kind="informational",
        mass_row_phi=phi,
        mass_row_t=t,
    )


@dataclass
class HadronMassResult:
    config_id: str
    m_gev: float
    m_mev: float
    xi_readout: float
    m_rest_gev: float
    lapse: float
    pipeline: str
    excitation_mev: float
    ground_mev: float


def hadron_mass_from_stack(
    config: dict[str, Any],
    *,
    report: hcls.CoherenceReport,
    bundle: sw.WitnessBundle,
    qm: dict[str, float] | None = None,
    phi: float = 0.0,
    t: float = 0.0,
) -> HadronMassResult:
    """Witness / coupling / HadronMassReadout + informational multiplicative gauge."""
    qm = qm or derived_quark_gev()
    xis = report.holonomy_xi_vertices
    if xis is None:
        xis = [float(s + 1) for s in report.shells]
    xi = mean_xi_for_valence(config["valence"], xis)
    cid = config["config_id"]
    structure: HadronStructure = config["structure"]
    exc_mev = 0.0
    pipeline = "hadron_ground+info_mult"

    if cid == "p":
        m_mev = bundle.derived_proton_mass_mev
        m_gev = iem.hadron_mass_from_xi(m_mev / 1000.0, float(xis[1]), phi=phi, t=t)
        pipeline = "witness_proton_vertex1"
        xi = float(xis[1])
        return HadronMassResult(
            cid, m_gev, m_gev * 1000.0, xi, bundle.derived_proton_mass_gev,
            iem.shell_lapse_xi(xi, phi=phi, t=t), pipeline, 0.0, m_mev,
        )
    if cid == "n":
        m_mev = bundle.derived_neutron_mass_mev
        m_gev = iem.hadron_mass_from_xi(m_mev / 1000.0, float(xis[1]), phi=phi, t=t)
        pipeline = "witness_neutron_vertex1"
        xi = float(xis[1])
        return HadronMassResult(
            cid, m_gev, m_gev * 1000.0, xi, bundle.derived_neutron_mass_gev,
            iem.shell_lapse_xi(xi, phi=phi, t=t), pipeline, 0.0, m_mev,
        )

    m_const_gev = constituent_sum_gev(config["valence"], qm)
    p_const_gev = proton_uud_constituent_gev(qm)
    witness_scale = (
        bundle.derived_proton_mass_gev / p_const_gev if p_const_gev > 0 else 1.0
    )
    m_const_mev = m_const_gev * witness_scale * 1000.0
    m_shell = readout_shell_from_xi(xi)
    ground_mev = hadron_ground_mev(
        structure=structure,
        valence=config["valence"],
        constituent_mev=m_const_mev,
        m_shell=m_shell,
    )
    m_gev = iem.hadron_mass_from_xi(ground_mev / 1000.0, xi, phi=phi, t=t)
    pipeline = "HadronMassReadout+info_mult"

    note = config.get("note") or ""
    if note in ("decuplet", "vector"):
        meson_anchor = ground_mev if structure == "meson" else None
        exc = hes.excitation_for_tag(
            note, derived_proton_mev=bundle.derived_proton_mass_mev, meson_anchor_mev=meson_anchor
        )
        exc_mev = exc.delta_mev
        m_mev = hes.apply_excitation_to_ground_mev(ground_mev, exc)
        m_gev = m_mev / 1000.0
        pipeline += exc.pipeline_suffix

    lapse = iem.shell_lapse_xi(xi, phi=phi, t=t)
    return HadronMassResult(
        config_id=cid,
        m_gev=m_gev,
        m_mev=m_gev * 1000.0,
        xi_readout=xi,
        m_rest_gev=ground_mev / 1000.0,
        lapse=lapse,
        pipeline=pipeline,
        excitation_mev=exc_mev,
        ground_mev=ground_mev,
    )


def particle_rows_from_stack(
    report: hcls.CoherenceReport,
    bundle: sw.WitnessBundle | None = None,
    *,
    keys: list[str] | None = None,
    phi: float = 0.0,
    t: float = 0.0,
) -> list[iem.ParticleMassRow]:
    bundle = bundle or sw.load_witness_bundle()
    keys = keys or list(iem.DEFAULT_PARTICLES)
    return iem.rows_from_coupling_particles(
        report, keys, bundle=bundle, mass_source="lean", phi=phi, t=t
    )

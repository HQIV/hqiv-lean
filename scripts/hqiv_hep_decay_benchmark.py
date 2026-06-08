#!/usr/bin/env python3
"""
Benchmark HQIV HEP decay-chain predictions against laboratory reference observations.

Comparison layer only: PDG / facility reference values are never fed into HQIV readouts.

Run:
  python3 scripts/hqiv_hep_decay_benchmark.py
  python3 scripts/hqiv_hep_decay_benchmark.py --json-out data/hep_decay_benchmark.json
  python3 scripts/hqiv_hep_decay_benchmark.py --strict
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Literal

import hqiv_hep_decay_chain as hep
import hqiv_hep_decay_sigma as hsig
import hqiv_hep_multichannel_expansion as mc
import hqiv_hep_production_readout as hpr
import hqiv_lean_physics_primitives as lean


def _repo_root() -> Path:
    """Locate the HQIV repo root even when this script is run from the paper folder."""
    for parent in Path(__file__).resolve().parents:
        if (parent / "lakefile.toml").exists() and (parent / "data").is_dir():
            return parent
    return Path(__file__).resolve().parents[1]


ROOT = _repo_root()
DEFAULT_OBSERVATIONS = ROOT / "data" / "hep_decay_observations.json"
DEFAULT_PUBLISHED = ROOT / "data" / "hadron_published_masses.json"
DEFAULT_JSON = ROOT / "data" / "hep_decay_benchmark.json"

MassXi = float
Status = Literal["pass", "fail", "skip", "known_gap", "readout"]


@dataclass(frozen=True)
class BenchmarkCase:
    panel: str
    case_id: str
    quantity: str
    reference: float | str | bool | None
    predicted: float | str | bool | None
    error: float | None
    error_pct: float | None
    tolerance: str
    status: Status
    notes: str = ""
    reference_sigma: float | None = None
    predicted_sigma: float | None = None
    n_sigma: float | None = None


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _branching_sigma_fields(
    observations: dict[str, Any],
    *,
    parent_id: str,
    channel: str,
    daughter_ids: list[str] | None,
    predicted: float,
    reference: float,
    reference_sigma: float | None,
    env: hep.ExperimentEnvironment,
    aggregate: str | None = None,
    contains_daughter: str | None = None,
) -> tuple[float | None, float | None, float | None]:
    policy = observations.get("branching_sigma_policy") or {}
    if not policy.get("enabled", True):
        return None, reference_sigma, None
    n_samples = int(policy.get("mc_samples", 200))
    _, pred_sigma = hsig.predict_branching_with_sigma(
        parent_id,
        channel,
        daughter_ids,
        env=env,
        aggregate=aggregate,
        contains_daughter=contains_daughter,
        n_samples=n_samples,
    )
    ref_sigma = float(reference_sigma) if reference_sigma is not None else 0.0
    n_sig = hsig.n_sigma(
        predicted,
        reference,
        pred_sigma=pred_sigma,
        ref_sigma=ref_sigma,
    )
    return pred_sigma, ref_sigma if reference_sigma is not None else None, n_sig


def _branching_pass(
    *,
    ok: bool,
    n_sigma: float | None,
    observations: dict[str, Any],
) -> bool:
    if ok:
        return True
    policy = observations.get("branching_sigma_policy") or {}
    band = float(policy.get("n_sigma_band", 2.0))
    return n_sigma is not None and n_sigma <= band


def load_reference_masses(
    *,
    observations: dict[str, Any],
    published_path: Path = DEFAULT_PUBLISHED,
) -> dict[str, float]:
    """Map catalog species_id → reference mass (MeV)."""
    published = load_json(published_path)
    out: dict[str, float] = {}
    for entry in published.get("entries", []):
        cid = entry.get("config_id")
        if cid:
            out[str(cid)] = float(entry["mass_MeV"])
    for sid, mass in (observations.get("mass_overrides_mev") or {}).items():
        out[str(sid)] = float(mass)
    return out


def reference_mass(
    species_id: str,
    refs: dict[str, float],
) -> float | None:
    sid = hep.BEAM_SPECIES.get(species_id, species_id)
    return refs.get(sid)


def mass_tolerance(
    species_id: str,
    observations: dict[str, Any],
) -> tuple[float, float]:
    tol = observations.get("mass_tolerances") or {}
    tight = tol.get("tight") or {}
    if species_id in (tight.get("species") or []):
        return float(tight.get("abs_mev", 0.01)), float(tight.get("rel", 1e-5))
    return float(tol.get("default_abs_mev", 15.0)), float(tol.get("default_rel", 0.08))


def within_tolerance(
    predicted: float,
    reference: float,
    *,
    abs_tol: float,
    rel_tol: float,
) -> bool:
    err = abs(predicted - reference)
    if err <= abs_tol:
        return True
    if reference != 0.0 and err / abs(reference) <= rel_tol:
        return True
    return False


def load_reference_sigmas(
    *,
    observations: dict[str, Any],
    published_path: Path = DEFAULT_PUBLISHED,
) -> dict[str, float]:
    sigs = hsig.load_pdg_sigma_mev(published_path)
    for sid, val in (observations.get("mass_sigma_overrides_mev") or {}).items():
        sigs[str(sid)] = float(val)
    return sigs


def benchmark_mass_panel(
    observations: dict[str, Any],
    refs: dict[str, float],
    *,
    mass_xi: MassXi = lean.XI_LOCKIN,
    ref_sigmas: dict[str, float] | None = None,
) -> list[BenchmarkCase]:
    rows: list[BenchmarkCase] = []
    sigma_policy = observations.get("mass_sigma_policy") or {}
    use_sigma = bool(sigma_policy.get("enabled", True))
    n_sigma_band = float(sigma_policy.get("n_sigma_band", 2.0))
    ref_sigmas = ref_sigmas or load_reference_sigmas(observations=observations)
    for sid in observations.get("mass_panel") or []:
        ref = reference_mass(sid, refs)
        if ref is None:
            rows.append(
                BenchmarkCase(
                    panel="mass",
                    case_id=sid,
                    quantity="mass_mev",
                    reference=None,
                    predicted=None,
                    error=None,
                    error_pct=None,
                    tolerance="n/a",
                    status="skip",
                    notes="no reference mass",
                )
            )
            continue
        pred = hep.particle_mass_mev(sid, xi=mass_xi)
        err = pred - ref
        err_pct = err / ref * 100.0 if ref else None
        abs_tol, rel_tol = mass_tolerance(sid, observations)
        ok = within_tolerance(pred, ref, abs_tol=abs_tol, rel_tol=rel_tol)
        pred_sigma = hsig.predicted_mass_sigma_mev(sid, xi=mass_xi) if use_sigma else None
        ref_sigma = ref_sigmas.get(sid)
        n_sig = None
        if use_sigma and pred_sigma is not None and ref_sigma is not None:
            n_sig = hsig.n_sigma(pred, ref, pred_sigma=pred_sigma, ref_sigma=ref_sigma)
            if not ok and n_sig <= n_sigma_band:
                ok = True
        tol = f"±{abs_tol} MeV or {100 * rel_tol:.3g}%"
        if use_sigma:
            tol += f"; σ gate ≤ {n_sigma_band:.1g}"
        note = ""
        if n_sig is not None:
            note = f"n_σ={n_sig:.2f}"
        rows.append(
            BenchmarkCase(
                panel="mass",
                case_id=sid,
                quantity="mass_mev",
                reference=ref,
                predicted=pred,
                error=err,
                error_pct=err_pct,
                tolerance=tol,
                status="pass" if ok else "fail",
                notes=note,
                reference_sigma=ref_sigma,
                predicted_sigma=pred_sigma,
                n_sigma=n_sig,
            )
        )
    return rows


def benchmark_kinematics_panel(observations: dict[str, Any]) -> list[BenchmarkCase]:
    rows: list[BenchmarkCase] = []
    for item in observations.get("kinematics") or []:
        case_id = str(item["id"])
        rel_tol = float(item.get("rel_tol", 0.02))
        ref_s = float(item["reference_sqrt_s_gev"])
        if item.get("facility"):
            setup = hep.FACILITY_PRESETS[str(item["facility"])]
        else:
            setup = hep.BeamTargetSetup(
                str(item["beam_id"]),
                float(item["beam_kinetic_gev"]),
                str(item["target_id"]),
                float(item.get("target_kinetic_gev", 0.0)),
            )
        pred_s = hep.collision_kinematics(setup).sqrt_s_gev
        err = pred_s - ref_s
        err_pct = err / ref_s * 100.0
        ok = within_tolerance(pred_s, ref_s, abs_tol=0.5, rel_tol=rel_tol)
        rows.append(
            BenchmarkCase(
                panel="kinematics",
                case_id=case_id,
                quantity="sqrt_s_gev",
                reference=ref_s,
                predicted=pred_s,
                error=err,
                error_pct=err_pct,
                tolerance=f"±0.5 GeV or {100 * rel_tol:.1g}%",
                status="pass" if ok else "fail",
            )
        )
    return rows


def reference_decay_q_mev(
    parent_id: str,
    daughter_ids: list[str],
    refs: dict[str, float],
) -> float | None:
    """Observation Q from published/reference masses (comparison only)."""
    parent = reference_mass(parent_id, refs)
    if parent is None:
        return None
    total = 0.0
    for did in daughter_ids:
        sid = hep.BEAM_SPECIES.get(did, did)
        if sid == "gamma":
            continue
        if sid in hep.SPECIAL_MASSES_MEV:
            total += hep.SPECIAL_MASSES_MEV[sid]
            continue
        m = reference_mass(sid, refs)
        if m is None:
            return None
        total += m
    return parent - total


def resolve_reference_q(
    item: dict[str, Any],
    refs: dict[str, float],
) -> float | None:
    if item.get("reference_q_from_masses"):
        return reference_decay_q_mev(
            str(item["parent_id"]),
            [str(d) for d in item["daughter_ids"]],
            refs,
        )
    ref_q = item.get("reference_q_mev")
    return float(ref_q) if ref_q is not None else None


def _find_decay_edge(
    parent_id: str,
    channel: str,
    daughter_ids: list[str],
    *,
    env: hep.ExperimentEnvironment,
) -> hep.HepDecayEdge | None:
    parent = hep.build_particle(parent_id)
    edges = hep.edges_from_particle(parent, env=env)
    want = {hep.BEAM_SPECIES.get(d, d) for d in daughter_ids}
    for edge in edges:
        if edge.mode.channel != channel:
            continue
        got = {d.species_id for d in edge.daughters}
        if got == want:
            return edge
    return None


def benchmark_decay_panel(
    observations: dict[str, Any],
    refs: dict[str, float],
    *,
    env: hep.ExperimentEnvironment | None = None,
) -> list[BenchmarkCase]:
    env = env or hep.ExperimentEnvironment()
    rows: list[BenchmarkCase] = []

    for item in observations.get("decay_channels") or []:
        case_id = str(item["id"])
        parent_id = str(item["parent_id"])
        channel = str(item["channel"])
        daughters = [str(d) for d in item["daughter_ids"]]
        edge = _find_decay_edge(parent_id, channel, daughters, env=env)

        if edge is None:
            if item.get("require_open"):
                rows.append(
                    BenchmarkCase(
                        panel="decay",
                        case_id=case_id,
                        quantity="channel_open",
                        reference=True,
                        predicted=False,
                        error=None,
                        error_pct=None,
                        tolerance="must exist",
                        status="fail",
                        notes="no matching open edge",
                    )
                )
            else:
                rows.append(
                    BenchmarkCase(
                        panel="decay",
                        case_id=case_id,
                        quantity="channel_open",
                        reference=False,
                        predicted=False,
                        error=None,
                        error_pct=None,
                        tolerance="optional",
                        status="pass",
                        notes="channel absent as expected",
                    )
                )
            continue

        if item.get("require_daughters"):
            got = {d.species_id for d in edge.daughters}
            want = {hep.BEAM_SPECIES.get(d, d) for d in daughters}
            ok_d = got == want
            rows.append(
                BenchmarkCase(
                    panel="decay",
                    case_id=f"{case_id}_daughters",
                    quantity="daughter_set",
                    reference=sorted(want),
                    predicted=sorted(got),
                    error=None,
                    error_pct=None,
                    tolerance="exact match",
                    status="pass" if ok_d else "fail",
                )
            )

        open_ok = edge.channel_open
        rows.append(
            BenchmarkCase(
                panel="decay",
                case_id=f"{case_id}_open",
                quantity="channel_open",
                reference=True,
                predicted=open_ok,
                error=None,
                error_pct=None,
                tolerance="open",
                status="pass" if open_ok else "fail",
            )
        )

        ref_q = resolve_reference_q(item, refs)
        if ref_q is not None and open_ok:
            err = edge.q_mev - ref_q
            err_pct = err / ref_q * 100.0 if ref_q else None
            q_tol = float(item.get("q_abs_tol_mev", 25.0))
            ok_q = abs(err) <= q_tol
            parent_sig = hsig.predicted_mass_sigma_mev(parent_id)
            daughter_sigs = [hsig.predicted_mass_sigma_mev(d) for d in daughters]
            q_sig = hsig.q_sigma_mev(parent_sig, daughter_sigs)
            n_sig = None
            if q_sig > 0.0:
                n_sig = abs(err) / q_sig
                q_sigma_band = float(item.get("q_n_sigma_band", 2.0))
                if not ok_q and n_sig <= q_sigma_band:
                    ok_q = True
            if not ok_q and item.get("expect_status") == "fail":
                q_status: Status = "known_gap"
            else:
                q_status = "pass" if ok_q else "fail"
            tol = f"±{q_tol} MeV"
            if n_sig is not None:
                tol += f"; σ gate ≤ {item.get('q_n_sigma_band', 2.0)}"
            note = item.get("notes", "")
            if n_sig is not None:
                note = f"{note}; n_σ(Q)={n_sig:.2f}".strip("; ")
            rows.append(
                BenchmarkCase(
                    panel="decay",
                    case_id=f"{case_id}_q",
                    quantity="q_mev",
                    reference=ref_q,
                    predicted=edge.q_mev,
                    error=err,
                    error_pct=err_pct,
                    tolerance=tol,
                    status=q_status,
                    notes=note,
                    predicted_sigma=q_sig,
                    n_sigma=n_sig,
                )
            )

        ref_br = item.get("reference_branching")
        if ref_br is not None and open_ok:
            ref_br = float(ref_br)
            err = edge.branching_ratio - ref_br
            br_tol = float(item.get("branching_abs_tol", 0.15))
            ok_br = abs(err) <= br_tol
            ref_sigma = item.get("reference_branching_sigma")
            pred_sigma, ref_sigma_out, n_sig = _branching_sigma_fields(
                observations,
                parent_id=parent_id,
                channel=channel,
                daughter_ids=daughters,
                predicted=edge.branching_ratio,
                reference=ref_br,
                reference_sigma=float(ref_sigma) if ref_sigma is not None else None,
                env=env,
            )
            ok_br = _branching_pass(ok=ok_br, n_sigma=n_sig, observations=observations)
            note = item.get("notes", "")
            if n_sig is not None:
                note = f"{note}; n_σ={n_sig:.2f}".strip("; ")
            rows.append(
                BenchmarkCase(
                    panel="decay",
                    case_id=f"{case_id}_branching",
                    quantity="branching_ratio",
                    reference=ref_br,
                    predicted=edge.branching_ratio,
                    error=err,
                    error_pct=err / ref_br * 100.0 if ref_br else None,
                    tolerance=f"±{br_tol}",
                    status="pass" if ok_br else "fail",
                    notes=note,
                    reference_sigma=ref_sigma_out,
                    predicted_sigma=pred_sigma,
                    n_sigma=n_sig,
                )
            )

    return rows


def benchmark_half_life_panel(
    observations: dict[str, Any],
    *,
    env: hep.ExperimentEnvironment | None = None,
) -> list[BenchmarkCase]:
    env = env or hep.ExperimentEnvironment()
    rows: list[BenchmarkCase] = []
    for item in observations.get("half_lives") or []:
        sid = str(item["species_id"])
        ref_hl = float(item["reference_half_life_s"])
        log_band = float(item.get("log10_ratio_band", 2.0))
        parent = hep.build_particle(sid)
        edges = hep.edges_from_particle(parent, env=env)
        pred_hl = None
        if edges:
            # Dominant open channel half-life.
            pred_hl = min(
                (e.half_life_s for e in edges if e.channel_open and math.isfinite(e.half_life_s)),
                default=math.inf,
            )
        if pred_hl is None or not math.isfinite(pred_hl):
            rows.append(
                BenchmarkCase(
                    panel="half_life",
                    case_id=str(item["id"]),
                    quantity="half_life_s",
                    reference=ref_hl,
                    predicted=None,
                    error=None,
                    error_pct=None,
                    tolerance=f"log10 ratio ≤ {log_band}",
                    status="skip",
                    notes="no finite predicted half-life",
                )
            )
            continue
        ratio = pred_hl / ref_hl if ref_hl > 0 else math.nan
        log_err = abs(math.log10(ratio)) if ratio > 0 else math.inf
        ok = log_err <= log_band
        pred_sigma = None
        n_sig = None
        if edges and math.isfinite(pred_hl):
            dom = min(
                (e for e in edges if e.channel_open and math.isfinite(e.half_life_s)),
                key=lambda e: e.half_life_s,
            )
            parent_sig = hsig.predicted_mass_sigma_mev(sid)
            daughter_sigs = [
                hsig.predicted_mass_sigma_mev(d.species_id) for d in dom.daughters
            ]
            q_sig = hsig.q_sigma_mev(parent_sig, daughter_sigs)
            w_sig = hsig.width_sigma_from_q(q_sig)
            pred_sigma = hsig.half_life_sigma_from_width(dom.width_per_s, w_sig)
            if pred_sigma and math.isfinite(pred_sigma) and pred_sigma > 0:
                n_sig = abs(pred_hl - ref_hl) / pred_sigma
                hl_sigma_band = float(item.get("half_life_n_sigma_band", 2.0))
                if not ok and n_sig <= hl_sigma_band:
                    ok = True
        if not ok and item.get("expect_status") == "fail":
            status: Status = "known_gap"
            note_suffix = " (tracked known gap)"
        else:
            status = "pass" if ok else "fail"
            note_suffix = ""
        note = (item.get("notes", "") + note_suffix).strip()
        if n_sig is not None:
            note = f"{note}; n_σ={n_sig:.2f}".strip("; ")
        rows.append(
            BenchmarkCase(
                panel="half_life",
                case_id=str(item["id"]),
                quantity="half_life_s",
                reference=ref_hl,
                predicted=pred_hl,
                error=pred_hl - ref_hl,
                error_pct=(ratio - 1.0) * 100.0 if math.isfinite(ratio) else None,
                tolerance=f"log10|pred/ref| ≤ {log_band}",
                status=status,
                notes=note,
                predicted_sigma=pred_sigma,
                n_sigma=n_sig,
            )
        )
    return rows


def _environment_from_dict(d: dict[str, Any]) -> hep.ExperimentEnvironment:
    return hep.ExperimentEnvironment(
        magnetic_field_tesla=float(d.get("magnetic_field_tesla", 0.0)),
        collider_reference_tesla=float(d.get("collider_reference_tesla", 4.0)),
        comoving_stream_fraction=float(d.get("comoving_stream_fraction", 0.0)),
        lab_temperature_K=float(d.get("lab_temperature_K", 293.15)),
        trap_embedding=bool(d.get("trap_embedding", False)),
    )


def benchmark_environment_panel(observations: dict[str, Any]) -> list[BenchmarkCase]:
    rows: list[BenchmarkCase] = []
    for item in observations.get("environment_checks") or []:
        case_id = str(item["id"])
        metric = str(item.get("metric", "weak_width_factor"))
        low_env = _environment_from_dict(item.get("low") or {})
        high_env = _environment_from_dict(item.get("high") or {})
        low_val = low_env.weak_width_factor() if metric == "weak_width_factor" else low_env.outside_support_factor()
        high_val = (
            high_env.weak_width_factor()
            if metric == "weak_width_factor"
            else high_env.outside_support_factor()
        )
        expect = str(item.get("expect", "low_less_than_high"))
        if expect == "low_less_than_high":
            ok = low_val < high_val
        else:
            ok = False
        rows.append(
            BenchmarkCase(
                panel="environment",
                case_id=case_id,
                quantity=metric,
                reference=f"low<{high_val:.6g}",
                predicted=f"low={low_val:.6g}, high={high_val:.6g}",
                error=high_val - low_val,
                error_pct=None,
                tolerance=expect,
                status="pass" if ok else "fail",
            )
        )
    return rows


def benchmark_production_panel(observations: dict[str, Any]) -> list[BenchmarkCase]:
    rows: list[BenchmarkCase] = []
    for item in observations.get("production_checks") or []:
        case_id = str(item["id"])
        sid = str(item["species_id"])
        must = bool(item.get("must_be_accessible", True))
        if item.get("facility"):
            setup = hep.FACILITY_PRESETS[str(item["facility"])]
        else:
            setup = hep.BeamTargetSetup(
                str(item["beam_id"]),
                float(item["beam_kinetic_gev"]),
                str(item["target_id"]),
                float(item.get("target_kinetic_gev", 0.0)),
            )
        kin = hep.collision_kinematics(setup)
        try:
            particle = hep.build_particle(sid)
            accessible = hep.production_accessible(particle, kin)
        except KeyError:
            accessible = False
        ok = accessible == must
        rows.append(
            BenchmarkCase(
                panel="production",
                case_id=case_id,
                quantity="kinematic_access",
                reference=must,
                predicted=accessible,
                error=None,
                error_pct=None,
                tolerance="match expected gate",
                status="pass" if ok else "fail",
                notes=f"sqrt(s)={kin.sqrt_s_gev:.4g} GeV",
            )
        )
    return rows


def benchmark_branching_new_states_panel(
    observations: dict[str, Any],
    *,
    env: hep.ExperimentEnvironment | None = None,
) -> list[BenchmarkCase]:
    """Branching ratios for charm/bottom new states (topology-weighted widths)."""
    env = env or hep.ExperimentEnvironment()
    rows: list[BenchmarkCase] = []
    for item in observations.get("branching_new_states") or []:
        case_id = str(item["id"])
        parent_id = str(item["parent_id"])
        if item.get("aggregate") == "strong_neutral_inclusive_contains":
            contains = str(item["contains_daughter"])
            ref_br = item.get("reference_branching")
            if ref_br is None:
                continue
            ref_br = float(ref_br)
            br_tol = float(item.get("branching_abs_tol", 0.25))
            parent = hep.build_particle(parent_id)
            edges = hep.edges_from_particle(parent, env=env)
            selected = [
                e
                for e in edges
                if e.mode.channel == "strong"
                and contains in e.mode.daughter_ids
                and mc.strong_neutral_light_cascade(e.mode.daughter_ids)
            ]
            pred = sum(e.branching_ratio for e in selected)
            err = pred - ref_br
            ref_sigma = item.get("reference_branching_sigma")
            pred_sigma, ref_sigma_out, n_sig = _branching_sigma_fields(
                observations,
                parent_id=parent_id,
                channel="strong",
                daughter_ids=None,
                predicted=pred,
                reference=ref_br,
                reference_sigma=float(ref_sigma) if ref_sigma is not None else None,
                env=env,
                aggregate="strong_neutral_inclusive_contains",
                contains_daughter=contains,
            )
            ok = abs(err) <= br_tol
            ok = _branching_pass(ok=ok, n_sigma=n_sig, observations=observations)
            note = item.get(
                "notes",
                f"strong charge/strangeness-neutral inclusive {contains}+X aggregate",
            )
            if n_sig is not None:
                note = f"{note}; n_σ={n_sig:.2f}".strip("; ")
            rows.append(
                BenchmarkCase(
                    panel="branching",
                    case_id=case_id,
                    quantity="inclusive_branching_ratio",
                    reference=ref_br,
                    predicted=pred,
                    error=err,
                    error_pct=err / ref_br * 100.0 if ref_br else None,
                    tolerance=f"±{br_tol}",
                    status="readout",
                    notes=note,
                    reference_sigma=ref_sigma_out,
                    predicted_sigma=pred_sigma,
                    n_sigma=n_sig,
                )
            )
            continue
        channel = str(item["channel"])
        daughters = [str(d) for d in item["daughter_ids"]]
        edge = _find_decay_edge(parent_id, channel, daughters, env=env)
        ref_br = item.get("reference_branching")
        if ref_br is None:
            continue
        ref_br = float(ref_br)
        br_tol = float(item.get("branching_abs_tol", 0.25))
        if edge is None or not edge.channel_open:
            rows.append(
                BenchmarkCase(
                    panel="branching",
                    case_id=case_id,
                    quantity="branching_ratio",
                    reference=ref_br,
                    predicted=None,
                    error=None,
                    error_pct=None,
                    tolerance=f"±{br_tol}",
                    status="fail" if item.get("require_open", True) else "skip",
                    notes="channel not open",
                )
            )
            continue
        err = edge.branching_ratio - ref_br
        ok = abs(err) <= br_tol
        ref_sigma = item.get("reference_branching_sigma")
        pred_sigma, ref_sigma_out, n_sig = _branching_sigma_fields(
            observations,
            parent_id=parent_id,
            channel=channel,
            daughter_ids=daughters,
            predicted=edge.branching_ratio,
            reference=ref_br,
            reference_sigma=float(ref_sigma) if ref_sigma is not None else None,
            env=env,
        )
        ok = _branching_pass(ok=ok, n_sigma=n_sig, observations=observations)
        note = item.get("notes", "")
        if n_sig is not None:
            note = f"{note}; n_σ={n_sig:.2f}".strip("; ")
        rows.append(
            BenchmarkCase(
                panel="branching",
                case_id=case_id,
                quantity="branching_ratio",
                reference=ref_br,
                predicted=edge.branching_ratio,
                error=err,
                error_pct=err / ref_br * 100.0 if ref_br else None,
                tolerance=f"±{br_tol}",
                status="readout",
                notes=note,
                reference_sigma=ref_sigma_out,
                predicted_sigma=pred_sigma,
                n_sigma=n_sig,
            )
        )
    return rows


def benchmark_branching_comparison_panel(
    observations: dict[str, Any],
    *,
    env: hep.ExperimentEnvironment | None = None,
) -> list[BenchmarkCase]:
    """Curated PDG branching comparisons with Monte Carlo σ propagation."""
    env = env or hep.ExperimentEnvironment()
    rows: list[BenchmarkCase] = []
    for item in observations.get("branching_comparison_panel") or []:
        case_id = str(item["id"])
        parent_id = str(item["parent_id"])
        channel = str(item["channel"])
        ref_br = float(item["reference_branching"])
        br_tol = float(item.get("branching_abs_tol", 0.15))
        ref_sigma = item.get("reference_branching_sigma")
        label = str(item.get("latex_label") or item.get("label", case_id))

        if item.get("aggregate") == "strong_neutral_inclusive_contains":
            contains = str(item["contains_daughter"])
            parent = hep.build_particle(parent_id)
            edges = hep.edges_from_particle(parent, env=env)
            selected = [
                e
                for e in edges
                if e.mode.channel == "strong"
                and contains in e.mode.daughter_ids
                and mc.strong_neutral_light_cascade(e.mode.daughter_ids)
            ]
            pred = sum(e.branching_ratio for e in selected) if selected else None
            quantity = "inclusive_branching_ratio"
            pred_sigma, ref_sigma_out, n_sig = (
                (None, None, None)
                if pred is None
                else _branching_sigma_fields(
                    observations,
                    parent_id=parent_id,
                    channel=channel,
                    daughter_ids=None,
                    predicted=pred,
                    reference=ref_br,
                    reference_sigma=float(ref_sigma) if ref_sigma is not None else None,
                    env=env,
                    aggregate="strong_neutral_inclusive_contains",
                    contains_daughter=contains,
                )
            )
        elif item.get("aggregate") == "sum_daughter_sets":
            daughter_sets = [
                [str(d) for d in daughter_set]
                for daughter_set in item["daughter_sets"]
            ]
            parent = hep.build_particle(parent_id)
            edges = hep.edges_from_particle(parent, env=env)
            wanted = [
                {hep.BEAM_SPECIES.get(d, d) for d in daughter_set}
                for daughter_set in daughter_sets
            ]
            selected = [
                e
                for e in edges
                if e.mode.channel == channel
                and {d.species_id for d in e.daughters} in wanted
            ]
            pred = sum(e.branching_ratio for e in selected) if selected else None
            quantity = "inclusive_branching_ratio"
            pred_sigma, ref_sigma_out, n_sig = (
                (None, None, None)
                if pred is None
                else _branching_sigma_fields(
                    observations,
                    parent_id=parent_id,
                    channel=channel,
                    daughter_ids=daughter_sets,  # type: ignore[arg-type]
                    predicted=pred,
                    reference=ref_br,
                    reference_sigma=float(ref_sigma) if ref_sigma is not None else None,
                    env=env,
                    aggregate="sum_daughter_sets",
                )
            )
        else:
            daughters = [str(d) for d in item["daughter_ids"]]
            edge = _find_decay_edge(parent_id, channel, daughters, env=env)
            pred = edge.branching_ratio if edge is not None and edge.channel_open else None
            quantity = "branching_ratio"
            pred_sigma, ref_sigma_out, n_sig = (
                (None, None, None)
                if pred is None
                else _branching_sigma_fields(
                    observations,
                    parent_id=parent_id,
                    channel=channel,
                    daughter_ids=daughters,
                    predicted=pred,
                    reference=ref_br,
                    reference_sigma=float(ref_sigma) if ref_sigma is not None else None,
                    env=env,
                )
            )

        if pred is None:
            rows.append(
                BenchmarkCase(
                    panel="branching_comparison",
                    case_id=case_id,
                    quantity=quantity,
                    reference=ref_br,
                    predicted=None,
                    error=None,
                    error_pct=None,
                    tolerance=f"±{br_tol}",
                    status="fail" if item.get("require_open", True) else "skip",
                    notes=f"{label}; channel not open",
                )
            )
            continue

        err = pred - ref_br
        ok = abs(err) <= br_tol
        ok = _branching_pass(ok=ok, n_sigma=n_sig, observations=observations)
        note = label
        if n_sig is not None:
            note = f"{label}; n_σ={n_sig:.2f}"
        rows.append(
            BenchmarkCase(
                panel="branching_comparison",
                case_id=case_id,
                quantity=quantity,
                reference=ref_br,
                predicted=pred,
                error=err,
                error_pct=err / ref_br * 100.0 if ref_br else None,
                tolerance=f"±{br_tol}",
                status="readout",
                notes=note,
                reference_sigma=ref_sigma_out,
                predicted_sigma=pred_sigma,
                n_sigma=n_sig,
            )
        )
    return rows


def benchmark_production_rates_panel(observations: dict[str, Any]) -> list[BenchmarkCase]:
    """Relative production rate proxies at facility √s (not absolute σ)."""
    rows: list[BenchmarkCase] = []
    for item in observations.get("production_rates") or []:
        case_id = str(item["id"])
        setup = hep.FACILITY_PRESETS[str(item["facility"])]
        kin = hep.collision_kinematics(setup)
        species: list[tuple[str, float]] = []
        for sid in item.get("species_ids") or []:
            try:
                species.append((str(sid), hep.particle_mass_mev(str(sid))))
            except KeyError:
                pass
        if not species:
            continue
        table = {
            r.species_id: r
            for r in hpr.production_rate_table(
                species,
                sqrt_s_gev=kin.sqrt_s_gev,
                accessible_mass_gev=kin.accessible_mass_gev,
                collision_mode=setup.resolved_collision_mode(),
            )
        }
        kind = str(item.get("kind", "fraction"))
        if kind == "ordering":
            a = str(item["species_a"])
            b = str(item["species_b"])
            ra = table.get(a)
            rb = table.get(b)
            if ra is None or rb is None:
                status: Status = "skip"
                pred = None
            else:
                pred = ra.normalized_fraction > rb.normalized_fraction
                expect = item.get("expect", "a_greater_than_b") == "a_greater_than_b"
                status = "pass" if pred == expect else "fail"
            rows.append(
                BenchmarkCase(
                    panel="production_rate",
                    case_id=case_id,
                    quantity="rate_ordering",
                    reference=item.get("expect", "a_greater_than_b"),
                    predicted=pred,
                    error=None,
                    error_pct=None,
                    tolerance="ordering",
                    status=status,
                    notes=f"√s={kin.sqrt_s_gev:.4g} GeV",
                )
            )
        elif kind == "min_fraction":
            sid = str(item["species_id"])
            row = table.get(sid)
            min_frac = float(item.get("min_normalized_fraction", 0.0))
            if row is None:
                rows.append(
                    BenchmarkCase(
                        panel="production_rate",
                        case_id=case_id,
                        quantity="normalized_fraction",
                        reference=min_frac,
                        predicted=None,
                        error=None,
                        error_pct=None,
                        tolerance=f"≥ {min_frac}",
                        status="skip",
                    )
                )
            else:
                ok = row.normalized_fraction >= min_frac
                rows.append(
                    BenchmarkCase(
                        panel="production_rate",
                        case_id=case_id,
                        quantity="normalized_fraction",
                        reference=min_frac,
                        predicted=row.normalized_fraction,
                        error=row.normalized_fraction - min_frac,
                        error_pct=None,
                        tolerance=f"≥ {min_frac}",
                        status="pass" if ok else "fail",
                        notes=f"rate_proxy={row.rate_proxy:.4g}",
                    )
                )
        elif kind == "reference_fraction":
            sid = str(item["species_id"])
            ref = float(item["reference_fraction"])
            tol = float(item.get("fraction_abs_tol", 0.15))
            row = table.get(sid)
            if row is None:
                status = "skip"
                pred = None
                err = None
            else:
                pred = row.normalized_fraction
                err = pred - ref
                status = "pass" if abs(err) <= tol else "fail"
            rows.append(
                BenchmarkCase(
                    panel="production_rate",
                    case_id=case_id,
                    quantity="normalized_fraction",
                    reference=ref,
                    predicted=pred,
                    error=err,
                    error_pct=err / ref * 100.0 if err is not None and ref else None,
                    tolerance=f"±{tol}",
                    status=status,
                    notes=f"√s={kin.sqrt_s_gev:.4g} GeV",
                )
            )
    return rows


def benchmark_multichannel_panel(observations: dict[str, Any]) -> list[BenchmarkCase]:
    """Open channel counts from full multi-channel expansion."""
    env = hep.ExperimentEnvironment()
    rows: list[BenchmarkCase] = []
    for item in observations.get("multichannel_counts") or []:
        sid = str(item["species_id"])
        min_open = int(item.get("min_open_channels", 1))
        try:
            p = hep.build_particle(sid)
            n_open = len(hep.edges_from_particle(p, env=env))
            n_gen = len(
                mc.generate_multichannel_modes(
                    sid,
                    parent_mass_mev=p.mass_mev,
                    mass_of=lambda d, xi=p.xi: hep.particle_mass_mev(d, xi=xi),
                )
            )
        except KeyError:
            rows.append(
                BenchmarkCase(
                    panel="multichannel",
                    case_id=str(item["id"]),
                    quantity="open_channels",
                    reference=min_open,
                    predicted=None,
                    error=None,
                    error_pct=None,
                    tolerance=f"≥ {min_open}",
                    status="skip",
                )
            )
            continue
        ok = n_open >= min_open and n_gen >= min_open
        rows.append(
            BenchmarkCase(
                panel="multichannel",
                case_id=str(item["id"]),
                quantity="open_channels",
                reference=min_open,
                predicted=n_open,
                error=n_open - min_open,
                error_pct=None,
                tolerance=f"≥ {min_open}",
                status="pass" if ok else "fail",
                notes=f"generated={n_gen}",
            )
        )
    return rows


def readout_parent_ids(observations: dict[str, Any]) -> list[str]:
    """Parents whose full open multichannel readout is exported for comparison tables."""
    parents: list[str] = []
    for key in ("mass_panel",):
        parents.extend(str(s) for s in observations.get(key) or [])
    for item in observations.get("multichannel_counts") or []:
        parents.append(str(item["species_id"]))
    for item in (observations.get("decay_channels") or []) + (
        observations.get("branching_new_states") or []
    ):
        parents.append(str(item["parent_id"]))
    out: list[str] = []
    seen: set[str] = set()
    for sid in parents:
        if sid not in seen:
            seen.add(sid)
            out.append(sid)
    return out


def reference_branching_index(observations: dict[str, Any]) -> dict[tuple[str, str, tuple[str, ...]], float]:
    """Map (parent, channel, daughters) → PDG reference branching (comparison only)."""
    out: dict[tuple[str, str, tuple[str, ...]], float] = {}
    source_rows = (
        (observations.get("decay_channels") or [])
        + (observations.get("branching_new_states") or [])
        + (observations.get("branching_comparison_panel") or [])
    )
    for item in source_rows:
        ref = item.get("reference_branching")
        if ref is None:
            continue
        if "daughter_ids" not in item:
            continue
        key = (
            str(item["parent_id"]),
            str(item["channel"]),
            tuple(str(d) for d in item["daughter_ids"]),
        )
        out[key] = float(ref)
    return out


def _edge_key(edge: hep.HepDecayEdge) -> tuple[str, str, tuple[str, ...]]:
    daughters = tuple(sorted(d.species_id for d in edge.daughters))
    return (edge.parent.species_id, edge.mode.channel, daughters)


def benchmark_readout_panel(
    observations: dict[str, Any],
    *,
    env: hep.ExperimentEnvironment | None = None,
) -> list[BenchmarkCase]:
    """Full open-channel readout: HQIV predictions from the Lean-aligned calculator."""
    env = env or hep.ExperimentEnvironment()
    ref_index = reference_branching_index(observations)
    rows: list[BenchmarkCase] = []
    for parent_id in readout_parent_ids(observations):
        try:
            parent = hep.build_particle(parent_id)
        except KeyError:
            continue
        for edge in hep.edges_from_particle(parent, env=env):
            daughters = tuple(sorted(d.species_id for d in edge.daughters))
            case_id = f"{parent_id}_{edge.mode.channel}_{'_'.join(daughters)}"
            ref_br = ref_index.get((parent_id, edge.mode.channel, daughters))
            pred = edge.branching_ratio
            err = None
            err_pct = None
            notes = ""
            if ref_br is not None:
                err = pred - ref_br
                err_pct = err / ref_br * 100.0 if ref_br else None
                notes = "PDG comparison row"
            rows.append(
                BenchmarkCase(
                    panel="readout",
                    case_id=case_id,
                    quantity="branching_ratio",
                    reference=ref_br,
                    predicted=pred,
                    error=err,
                    error_pct=err_pct,
                    tolerance="diagnostic",
                    status="readout",
                    notes=notes,
                )
            )
    return rows


def worst_reference_deviations(
    rows: list[BenchmarkCase],
    *,
    limit: int = 12,
) -> list[dict[str, Any]]:
    """Largest |error_pct| among rows carrying a PDG branching reference."""
    scored: list[tuple[float, BenchmarkCase]] = []
    for row in rows:
        if row.reference is None or row.predicted is None or row.error_pct is None:
            continue
        if not isinstance(row.reference, (int, float)) or not isinstance(row.predicted, (int, float)):
            continue
        scored.append((abs(float(row.error_pct)), row))
    scored.sort(key=lambda item: item[0], reverse=True)
    out: list[dict[str, Any]] = []
    for _, row in scored[:limit]:
        out.append(
            {
                "case_id": row.case_id,
                "panel": row.panel,
                "reference": row.reference,
                "predicted": row.predicted,
                "error_pct": row.error_pct,
                "notes": row.notes,
            }
        )
    return out


def error_distribution_summary(
    rows: list[BenchmarkCase],
    *,
    panel: str,
    label: str,
) -> dict[str, Any]:
    """Histogram absolute relative errors for rows with comparison references."""
    selected = [
        abs(float(r.error_pct))
        for r in rows
        if r.panel == panel
        and r.reference is not None
        and r.predicted is not None
        and r.error_pct is not None
        and isinstance(r.reference, (int, float))
        and isinstance(r.predicted, (int, float))
    ]
    open_count = sum(1 for r in rows if r.panel == panel)
    bins = {
        "within_10pct": sum(1 for e in selected if e <= 10.0),
        "within_20pct": sum(1 for e in selected if e <= 20.0),
        "within_50pct": sum(1 for e in selected if e <= 50.0),
        "above_50pct": sum(1 for e in selected if e > 50.0),
    }
    count = len(selected)
    return {
        "label": label,
        "panel": panel,
        "open_channel_count": open_count,
        "reference_matched_count": count,
        **bins,
        "within_10pct_fraction": bins["within_10pct"] / count if count else None,
        "within_20pct_fraction": bins["within_20pct"] / count if count else None,
        "mean_abs_error_pct": sum(selected) / count if count else None,
        "median_abs_error_pct": sorted(selected)[count // 2] if count else None,
        "max_abs_error_pct": max(selected) if count else None,
    }


def benchmark_branching_normalization() -> list[BenchmarkCase]:
    rows: list[BenchmarkCase] = []
    env = hep.ExperimentEnvironment()
    for sid in ("lambda", "K_plus", "sigma_plus", "D_plus", "lambda_c", "Jpsi", "B_plus"):
        parent = hep.build_particle(sid)
        edges = hep.edges_from_particle(parent, env=env)
        if len(edges) <= 1:
            continue
        total = sum(e.branching_ratio for e in edges)
        err = total - 1.0
        ok = abs(err) < 1e-8
        rows.append(
            BenchmarkCase(
                panel="decay",
                case_id=f"{sid}_branching_sum",
                quantity="branching_sum",
                reference=1.0,
                predicted=total,
                error=err,
                error_pct=err * 100.0,
                tolerance="±1e-8",
                status="pass" if ok else "fail",
            )
        )
    return rows


def serialize_case(row: BenchmarkCase) -> dict[str, Any]:
    d = asdict(row)
    for key in ("reference", "predicted"):
        val = d[key]
        if isinstance(val, float) and (math.isinf(val) or math.isnan(val)):
            d[key] = str(val)
    return d


def build_payload(
    *,
    observations_path: Path = DEFAULT_OBSERVATIONS,
    published_path: Path = DEFAULT_PUBLISHED,
    mass_xi: MassXi = lean.XI_LOCKIN,
) -> dict[str, Any]:
    observations = load_json(observations_path)
    refs = load_reference_masses(observations=observations, published_path=published_path)
    env = hep.ExperimentEnvironment()

    rows: list[BenchmarkCase] = []
    rows.extend(
        benchmark_mass_panel(
            observations,
            refs,
            mass_xi=mass_xi,
            ref_sigmas=load_reference_sigmas(
                observations=observations,
                published_path=published_path,
            ),
        )
    )
    rows.extend(benchmark_kinematics_panel(observations))
    rows.extend(benchmark_decay_panel(observations, refs, env=env))
    rows.extend(benchmark_branching_new_states_panel(observations, env=env))
    rows.extend(benchmark_branching_comparison_panel(observations, env=env))
    rows.extend(benchmark_half_life_panel(observations, env=env))
    rows.extend(benchmark_environment_panel(observations))
    rows.extend(benchmark_production_panel(observations))
    rows.extend(benchmark_production_rates_panel(observations))
    rows.extend(benchmark_multichannel_panel(observations))
    rows.extend(benchmark_branching_normalization())
    readout_rows = benchmark_readout_panel(observations, env=env)
    rows.extend(readout_rows)

    by_status = {"pass": 0, "fail": 0, "skip": 0, "known_gap": 0, "readout": 0}
    by_panel: dict[str, dict[str, int]] = {}
    for row in rows:
        by_status[row.status] += 1
        by_panel.setdefault(
            row.panel,
            {"pass": 0, "fail": 0, "skip": 0, "known_gap": 0, "readout": 0},
        )
        by_panel[row.panel][row.status] += 1

    structural_rows = [r for r in rows if r.status != "readout"]
    readout_only = [r for r in rows if r.panel == "readout"]
    reference_rows = [
        r for r in rows if r.reference is not None and isinstance(r.reference, (int, float))
    ]
    reference_branching_rows = [
        r
        for r in rows
        if r.quantity in ("branching_ratio", "inclusive_branching_ratio")
        and r.reference is not None
        and isinstance(r.reference, (int, float))
        and r.predicted is not None
    ]
    comparison_rows = [r for r in rows if r.panel == "branching_comparison"]
    outliers = worst_reference_deviations(reference_branching_rows)

    mass_rows = [r for r in rows if r.panel == "mass" and r.status != "skip"]
    mass_err = [abs(r.error_pct or 0.0) for r in mass_rows]
    serialized = [serialize_case(r) for r in rows]
    sigma_summary = hsig.benchmark_sigma_summary(serialized)

    return {
        "source": "scripts/hqiv_hep_decay_benchmark.py",
        "comparison_policy": observations.get("comparison_policy"),
        "citation": observations.get("citation"),
        "observations_file": str(observations_path.relative_to(ROOT)),
        "predictions_from": "scripts/hqiv_hep_decay_chain.py",
        "lean_modules": [
            "Hqiv.Physics.HepDecayReadout",
            "Hqiv.Physics.TuftGlobalHadronReadout",
            "Hqiv.Physics.HadronMassReadout",
            "Hqiv.Physics.WeakFanoHopfBridge",
            "Hqiv.Physics.NuclearAndAtomicSpectra",
            "Hqiv.Physics.Forces",
        ],
        "mass_xi": mass_xi,
        "mass_sigma_policy": observations.get("mass_sigma_policy"),
        "rows": serialized,
        "summary": {
            "total": len(rows),
            "pass": by_status["pass"],
            "fail": by_status["fail"],
            "skip": by_status["skip"],
            "known_gap": by_status["known_gap"],
            "by_panel": by_panel,
            "mean_abs_mass_error_pct": sum(mass_err) / len(mass_err) if mass_err else None,
            "max_abs_mass_error_pct": max(mass_err) if mass_err else None,
            **sigma_summary,
            "readout_channel_count": len(readout_only),
            "reference_comparison_count": len(reference_rows),
            "branching_comparison_count": len(comparison_rows),
            "readout_error_distribution": error_distribution_summary(
                rows,
                panel="readout",
                label="full open-channel readout rows with direct PDG branch references",
            ),
            "diagnostic_branching_error_distribution": error_distribution_summary(
                rows,
                panel="branching_comparison",
                label="curated diagnostic branching comparisons",
            ),
            "worst_reference_deviations": outliers,
        },
    }


def print_report(payload: dict[str, Any]) -> None:
    print("HQIV HEP decay benchmark — observations vs predictions")
    print("=" * 88)
    print(payload.get("comparison_policy", ""))
    s = payload["summary"]
    print(
        f"Cases: {s['total']}  pass={s['pass']}  fail={s['fail']}  "
        f"known_gap={s.get('known_gap', 0)}  skip={s['skip']}  "
        f"mean|mass err|={s.get('mean_abs_mass_error_pct') or 0:.2f}%  "
        f"mean n_σ={s.get('mean_n_sigma') or 0:.2f}"
    )
    print()
    print(f"{'panel':<12} {'case':<28} {'quantity':<16} {'ref':>12} {'pred':>12} {'status':>6}")
    print("-" * 88)
    for row in payload["rows"]:
        ref = row["reference"]
        pred = row["predicted"]
        if isinstance(ref, float):
            ref_s = f"{ref:12.4g}"
        else:
            ref_s = f"{str(ref):>12}"[:12]
        if isinstance(pred, float):
            pred_s = f"{pred:12.4g}"
        else:
            pred_s = f"{str(pred):>12}"[:12]
        print(
            f"{row['panel']:<12} {row['case_id']:<28} {row['quantity']:<16} "
            f"{ref_s} {pred_s} {row['status']:>6}"
        )
    print()
    print("By panel:", json.dumps(s["by_panel"], sort_keys=True))


def failing_cases(payload: dict[str, Any]) -> list[dict[str, Any]]:
    return [r for r in payload["rows"] if r["status"] == "fail"]


def main() -> int:
    parser = argparse.ArgumentParser(description="HQIV HEP decay observations vs predictions")
    parser.add_argument("--observations", type=Path, default=DEFAULT_OBSERVATIONS)
    parser.add_argument("--published", type=Path, default=DEFAULT_PUBLISHED)
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    parser.add_argument("--strict", action="store_true", help="exit 1 if any case fails")
    args = parser.parse_args()

    payload = build_payload(
        observations_path=args.observations,
        published_path=args.published,
    )
    print_report(payload)
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"\nWrote {args.json_out}")

    if args.strict and payload["summary"]["fail"] > 0:
        print(f"\nSTRICT: {payload['summary']['fail']} failing case(s)")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

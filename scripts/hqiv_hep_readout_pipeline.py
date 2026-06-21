#!/usr/bin/env python3
"""
HQIV HEP readout pipeline — collider-local input through discharge numerics to artifacts.

**General use** (beam / bottle / facility → branching readout at a parent):

  PYTHONPATH=scripts python3 scripts/hqiv_hep_readout_pipeline.py run \\
    --facility SPS_p_beam_400GeV --env collider_hadron --parent B_plus

**Custom beam mix** (bottle / dump composition):

  PYTHONPATH=scripts python3 scripts/hqiv_hep_readout_pipeline.py run \\
    --beam p --beam-energy 24 --target p --beam-mix 'p:0.85,pi+:12@0.15' \\
    --env ucn_bottle --heavy --json-out data/hep_readout_runs/ps_dump.json

**Paper reproduction** (data/, generated TeX, spine law, benchmarks):

  PYTHONPATH=scripts python3 scripts/hqiv_hep_readout_pipeline.py paper --strict

Lean spine: ``HepDecayReadout.lean``, ``SpineDischargeWeight.lean``,
``SpineDischargeUniqueness.lean``.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Literal

import hqiv_hep_decay_benchmark as hbench
import hqiv_hep_decay_chain as hep
import hqiv_hep_multichannel_expansion as mc
import hqiv_repo_paths as paths
import hqiv_spine_discharge_export as spine_export
import hqiv_spine_gap_closure_terms as spine_gaps

ROOT = paths.repo_root(Path(__file__))
PAPER_DIR = ROOT / "papers" / "hep_decay_readout"
GENERATED_DIR = PAPER_DIR / "generated"
DEFAULT_RUNS = ROOT / "data" / "hep_readout_runs"


@dataclass(frozen=True)
class ColliderLocalInput:
    """Serializable collider + laboratory dressing (comparison never feeds predictions)."""

    facility: str | None = None
    beam_id: str = "p"
    beam_kinetic_energy_gev: float = 400.0
    target_id: str = "p"
    target_kinetic_energy_gev: float = 0.0
    beam_fraction: float = 1.0
    collision_mode: str = "auto"
    beam_mix: str | None = None
    environment: str = "lab"
    magnetic_field_tesla: float = 0.0
    collider_reference_tesla: float = 4.0
    comoving_stream_fraction: float = 0.0
    lab_temperature_K: float = 293.15
    trap_embedding: bool = False

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


ENV_PRESETS: dict[str, dict[str, Any]] = {
    "lab": {
        "magnetic_field_tesla": 0.0,
        "collider_reference_tesla": 4.0,
        "comoving_stream_fraction": 0.0,
        "lab_temperature_K": 293.15,
        "trap_embedding": False,
    },
    "ucn_bottle": {
        "magnetic_field_tesla": 1.0,
        "collider_reference_tesla": 1.0,
        "comoving_stream_fraction": 0.0,
        "lab_temperature_K": 4.0,
        "trap_embedding": True,
    },
    "collider_hadron": {
        "magnetic_field_tesla": 4.0,
        "collider_reference_tesla": 4.0,
        "comoving_stream_fraction": 0.5,
        "lab_temperature_K": 293.15,
        "trap_embedding": False,
    },
}


def resolve_beam_setup(inp: ColliderLocalInput) -> hep.BeamTargetSetup:
    if inp.facility:
        preset = hep.FACILITY_PRESETS.get(inp.facility)
        if preset is None:
            raise ValueError(
                f"unknown facility {inp.facility!r}; "
                f"choices: {sorted(hep.FACILITY_PRESETS)}"
            )
        return preset
    mix = (
        hep.parse_beam_mix(inp.beam_mix, default_energy_gev=inp.beam_kinetic_energy_gev)
        if inp.beam_mix
        else ()
    )
    return hep.BeamTargetSetup(
        inp.beam_id,
        inp.beam_kinetic_energy_gev,
        inp.target_id,
        inp.target_kinetic_energy_gev,
        inp.beam_fraction,
        collision_mode=inp.collision_mode,
        beam_mix=mix,
    )


def resolve_environment(inp: ColliderLocalInput) -> hep.ExperimentEnvironment:
    base = dict(ENV_PRESETS.get(inp.environment, ENV_PRESETS["lab"]))
    base["magnetic_field_tesla"] = inp.magnetic_field_tesla
    base["collider_reference_tesla"] = inp.collider_reference_tesla
    base["comoving_stream_fraction"] = inp.comoving_stream_fraction
    base["lab_temperature_K"] = inp.lab_temperature_K
    base["trap_embedding"] = inp.trap_embedding
    return hep.ExperimentEnvironment(**base)


def kinematics_summary(setup: hep.BeamTargetSetup) -> dict[str, Any]:
    kin = hep.collision_kinematics(setup)
    return {
        "sqrt_s_gev": kin.sqrt_s_gev,
        "s_gev2": kin.s_gev2,
        "xi_collision": kin.xi_collision,
        "beam_id": kin.beam_id,
        "target_id": kin.target_id,
        "accessible_mass_gev": kin.accessible_mass_gev,
        "collision_mode": setup.resolved_collision_mode(),
    }


def parent_discharge_table(
    parent_id: str,
    *,
    setup: hep.BeamTargetSetup,
    env: hep.ExperimentEnvironment,
) -> list[dict[str, Any]]:
    """Spine discharge + widths + BR for all open modes of one parent."""
    parent = hep.build_particle(parent_id)
    edges = hep.edges_from_particle(parent, env=env)
    rows: list[dict[str, Any]] = []
    for edge in sorted(edges, key=lambda e: -e.branching_ratio):
        ds = tuple(d.species_id for d in edge.daughters)
        spine = mc.open_flavour_topology_weight(parent_id, edge.mode.channel, ds)
        rows.append(
            {
                "parent": parent_id,
                "channel": edge.mode.channel,
                "daughters": list(ds),
                "q_mev": edge.q_mev,
                "width_per_s": edge.width_per_s,
                "half_life_s": edge.half_life_s,
                "branching_ratio": edge.branching_ratio,
                "spine_discharge_weight": spine,
                "channel_open": edge.channel_open,
            }
        )
    return rows


@dataclass
class RunResult:
    collider_input: ColliderLocalInput
    kinematics: dict[str, Any]
    environment: dict[str, Any]
    parent_tables: dict[str, list[dict[str, Any]]] = field(default_factory=dict)
    chain: dict[str, Any] | None = None


def run_local_readout(
    inp: ColliderLocalInput,
    *,
    parents: tuple[str, ...] = (),
    chain: bool = False,
    max_depth: int = 5,
    include_heavy: bool = False,
    include_beam_dump: bool = False,
) -> RunResult:
    setup = resolve_beam_setup(inp)
    env = resolve_environment(inp)
    kin = kinematics_summary(setup)
    env_dict = {
        "preset": inp.environment,
        "weak_width_factor": env.weak_width_factor(),
        "outside_support_factor": env.outside_support_factor(),
        **asdict(env),
    }
    result = RunResult(inp, kin, env_dict)
    for pid in parents:
        result.parent_tables[pid] = parent_discharge_table(pid, setup=setup, env=env)
    if chain:
        exp = hep.run_experiment(
            setup,
            env=env,
            max_depth=max_depth,
            include_heavy=include_heavy,
            include_beam_dump=include_beam_dump,
        )
        result.chain = hep.build_payload(exp)
    return result


def run_payload_to_dict(result: RunResult) -> dict[str, Any]:
    return {
        "source": "scripts/hqiv_hep_readout_pipeline.py",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "collider_input": result.collider_input.to_dict(),
        "kinematics": result.kinematics,
        "environment": result.environment,
        "parent_discharge_tables": result.parent_tables,
        "decay_chain": result.chain,
    }


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _import_tex_exports(benchmark_json: Path) -> None:
    from export_hep_branching_table import (  # noqa: WPS433 — pipeline sibling
        DEFAULT_SPECTRUM_TEX,
        DEFAULT_SUMMARY_TEX,
        DEFAULT_TEX,
        build_error_distribution_tex,
        build_spectrum_tex,
        build_tex,
    )

    payload = json.loads(benchmark_json.read_text(encoding="utf-8"))
    rows = [
        r
        for r in payload.get("rows", [])
        if r.get("panel") == "branching_comparison" and r.get("predicted") is not None
    ]
    GENERATED_DIR.mkdir(parents=True, exist_ok=True)
    DEFAULT_TEX.write_text(build_tex(rows), encoding="utf-8")
    DEFAULT_SUMMARY_TEX.write_text(
        build_error_distribution_tex(payload.get("summary") or {}),
        encoding="utf-8",
    )
    DEFAULT_SPECTRUM_TEX.write_text(
        build_spectrum_tex(payload.get("summary") or {}),
        encoding="utf-8",
    )


def _import_electroweak_tex(ew_json: Path) -> None:
    from export_electroweak_mass_table import (  # noqa: WPS433
        DEFAULT_TEX as EW_TEX,
        build_tex as build_ew_tex,
    )

    payload = json.loads(ew_json.read_text(encoding="utf-8"))
    GENERATED_DIR.mkdir(parents=True, exist_ok=True)
    EW_TEX.write_text(build_ew_tex(payload), encoding="utf-8")


def reproduce_paper(
    *,
    strict: bool = False,
    skip_tests: bool = False,
    skip_collider_witnesses: bool = False,
    out_manifest: Path | None = None,
) -> dict[str, Any]:
    """Refresh repo ``data/`` + ``papers/hep_decay_readout/generated/`` for the note."""
    steps: list[dict[str, Any]] = []
    errors: list[str] = []

    def record(name: str, path: Path, extra: dict[str, Any] | None = None) -> None:
        row = {"step": name, "path": str(path.relative_to(ROOT))}
        if extra:
            row.update(extra)
        steps.append(row)

    # Spine law + gap diagnostics
    spine_law = ROOT / "data" / "spine_discharge_law.json"
    spine_payload = spine_export.build_payload()
    _write_json(spine_law, spine_payload)
    record("spine_discharge_law", spine_law)

    benchmark_json = ROOT / "data" / "hep_decay_benchmark.json"
    bench_payload = hbench.build_payload()
    _write_json(benchmark_json, bench_payload)
    record(
        "hep_decay_benchmark",
        benchmark_json,
        {"pass": bench_payload["summary"]["pass"], "fail": bench_payload["summary"]["fail"]},
    )
    if strict and bench_payload["summary"]["fail"] > 0:
        errors.append(f"benchmark: {bench_payload['summary']['fail']} failing case(s)")

    gap_json = ROOT / "data" / "spine_gap_closure_terms.json"
    _write_json(gap_json, spine_gaps.build_payload(benchmark_json))
    record("spine_gap_closure_terms", gap_json)

    # Paper TeX fragments
    _import_tex_exports(benchmark_json)
    record("branching_comparison_tex", GENERATED_DIR / "branching_comparison.tex")
    record("readout_error_distribution_tex", GENERATED_DIR / "readout_error_distribution.tex")

    from export_excited_mass_table import build_payload, build_rows, build_tex  # noqa: WPS433

    excited_json = ROOT / "data" / "excited_mass_comparison.json"
    excited_tex = GENERATED_DIR / "excited_mass_comparison.tex"
    excited_rows = build_rows()
    excited_payload = build_payload(excited_rows)
    _write_json(excited_json, excited_payload)
    excited_tex.write_text(build_tex(excited_rows, excited_payload), encoding="utf-8")
    record("excited_mass_comparison_tex", excited_tex, {"rows": excited_payload["row_count"]})

    from export_sigma_audit_tex import export_all as export_sigma_audit  # noqa: WPS433

    export_sigma_audit(
        excited_json=excited_json,
        benchmark_json=benchmark_json,
    )
    record("sigma_audit_tex", GENERATED_DIR / "sigma_floor_sensitivity.tex")

    from hqiv_hep_anomaly_discharge import build_payload as anomaly_build_payload  # noqa: WPS433
    from hqiv_hep_anomaly_discharge import build_tex as anomaly_build_tex  # noqa: WPS433

    anomaly_json = ROOT / "data" / "hep_anomaly_discharge.json"
    anomaly_tex = GENERATED_DIR / "anomaly_discharge_summary.tex"
    anomaly_payload = anomaly_build_payload(
        benchmark_path=benchmark_json,
        excited_path=excited_json,
    )
    _write_json(anomaly_json, anomaly_payload)
    anomaly_tex.write_text(anomaly_build_tex(anomaly_payload), encoding="utf-8")
    record(
        "anomaly_discharge_summary",
        anomaly_tex,
        {"discharged": anomaly_payload["summary"]["discharged_count"]},
    )

    # Electroweak mass panel
    try:
        import hqiv_electroweak_mass_benchmark as ew_bench

        ew_obs_path = ROOT / "data" / "electroweak_mass_observations.json"
        ew_cert_path = ROOT / "data" / "electroweak_mass_witness_certificate.json"
        ew_json = ROOT / "data" / "electroweak_mass_benchmark.json"
        obs = json.loads(ew_obs_path.read_text(encoding="utf-8"))
        ew_payload = ew_bench.build_payload(
            obs,
            observations_path=ew_obs_path,
            certificate_path=ew_cert_path,
        )
        _write_json(ew_cert_path, ew_payload["certificate"])
        _write_json(ew_json, ew_payload)
        _import_electroweak_tex(ew_json)
        record(
            "electroweak_mass_benchmark",
            ew_json,
            {"fail": ew_payload["summary"].get("fail", 0)},
        )
        if strict and ew_payload["summary"].get("fail", 0) > 0:
            errors.append("electroweak_mass_benchmark failed")
    except Exception as exc:  # pragma: no cover — soft optional step
        steps.append({"step": "electroweak_mass_benchmark", "skipped": str(exc)})

    # Collider witnesses (shared with gluon note)
    if not skip_collider_witnesses:
        import hqiv_hep_collider_refinements as hep_ref
        import hqiv_strong_sector_collider_discharge as strong_dis

        strong_json = ROOT / "data" / "strong_sector_collider_discharge.json"
        strong_payload = strong_dis.build_witness()
        _write_json(strong_json, strong_payload)
        record(
            "strong_sector_collider_discharge",
            strong_json,
            {"fail": strong_payload["summary"]["fail"]},
        )
        if strict and strong_payload["summary"]["fail"] > 0:
            errors.append("strong_sector_collider_discharge witness failed")

        ref_json = ROOT / "data" / "hep_collider_refinement_witness.json"
        ref_payload = hep_ref.build_witness()
        _write_json(ref_json, ref_payload)
        record(
            "hep_collider_refinement_witness",
            ref_json,
            {"fail": ref_payload["summary"]["fail"]},
        )
        if strict and ref_payload["summary"]["fail"] > 0:
            errors.append("hep_collider_refinement witness failed")

    # Certified strong discharge snapshot (φ, Δ, ρ⁰) at lab env
    demo_inp = ColliderLocalInput(facility="SPS_p_beam_400GeV", environment="lab")
    demo = run_local_readout(
        demo_inp,
        parents=("phi", "delta_p", "rho_zero", "B_plus"),
    )
    demo_json = ROOT / "data" / "hep_readout_pipeline_demo.json"
    _write_json(demo_json, run_payload_to_dict(demo))
    record("certified_strong_discharge_demo", demo_json)

    if not skip_tests:
        import os

        proc = subprocess.run(
            [
                sys.executable,
                "-m",
                "unittest",
                "discover",
                "-s",
                str(ROOT / "scripts"),
                "-p",
                "test_hqiv_hep*.py",
                "-q",
            ],
            cwd=str(ROOT),
            env={**os.environ, "PYTHONPATH": str(ROOT / "scripts")},
            capture_output=True,
            text=True,
        )
        steps.append(
            {
                "step": "unittest_hep",
                "ok": proc.returncode == 0,
                "tail": proc.stdout.splitlines()[-3:] + proc.stderr.splitlines()[-3:],
            }
        )
        if strict and proc.returncode != 0:
            errors.append("unittest discover test_hqiv_hep*.py failed")

    manifest = {
        "source": "scripts/hqiv_hep_readout_pipeline.py",
        "mode": "paper",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "strict": strict,
        "steps": steps,
        "errors": errors,
        "ok": not errors,
    }
    manifest_path = out_manifest or (ROOT / "data" / "hep_readout_pipeline_manifest.json")
    _write_json(manifest_path, manifest)
    return manifest


def cmd_run(args: argparse.Namespace) -> int:
    inp = ColliderLocalInput(
        facility=args.facility,
        beam_id=args.beam,
        beam_kinetic_energy_gev=args.beam_energy,
        target_id=args.target,
        target_kinetic_energy_gev=args.target_energy,
        beam_fraction=args.beam_fraction,
        collision_mode=args.collision_mode,
        beam_mix=args.beam_mix,
        environment=args.env,
        magnetic_field_tesla=args.b_tesla,
        collider_reference_tesla=args.collider_reference_tesla,
        comoving_stream_fraction=args.comoving_stream_fraction,
        lab_temperature_K=args.temperature_k,
        trap_embedding=args.trap,
    )
    parents = tuple(args.parent) if args.parent else ()
    result = run_local_readout(
        inp,
        parents=parents,
        chain=args.chain,
        max_depth=args.max_depth,
        include_heavy=args.heavy,
        include_beam_dump=args.beam_dump,
    )
    payload = run_payload_to_dict(result)
    out = args.json_out or (
        DEFAULT_RUNS / f"{args.facility or 'custom'}_{datetime.now(timezone.utc):%Y%m%d_%H%M%S}.json"
    )
    _write_json(out, payload)
    print(f"√s = {result.kinematics['sqrt_s_gev']:.3g} GeV  mode={result.kinematics['collision_mode']}")
    print(f"weak dressing F_weak = {result.environment['weak_width_factor']:.4f}")
    for pid, table in result.parent_tables.items():
        print(f"\n{pid} ({len(table)} modes):")
        for row in table[:8]:
            br = row["branching_ratio"]
            ds = ",".join(row["daughters"])
            print(f"  {row['channel']:8} {ds:30} BR={br:.4g}  spine={row['spine_discharge_weight']:.4g}")
    if args.chain:
        n_nodes = len(result.chain.get("nodes", [])) if result.chain else 0
        print(f"\nDecay chain nodes: {n_nodes}")
    print(f"\nWrote {out}")
    return 0


def cmd_paper(args: argparse.Namespace) -> int:
    manifest = reproduce_paper(
        strict=args.strict,
        skip_tests=args.skip_tests,
        skip_collider_witnesses=args.skip_collider,
    )
    print("HQIV HEP paper reproduction pipeline")
    for step in manifest["steps"]:
        if "path" in step:
            extra = ""
            if "fail" in step:
                extra = f" fail={step['fail']}"
            elif "pass" in step:
                extra = f" pass={step['pass']}"
            print(f"  {step['step']}: {step['path']}{extra}")
        else:
            print(f"  {step['step']}: {step}")
    if manifest["errors"]:
        print("\nSTRICT failures:")
        for err in manifest["errors"]:
            print(f"  - {err}")
        return 1
    print(f"\nManifest: {ROOT / 'data' / 'hep_readout_pipeline_manifest.json'}")
    return 0


def cmd_list(args: argparse.Namespace) -> int:
    kind: Literal["facilities", "envs", "parents"] = args.what
    if kind == "facilities":
        for name, setup in sorted(hep.FACILITY_PRESETS.items()):
            kin = hep.collision_kinematics(setup)
            print(f"{name:28} √s={kin.sqrt_s_gev:8.2f} GeV  {setup.resolved_collision_mode()}")
    elif kind == "envs":
        for name, preset in sorted(ENV_PRESETS.items()):
            env = hep.ExperimentEnvironment(**preset)
            print(
                f"{name:18} F_weak={env.weak_width_factor():.4f}  "
                f"outside={env.outside_support_factor():.4f}  trap={preset.get('trap_embedding')}"
            )
    else:
        demo_parents = (
            "pi_plus",
            "K_plus",
            "lambda",
            "phi",
            "rho_zero",
            "rho_plus",
            "omega_meson",
            "delta_p",
            "D_plus",
            "B_plus",
            "Jpsi",
            "Upsilon",
        )
        for pid in demo_parents:
            print(pid)
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="HQIV HEP readout pipeline (collider input → discharge → paper artifacts)"
    )
    sub = parser.add_subparsers(dest="command", required=True)

    run = sub.add_parser("run", help="Collider-local discharge readout")
    run.add_argument("--facility", choices=sorted(hep.FACILITY_PRESETS), default=None)
    run.add_argument("--beam", default="p")
    run.add_argument("--beam-energy", type=float, default=400.0)
    run.add_argument("--target", default="p")
    run.add_argument("--target-energy", type=float, default=0.0)
    run.add_argument("--beam-fraction", type=float, default=1.0)
    run.add_argument("--collision-mode", default="auto")
    run.add_argument("--beam-mix", default=None, help="e.g. p:0.85,pi+:12@0.15")
    run.add_argument("--env", choices=sorted(ENV_PRESETS), default="lab")
    run.add_argument("--B-tesla", type=float, default=0.0, dest="b_tesla")
    run.add_argument("--collider-reference-tesla", type=float, default=4.0)
    run.add_argument("--comoving-stream-fraction", type=float, default=0.0)
    run.add_argument("--temperature-k", type=float, default=293.15)
    run.add_argument("--trap", action="store_true", help="UCN bottle / trap embedding")
    run.add_argument("--parent", action="append", default=[], help="parent species (repeatable)")
    run.add_argument("--chain", action="store_true", help="also expand full decay chain")
    run.add_argument("--heavy", action="store_true")
    run.add_argument("--beam-dump", action="store_true")
    run.add_argument("--max-depth", type=int, default=5)
    run.add_argument("--json-out", type=Path, default=None)
    run.set_defaults(func=cmd_run)

    paper = sub.add_parser("paper", help="Reproduce paper data/ and generated/ TeX")
    paper.add_argument("--strict", action="store_true")
    paper.add_argument("--skip-tests", action="store_true")
    paper.add_argument("--skip-collider", action="store_true")
    paper.set_defaults(func=cmd_paper)

    lst = sub.add_parser("list", help="List facilities, environment presets, or patch parents")
    lst.add_argument(
        "what",
        choices=("facilities", "envs", "parents"),
        nargs="?",
        default="facilities",
    )
    lst.set_defaults(func=cmd_list)
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())

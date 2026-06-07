#!/usr/bin/env python3
"""
HQIV discharged decay calculator — unified nuclear + HEP CLI.

Subcommands:
  hep        — beam/target experiment with hadronic decay chains
  nuclear    — isotope / free-neutron β chains
  benchmark  — observations vs predictions regression panel
  discharge  — full readout: HEP experiment + benchmark summary + JSON export

Examples:
  python3 scripts/hqiv_decay_calculator.py hep --facility SPS_p_beam_400GeV
  python3 scripts/hqiv_decay_calculator.py hep --beam-dump --facility PS_p_beam_dump_24GeV
  python3 scripts/hqiv_decay_calculator.py nuclear --seed n --max-depth 4
  python3 scripts/hqiv_decay_calculator.py benchmark --strict
  python3 scripts/hqiv_decay_calculator.py discharge --facility NA62_K_75GeV
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import hqiv_decay_chain as dc
import hqiv_hep_decay_benchmark as bench
import hqiv_hep_decay_chain as hep

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_DISCHARGE_JSON = ROOT / "data" / "decay_calculator_discharge.json"


def cmd_hep(args: argparse.Namespace) -> int:
    if args.facility:
        setup = hep.FACILITY_PRESETS[args.facility]
    else:
        beam_e = args.beam_energy if args.beam_energy is not None else 400.0
        mix = (
            hep.parse_beam_mix(args.beam_mix, default_energy_gev=beam_e)
            if args.beam_mix
            else ()
        )
        setup = hep.BeamTargetSetup(
            args.beam,
            beam_e,
            args.target,
            args.target_energy,
            args.beam_fraction,
            beam_mix=mix,
        )
    env = hep.ExperimentEnvironment(
        magnetic_field_tesla=args.b_tesla,
        lab_temperature_K=args.temperature_k,
        trap_embedding=args.trap,
    )
    production = args.produce.split(",") if args.produce else None
    result = hep.run_experiment(
        setup,
        env=env,
        production_ids=production,
        max_depth=args.max_depth,
        follow=args.follow,
        include_beam_dump=args.beam_dump,
        include_heavy=args.heavy,
    )
    hep.print_report(result)
    if args.json_out:
        payload = hep.build_payload(result)
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        print(f"\nWrote {args.json_out}")
    return 0


def cmd_nuclear(args: argparse.Namespace) -> int:
    label = args.seed.strip()
    if label in ("n", "neutron"):
        state = dc.NuclearState(1, 0, label="n")
    elif label in ("p", "proton"):
        state = dc.NuclearState(1, 1, label="p")
    elif "Z" in label and "A" in label.upper():
        # Z6A12 style
        import re

        m = re.match(r"Z(\d+)A(\d+)", label, re.I)
        if not m:
            raise SystemExit(f"cannot parse nuclear label {label!r}")
        state = dc.NuclearState(int(m.group(2)), int(m.group(1)), label=label)
    else:
        raise SystemExit(f"unknown nuclear seed {label!r}; use n, p, or Z6A12")

    result = dc.expand_chain(
        state,
        max_depth=args.max_depth,
        q_policy=args.q_policy,
        residual_mode=args.residual_mode,
        qualify_em_tipping=args.qualify_em_tipping,
    )
    print("HQIV nuclear decay-chain readout")
    print("=" * 72)
    dc._print_tree(dc._serialize_node(result.nodes[0]), indent=0)
    print(f"\nNodes: {len(result.nodes)}  terminal: {len(result.terminal)}")
    if args.json_out:
        payload = dc.build_payload(
            roots=[state],
            max_depth=args.max_depth,
            q_policy=args.q_policy,
            include_hadron_demo=False,
            qualify_em_tipping=args.qualify_em_tipping,
        )
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        print(f"Wrote {args.json_out}")
    return 0


def cmd_benchmark(args: argparse.Namespace) -> int:
    payload = bench.build_payload(
        observations_path=args.observations,
        published_path=args.published,
    )
    bench.print_report(payload)
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"\nWrote {args.json_out}")
    if args.strict and payload["summary"]["fail"] > 0:
        print(f"\nSTRICT: {payload['summary']['fail']} failing case(s)")
        return 1
    return 0


def cmd_discharge(args: argparse.Namespace) -> int:
    """Run HEP experiment + nuclear bridge + benchmark; write combined discharge JSON."""
    if args.facility:
        setup = hep.FACILITY_PRESETS[args.facility]
    else:
        beam_e = args.beam_energy if args.beam_energy is not None else 400.0
        setup = hep.BeamTargetSetup(args.beam, beam_e, args.target, args.target_energy)
    env = hep.ExperimentEnvironment(
        magnetic_field_tesla=args.b_tesla,
        lab_temperature_K=args.temperature_k,
    )
    hep_result = hep.run_experiment(
        setup,
        env=env,
        max_depth=args.max_depth,
        include_beam_dump=args.beam_dump,
        include_heavy=getattr(args, "heavy", False),
        follow=args.follow,
    )
    bench_payload = bench.build_payload()
    nuclear_state = dc.NuclearState(1, 0, label="n")
    nuclear_result = dc.expand_chain(
        nuclear_state,
        max_depth=max(args.max_depth, 4),
        q_policy="nucleon_gap",
        residual_mode="effective",
    )
    discharge = {
        "source": "scripts/hqiv_decay_calculator.py",
        "mode": "discharge",
        "hep": hep.build_payload(hep_result),
        "nuclear": dc.build_payload(
            roots=[nuclear_state],
            max_depth=max(args.max_depth, 4),
            q_policy="nucleon_gap",
            include_hadron_demo=False,
        ),
        "benchmark": bench_payload,
        "discharge_summary": {
            "sqrt_s_gev": hep_result.kinematics.sqrt_s_gev,
            "accessible_species": len(hep_result.produced),
            "decay_roots": len(hep_result.root_nodes),
            "nuclear_nodes": len(nuclear_result.nodes),
            "benchmark_pass": bench_payload["summary"]["pass"],
            "benchmark_fail": bench_payload["summary"]["fail"],
            "benchmark_known_gap": bench_payload["summary"].get("known_gap", 0),
        },
    }
    hep.print_report(hep_result)
    print()
    print("HQIV nuclear β bridge (free neutron seed)")
    print("=" * 72)
    dc._print_tree(dc._serialize_node(nuclear_result.nodes[0]), indent=0)
    print()
    bench.print_report(bench_payload)
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(discharge, indent=2) + "\n", encoding="utf-8")
    print(f"\nWrote {args.json_out}")
    if args.strict and bench_payload["summary"]["fail"] > 0:
        return 1
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="HQIV discharged decay calculator (nuclear + HEP + benchmark)"
    )
    sub = parser.add_subparsers(dest="command", required=True)

    p_hep = sub.add_parser("hep", help="HEP beam/target decay chains")
    p_hep.add_argument("--facility", choices=sorted(hep.FACILITY_PRESETS), default=None)
    p_hep.add_argument("--beam", default="p")
    p_hep.add_argument("--beam-energy", type=float, default=None)
    p_hep.add_argument("--target", default="p")
    p_hep.add_argument("--target-energy", type=float, default=0.0)
    p_hep.add_argument("--beam-fraction", type=float, default=1.0)
    p_hep.add_argument("--beam-mix", type=str, default=None)
    p_hep.add_argument("--follow", choices=("heaviest", "all_hadronic"), default="heaviest")
    p_hep.add_argument("--beam-dump", action="store_true")
    p_hep.add_argument(
        "--heavy",
        action="store_true",
        help="include charm/bottom decay roots",
    )
    p_hep.add_argument("--B-tesla", type=float, default=0.0, dest="b_tesla")
    p_hep.add_argument("--temperature-K", type=float, default=293.15, dest="temperature_k")
    p_hep.add_argument("--trap", action="store_true")
    p_hep.add_argument("--produce", type=str, default=None)
    p_hep.add_argument("--max-depth", type=int, default=5)
    p_hep.add_argument("--json-out", type=Path, default=hep.DEFAULT_JSON)
    p_hep.set_defaults(func=cmd_hep)

    p_nuc = sub.add_parser("nuclear", help="Nuclear β decay chains")
    p_nuc.add_argument("--seed", default="n", help="n, p, or Z6A12")
    p_nuc.add_argument("--max-depth", type=int, default=6)
    p_nuc.add_argument(
        "--q-policy", choices=("nucleon_gap", "mass_budget"), default="nucleon_gap"
    )
    p_nuc.add_argument(
        "--residual-mode", choices=("effective", "raw"), default="effective"
    )
    p_nuc.add_argument("--qualify-em-tipping", action="store_true")
    p_nuc.add_argument("--json-out", type=Path, default=dc.DEFAULT_JSON)
    p_nuc.set_defaults(func=cmd_nuclear)

    p_bench = sub.add_parser("benchmark", help="Observations vs predictions")
    p_bench.add_argument("--observations", type=Path, default=bench.DEFAULT_OBSERVATIONS)
    p_bench.add_argument("--published", type=Path, default=bench.DEFAULT_PUBLISHED)
    p_bench.add_argument("--json-out", type=Path, default=bench.DEFAULT_JSON)
    p_bench.add_argument("--strict", action="store_true")
    p_bench.set_defaults(func=cmd_benchmark)

    p_dis = sub.add_parser("discharge", help="Full HEP + benchmark discharge")
    p_dis.add_argument("--facility", choices=sorted(hep.FACILITY_PRESETS), default=None)
    p_dis.add_argument("--beam", default="p")
    p_dis.add_argument("--beam-energy", type=float, default=None)
    p_dis.add_argument("--target", default="p")
    p_dis.add_argument("--target-energy", type=float, default=0.0)
    p_dis.add_argument("--beam-dump", action="store_true")
    p_dis.add_argument(
        "--heavy",
        action="store_true",
        help="include charm/bottom decay roots",
    )
    p_dis.add_argument("--follow", choices=("heaviest", "all_hadronic"), default="heaviest")
    p_dis.add_argument("--B-tesla", type=float, default=0.0, dest="b_tesla")
    p_dis.add_argument("--temperature-K", type=float, default=293.15, dest="temperature_k")
    p_dis.add_argument("--max-depth", type=int, default=5)
    p_dis.add_argument("--json-out", type=Path, default=DEFAULT_DISCHARGE_JSON)
    p_dis.add_argument("--strict", action="store_true")
    p_dis.set_defaults(func=cmd_discharge)

    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())

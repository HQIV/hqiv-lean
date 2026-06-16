#!/usr/bin/env python3
"""
Carrier-peaking molecule ladder — LiF and H₂O first, scaling without dense support.

Uses sparse OSH carrier bookkeeping (Lean ``CarrierPeaking`` / ``OSHoracle``):
encode discrete geometry on a sparse register, one HQIV-native phase step, read
16/32-sector peaks — never build the full ``(L+1)²`` Hilbert vector.

Binding energies are **witnesses** from the parameter-free dynamic binding chart;
the carrier pipeline does not inject macroscopic force laws.

Run:
  PYTHONPATH=scripts:. python3 scripts/hqiv_carrier_peaking_molecule_ladder.py
  PYTHONPATH=scripts:. python3 scripts/hqiv_carrier_peaking_molecule_ladder.py --json-out data/carrier_peaking_molecule_ladder.json
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Literal

import hqiv_electronic_valence_shells as evs
from fragment_aware_bonded_horizon import BondGeometry, FragmentConfig
from hqiv_dynamic_binding_chart import GMTKN55_SUITE, MoleculeBenchmark, dynamic_binding_for_benchmark
from hqiv_lab.carrier_peaking import (
    REFERENCE_M_DEFAULT,
    enumerate_geometry_levels,
    flat_indices_for_molecule_geometry,
    run_carrier_peaking,
    shells_from_compton_list,
)

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_JSON = ROOT / "data" / "carrier_peaking_molecule_ladder.json"

BindingKind = Literal["dissociation", "atomization"]

# LiF — alkali halide (ionic); W4-17 dissociation ≈ 5.99 eV, r_e ≈ 1.564 Å.
LIF_BENCHMARK = MoleculeBenchmark(
    "LiF",
    "dissociation",
    (FragmentConfig("Li", 3, 3), FragmentConfig("F", 9, 9)),
    (BondGeometry(0, 1, 1.5636),),
    5.991,
    "W4-17 / literature",
)

LADDER_MOLECULES: tuple[MoleculeBenchmark, ...] = (LIF_BENCHMARK,) + tuple(
    b for b in GMTKN55_SUITE if b.name.upper() == "H2O"
)


@dataclass(frozen=True)
class LadderConfig:
    L: int = 11
    n_levels: int = 4
    reference_m: int = REFERENCE_M_DEFAULT
    peak_min_frac: float = 0.35
    encodings: tuple[str, ...] = ("mixed_radix", "contact_ell")


def _bench_by_name(name: str) -> MoleculeBenchmark:
    key = name.upper()
    for b in LADDER_MOLECULES:
        if b.name.upper() == key:
            return b
    raise KeyError(f"unknown ladder molecule {name!r}; choices: {[b.name for b in LADDER_MOLECULES]}")


def _compton_shells(bench: MoleculeBenchmark) -> list[int]:
    return [evs.electronic_compton_shells(f.z_nuclear)[0] for f in bench.fragments]


def _bond_distance_grid(bench: MoleculeBenchmark, n_levels: int) -> list[float]:
    if not bench.bonds:
        return []
    b0 = bench.bonds[0].distance_angstrom
    span = 0.12 if len(bench.bonds) == 1 else 0.12
    lo = max(0.4, b0 - span)
    hi = b0 + span
    if n_levels == 1:
        return [b0]
    step = (hi - lo) / (n_levels - 1)
    return [lo + i * step for i in range(n_levels)]


def _geometry_specs(bench: MoleculeBenchmark, n_levels: int) -> list[dict[str, int]]:
    n_bonds = len(bench.bonds)
    centre_bonds = sum(1 for b in bench.bonds if b.frag_i == 0 or b.frag_j == 0)
    include_angle = centre_bonds >= 2 and max(f.z_nuclear for f in bench.fragments) > 1
    specs = enumerate_geometry_levels(n_bonds, n_levels=n_levels, include_angle=include_angle)
    return [asdict(s) for s in specs]


def audit_molecule(
    bench: MoleculeBenchmark,
    cfg: LadderConfig,
) -> dict[str, Any]:
    shells = shells_from_compton_list(_compton_shells(bench), cfg.L)
    specs = enumerate_geometry_levels(
        len(bench.bonds),
        n_levels=cfg.n_levels,
        include_angle=sum(1 for b in bench.bonds if b.frag_i == 0 or b.frag_j == 0) >= 2
        and max(f.z_nuclear for f in bench.fragments) > 1,
    )
    dist_grid = _bond_distance_grid(bench, cfg.n_levels)

    encoding_runs: dict[str, Any] = {}
    for enc in cfg.encodings:
        flats = flat_indices_for_molecule_geometry(
            encoding=enc,  # type: ignore[arg-type]
            L=cfg.L,
            specs=specs,
            bond_distances_angstrom=dist_grid,
        )
        encoding_runs[enc] = run_carrier_peaking(
            cfg.L,
            shells,
            flats,
            reference_m=cfg.reference_m,
            peak_min_frac=cfg.peak_min_frac,
        )

    binding = dynamic_binding_for_benchmark(bench)
    L_scan = [cfg.L, cfg.L + 1, cfg.L + 2]
    scaling: list[dict[str, Any]] = []
    primary_enc = "mixed_radix"
    flats_primary = flat_indices_for_molecule_geometry(
        encoding=primary_enc,  # type: ignore[arg-type]
        L=cfg.L,
        specs=specs,
        bond_distances_angstrom=dist_grid,
    )
    for L_try in L_scan:
        sh = shells_from_compton_list(_compton_shells(bench), L_try)
        rep = run_carrier_peaking(
            L_try,
            sh,
            flats_primary,
            reference_m=cfg.reference_m,
            peak_min_frac=cfg.peak_min_frac,
        )
        scaling.append(
            {
                "L": L_try,
                "sparse_basis_card": rep["sparse_basis_card"],
                "sparse_seed_len": rep["sparse_seed_len"],
                "compression_vs_dense_card": rep["compression_vs_dense_card"],
                "flip_count": rep["flip_count"],
                "peaks16_count": len(rep["peaks16"]),
            }
        )

    primary = encoding_runs[primary_enc]
    return {
        "molecule": bench.name,
        "kind": bench.kind,
        "n_atoms": len(bench.fragments),
        "n_bonds": len(bench.bonds),
        "compton_shells": _compton_shells(bench),
        "geometry_level_count": len(specs),
        "geometry_specs_sample": _geometry_specs(bench, cfg.n_levels)[:4],
        "binding_witness": {
            "binding_ev": binding.binding_ev,
            "reference_ev": binding.reference_ev,
            "error_pct": binding.error_pct,
            "contact_xi": binding.contact_xi,
            "compton_triplet": binding.compton_triplet_m,
        },
        "config": asdict(cfg),
        "encodings": encoding_runs,
        "scaling_L_sweep": scaling,
        "scaling_summary": {
            "sparse_support_independent_of_L_card": all(
                s["sparse_seed_len"] == primary["sparse_seed_len"] for s in scaling
            ),
            "dense_card_grows_quadratically": scaling[0]["sparse_basis_card"] < scaling[-1]["sparse_basis_card"],
            "primary_flip_signal": primary["flip_count"],
            "primary_peaks16": primary["peaks16"],
            "mixed_radix_injective": primary["encoding_injective"],
        },
    }


def run_ladder(cfg: LadderConfig | None = None) -> dict[str, Any]:
    cfg = cfg or LadderConfig()
    rows = [audit_molecule(b, cfg) for b in LADDER_MOLECULES]
    return {
        "program": "hqiv_carrier_peaking_molecule_ladder",
        "lean_spine": [
            "Hqiv.QuantumComputing.CarrierPeaking",
            "Hqiv.QuantumComputing.OSHoracle",
            "Hqiv.QuantumComputing.OSHoracleHQIVNative",
        ],
        "molecules": rows,
        "summary": {
            "count": len(rows),
            "all_mixed_radix_injective": all(
                r["scaling_summary"]["mixed_radix_injective"] for r in rows
            ),
            "all_sparse_independent_of_L": all(
                r["scaling_summary"]["sparse_support_independent_of_L_card"] for r in rows
            ),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Carrier-peaking ladder (LiF, H2O).")
    parser.add_argument("--L", type=int, default=11, help="Harmonic cutoff (default 11).")
    parser.add_argument("--levels", type=int, default=4, help="Bins per geometry DOF (default 4).")
    parser.add_argument("--json-out", default=str(DEFAULT_JSON), help="Output JSON path.")
    args = parser.parse_args()

    cfg = LadderConfig(L=args.L, n_levels=args.levels)
    report = run_ladder(cfg)

    out = Path(args.json_out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2))

    print("HQIV carrier-peaking molecule ladder")
    print("=" * 36)
    for row in report["molecules"]:
        pri = row["encodings"]["mixed_radix"]
        bw = row["binding_witness"]
        ss = row["scaling_summary"]
        print(
            f"  {row['molecule']:4s}  levels={row['geometry_level_count']:2d}  "
            f"seed={pri['sparse_seed_len']:2d}  card={pri['sparse_basis_card']:3d}  "
            f"compress={pri['compression_vs_dense_card']:.2f}x  "
            f"flip={pri['flip_count']:2d}  peaks16={len(pri['peaks16'])}  "
            f"bind={bw['binding_ev']:.2f} eV (ref {bw['reference_ev']:.2f})"
        )
        print(
            f"         scaling: L-indep seed={ss['sparse_support_independent_of_L_card']}  "
            f"injective={ss['mixed_radix_injective']}"
        )
    print(f"Wrote {out}")


if __name__ == "__main__":
    main()

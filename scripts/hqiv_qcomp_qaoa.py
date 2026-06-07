#!/usr/bin/env python3
"""
HQIV QComp pipeline — general QAOA over molecular geometry.

Cost landscape: parameter-free ``hqiv_dynamic_binding_chart`` binding energy
(network surplus × vev × geometry × κ(ξ)), not a fitted UCC or force field.

Outputs (printed and JSON):
  • bond_lengths_angstrom[]
  • binding_energy_per_bond_ev[]
  • centre_angle_deg, per-bond angles_deg
  • total binding_energy_ev, network feedback factors

Lean spine (symbolic cover): ``Hqiv.QuantumComputing.SymbolicDomainCoverExamples.qaoaSpec``
(ring ansatz, shell-local 2-qubit routes).

Run:
  python3 scripts/hqiv_qcomp_qaoa.py H2O
  python3 scripts/hqiv_qcomp_qaoa.py H2O --p 3 --bits 2 --json-out data/qaoa_h2o.json
  python3 scripts/hqiv_qcomp_qaoa.py --list
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Literal

import hqiv_curvature_contact_network as ccn
import hqiv_shell_aware_binding as sab
from fragment_aware_bonded_horizon import BondGeometry, FragmentConfig
from hqiv_dynamic_binding_chart import (
    EV_PER_LAMBDA_UNIT,
    GMTKN55_SUITE,
    MoleculeBenchmark,
    dynamic_binding_for_benchmark,
)

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_JSON = ROOT / "data" / "qcomp_qaoa_readout.json"

LEAN_QAOA_FAMILY = "symbolic_qaoa"  # SymbolicDomainCoverExamples.qaoaSpec


@dataclass(frozen=True)
class GeometryDOF:
    """One discretized geometric degree of freedom for QAOA bit encoding."""

    name: str
    kind: Literal["bond_length", "centre_angle"]
    bond_index: int | None
    min_val: float
    max_val: float
    n_bits: int
    reference_val: float

    @property
    def n_levels(self) -> int:
        return 2**self.n_bits


@dataclass(frozen=True)
class MolecularQAOASpec:
    benchmark: MoleculeBenchmark
    dofs: tuple[GeometryDOF, ...]
    z_centre: int | None

    @property
    def n_qubits(self) -> int:
        return sum(d.n_bits for d in self.dofs)


def _bench_by_name(name: str) -> MoleculeBenchmark:
    key = name.upper()
    for b in GMTKN55_SUITE:
        if b.name.upper() == key:
            return b
    raise KeyError(f"unknown molecule {name!r}; use --list")


def default_geometry_dofs(
    bench: MoleculeBenchmark,
    *,
    bond_length_bits: int = 2,
    angle_bits: int = 2,
    length_span: float = 0.12,
) -> tuple[GeometryDOF, ...]:
    """Build DOFs from benchmark geometry (centre angle + each bond length)."""
    dofs: list[GeometryDOF] = []
    z_centre = max((f.z_nuclear for f in bench.fragments), default=1)
    centre_bonds = sum(1 for b in bench.bonds if b.frag_i == 0 or b.frag_j == 0)
    if centre_bonds >= 2 and z_centre > 1:
        ref_ang = bench.bonds[0].bond_angle_rad
        if ref_ang is None:
            import hqiv_chemistry_tuft_dynamics as ctd

            ref_ang = ctd.dynamic_centre_angle_rad(z_centre, centre_bonds)
        span = math.radians(18.0)
        dofs.append(
            GeometryDOF(
                name="centre_angle",
                kind="centre_angle",
                bond_index=None,
                min_val=ref_ang - span,
                max_val=ref_ang + span,
                n_bits=angle_bits,
                reference_val=ref_ang,
            )
        )
    for i, bond in enumerate(bench.bonds):
        d0 = bond.distance_angstrom
        dofs.append(
            GeometryDOF(
                name=f"bond_{i}_length",
                kind="bond_length",
                bond_index=i,
                min_val=max(0.4, d0 - length_span),
                max_val=d0 + length_span,
                n_bits=bond_length_bits,
                reference_val=d0,
            )
        )
    return tuple(dofs)


def spec_from_molecule(
    name: str,
    *,
    bond_length_bits: int = 2,
    angle_bits: int = 2,
) -> MolecularQAOASpec:
    bench = _bench_by_name(name)
    z_centre = max((f.z_nuclear for f in bench.fragments), default=1)
    if z_centre <= 1:
        z_centre = None
    return MolecularQAOASpec(
        benchmark=bench,
        dofs=default_geometry_dofs(
            bench,
            bond_length_bits=bond_length_bits,
            angle_bits=angle_bits,
        ),
        z_centre=z_centre if z_centre and z_centre > 1 else None,
    )


def _decode_bits(dof: GeometryDOF, bits: int) -> float:
    level = bits % dof.n_levels
    if dof.n_levels == 1:
        return dof.reference_val
    t = level / (dof.n_levels - 1)
    return dof.min_val + t * (dof.max_val - dof.min_val)


def decode_bitstring(spec: MolecularQAOASpec, x: int) -> dict[str, float]:
    """Decode integer bitstring to named geometry values."""
    out: dict[str, float] = {}
    shift = 0
    for dof in spec.dofs:
        mask = (1 << dof.n_bits) - 1
        bits = (x >> shift) & mask
        out[dof.name] = _decode_bits(dof, bits)
        shift += dof.n_bits
    return out


def bonds_from_geometry(
    spec: MolecularQAOASpec,
    geom: dict[str, float],
) -> tuple[BondGeometry, ...]:
    bench = spec.benchmark
    centre_rad = geom.get("centre_angle")
    out: list[BondGeometry] = []
    for i, b in enumerate(bench.bonds):
        d = geom.get(f"bond_{i}_length", b.distance_angstrom)
        ang = centre_rad if centre_rad is not None else b.bond_angle_rad
        out.append(
            BondGeometry(
                b.frag_i,
                b.frag_j,
                d,
                bond_angle_rad=ang,
            )
        )
    return tuple(out)


def evaluate_geometry(
    spec: MolecularQAOASpec,
    geom: dict[str, float],
) -> dict[str, Any]:
    """Full HQIV chemistry readout at a geometry point."""
    bench = spec.benchmark
    bonds = bonds_from_geometry(spec, geom)
    net = ccn.build_network_from_molecule(bench.name, bench.fragments, bonds)
    shell = sab.resolve_shell_aware_readout(
        kind=bench.kind,
        fragments=bench.fragments,
        compton_triplet=net.compton_triplet,
        net=net,
        molecule_name=bench.name,
    )
    fb = ccn.network_binding_feedback(
        net,
        curvature_contrast_weight=shell.curvature_feedback_weight,
    )
    import hqiv_dynamic_binding_chart as chart
    import hqiv_lean_physics_primitives as lean

    triplet = net.compton_triplet
    eta_p = lean.dynamic_compton_eta_second_order(shell.eta_p_linear, triplet)
    surplus = chart.surplus_dimless_for_molecule(
        bench,
        shell.surplus_angles_rad,
        surplus_dress_factor=shell.surplus_dress_factor,
    )
    dimless = eta_p * surplus * fb.dimless_prefactor
    total_ev = dimless * EV_PER_LAMBDA_UNIT
    err_pct = (total_ev - bench.reference_ev) / bench.reference_ev * 100.0

    geoms = ccn.covalent_bond_geometries(net)
    weights = [
        max(g.geff_combined * max(g.valley_alignment_weight, 1e-12), 1e-12)
        for g in geoms
    ]
    wsum = sum(weights) or 1.0
    per_bond = [total_ev * w / wsum for w in weights]

    bond_rows: list[dict[str, Any]] = []
    for i, (g, be) in enumerate(zip(geoms, per_bond)):
        bond_rows.append(
            {
                "bond_index": i,
                "frag_i": bonds[i].frag_i,
                "frag_j": bonds[i].frag_j,
                "distance_angstrom": bonds[i].distance_angstrom,
                "bond_angle_deg": math.degrees(g.bond_angle_rad),
                "ideal_angle_deg": math.degrees(g.ideal_bond_angle_rad),
                "valley_alignment": g.valley_alignment_weight,
                "binding_energy_ev": be,
                "geff_combined": g.geff_combined,
            }
        )

    centre_deg = None
    if "centre_angle" in geom:
        centre_deg = math.degrees(geom["centre_angle"])

    return {
        "molecule": bench.name,
        "kind": bench.kind,
        "binding_energy_total_ev": total_ev,
        "binding_energy_per_bond_ev": per_bond,
        "reference_ev": bench.reference_ev,
        "error_pct": err_pct,
        "bond_lengths_angstrom": [b.distance_angstrom for b in bonds],
        "centre_angle_deg": centre_deg,
        "bond_angles_deg": [math.degrees(g.bond_angle_rad) for g in geoms],
        "eta_p_second_order": eta_p,
        "surplus_dimless": surplus,
        "dimless_core": dimless,
        "network_binding_feedback": {
            "contact_xi": fb.contact_xi,
            "networked_vev": fb.networked_vev_geometric_mean,
            "steric_multiplier": fb.steric_multiplier,
            "geometry_alignment": fb.geometry_alignment_factor,
            "curvature_feedback": fb.curvature_feedback_at_xi,
            "dimless_prefactor": fb.dimless_prefactor,
        },
        "shell_readout": shell.to_dict(),
        "bonds": bond_rows,
    }


def qaoa_cost(spec: MolecularQAOASpec, x: int) -> float:
    """QAOA maximizes binding → minimize negative binding energy."""
    geom = decode_bitstring(spec, x)
    ev = evaluate_geometry(spec, geom)["binding_energy_total_ev"]
    return -ev


def _scaled_costs(spec: MolecularQAOASpec) -> tuple[list[float], list[float]]:
    """Return (raw costs, scaled to [0, π] for QAOA phases)."""
    dim = 1 << spec.n_qubits
    costs = [qaoa_cost(spec, i) for i in range(dim)]
    c_min, c_max = min(costs), max(costs)
    if c_max == c_min:
        return costs, [0.0] * dim
    scaled = [math.pi * (c - c_min) / (c_max - c_min) for c in costs]
    return costs, scaled


def _qaoa_probabilities(
    n: int,
    scaled: list[float],
    gammas: list[float],
    betas: list[float],
) -> list[float]:
    """Classical QAOA probability surrogate (cost diagonal + Rx mixer per qubit)."""
    dim = 1 << n
    p = [1.0 / dim] * dim
    for gamma, beta in zip(gammas, betas):
        weights = [p[i] * math.exp(-gamma * scaled[i]) for i in range(dim)]
        norm = sum(weights) or 1.0
        p = [w / norm for w in weights]
        cos_b = math.cos(beta) ** 2
        sin_b = math.sin(beta) ** 2
        for k in range(n):
            p_new = [0.0] * dim
            for i in range(dim):
                j = i ^ (1 << k)
                p_new[i] += cos_b * p[i] + sin_b * p[j]
            norm = sum(p_new) or 1.0
            p = [x / norm for x in p_new]
    return p


def qaoa_expectation_cost(
    spec: MolecularQAOASpec,
    gammas: list[float],
    betas: list[float],
) -> float:
    """
    ⟨C⟩ under classical QAOA (exact enumeration, n ≤ 14 qubits).

    Cost: diagonal HQIV binding; mixer: product of Rx(β) on each qubit.
    """
    if spec.n_qubits > 14:
        raise ValueError(f"too many qubits ({spec.n_qubits}) for exact QAOA simulation")
    costs, scaled = _scaled_costs(spec)
    p = _qaoa_probabilities(spec.n_qubits, scaled, gammas, betas)
    return sum(p[i] * costs[i] for i in range(len(costs)))


def run_classical_qaoa(
    spec: MolecularQAOASpec,
    *,
    p_layers: int = 2,
    maxiter: int = 80,
) -> dict[str, Any]:
    """Optimize QAOA (γ, β) vectors then report best measured bitstring."""
    from scipy.optimize import minimize

    n_param = 2 * p_layers
    x0 = [0.5] * n_param

    def objective(params: list[float]) -> float:
        gammas = params[:p_layers]
        betas = params[p_layers:]
        return qaoa_expectation_cost(spec, gammas, betas)

    res = minimize(objective, x0, method="COBYLA", options={"maxiter": maxiter})
    gammas = list(res.x[:p_layers])
    betas = list(res.x[p_layers:])

    costs, scaled = _scaled_costs(spec)
    p = _qaoa_probabilities(spec.n_qubits, scaled, gammas, betas)
    best_i = max(range(len(costs)), key=lambda i: p[i] * (-costs[i]))
    geom = decode_bitstring(spec, best_i)
    readout = evaluate_geometry(spec, geom)

    return {
        "method": "classical_qaoa",
        "lean_family": LEAN_QAOA_FAMILY,
        "p_layers": p_layers,
        "n_qubits": spec.n_qubits,
        "gammas": gammas,
        "betas": betas,
        "optimizer_success": bool(res.success),
        "optimizer_message": str(res.message),
        "expectation_cost": float(res.fun),
        "best_bitstring": best_i,
        "best_geometry": geom,
        "readout": readout,
    }


def run_reference_readout(spec: MolecularQAOASpec) -> dict[str, Any]:
    """Benchmark geometry without QAOA optimization."""
    geom = {d.name: d.reference_val for d in spec.dofs}
    readout = evaluate_geometry(spec, geom)
    chart = dynamic_binding_for_benchmark(spec.benchmark)
    return {
        "method": "reference_geometry",
        "lean_family": LEAN_QAOA_FAMILY,
        "readout": readout,
        "chart_binding_ev": chart.binding_ev,
        "chart_error_pct": chart.error_pct,
    }


def run_brute_force(spec: MolecularQAOASpec) -> dict[str, Any]:
    """Exhaustive search over all geometry bitstrings (small n)."""
    dim = 1 << spec.n_qubits
    best_i = min(range(dim), key=lambda i: qaoa_cost(spec, i))
    geom = decode_bitstring(spec, best_i)
    return {
        "method": "brute_force",
        "lean_family": LEAN_QAOA_FAMILY,
        "n_qubits": spec.n_qubits,
        "best_bitstring": best_i,
        "best_geometry": geom,
        "readout": evaluate_geometry(spec, geom),
    }


def print_report(payload: dict[str, Any]) -> None:
    """Human-readable geometry + binding table."""
    print("HQIV QComp QAOA chemistry readout")
    print("=" * 72)
    print(f"Lean family: {payload.get('lean_family', LEAN_QAOA_FAMILY)}")
    if "method" in payload:
        print(f"Method:      {payload['method']}")
    if "p_layers" in payload:
        print(f"QAOA:        p={payload['p_layers']}  qubits={payload['n_qubits']}")

    readout = payload.get("readout") or payload
    if "readout" in payload and isinstance(payload["readout"], dict):
        readout = payload["readout"]

    print()
    print(f"Molecule: {readout['molecule']}  ({readout['kind']})")
    print(f"Total BE: {readout['binding_energy_total_ev']:.4f} eV  "
          f"(ref {readout['reference_ev']:.4f} eV, err {readout['error_pct']:+.2f}%)")
    print()
    print("Bond lengths (Å):")
    for i, r in enumerate(readout.get("bond_lengths_angstrom", [])):
        print(f"  bond {i}: {r:.4f}")
    if readout.get("centre_angle_deg") is not None:
        print(f"Centre angle (H–X–H): {readout['centre_angle_deg']:.2f}°")
    print()
    print("Per-bond binding (eV) and angles:")
    print(f"  {'bond':<6} {'BE/eV':>8} {'r/Å':>8} {'θ/°':>8} {'θ_ideal/°':>10} {'valley':>8}")
    for row in readout.get("bonds", []):
        print(
            f"  {row['bond_index']:<6} {row['binding_energy_ev']:8.4f} "
            f"{row['distance_angstrom']:8.4f} {row['bond_angle_deg']:8.2f} "
            f"{row['ideal_angle_deg']:10.2f} {row['valley_alignment']:8.4f}"
        )
    nfb = readout.get("network_binding_feedback", {})
    if nfb:
        print()
        print("Network feedback:")
        print(f"  vev_net={nfb.get('networked_vev', 0):.4f}  steric={nfb.get('steric_multiplier', 1):.4f}  "
              f"geom={nfb.get('geometry_alignment', 1):.4f}  κ_fb={nfb.get('curvature_feedback', 1):.4f}")


def build_payload(
    spec: MolecularQAOASpec,
    *,
    p_layers: int = 2,
    methods: tuple[str, ...] = ("reference_geometry", "brute_force", "classical_qaoa"),
) -> dict[str, Any]:
    out: dict[str, Any] = {
        "source": "scripts/hqiv_qcomp_qaoa.py",
        "lean_modules": [
            "Hqiv.QuantumComputing.SymbolicDomainCoverExamples",
            "Hqiv.QuantumChemistry.CurvatureContactNetwork",
            "Hqiv.QuantumChemistry.DynamicBindingChart",
        ],
        "molecule": spec.benchmark.name,
        "n_qubits": spec.n_qubits,
        "geometry_dofs": [asdict(d) for d in spec.dofs],
        "z_centre": spec.z_centre,
    }
    runs: dict[str, Any] = {}
    if "reference_geometry" in methods:
        runs["reference"] = run_reference_readout(spec)
    if "brute_force" in methods and spec.n_qubits <= 14:
        runs["brute_force"] = run_brute_force(spec)
    if "classical_qaoa" in methods:
        try:
            runs["qaoa"] = run_classical_qaoa(spec, p_layers=p_layers)
        except ImportError as exc:
            runs["qaoa"] = {"error": str(exc)}
    out["runs"] = runs
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description="HQIV QComp QAOA chemistry pipeline")
    parser.add_argument("molecule", nargs="?", default="H2O", help="GMTKN55 molecule name")
    parser.add_argument("--list", action="store_true", help="List available molecules")
    parser.add_argument("--p", type=int, default=2, help="QAOA layers")
    parser.add_argument("--bits", type=int, default=2, help="Bits per bond length DOF")
    parser.add_argument("--angle-bits", type=int, default=2, help="Bits for centre angle DOF")
    parser.add_argument(
        "--method",
        choices=("all", "reference", "brute", "qaoa"),
        default="all",
    )
    parser.add_argument("--json-out", type=Path, default=None)
    args = parser.parse_args()

    if args.list:
        print("GMTKN55 molecules:", ", ".join(b.name for b in GMTKN55_SUITE))
        return

    spec = spec_from_molecule(
        args.molecule,
        bond_length_bits=args.bits,
        angle_bits=args.angle_bits,
    )
    methods: list[str] = []
    if args.method in ("all", "reference"):
        methods.append("reference_geometry")
    if args.method in ("all", "brute"):
        methods.append("brute_force")
    if args.method in ("all", "qaoa"):
        methods.append("classical_qaoa")

    payload = build_payload(spec, p_layers=args.p, methods=tuple(methods))

    for key, run in payload["runs"].items():
        print()
        print(f"--- {key} ---")
        print_report(run)

    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
        print()
        print(f"Wrote {args.json_out}")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
HQIV bond-state network model.

Binding energy lives in the same place as proton (or any hadron) mass:

  • **Inside curvature** — trapped volume × Planck budget at each fragment shell,
    with a joint readout when the molecule closes (same spine as hadron mass).
  • **Outside curvature** — contact bonding via `G_eff(θ) = (θ/θ₀)^α` on bond contact
    points (α = 3/5 from the lattice; θ in the Compton IR window).

The network layer still carries separated traces, edge contact closures, and optional
graph hyperclosure; the eV readout is the projection of inside/outside surplus, not
a scalar shortcut.

Lean: `Hqiv.QuantumChemistry.BondStateNetwork`, `CurvatureBondContact`.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Iterable

import hqiv_curvature_bond_state as cbs
import hqiv_nuclear_curvature_binding as ncb
from fragment_aware_bonded_horizon import BOHR_RADIUS_ANGSTROM, BondGeometry, FragmentConfig
from nuclear_torus_casimir_float import EV_PER_LAMBDA_UNIT, associator_perturbation

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_JSON = ROOT / "data" / "bond_state_network_chart.json"


@dataclass(frozen=True)
class MoleculeCase:
    name: str
    fragments: tuple[FragmentConfig, ...]
    bonds: tuple[BondGeometry, ...]
    observable: str
    reference_ev: float
    reference_source: str


CASES: tuple[MoleculeCase, ...] = (
    MoleculeCase(
        "H2",
        (FragmentConfig("H", 1, 1), FragmentConfig("H", 1, 1)),
        (BondGeometry(0, 1, 0.7414),),
        "dissociation",
        4.478,
        "NIST / W4-17",
    ),
    MoleculeCase(
        "LiH",
        (FragmentConfig("Li", 3, 3), FragmentConfig("H", 1, 1)),
        (BondGeometry(0, 1, 1.5956),),
        "dissociation",
        2.515,
        "W4-17/GMTKN55",
    ),
    MoleculeCase(
        "HF",
        (FragmentConfig("F", 9, 9), FragmentConfig("H", 1, 1)),
        (BondGeometry(0, 1, 0.9168),),
        "dissociation",
        5.87,
        "W4-17/GMTKN55",
    ),
    MoleculeCase(
        "H2O",
        (
            FragmentConfig("O", 8, 8),
            FragmentConfig("H", 1, 1),
            FragmentConfig("H", 1, 1),
        ),
        (BondGeometry(0, 1, 0.9572), BondGeometry(0, 2, 0.9572)),
        "atomization",
        9.51,
        "W4-17/GMTKN55",
    ),
    MoleculeCase(
        "CH4",
        (FragmentConfig("C", 6, 6),) + tuple(FragmentConfig("H", 1, 1) for _ in range(4)),
        tuple(BondGeometry(0, i + 1, 1.09) for i in range(4)),
        "atomization",
        17.0,
        "W4-17/GMTKN55",
    ),
    MoleculeCase(
        "NH3",
        (FragmentConfig("N", 7, 7),) + tuple(FragmentConfig("H", 1, 1) for _ in range(3)),
        tuple(BondGeometry(0, i + 1, 1.012) for i in range(3)),
        "atomization",
        10.07,
        "W4-17/GMTKN55",
    ),
    MoleculeCase(
        "T2",
        (FragmentConfig("T", 1, 3), FragmentConfig("T", 1, 3)),
        (BondGeometry(0, 1, 0.7414),),
        "dissociation",
        4.478,
        "same geometry as H2; tritium mass in fragment shell only",
    ),
    MoleculeCase(
        "T2O",
        (
            FragmentConfig("O", 8, 8),
            FragmentConfig("T", 1, 3),
            FragmentConfig("T", 1, 3),
        ),
        (BondGeometry(0, 1, 0.9572), BondGeometry(0, 2, 0.9572)),
        "atomization",
        9.51,
        "same geometry as H2O; tritium replaces protium",
    ),
)

MOLECULAR_HOSTS: dict[str, MoleculeCase] = {case.name: case for case in CASES}

ELECTRON_MASS_MEV = 0.5109989461
PROTON_MASS_MEV = 938.272


@dataclass(frozen=True)
class Trace8:
    values: tuple[float, ...]

    def __post_init__(self) -> None:
        if len(self.values) != 8:
            raise ValueError("Trace8 must have exactly 8 carrier slots")

    def __add__(self, other: "Trace8") -> "Trace8":
        return Trace8(tuple(a + b for a, b in zip(self.values, other.values)))

    def l1(self) -> float:
        return sum(abs(x) for x in self.values)

    @staticmethod
    def zero() -> "Trace8":
        return Trace8((0.0,) * 8)


@dataclass(frozen=True)
class FragmentState:
    index: int
    label: str
    z_nuclear: int
    electrons: int
    mass_number: int
    nuclear_shell: int
    valence_s_shell: int
    valence_p_shell: int | None
    inside_binding_ev: float
    inside_ratio: float
    trace: Trace8


@dataclass(frozen=True)
class BondClosureState:
    frag_i: int
    frag_j: int
    distance_angstrom: float
    contact_theta_rad: float
    geff_theta_coupling: float
    outside_contact_dimless: float
    outside_contact_ev: float
    geometry_weight: float
    trace: Trace8


@dataclass(frozen=True)
class NetworkEvaluation:
    name: str
    observable: str
    predicted_ev: float
    reference_ev: float
    error_pct: float
    inside_surplus_ev: float
    outside_contact_ev: float
    hyperclosure_ev: float
    separated_inside_ev: float
    joint_inside_ev: float
    fragments: list[dict[str, Any]]
    bonds: list[dict[str, Any]]
    hyperclosure_trace_l1: float
    notes: str


def _normalize(v: Iterable[float]) -> tuple[float, ...]:
    vals = tuple(float(x) for x in v)
    norm = math.sqrt(sum(x * x for x in vals))
    if norm <= 0.0:
        out = [0.0] * len(vals)
        out[0] = 1.0
        return tuple(out)
    return tuple(x / norm for x in vals)


def _distance_weight(distance_angstrom: float) -> float:
    lattice_distance = distance_angstrom / BOHR_RADIUS_ANGSTROM
    return 1.0 / (1.0 + lattice_distance)


def _occupation_trace(electrons: int, *, shell: int, z_nuclear: int) -> Trace8:
    """Carrier trace for network bookkeeping; inside binding is separate."""
    vals = [0.0] * 8
    occ = list(range(max(electrons, 0)))
    inside_ratio = cbs.meta_horizon_inside_ratio(shell)
    for ell in occ:
        carrier = ell % 8
        vals[carrier] += (ell + 1.0) * inside_ratio * (1.0 + math.log1p(max(z_nuclear, 1)) / 8.0)
    if not occ:
        vals[0] = inside_ratio
    return Trace8(tuple(vals))


def fragment_state(index: int, frag: FragmentConfig) -> FragmentState:
    mass_number = ncb.stable_mass_number(frag.z_nuclear, frag.electrons)
    nuclear_shell = ncb.nucleus_curvature_shell(mass_number)
    valence_s, valence_p = ncb.valence_shells_for_nucleus(frag.z_nuclear, nuclear_shell)
    inside_ratio = cbs.meta_horizon_inside_ratio(nuclear_shell)
    inside_ev = cbs.inside_binding_ev_anchor(nuclear_shell)
    trace = _occupation_trace(frag.electrons, shell=nuclear_shell, z_nuclear=frag.z_nuclear)
    return FragmentState(
        index=index,
        label=frag.label,
        z_nuclear=frag.z_nuclear,
        electrons=frag.electrons,
        mass_number=mass_number,
        nuclear_shell=nuclear_shell,
        valence_s_shell=valence_s,
        valence_p_shell=valence_p,
        inside_binding_ev=inside_ev,
        inside_ratio=inside_ratio,
        trace=trace,
    )


def _carrier_overlap(a: Trace8, b: Trace8) -> float:
    va = _normalize(a.values)
    vb = _normalize(b.values)
    return max(0.0, sum(x * y for x, y in zip(va, vb)))


def _shell_contact(a: FragmentState, b: FragmentState) -> float:
    ds = abs(a.valence_s_shell - b.valence_s_shell)
    dp = 0
    if a.valence_p_shell is not None and b.valence_p_shell is not None:
        dp = abs(a.valence_p_shell - b.valence_p_shell)
    return 1.0 / (1.0 + float(ds + dp))


def bond_closure_state(fragments: tuple[FragmentState, ...], bond: BondGeometry) -> BondClosureState:
    a = fragments[bond.frag_i]
    b = fragments[bond.frag_j]
    dw = _distance_weight(bond.distance_angstrom)
    overlap = _carrier_overlap(a.trace, b.trace)
    contact = _shell_contact(a, b)
    triplet = cbs.contact_shell_triplet(a.valence_s_shell, b.valence_s_shell)
    theta = cbs.contact_phase_theta_rad(triplet)
    geff_coupling = cbs.outside_contact_coupling(theta)
    m_contact = max(a.nuclear_shell, b.nuclear_shell)
    shell_angle = (
        float(a.valence_s_shell + 1),
        float(b.valence_s_shell + 1),
        float(abs(a.valence_s_shell - b.valence_s_shell) + 1),
    )
    angles = tuple((x % 8.0) / 8.0 * 2.0 * math.pi for x in shell_angle)
    associator = sum(associator_perturbation(ell, angles) for ell in (0, 1, 2)) / 3.0
    geometry = dw * (0.5 + 0.5 * overlap) * contact * (1.0 + associator / 8.0)
    outside_dimless = cbs.outside_contact_dimless(theta, m_contact=m_contact, geometry_weight=geometry)
    outside_ev = outside_dimless * EV_PER_LAMBDA_UNIT
    trace = Trace8(
        tuple(
            outside_dimless * math.sqrt(max(ai, 0.0) * max(bi, 0.0))
            for ai, bi in zip(a.trace.values, b.trace.values)
        )
    )
    return BondClosureState(
        frag_i=bond.frag_i,
        frag_j=bond.frag_j,
        distance_angstrom=bond.distance_angstrom,
        contact_theta_rad=theta,
        geff_theta_coupling=geff_coupling,
        outside_contact_dimless=outside_dimless,
        outside_contact_ev=outside_ev,
        geometry_weight=geometry,
        trace=trace,
    )


def hyperclosure_trace(bonds: tuple[BondClosureState, ...]) -> Trace8:
    if len(bonds) < 2:
        return Trace8.zero()
    vals = []
    graph_factor = 1.0 / math.sqrt(float(len(bonds)))
    for slot in range(8):
        active = [max(b.trace.values[slot], 0.0) for b in bonds if b.trace.values[slot] > 0.0]
        if not active:
            vals.append(0.0)
            continue
        vals.append(graph_factor * math.prod(active) ** (1.0 / len(active)))
    return Trace8(tuple(vals))


def evaluate_case(case: MoleculeCase) -> NetworkEvaluation:
    fragments = tuple(fragment_state(i, frag) for i, frag in enumerate(case.fragments))
    bonds = tuple(bond_closure_state(fragments, bond) for bond in case.bonds)
    hyper_trace = hyperclosure_trace(bonds)

    mass_numbers = tuple(f.mass_number for f in fragments)
    fragment_shells = tuple(f.nuclear_shell for f in fragments)
    joint_shell = cbs.joint_readout_shell(mass_numbers)

    separated_inside = sum(f.inside_binding_ev for f in fragments)
    joint_inside = cbs.inside_binding_ev_anchor(joint_shell)
    inside_surplus = joint_inside - separated_inside

    outside_total = sum(b.outside_contact_ev for b in bonds)
    hyperclosure_ev = hyper_trace.l1() * EV_PER_LAMBDA_UNIT / max(len(bonds), 1)

    # Positive chemistry binding: outside contact lowers energy; inside joint may shift.
    predicted_ev = -(inside_surplus) + outside_total + hyperclosure_ev
    error_pct = (predicted_ev - case.reference_ev) / case.reference_ev * 100.0
    return NetworkEvaluation(
        name=case.name,
        observable=case.observable,
        predicted_ev=predicted_ev,
        reference_ev=case.reference_ev,
        error_pct=error_pct,
        inside_surplus_ev=inside_surplus,
        outside_contact_ev=outside_total,
        hyperclosure_ev=hyperclosure_ev,
        separated_inside_ev=separated_inside,
        joint_inside_ev=joint_inside,
        fragments=[
            {k: v for k, v in asdict(f).items() if k != "trace"} | {"trace": f.trace.values}
            for f in fragments
        ],
        bonds=[asdict(b) | {"trace": b.trace.values} for b in bonds],
        hyperclosure_trace_l1=hyper_trace.l1(),
        notes=(
            "inside curvature surplus (hadron spine) + outside G_eff(θ) contact bonding; "
            f"joint shell m={joint_shell}"
        ),
    )


def nucleus_outside_contact_dimless_share(
    case: MoleculeCase,
    *,
    nucleus_label: str,
) -> tuple[float, int]:
    """
    Sum of bond ``outside_contact_dimless`` at contacts touching ``nucleus_label``.

    Returns (mean share per matching fragment, nuclear readout shell).
    """
    fragments = tuple(fragment_state(i, frag) for i, frag in enumerate(case.fragments))
    bonds = tuple(bond_closure_state(fragments, bond) for bond in case.bonds)
    shares: list[float] = []
    shells: list[int] = []
    for i, frag in enumerate(case.fragments):
        if frag.label != nucleus_label:
            continue
        share = 0.0
        for bond in bonds:
            if bond.frag_i == i or bond.frag_j == i:
                share += bond.outside_contact_dimless
        shares.append(share)
        shells.append(fragments[i].nuclear_shell)
    if not shares:
        raise ValueError(f"no fragment with label {nucleus_label!r} in {case.name}")
    return sum(shares) / len(shares), shells[0]


def molecular_binding_phi_epsilon(
    outside_dimless_share: float,
    *,
    m_nuclear: int,
    m_e_mev: float = ELECTRON_MASS_MEV,
    m_p_mev: float = PROTON_MASS_MEV,
) -> float:
    """
    Weak-field outside slot from molecular bond closure inherited by one nucleus.

    Normalises the contact dimless surplus by lock-in shell depth and lepton/proton
    scale (same monogamy γ as the gravity ``G_eff`` fold):
      ε_mol = γ · share · (m_e / M_p) / (m_nuc + 1).
    """
    if outside_dimless_share <= 0.0 or m_nuclear < 0:
        return 0.0
    import hqiv_lean_physics_primitives as lean

    return (
        lean.GAMMA
        * outside_dimless_share
        * (m_e_mev / m_p_mev)
        / float(m_nuclear + 1)
    )


def molecular_host_phi_epsilon(
    host: str,
    *,
    nucleus_label: str | None = None,
) -> float:
    """Outside ε from a named molecular host (``T2``, ``T2O``, ``H2``, …)."""
    case = MOLECULAR_HOSTS.get(host)
    if case is None:
        raise ValueError(f"unknown molecular host {host!r}")
    label = nucleus_label or case.fragments[0].label
    share, m_nuc = nucleus_outside_contact_dimless_share(case, nucleus_label=label)
    return molecular_binding_phi_epsilon(share, m_nuclear=m_nuc)


def molecular_host_readout(host: str, *, nucleus_label: str | None = None) -> dict[str, float]:
    case = MOLECULAR_HOSTS[host]
    label = nucleus_label or case.fragments[0].label
    share, m_nuc = nucleus_outside_contact_dimless_share(case, nucleus_label=label)
    eps = molecular_binding_phi_epsilon(share, m_nuclear=m_nuc)
    import hqiv_nuclear_outside_temperature_dynamics as notd

    return {
        "host": host,
        "nucleus_label": label,
        "outside_dimless_share": share,
        "m_nuclear_shell": float(m_nuc),
        "phi_epsilon": eps,
        "geff_modulator": notd.outside_gravity_geff_modulator(eps),
        "geff_ppm": (notd.outside_gravity_geff_modulator(eps) - 1.0) * 1.0e6,
    }


def build_payload(cases: tuple[MoleculeCase, ...] = CASES) -> dict[str, Any]:
    rows = [evaluate_case(case) for case in cases]
    abs_err = [abs(r.error_pct) for r in rows]
    return {
        "source": "scripts/hqiv_bond_state_network.py",
        "lean_module": "Hqiv.QuantumChemistry.BondStateNetwork",
        "parameter_policy": "no_fitted_coefficients",
        "formula": (
            "E_bind = −(inside_joint − inside_separated) + Σ G_eff(θ) contact "
            "+ hyperclosure projection"
        ),
        "physics": {
            "inside": "metaHorizonTrappedInsideRatio × nucleon composite trace (hadron spine)",
            "outside": "G_eff(θ/θ₀) = (θ/θ₀)^α at bond contact points, α=3/5",
            "theta_window": "Compton IR phaseTheta = π/2",
        },
        "cases": [asdict(row) for row in rows],
        "summary": {
            "count": len(rows),
            "mean_abs_error_pct": sum(abs_err) / len(abs_err),
            "max_abs_error_pct": max(abs_err),
        },
    }


def print_report(payload: dict[str, Any]) -> None:
    print("HQIV bond-state network chart (inside/outside curvature)")
    print("=" * 72)
    print(payload["formula"])
    print()
    print(
        f"{'name':<6} {'obs':<13} {'pred/eV':>10} {'ref/eV':>10} {'err%':>9} "
        f"{'inside':>9} {'outside':>9}"
    )
    for row in payload["cases"]:
        print(
            f"{row['name']:<6} {row['observable']:<13} {row['predicted_ev']:10.3f} "
            f"{row['reference_ev']:10.3f} {row['error_pct']:+9.2f} "
            f"{row['inside_surplus_ev']:9.3f} {row['outside_contact_ev']:9.3f}"
        )
    s = payload["summary"]
    print()
    print(f"Summary: n={s['count']} mean|err|={s['mean_abs_error_pct']:.2f}% max|err|={s['max_abs_error_pct']:.2f}%")


def main() -> None:
    parser = argparse.ArgumentParser(description="HQIV bond-state network chart")
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()

    payload = build_payload()
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(payload, indent=2) + "\n")
    print_report(payload)
    print()
    print(f"Wrote {args.json_out}")


if __name__ == "__main__":
    main()

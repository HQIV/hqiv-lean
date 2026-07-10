#!/usr/bin/env python3
"""
Discrete saddle barrier and defect formation energy readouts.

Lean:
  ``Hqiv.Physics.HomogeneousCurvatureSecondOrder``
    — defectFormationEnergyEv, contactEdgeGateEv, discreteSaddleBarrierEv,
      harmonicSaddleGateEv
  ``Hqiv.QuantumChemistry.CoupledRelaxation``
    — barrierTransmissionFromGate, activationRateFromSaddle,
      discreteSaddleFromContacts
  ``Hqiv.QuantumChemistry.CarbonAllotropeFeedback``
    — graphene_defectFormationEnergyEv (= E_bind / 20)

Same matrix spine as force/Hessian: coordination excess δ feeds
localCurvatureDefectExcess = γ·(4/8)·max(δ,0); formation energy and edge
gates are E_bind × that excess; the discrete saddle is the path maximum.

No fitted Arrhenius prefactor; NIST / handbook barriers are quarantine only.

Run:
  PYTHONPATH=.:scripts python3 scripts/hqiv_discrete_saddle_defect_readout.py
  PYTHONPATH=.:scripts python3 scripts/hqiv_discrete_saddle_defect_readout.py \\
    --json-out data/discrete_saddle_defect_audit.json
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Sequence

_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

import hqiv_carbon_feedback_tease as cft
import hqiv_chemistry_coupled_readout as ccr
import hqiv_contact_force_readout as cfr
import hqiv_homogeneous_curvature_feedback as hcf
import hqiv_ionic_bond_network as ibn
import hqiv_lean_physics_primitives as lean
import hqiv_metallic_bond_network as mbn
import hqiv_preferred_axis_dress as pad
from hqiv_lab.crystal_geometry import covalent_network_em_packing_dress

STRONG = lean.STRONG_CHANNEL_FRACTION
GAMMA = lean.GAMMA
DEFAULT_JSON = _REPO_ROOT / "data" / "discrete_saddle_defect_audit.json"

# Quarantine-only handbook barrier / vacancy scales (eV) — never inputs.
NIST_COMPARISON: dict[str, dict[str, float]] = {
    "NaCl": {"vacancy_formation_eV": 2.0},
    "Si": {"vacancy_formation_eV": 3.6},
    "Cu": {"vacancy_formation_eV": 1.3},
    "graphene": {"Stone_Wales_barrier_eV": 5.0},
}


def defect_formation_energy_ev(binding_ev: float, delta_coord: float) -> float:
    """Lean ``defectFormationEnergyEv``."""
    return float(binding_ev) * hcf.local_curvature_defect_excess(delta_coord)


def contact_edge_gate_ev(binding_ev: float, delta_coord: float) -> float:
    """Lean ``contactEdgeGateEv``."""
    return defect_formation_energy_ev(binding_ev, delta_coord)


def discrete_saddle_barrier_ev(edge_gates: Sequence[float]) -> float:
    """Lean ``discreteSaddleBarrierEv``: max along path, empty → 0."""
    acc = 0.0
    for g in edge_gates:
        acc = max(acc, float(g))
    return acc


def harmonic_saddle_gate_ev(binding_ev: float) -> float:
    """Lean ``harmonicSaddleGateEv``: strong² · D (F²/2k on Morse backbone)."""
    return (STRONG ** 2) * float(binding_ev)


def discrete_saddle_from_contacts(
    bindings: Sequence[float], excesses: Sequence[float]
) -> float:
    """Lean ``discreteSaddleFromContacts``."""
    n = min(len(bindings), len(excesses))
    gates = [contact_edge_gate_ev(bindings[i], excesses[i]) for i in range(n)]
    return discrete_saddle_barrier_ev(gates)


def coordination_excess_vs_reference(k: float, k_ref: float) -> float:
    """Lean ``coordinationExcessVsReference``."""
    return abs(float(k) - float(k_ref)) / max(float(k_ref), 1.0)


def vacancy_excess(coordination: float) -> float:
    """Single-site vacancy: remove one neighbour from CN reference → δ = 1/CN."""
    return coordination_excess_vs_reference(max(coordination - 1.0, 0.0), coordination)


def vacancy_formation_energy_ev(
    binding_ev: float, delta_coord: float, n_coord: float
) -> float:
    """
    Lean ``vacancyFormationEnergyEv``:
    ``E_vac = E_def / max(CN, 1)`` (= ``E_bind · γ · (4/8) / CN²`` for δ=1/CN).

    Cooperative lattice share of the single-site defect across the coordination shell.
    """
    return defect_formation_energy_ev(binding_ev, delta_coord) / max(float(n_coord), 1.0)


def grain_boundary_formation_energy_ev(
    binding_ev: float, delta_coord: float, n_coord: float
) -> float:
    """
    Lean ``grainBoundaryFormationEnergyEv``:
    ``E_gb = γ · E_vac`` (= ``E_bind · γ² · (4/8) / CN²`` for δ=1/CN).

    Interface share of the cooperative vacancy across a misoriented contact.
    """
    return lean.GAMMA * vacancy_formation_energy_ev(binding_ev, delta_coord, n_coord)


def crystal_defect_row(
    *,
    name: str,
    crystal_kind: str,
    binding_ev: float,
    contact_dist_ang: float,
    n_coord: float,
    z_i: int,
    z_j: int,
) -> dict[str, Any]:
    """Vacancy-scale defect + Morse force/Hessian + activation softener."""
    delta = vacancy_excess(n_coord)
    e_def = defect_formation_energy_ev(binding_ev, delta)
    e_vac = vacancy_formation_energy_ev(binding_ev, delta, n_coord)
    e_gb = grain_boundary_formation_energy_ev(binding_ev, delta, n_coord)
    # One-edge path: cooperative vacancy as the saddle gate.
    barrier = discrete_saddle_barrier_ev([e_vac])
    # Two-edge rearrangement tease: break + reform with half excess on reform.
    path_barrier = discrete_saddle_from_contacts(
        [binding_ev, binding_ev], [delta, 0.5 * delta]
    )
    # Cluster-path average: n_coord equal edge gates at vacancy scale.
    cluster_gates = [e_vac] * max(int(n_coord), 1)
    cluster_barrier = discrete_saddle_barrier_ev(cluster_gates)
    harm = harmonic_saddle_gate_ev(binding_ev)
    T = ccr.barrier_transmission_from_gate(barrier, binding_ev)
    rate = ccr.activation_rate_from_saddle(1.0, barrier, binding_ev)
    force = cfr.contact_force_morse_backbone(binding_ev, contact_dist_ang)
    hess = cfr.contact_hessian_n_m(binding_ev, contact_dist_ang)
    row: dict[str, Any] = {
        "name": name,
        "crystal_kind": crystal_kind,
        "binding_ev_per_contact": binding_ev,
        "contact_dist_angstrom": contact_dist_ang,
        "coordination": n_coord,
        "z_i": z_i,
        "z_j": z_j,
        "vacancy_coordination_excess": delta,
        "defect_formation_energy_eV": e_def,
        "vacancy_formation_energy_eV": e_vac,
        "grain_boundary_formation_energy_eV": e_gb,
        "discrete_saddle_barrier_eV": barrier,
        "two_edge_path_barrier_eV": path_barrier,
        "cluster_path_barrier_eV": cluster_barrier,
        "harmonic_saddle_gate_eV": harm,
        "barrier_transmission": T,
        "activation_rate_unit_contact": rate,
        "contact_force_N": force,
        "contact_hessian_N_m": hess,
        "local_curvature_defect_excess": hcf.local_curvature_defect_excess(delta),
        "formula": (
            "E_def = E_bind · γ · (4/8) · δ;  "
            "E_vac = E_def / CN;  "
            "E_gb = γ · E_vac"
        ),
        "scaling_mode": "cooperative_vacancy_over_n_coord",
    }
    ref = NIST_COMPARISON.get(name)
    if ref is not None:
        row["nist_comparison_quarantine"] = dict(ref)
        vac = ref.get("vacancy_formation_eV")
        if vac and vac > 0:
            row["defect_vs_nist_ratio"] = e_def / vac
            row["vacancy_vs_nist_ratio"] = e_vac / vac
    return row


def carbon_fork_row() -> dict[str, Any]:
    """Graphene vs diamond defect formation (proved E_bind/20)."""
    # Characteristic C–C depth from allotrope geometry (no NIST pin).
    dressed = covalent_network_em_packing_dress(6, coordination=4, em_feedback=True)
    r = float(dressed["bond_length_angstrom"])
    bind = cfr.covalent_network_binding_ev(6, r, coordination=4)
    delta_g = cft.coordination_excess(cft.GRAPHENE)
    delta_d = cft.coordination_excess(cft.DIAMOND)
    e_g = defect_formation_energy_ev(bind, delta_g)
    e_d = defect_formation_energy_ev(bind, delta_d)
    return {
        "name": "graphene_vs_diamond",
        "crystal_kind": "covalent_network_fork",
        "binding_ev_per_contact": bind,
        "graphene_coordination_excess": delta_g,
        "diamond_coordination_excess": delta_d,
        "graphene_defect_formation_eV": e_g,
        "diamond_defect_formation_eV": e_d,
        "graphene_over_bind_ratio": e_g / bind if bind else None,
        "proved_ratio": 1.0 / 20.0,
        "ratio_matches_lean": abs(e_g / bind - 0.05) < 1e-12 if bind else False,
        "discrete_saddle_graphene_eV": discrete_saddle_barrier_ev([e_g]),
        "barrier_transmission_graphene": ccr.barrier_transmission_from_gate(e_g, bind),
        "nist_comparison_quarantine": NIST_COMPARISON.get("graphene"),
    }


def build_audit() -> dict[str, Any]:
    salts = [
        (ibn.NACL_SALT, ibn.ionic_lattice_binding_ev_per_contact),
        (ibn.LIF_SALT, ibn.ionic_lattice_binding_ev_per_contact),
    ]
    crystal_rows: list[dict[str, Any]] = []
    for salt, _ in salts:
        bind = ibn.ionic_lattice_binding_ev_per_contact(
            salt.cation,
            salt.anion,
            distance_angstrom=salt.lattice_bond_angstrom,
        )
        crystal_rows.append(
            crystal_defect_row(
                name=salt.name,
                crystal_kind="ionic",
                binding_ev=bind,
                contact_dist_ang=salt.lattice_bond_angstrom,
                n_coord=float(salt.coordination),
                z_i=salt.cation.z_nuclear,
                z_j=salt.anion.z_nuclear,
            )
        )

    for lattice in (mbn.CU_LATTICE, mbn.AL_LATTICE):
        bind = mbn.metallic_lattice_binding_ev_per_contact(
            lattice.metal,
            distance_angstrom=lattice.nearest_neighbor_angstrom,
            coordination=lattice.coordination,
        )
        z = lattice.metal.z_nuclear
        crystal_rows.append(
            crystal_defect_row(
                name=lattice.name,
                crystal_kind="metallic",
                binding_ev=bind,
                contact_dist_ang=lattice.nearest_neighbor_angstrom,
                n_coord=float(lattice.coordination),
                z_i=z,
                z_j=z,
            )
        )

    for z, name in ((14, "Si"), (32, "Ge")):
        dressed = covalent_network_em_packing_dress(z, coordination=4, em_feedback=True)
        r = float(dressed["bond_length_angstrom"])
        bind = cfr.covalent_network_binding_ev(z, r, coordination=4)
        crystal_rows.append(
            crystal_defect_row(
                name=name,
                crystal_kind="covalent_network",
                binding_ev=bind,
                contact_dist_ang=r,
                n_coord=4.0,
                z_i=z,
                z_j=z,
            )
        )

    fork = carbon_fork_row()

    # Vacancy identity: δ=1/CN → E_vac = E_bind · γ · (4/8) / CN²
    _e_vac_id = vacancy_formation_energy_ev(6.0, 1.0 / 6.0, 6.0)
    _e_vac_expect = 6.0 * lean.GAMMA * STRONG / 36.0
    _e_gb_id = grain_boundary_formation_energy_ev(6.0, 1.0 / 6.0, 6.0)
    identity = {
        "defect_zero_at_delta0": defect_formation_energy_ev(5.0, 0.0) == 0.0,
        "vacancy_zero_at_delta0": vacancy_formation_energy_ev(5.0, 0.0, 6.0) == 0.0,
        "vacancy_is_defect_over_cn": abs(_e_vac_id - _e_vac_expect) < 1e-12,
        "grain_boundary_is_gamma_vacancy": abs(_e_gb_id - lean.GAMMA * _e_vac_id)
        < 1e-12,
        "saddle_nil": discrete_saddle_barrier_ev([]) == 0.0,
        "saddle_nonneg": discrete_saddle_barrier_ev([-1.0, 2.0, 0.5]) == 2.0,
        "transmission_open": abs(ccr.barrier_transmission_from_gate(0.0, 1.0) - 1.0)
        < 1e-15,
        "activation_open": abs(ccr.activation_rate_from_saddle(3.0, 0.0, 1.0) - 3.0)
        < 1e-15,
        "graphene_ratio_1_20": fork["ratio_matches_lean"],
        "harmonic_gate_strong_sq": abs(
            harmonic_saddle_gate_ev(4.0) - (STRONG ** 2) * 4.0
        )
        < 1e-15,
    }

    return {
        "source": "scripts/hqiv_discrete_saddle_defect_readout.py",
        "lean_modules": [
            "Hqiv.Physics.HomogeneousCurvatureSecondOrder",
            "Hqiv.QuantumChemistry.CoupledRelaxation",
            "Hqiv.QuantumChemistry.CarbonAllotropeFeedback",
        ],
        "formula": {
            "defect_formation_eV": "E_bind · γ · (4/8) · max(δ, 0)",
            "vacancy_formation_eV": "E_def / CN  (= E_bind · γ · (4/8) / CN² for δ=1/CN)",
            "grain_boundary_eV": "γ · E_vac  (= E_bind · γ² · (4/8) / CN² for δ=1/CN)",
            "edge_gate_eV": "vacancy formation on that contact (cooperative)",
            "discrete_saddle_eV": "max_{e ∈ path} edge_gate(e)",
            "cluster_path_eV": "max of n_coord equal vacancy gates",
            "harmonic_saddle_eV": "strong² · D  (= F²/(2k) on Morse backbone)",
            "barrier_transmission": "1 / (1 + B / max(strong · D, ε))",
            "activation_rate": "contact_rate · transmission",
        },
        "identity_checks": identity,
        "all_identity_checks_pass": all(identity.values()),
        "crystal_rows": crystal_rows,
        "carbon_fork": fork,
        "comparison_policy": "NIST/handbook vacancy and Stone–Wales barriers are quarantine only",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    parser.add_argument(
        "--gmtkn-json-out",
        type=Path,
        default=_REPO_ROOT / "data" / "gmtkn_activation_audit.json",
        help="Also write GMTKN bond-rearrangement activation audit",
    )
    parser.add_argument(
        "--skip-gmtkn",
        action="store_true",
        help="Skip GMTKN activation subset (crystal/defect only)",
    )
    args = parser.parse_args()
    payload = build_audit()
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(payload, indent=2) + "\n")
    print(f"wrote {args.json_out}")
    print(f"identity_checks: {payload['all_identity_checks_pass']}")
    for row in payload["crystal_rows"]:
        vac = row.get("vacancy_formation_energy_eV")
        gb = row.get("grain_boundary_formation_energy_eV")
        vac_s = f"  E_vac={vac:.4f}" if vac is not None else ""
        gb_s = f"  E_gb={gb:.4f}" if gb is not None else ""
        print(
            f"  {row['name']:6} δ={row['vacancy_coordination_excess']:.3f}  "
            f"E_def={row['defect_formation_energy_eV']:.4f} eV"
            f"{vac_s}{gb_s} eV  "
            f"saddle={row['discrete_saddle_barrier_eV']:.4f} eV  "
            f"T={row['barrier_transmission']:.4f}"
        )
    fork = payload["carbon_fork"]
    print(
        f"  C-fork  graphene E_def={fork['graphene_defect_formation_eV']:.4f} eV  "
        f"(E/20={fork['binding_ev_per_contact']/20:.4f})  "
        f"match={fork['ratio_matches_lean']}"
    )
    if not args.skip_gmtkn:
        import hqiv_bond_rearrangement_path as brp

        gmtkn = brp.build_gmtkn_activation_audit()
        args.gmtkn_json_out.parent.mkdir(parents=True, exist_ok=True)
        args.gmtkn_json_out.write_text(json.dumps(gmtkn, indent=2) + "\n")
        print(f"wrote {args.gmtkn_json_out}")
        print(f"gmtkn_identity_checks: {gmtkn['all_identity_checks_pass']}")
        for row in gmtkn["rows"]:
            if "error" in row:
                print(f"  GMTKN {row['molecule']}: ERROR {row['error']}")
                continue
            print(
                f"  GMTKN {row['molecule']:4} δ={row['delta_coord']:.3f}  "
                f"B={row['path_barrier_ev']:.4f} eV  "
                f"T={row['barrier_transmission']:.4f}  "
                f"kind={row['contact_kind']}"
            )


if __name__ == "__main__":
    main()

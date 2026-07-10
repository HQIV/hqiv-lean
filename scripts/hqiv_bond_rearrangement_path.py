#!/usr/bin/env python3
"""
Bond rearrangement paths on CurvatureContactNetwork.

Lean: ``Hqiv.QuantumChemistry.BondRearrangementPath``

A discrete dissociation / atomization path is a finite sequence of contact-edge
gates.  Each step carries binding depth D and coordination excess δ from a
break / reform / vacancy stress; the path barrier is max(edge gates).

No continuum TS search; no fitted Arrhenius prefactor.  GMTKN / W4-17 reference
energies are quarantine only.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Any, Sequence

import hqiv_chemistry_coupled_readout as ccr
import hqiv_curvature_contact_network as ccn
import hqiv_discrete_saddle_defect_readout as dsd
import hqiv_dynamic_binding_chart as dbc


class RearrangementKind(str, Enum):
    """Lean ``RearrangementKind``."""

    BREAK = "break"
    REFORM = "reform"
    VACANCY = "vacancy"


@dataclass(frozen=True)
class BondRearrangementStep:
    """Lean ``BondRearrangementStep``."""

    binding_ev: float
    delta_coord: float
    kind: RearrangementKind = RearrangementKind.BREAK
    edge_index: int = 0
    node_i: int | None = None
    node_j: int | None = None
    contact_kind: str | None = None
    distance_angstrom: float | None = None

    def gate_ev(self) -> float:
        """Lean ``bondRearrangementStepGate``."""
        return dsd.contact_edge_gate_ev(self.binding_ev, self.delta_coord)


@dataclass(frozen=True)
class BondRearrangementPath:
    """Lean ``BondRearrangementPath``."""

    molecule: str
    steps: tuple[BondRearrangementStep, ...]
    label: str = ""

    @property
    def barrier_ev(self) -> float:
        """Lean ``bondRearrangementPathBarrier``."""
        return dsd.discrete_saddle_barrier_ev([s.gate_ev() for s in self.steps])

    def activation_rate(self, contact_rate: float = 1.0, scale_ev: float | None = None) -> float:
        """Lean ``activationRateFromPath``."""
        scale = float(scale_ev) if scale_ev is not None else (
            max((s.binding_ev for s in self.steps), default=1.0)
        )
        return ccr.activation_rate_from_saddle(contact_rate, self.barrier_ev, scale)

    def transmission(self, scale_ev: float | None = None) -> float:
        scale = float(scale_ev) if scale_ev is not None else (
            max((s.binding_ev for s in self.steps), default=1.0)
        )
        return ccr.barrier_transmission_from_gate(self.barrier_ev, scale)


def break_coordination_excess(cn_ref: float) -> float:
    """
    Lean ``breakCoordinationExcess``: ``1 / max(CN, 1)``.

    Same as ``coordination_excess_vs_reference(CN−1, CN)`` / vacancy excess.
    """
    return 1.0 / max(float(cn_ref), 1.0)


def break_edge_delta(cn_i: float, cn_j: float) -> float:
    """Lean ``breakEdgeDelta``: max endpoint excess on a break."""
    return max(break_coordination_excess(cn_i), break_coordination_excess(cn_j))


_BOND_KINDS = frozenset(
    {
        ccn.ContactKind.COVALENT_BOND,
        ccn.ContactKind.IONIC_BOND,
        ccn.ContactKind.METALLIC_BOND,
    }
)


def bonding_contacts(
    network: ccn.CurvatureContactNetwork,
) -> tuple[ccn.NetworkContact, ...]:
    """Covalent / ionic / metallic edges with a partner (rearrangement candidates)."""
    return tuple(
        c
        for c in network.contacts
        if c.kind in _BOND_KINDS and c.j is not None
    )


def bonding_coordination(
    network: ccn.CurvatureContactNetwork,
) -> dict[int, int]:
    """Per-node CN from covalent/ionic/metallic edges only (no steric inflation)."""
    cn: dict[int, int] = {n.index: 0 for n in network.nodes}
    for c in bonding_contacts(network):
        assert c.j is not None
        cn[c.i] = cn.get(c.i, 0) + 1
        cn[c.j] = cn.get(c.j, 0) + 1
    return cn


def per_bond_binding_ev(
    total_binding_ev: float,
    network: ccn.CurvatureContactNetwork,
) -> list[float]:
    """
    Split total molecule binding across bonding contacts by geff×valley weight
    (same pattern as ``hqiv_qcomp_qaoa``).  Equal split when weights unavailable.
    """
    edges = bonding_contacts(network)
    if not edges:
        return []
    weights: list[float] = []
    for c in edges:
        if c.bond_geometry is not None:
            g = c.bond_geometry
            w = max(g.geff_combined * max(g.valley_alignment_weight, 1e-12), 1e-12)
        else:
            w = max(float(c.increment_factor) * max(float(c.weight), 1e-12), 1e-12)
        weights.append(w)
    wsum = sum(weights) or 1.0
    return [float(total_binding_ev) * w / wsum for w in weights]


def single_bond_break_path(
    *,
    molecule: str,
    binding_ev: float,
    delta: float,
    edge_index: int = 0,
    node_i: int | None = None,
    node_j: int | None = None,
    contact_kind: str | None = None,
    distance_angstrom: float | None = None,
    label: str = "",
) -> BondRearrangementPath:
    """Lean ``singleBondBreakPath``."""
    step = BondRearrangementStep(
        binding_ev=binding_ev,
        delta_coord=delta,
        kind=RearrangementKind.BREAK,
        edge_index=edge_index,
        node_i=node_i,
        node_j=node_j,
        contact_kind=contact_kind,
        distance_angstrom=distance_angstrom,
    )
    return BondRearrangementPath(molecule=molecule, steps=(step,), label=label or f"{molecule}:break[{edge_index}]")


def break_path_from_network(
    *,
    molecule: str,
    network: ccn.CurvatureContactNetwork,
    total_binding_ev: float,
    edge_index: int = 0,
    label: str = "",
) -> BondRearrangementPath:
    """
    Build a one-edge break path from a live contact network.

    δ = max(|CN_i−1|/CN_i, |CN_j−1|/CN_j) using intact-molecule coordination.
    D = weight-split per-bond binding (or total for a single edge).
    """
    edges = bonding_contacts(network)
    if not edges:
        raise ValueError(f"{molecule}: no bonding contacts for rearrangement path")
    idx = int(edge_index) % len(edges)
    edge = edges[idx]
    per_bond = per_bond_binding_ev(total_binding_ev, network)
    d_e = per_bond[idx] if idx < len(per_bond) else float(total_binding_ev) / len(edges)
    assert edge.j is not None
    cn_map = bonding_coordination(network)
    cn_i = float(cn_map.get(edge.i, 1))
    cn_j = float(cn_map.get(edge.j, 1))
    delta = break_edge_delta(cn_i, cn_j)
    return single_bond_break_path(
        molecule=molecule,
        binding_ev=d_e,
        delta=delta,
        edge_index=idx,
        node_i=edge.i,
        node_j=edge.j,
        contact_kind=edge.kind.value,
        distance_angstrom=edge.distance_angstrom,
        label=label or f"{molecule}:break[{idx}] {edge.kind.value}",
    )


def break_reform_tease_path(
    *,
    molecule: str,
    network: ccn.CurvatureContactNetwork,
    total_binding_ev: float,
    edge_index: int = 0,
) -> BondRearrangementPath:
    """Two-step path: break then reform at half excess (saddle tease)."""
    break_path = break_path_from_network(
        molecule=molecule,
        network=network,
        total_binding_ev=total_binding_ev,
        edge_index=edge_index,
    )
    br = break_path.steps[0]
    reform = BondRearrangementStep(
        binding_ev=br.binding_ev,
        delta_coord=0.5 * br.delta_coord,
        kind=RearrangementKind.REFORM,
        edge_index=br.edge_index,
        node_i=br.node_i,
        node_j=br.node_j,
        contact_kind=br.contact_kind,
        distance_angstrom=br.distance_angstrom,
    )
    return BondRearrangementPath(
        molecule=molecule,
        steps=(br, reform),
        label=f"{molecule}:break+reform[{br.edge_index}]",
    )


def atomization_ladder_step(
    binding_ev: float, centre_cn0: float, k: int
) -> BondRearrangementStep:
    """Lean ``atomizationLadderStep``: centre CN after k breaks vs terminal CN=1."""
    return BondRearrangementStep(
        binding_ev=float(binding_ev),
        delta_coord=break_edge_delta(float(centre_cn0) - k, 1.0),
        kind=RearrangementKind.BREAK,
        edge_index=k,
    )


def atomization_ladder_path(
    *,
    molecule: str,
    binding_ev_per_step: float,
    centre_cn0: float,
    n_steps: int,
    label: str = "",
) -> BondRearrangementPath:
    """Lean ``atomizationLadderPath``: sequential terminal breaks from a centre."""
    n = max(int(n_steps), 0)
    steps = tuple(
        atomization_ladder_step(binding_ev_per_step, centre_cn0, k) for k in range(n)
    )
    return BondRearrangementPath(
        molecule=molecule,
        steps=steps,
        label=label or f"{molecule}:atomization_ladder[n={n},CN0={centre_cn0:g}]",
    )


def atomization_ladder_from_network(
    *,
    molecule: str,
    network: ccn.CurvatureContactNetwork,
    total_binding_ev: float,
    centre_index: int | None = None,
) -> BondRearrangementPath:
    """
    Full atomization ladder: break every bonding contact at the heaviest centre.

    Per-step D = total_binding / n_bonds (equal split).  Centre CN₀ = bonding
    degree; each step uses remaining centre CN against a terminal (δ → 1).
    """
    edges = bonding_contacts(network)
    if not edges:
        raise ValueError(f"{molecule}: no bonding contacts for atomization ladder")
    cn_map = bonding_coordination(network)
    if centre_index is None:
        # Heaviest node with maximum bonding CN (CH4 → C, H2O → O).
        centre_index = max(
            cn_map.keys(),
            key=lambda i: (
                cn_map[i],
                network.nodes[i].z_nuclear if i < len(network.nodes) else 0,
            ),
        )
    centre_cn0 = float(cn_map.get(centre_index, 1))
    n = len(edges)
    d_step = float(total_binding_ev) / max(n, 1)
    return atomization_ladder_path(
        molecule=molecule,
        binding_ev_per_step=d_step,
        centre_cn0=centre_cn0,
        n_steps=n,
        label=f"{molecule}:atomization_ladder[centre={centre_index},CN0={centre_cn0:g},n={n}]",
    )


def activated_transport_rate_slot(
    contact_rate: float,
    path: BondRearrangementPath,
    scale_ev: float | None = None,
) -> float:
    """
    Lean ``activatedTransportRateSlot`` / ``activationRateFromPath``:
    diffusion-limited contact rate softened by a path barrier.
    """
    return path.activation_rate(contact_rate=contact_rate, scale_ev=scale_ev)


def path_from_benchmark(
    bench: dbc.MoleculeBenchmark,
    *,
    edge_index: int = 0,
    use_nested_wf_geometry: bool = True,
) -> dict[str, Any]:
    """Full GMTKN-style dissociation / partial-atomization path readout."""
    result = dbc.dynamic_binding_for_benchmark(
        bench, use_nested_wf_geometry=use_nested_wf_geometry
    )
    geom_bench = (
        dbc.benchmark_with_nested_wf_geometry(bench)
        if use_nested_wf_geometry
        else bench
    )
    net = ccn.build_network_from_molecule(
        geom_bench.name, geom_bench.fragments, geom_bench.bonds
    )
    path = break_path_from_network(
        molecule=bench.name,
        network=net,
        total_binding_ev=result.binding_ev,
        edge_index=edge_index,
    )
    tease = break_reform_tease_path(
        molecule=bench.name,
        network=net,
        total_binding_ev=result.binding_ev,
        edge_index=edge_index,
    )
    harm = dsd.harmonic_saddle_gate_ev(path.steps[0].binding_ev)
    ladder: dict[str, Any] | None = None
    if bench.name in ("H2O", "CH4", "NH3"):
        lad = atomization_ladder_from_network(
            molecule=bench.name,
            network=net,
            total_binding_ev=result.binding_ev,
        )
        ladder = {
            "label": lad.label,
            "n_steps": len(lad.steps),
            "step_deltas": [s.delta_coord for s in lad.steps],
            "step_gates_ev": [s.gate_ev() for s in lad.steps],
            "path_barrier_ev": lad.barrier_ev,
            "barrier_transmission": lad.transmission(),
            "activation_rate_unit_contact": lad.activation_rate(),
            "activated_vs_bare_contact": activated_transport_rate_slot(1.0, lad),
        }
    return {
        "molecule": bench.name,
        "kind": bench.kind,
        "reference_ev_quarantine": bench.reference_ev,
        "total_binding_ev": result.binding_ev,
        "path_label": path.label,
        "edge_index": path.steps[0].edge_index,
        "contact_kind": path.steps[0].contact_kind,
        "distance_angstrom": path.steps[0].distance_angstrom,
        "node_i": path.steps[0].node_i,
        "node_j": path.steps[0].node_j,
        "binding_ev_edge": path.steps[0].binding_ev,
        "delta_coord": path.steps[0].delta_coord,
        "edge_gate_ev": path.steps[0].gate_ev(),
        "path_barrier_ev": path.barrier_ev,
        "break_reform_barrier_ev": tease.barrier_ev,
        "harmonic_saddle_gate_ev": harm,
        "barrier_transmission": path.transmission(),
        "activation_rate_unit_contact": path.activation_rate(),
        "activated_transport_unit_contact": activated_transport_rate_slot(1.0, path),
        "atomization_ladder": ladder,
        "coordination": bonding_coordination(net),
        "network_coordination_with_steric": dict(net.coordination),
        "n_bonding_contacts": len(bonding_contacts(net)),
        "comparison_policy": "GMTKN/W4-17 reference_ev is quarantine only",
    }


# First GMTKN activation witnesses + expanded H-transfer / polyatomic panel.
GMTKN_ACTIVATION_SUBSET: tuple[str, ...] = ("H2", "HF", "LiH", "N2", "H2O", "CH4")
GMTKN_ACTIVATION_EXTENDED: tuple[str, ...] = GMTKN_ACTIVATION_SUBSET + (
    "NH3",
    "HCl",
    "H2S",
    "HCN",
    "C2H2",
    "PH3",
)


def _benchmark_by_name(name: str) -> dbc.MoleculeBenchmark | None:
    for suite in (
        dbc.GMTKN55_SUITE,
        dbc.EXPANDED_MOLECULE_SUITE,
        dbc.OPEN_SHELL_DIAGNOSTIC_SUITE,
        dbc.ALL_MOLECULE_BENCHMARKS,
    ):
        for b in suite:
            if b.name == name:
                return b
    return None


def build_gmtkn_activation_audit(
    *,
    subset: tuple[str, ...] | None = None,
) -> dict[str, Any]:
    """GMTKN dissociation / partial-atomization activation panel."""
    names = subset if subset is not None else GMTKN_ACTIVATION_EXTENDED
    rows: list[dict[str, Any]] = []
    for name in names:
        bench = _benchmark_by_name(name)
        if bench is None:
            rows.append({"molecule": name, "error": "benchmark not found"})
            continue
        rows.append(path_from_benchmark(bench, edge_index=0))

    identity = {
        "break_cn1": abs(break_coordination_excess(1.0) - 1.0) < 1e-15,
        "break_cn4": abs(break_coordination_excess(4.0) - 0.25) < 1e-15,
        "break_cn2": abs(break_coordination_excess(2.0) - 0.5) < 1e-15,
        "nil_path_barrier": BondRearrangementPath("∅", ()).barrier_ev == 0.0,
        "nil_path_activation": abs(
            BondRearrangementPath("∅", ()).activation_rate(2.5) - 2.5
        )
        < 1e-15,
        "nil_activated_transport": abs(
            activated_transport_rate_slot(2.5, BondRearrangementPath("∅", ())) - 2.5
        )
        < 1e-15,
        "ch4_ladder_n4": True,
        "h2o_ladder_n2": True,
        "all_rows_ok": all("error" not in r for r in rows),
    }
    by_name = {r["molecule"]: r for r in rows if "error" not in r}
    if "CH4" in by_name and by_name["CH4"].get("atomization_ladder"):
        lad = by_name["CH4"]["atomization_ladder"]
        identity["ch4_ladder_n4"] = lad["n_steps"] == 4 and all(
            abs(d - 1.0) < 1e-12 for d in lad["step_deltas"]
        )
    if "H2O" in by_name and by_name["H2O"].get("atomization_ladder"):
        lad = by_name["H2O"]["atomization_ladder"]
        identity["h2o_ladder_n2"] = lad["n_steps"] == 2 and all(
            abs(d - 1.0) < 1e-12 for d in lad["step_deltas"]
        )
    return {
        "source": "scripts/hqiv_bond_rearrangement_path.py",
        "lean_modules": [
            "Hqiv.QuantumChemistry.BondRearrangementPath",
            "Hqiv.QuantumChemistry.MolecularReactionTransport",
        ],
        "subset": list(names),
        "core_subset": list(GMTKN_ACTIVATION_SUBSET),
        "formula": {
            "break_delta": "max(1/CN_i, 1/CN_j)  (= vacancy-style coordination excess)",
            "edge_gate_eV": "D_edge · γ · (4/8) · δ",
            "path_barrier_eV": "max_step edge_gate",
            "atomization_ladder": "n sequential breaks; δ_k = max(1/(CN0−k), 1)",
            "transmission": "1 / (1 + B / max(strong · D, ε))",
            "activation": "contact_rate · transmission",
            "activated_transport": "transportRateSlot · path transmission",
        },
        "identity_checks": identity,
        "all_identity_checks_pass": all(identity.values()),
        "rows": rows,
        "comparison_policy": "GMTKN/W4-17 reference energies are quarantine only",
    }

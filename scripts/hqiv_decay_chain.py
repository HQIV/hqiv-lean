#!/usr/bin/env python3
"""
HQIV decay-chain calculator (Lean-aligned mathematical kernel).

Python mirror orchestrating existing HQIV mirrors:
  - Hqiv.Physics.DynamicNucleonPN / DynamicBetaIsotope / DynamicIsotopeStability
  - Hqiv.Physics.NuclearAndAtomicSpectra (beta_decay_rate, half_life_from_width)
  - Hqiv.Physics.Forces (G_F_from_beta)
  - Hqiv.Physics.WeakFanoHopfBridge
  - Hqiv.Physics.TuftGlobalHadronReadout / HadronMassReadout

Ledgers remain separate in every edge readout:
  mass gap | curvature overlap | weak width | bridge energy | lab dressing
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Literal

import hqiv_dynamic_beta_isotope as dbi
import hqiv_dynamic_nucleon_pn as pn
import hqiv_isotope_stability_halflife as stability
import hqiv_lean_physics_primitives as lean
import hqiv_nuclear_outside_temperature_dynamics as notd
import hqiv_tuft_global_hadron_readout as tuft
import hqiv_weak_fano_hopf_bridge as weak_bridge

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_JSON = ROOT / "data" / "decay_chain_readout.json"

# --- Lean formula mapping (audit trail) ---
LEAN_MAPPING = {
    "referenceM": "OctonionicLightCone.referenceM = 4",
    "xiLockin": "ContinuousXiCoupling.xiLockin = 5",
    "nucleonMassAtXi": "DynamicNucleonPN.nucleonMassAtXi",
    "derivedDeltaM": "DerivedNucleonMass.derivedDeltaM",
    "betaMinusEndpointQAtXi": "DynamicBetaIsotope.betaMinusEndpointQAtXi = derivedDeltaM - m_e",
    "betaMinusEndpointQFromBudgets": "DynamicBetaIsotope.betaMinusEndpointQFromBudgets",
    "betaMinusResidualAtXi": "DynamicBetaIsotope.betaMinusResidualAtXi",
    "betaWeakWidthFromResidual": "DynamicBetaIsotope.betaWeakWidthFromResidual",
    "beta_decay_rate": "NuclearAndAtomicSpectra.beta_decay_rate = G_F^2 m_e^5 M^2",
    "half_life_from_width": "NuclearAndAtomicSpectra.half_life_from_width = ln2/Gamma",
    "G_F_from_beta": "Forces.G_F_from_beta",
    "weakBridgeEnergyMeV": "WeakFanoHopfBridge.weakBridgeEnergyMeV",
    "tuftExcitedMassGlobalAtXi_MeV": "TuftGlobalHadronReadout.tuftExcitedMassGlobalAtXi_MeV",
    "weakBetaChannelOpen": "DynamicIsotopeStability.weakBetaChannelOpen",
}

ChannelTag = Literal[
    "beta_minus",
    "beta_plus",
    "gamma",
    "strong_overlap",
    "weak_hadron",
    "stable",
]

QPolicy = Literal["nucleon_gap", "mass_budget"]
ResidualMode = Literal["effective", "raw"]


@dataclass(frozen=True)
class NuclearState:
    """Nuclear decay state (A, Z) at horizon coordinate xi."""

    A: int
    Z: int
    xi: float = notd.XI_LOCKIN
    label: str | None = None

    @property
    def N(self) -> int:
        return max(self.A - self.Z, 0)

    @property
    def key(self) -> str:
        return self.label or f"Z{self.Z}A{self.A}"


@dataclass(frozen=True)
class HadronState:
    """HEP hadron excitation channel at xi (TUFT global readout)."""

    channel: tuft.TuftExcitationChannel
    xi: float = lean.XI_LOCKIN

    @property
    def key(self) -> str:
        tag = self.channel.pdg_key or f"n{self.channel.n}_l{self.channel.ell}"
        sector = "baryon" if self.channel.is_baryon else "meson"
        return f"{sector}:{tag}"


DecayState = NuclearState | HadronState


@dataclass(frozen=True)
class DecayChannel:
    """Open decay channel from a parent state."""

    tag: ChannelTag
    endpoint_q_mev: float
    residual_mev: float
    width_per_s: float
    half_life_s: float
    kinematic_open: bool
    residual_open: bool
    channel_open: bool
    emitted: tuple[str, ...] = ()
    weak_bridge_mev: float = 0.0
    neutrino_mass_mev: float = 0.0
    geometry_factor: float = 1.0
    q_policy: QPolicy = "mass_budget"
    lean_refs: tuple[str, ...] = ()


@dataclass(frozen=True)
class DecayEdge:
    """Directed transition parent -> daughter + emitted species."""

    parent: DecayState
    daughter: DecayState
    channel: DecayChannel
    branching_ratio: float = 1.0


@dataclass
class DecayNode:
    """Node in an expanded decay chain with cumulative weight and time."""

    state: DecayState
    depth: int
    cumulative_weight: float
    cumulative_time_s: float
    via: DecayEdge | None = None
    children: list[DecayNode] = field(default_factory=list)


@dataclass(frozen=True)
class DecayChainResult:
    """Full chain expansion from a root state."""

    root: DecayState
    nodes: list[DecayNode]
    terminal: list[DecayNode]
    max_depth: int
    min_branch: float
    xi: float
    q_policy: QPolicy
    lean_modules: tuple[str, ...]


def _nuclear_environment(state: NuclearState) -> pn.NucleonEnvironment:
    return stability.isotope_environment(state.A, state.Z, xi=state.xi)


def nuclear_mass_budget_mev(state: NuclearState) -> float:
    """Isotope mass budget: Z·m_p + N·m_n at shared environment."""
    env = _nuclear_environment(state)
    pair = pn.pn_pair_readout(env)
    return dbi.isotope_mass_budget(state.A, state.Z, pair)


def hadron_mass_mev(state: HadronState) -> float:
    """TUFT global excited mass at xi."""
    return tuft.tuft_excited_mass_global_at_xi_mev(state.xi, state.channel)


def state_mass_mev(state: DecayState) -> float:
    if isinstance(state, NuclearState):
        return nuclear_mass_budget_mev(state)
    return hadron_mass_mev(state)


def beta_minus_daughter(state: NuclearState) -> NuclearState | None:
    if state.N <= 0:
        return None
    return NuclearState(
        A=state.A,
        Z=state.Z + 1,
        xi=state.xi,
        label=f"Z{state.Z + 1}A{state.A}",
    )


def beta_plus_daughter(state: NuclearState) -> NuclearState | None:
    if state.Z <= 0:
        return None
    return NuclearState(
        A=state.A,
        Z=state.Z - 1,
        xi=state.xi,
        label=f"Z{state.Z - 1}A{state.A}",
    )


def endpoint_q_beta_minus(
    parent: NuclearState,
    *,
    q_policy: QPolicy = "mass_budget",
    m_e_mev: float | None = None,
) -> float | None:
    """Endpoint Q for β− step."""
    m_e = dbi.model_electron_mass_mev() if m_e_mev is None else m_e_mev
    if q_policy == "nucleon_gap":
        env = _nuclear_environment(parent)
        pair = pn.pn_pair_readout(env)
        return dbi.beta_minus_endpoint_q_nucleon_gap(pair, m_e_mev=m_e)
    daughter = beta_minus_daughter(parent)
    if daughter is None:
        return None
    return (
        nuclear_mass_budget_mev(parent)
        - nuclear_mass_budget_mev(daughter)
        - m_e
    )


def endpoint_q_beta_plus(
    parent: NuclearState,
    *,
    q_policy: QPolicy = "mass_budget",
    m_e_mev: float | None = None,
) -> float | None:
    m_e = dbi.model_electron_mass_mev() if m_e_mev is None else m_e_mev
    if q_policy == "nucleon_gap":
        env = _nuclear_environment(parent)
        pair = pn.pn_pair_readout(env)
        gap = pair.proton.mass_mev - pair.neutron.mass_mev
        return gap - m_e
    daughter = beta_plus_daughter(parent)
    if daughter is None:
        return None
    return (
        nuclear_mass_budget_mev(parent)
        - nuclear_mass_budget_mev(daughter)
        - m_e
    )


def beta_residuals(
    state: NuclearState,
) -> tuple[float, float, float, float]:
    """Raw and effective β± residuals (MeV). Returns (β− raw, β+ raw, β− eff, β+ eff)."""
    env = _nuclear_environment(state)
    base = dbi.beta_channel_readout(state.key, state.A, state.Z, env)
    shield = max(env.well_depth_mev, 0.0) if env.bonded else 0.0
    own = notd.nucleon_own_binding_mev(env.shell, env.xi, bonded=env.bonded)
    n_count = state.N
    if state.A > 1:
        neutron_drive = max(0.0, (n_count - state.Z) / state.A) * own
        proton_drive = max(0.0, (state.Z - n_count) / state.A) * own
    else:
        neutron_drive = proton_drive = 0.0
    beta_minus_eff = base.beta_minus_residual_mev + neutron_drive - shield
    beta_plus_eff = base.beta_plus_residual_mev + proton_drive - shield
    return (
        base.beta_minus_residual_mev,
        base.beta_plus_residual_mev,
        beta_minus_eff,
        beta_plus_eff,
    )


def width_geometry_factor(
    state: NuclearState,
    *,
    residual_mev: float,
) -> float:
    env = _nuclear_environment(state)
    if state.A <= 1 or not env.bonded:
        return 1.0
    cluster_total = pn.cluster_caustic_total_mev(state.A, shell=env.shell, xi=env.xi)
    pair = pn.pn_pair_readout(env)
    width_well = dbi.beta_width_well_depth_mev(
        state.A,
        state.Z,
        cluster_total_mev=cluster_total,
        proton_mass_mev=pair.proton.mass_mev,
        neutron_mass_mev=pair.neutron.mass_mev,
    )
    return dbi.beta_geometry_width_factor(
        state.A,
        residual_mev=residual_mev,
        well_depth_mev=width_well,
        bonded=env.bonded,
    )


def weak_width_and_halflife(
    state: NuclearState,
    *,
    channel: Literal["beta_minus", "beta_plus"],
    endpoint_q_mev: float,
    residual_mev: float,
    neutrino_mass_mev: float | None = None,
    weak_bridge_mev: float | None = None,
    local_curvature_width_factor: float = 1.0,
) -> tuple[float, float, float, float]:
    """Returns (width_per_s, half_life_s, bridge_mev, geometry_factor)."""
    env = _nuclear_environment(state)
    nu_mev = (
        stability.model_electron_neutrino_mass_mev()
        if neutrino_mass_mev is None
        else neutrino_mass_mev
    )
    bridge = (
        weak_bridge.weak_bridge_energy_mev(nu_mev)
        if weak_bridge_mev is None
        else weak_bridge_mev
    )
    shield = max(env.well_depth_mev, 0.0) if env.bonded else 0.0
    cluster_total = (
        pn.cluster_caustic_total_mev(state.A, shell=env.shell, xi=env.xi)
        if env.bonded
        else 0.0
    )
    width_well: float | None = None
    if env.bonded and state.N > 0 and channel == "beta_minus":
        pair = pn.pn_pair_readout(env)
        width_well = dbi.beta_width_well_depth_mev(
            state.A,
            state.Z,
            cluster_total_mev=cluster_total,
            proton_mass_mev=pair.proton.mass_mev,
            neutron_mass_mev=pair.neutron.mass_mev,
        )
    geom = width_geometry_factor(state, residual_mev=residual_mev)
    half_life = dbi.weak_beta_half_life_seconds(
        endpoint_q_mev,
        residual_mev,
        A=state.A,
        well_depth_mev=shield,
        width_well_depth_mev=width_well,
        bonded=env.bonded,
        neutrino_mass_mev=nu_mev,
        weak_bridge_energy_mev=bridge,
        local_curvature_width_factor=local_curvature_width_factor,
    )
    width = 0.0 if not math.isfinite(half_life) or half_life <= 0.0 else math.log(2.0) / half_life
    return width, half_life, bridge, geom


def evaluate_nuclear_channel(
    state: NuclearState,
    *,
    channel: Literal["beta_minus", "beta_plus"],
    q_policy: QPolicy = "mass_budget",
    residual_mode: ResidualMode = "effective",
) -> DecayChannel | None:
    """Build a DecayChannel for one β mode, or None if daughter invalid."""
    daughter_fn = beta_minus_daughter if channel == "beta_minus" else beta_plus_daughter
    daughter = daughter_fn(state)
    if daughter is None:
        return None

    endpoint_fn = endpoint_q_beta_minus if channel == "beta_minus" else endpoint_q_beta_plus
    endpoint_q = endpoint_fn(state, q_policy=q_policy)
    if endpoint_q is None:
        return None

    raw_minus, raw_plus, eff_minus, eff_plus = beta_residuals(state)
    if residual_mode == "raw":
        residual = raw_minus if channel == "beta_minus" else raw_plus
    else:
        residual = eff_minus if channel == "beta_minus" else eff_plus

    kinematic_open = endpoint_q > 0.0
    residual_open = residual > 0.0
    channel_open = kinematic_open and residual_open

    emitted = ("e-", "nu_e_bar") if channel == "beta_minus" else ("e+", "nu_e")

    if not channel_open:
        return DecayChannel(
            tag=channel,
            endpoint_q_mev=endpoint_q,
            residual_mev=residual,
            width_per_s=0.0,
            half_life_s=math.inf,
            kinematic_open=kinematic_open,
            residual_open=residual_open,
            channel_open=False,
            emitted=emitted,
            q_policy=q_policy,
            lean_refs=("DynamicIsotopeStability.weakBetaChannelOpen",),
        )

    width, half_life, bridge, geom = weak_width_and_halflife(
        state,
        channel=channel,
        endpoint_q_mev=endpoint_q,
        residual_mev=residual,
    )
    return DecayChannel(
        tag=channel,
        endpoint_q_mev=endpoint_q,
        residual_mev=residual,
        width_per_s=width,
        half_life_s=half_life,
        kinematic_open=True,
        residual_open=True,
        channel_open=True,
        emitted=emitted,
        weak_bridge_mev=bridge,
        geometry_factor=geom,
        q_policy=q_policy,
        lean_refs=(
            "DynamicBetaIsotope.betaWeakWidthFromResidual",
            "NuclearAndAtomicSpectra.half_life_from_width",
        ),
    )


def open_channels_nuclear(
    state: NuclearState,
    *,
    q_policy: QPolicy = "mass_budget",
    residual_mode: ResidualMode = "effective",
) -> list[DecayChannel]:
    channels: list[DecayChannel] = []
    for tag in ("beta_minus", "beta_plus"):
        ch = evaluate_nuclear_channel(
            state, channel=tag, q_policy=q_policy, residual_mode=residual_mode
        )
        if ch is not None:
            channels.append(ch)
    return channels


def branching_ratios(channels: list[DecayChannel]) -> dict[int, float]:
    """Normalize open channel widths to branching ratios."""
    open_ch = [c for c in channels if c.channel_open and c.width_per_s > 0.0]
    total = sum(c.width_per_s for c in open_ch)
    if total <= 0.0:
        return {i: 0.0 for i in range(len(channels))}
    out: dict[int, float] = {}
    for i, ch in enumerate(channels):
        if ch in open_ch:
            out[i] = ch.width_per_s / total
        else:
            out[i] = 0.0
    return out


def edges_from_nuclear_state(
    state: NuclearState,
    *,
    q_policy: QPolicy = "mass_budget",
    residual_mode: ResidualMode = "effective",
) -> list[DecayEdge]:
    channels = open_channels_nuclear(
        state, q_policy=q_policy, residual_mode=residual_mode
    )
    br = branching_ratios(channels)
    edges: list[DecayEdge] = []
    for i, ch in enumerate(channels):
        if not ch.channel_open:
            continue
        if ch.tag == "beta_minus":
            daughter = beta_minus_daughter(state)
        else:
            daughter = beta_plus_daughter(state)
        if daughter is None:
            continue
        edges.append(
            DecayEdge(
                parent=state,
                daughter=daughter,
                channel=ch,
                branching_ratio=br.get(i, 0.0),
            )
        )
    return edges


def evaluate_hadron_weak_hadron_edge(
    parent: HadronState,
    daughter: HadronState,
    *,
    q_policy: QPolicy = "mass_budget",
) -> DecayEdge | None:
    """
    Generic HEP mass-budget edge between two TUFT channels.

    Uses nuclear weak-width slot with residual = max(Q, 0) when no overlap ledger
    is defined for hadrons (extension hook; overlap ledger TBD in Lean).
    """
    m_parent = hadron_mass_mev(parent)
    m_daughter = hadron_mass_mev(daughter)
    m_e = dbi.model_electron_mass_mev()
    nu_mev = stability.model_electron_neutrino_mass_mev()
    bridge = weak_bridge.weak_bridge_energy_mev(nu_mev)
    q = m_parent - m_daughter - m_e - bridge
    residual = max(q, 0.0)
    kinematic_open = q > 0.0
    channel_open = kinematic_open and residual > 0.0
    if not channel_open:
        ch = DecayChannel(
            tag="weak_hadron",
            endpoint_q_mev=q,
            residual_mev=residual,
            width_per_s=0.0,
            half_life_s=math.inf,
            kinematic_open=kinematic_open,
            residual_open=residual > 0.0,
            channel_open=False,
            emitted=("hadron_products",),
            weak_bridge_mev=bridge,
            q_policy=q_policy,
            lean_refs=("TuftGlobalHadronReadout.tuftExcitedMassGlobalAtXi_MeV",),
        )
        return DecayEdge(parent=parent, daughter=daughter, channel=ch, branching_ratio=0.0)

    half_life = dbi.weak_beta_half_life_seconds(
        q,
        residual,
        A=1,
        bonded=False,
        neutrino_mass_mev=nu_mev,
        weak_bridge_energy_mev=bridge,
    )
    width = 0.0 if not math.isfinite(half_life) or half_life <= 0.0 else math.log(2.0) / half_life
    ch = DecayChannel(
        tag="weak_hadron",
        endpoint_q_mev=q,
        residual_mev=residual,
        width_per_s=width,
        half_life_s=half_life,
        kinematic_open=True,
        residual_open=True,
        channel_open=True,
        emitted=("hadron_weak_products",),
        weak_bridge_mev=bridge,
        q_policy=q_policy,
        lean_refs=(
            "TuftGlobalHadronReadout.tuftExcitedMassGlobalAtXi_MeV",
            "DynamicBetaIsotope.betaWeakWidthFromResidual",
        ),
    )
    return DecayEdge(parent=parent, daughter=daughter, channel=ch, branching_ratio=1.0)


def expand_chain(
    root: DecayState,
    *,
    max_depth: int = 8,
    min_branch: float = 1e-6,
    q_policy: QPolicy = "mass_budget",
    residual_mode: ResidualMode = "effective",
    qualify_em_tipping: bool = False,
) -> DecayChainResult:
    """
    Iteratively expand decay chain from root.

    Nuclear states follow β± edges; hadron roots require explicit daughter list
    via expand_hadron_chain.

    When ``qualify_em_tipping`` is True, use raw overlap residuals for channel
    openness (same active-channel rule as ``hqiv_isotope_stability_halflife``).
    """
    mode: ResidualMode = "raw" if qualify_em_tipping else residual_mode
    root_node = DecayNode(
        state=root,
        depth=0,
        cumulative_weight=1.0,
        cumulative_time_s=0.0,
    )
    all_nodes: list[DecayNode] = [root_node]
    terminal: list[DecayNode] = []
    frontier: list[DecayNode] = [root_node]

    while frontier:
        node = frontier.pop(0)
        if node.depth >= max_depth:
            terminal.append(node)
            continue
        if not isinstance(node.state, NuclearState):
            terminal.append(node)
            continue

        edges = edges_from_nuclear_state(
            node.state, q_policy=q_policy, residual_mode=mode
        )
        open_edges = [e for e in edges if e.channel.channel_open and e.branching_ratio >= min_branch]
        if not open_edges:
            terminal.append(node)
            continue

        for edge in open_edges:
            child_weight = node.cumulative_weight * edge.branching_ratio
            if child_weight < min_branch:
                continue
            dt = edge.channel.half_life_s if math.isfinite(edge.channel.half_life_s) else 0.0
            child = DecayNode(
                state=edge.daughter,
                depth=node.depth + 1,
                cumulative_weight=child_weight,
                cumulative_time_s=node.cumulative_time_s + dt,
                via=edge,
            )
            node.children.append(child)
            all_nodes.append(child)
            if child.depth < max_depth:
                frontier.append(child)
            else:
                terminal.append(child)

    xi = root.xi if hasattr(root, "xi") else notd.XI_LOCKIN
    return DecayChainResult(
        root=root,
        nodes=all_nodes,
        terminal=terminal,
        max_depth=max_depth,
        min_branch=min_branch,
        xi=xi,
        q_policy=q_policy,
        lean_modules=(
            "Hqiv.Physics.DynamicBetaIsotope",
            "Hqiv.Physics.DynamicIsotopeStability",
            "Hqiv.Physics.DynamicNucleonPN",
            "Hqiv.Physics.TuftGlobalHadronReadout",
        ),
    )


def expand_hadron_chain(
    parent: HadronState,
    daughters: list[HadronState],
    *,
    q_policy: QPolicy = "mass_budget",
) -> DecayChainResult:
    """Single-step hadron decay fan-out with mass-budget Q and width normalization."""
    edges: list[DecayEdge] = []
    for d in daughters:
        edge = evaluate_hadron_weak_hadron_edge(parent, d, q_policy=q_policy)
        if edge is not None and edge.channel.channel_open:
            edges.append(edge)
    br = branching_ratios([e.channel for e in edges])
    for i, edge in enumerate(edges):
        edges[i] = DecayEdge(
            parent=edge.parent,
            daughter=edge.daughter,
            channel=edge.channel,
            branching_ratio=br.get(i, 0.0),
        )

    root = DecayNode(state=parent, depth=0, cumulative_weight=1.0, cumulative_time_s=0.0)
    children: list[DecayNode] = []
    for edge in edges:
        if edge.branching_ratio <= 0.0:
            continue
        dt = edge.channel.half_life_s if math.isfinite(edge.channel.half_life_s) else 0.0
        child = DecayNode(
            state=edge.daughter,
            depth=1,
            cumulative_weight=edge.branching_ratio,
            cumulative_time_s=dt,
            via=edge,
        )
        root.children.append(child)
        children.append(child)

    nodes = [root, *children]
    terminal = children if children else [root]
    return DecayChainResult(
        root=parent,
        nodes=nodes,
        terminal=terminal,
        max_depth=1,
        min_branch=0.0,
        xi=parent.xi,
        q_policy=q_policy,
        lean_modules=("Hqiv.Physics.TuftGlobalHadronReadout",),
    )


def _serialize_state(state: DecayState) -> dict:
    if isinstance(state, NuclearState):
        return {
            "kind": "nuclear",
            "A": state.A,
            "Z": state.Z,
            "N": state.N,
            "xi": state.xi,
            "label": state.key,
            "mass_mev": nuclear_mass_budget_mev(state),
        }
    ch = state.channel
    return {
        "kind": "hadron",
        "sector": "baryon" if ch.is_baryon else "meson",
        "chart_shell": ch.chart_shell,
        "n": ch.n,
        "ell": ch.ell,
        "valence_quarks": ch.valence_quarks,
        "n_strange": ch.n_strange,
        "isoscalar": ch.isoscalar,
        "pdg_key": ch.pdg_key,
        "xi": state.xi,
        "label": state.key,
        "mass_mev": hadron_mass_mev(state),
    }


def _serialize_channel(ch: DecayChannel) -> dict:
    return {
        "tag": ch.tag,
        "endpoint_q_mev": ch.endpoint_q_mev,
        "residual_mev": ch.residual_mev,
        "width_per_s": ch.width_per_s,
        "half_life_s": ch.half_life_s if math.isfinite(ch.half_life_s) else None,
        "kinematic_open": ch.kinematic_open,
        "residual_open": ch.residual_open,
        "channel_open": ch.channel_open,
        "emitted": list(ch.emitted),
        "weak_bridge_mev": ch.weak_bridge_mev,
        "geometry_factor": ch.geometry_factor,
        "q_policy": ch.q_policy,
        "lean_refs": list(ch.lean_refs),
    }


def _serialize_node(node: DecayNode) -> dict:
    out = {
        "state": _serialize_state(node.state),
        "depth": node.depth,
        "cumulative_weight": node.cumulative_weight,
        "cumulative_time_s": node.cumulative_time_s,
        "children": [_serialize_node(c) for c in node.children],
    }
    if node.via is not None:
        out["via"] = {
            "channel": _serialize_channel(node.via.channel),
            "branching_ratio": node.via.branching_ratio,
            "daughter": _serialize_state(node.via.daughter),
        }
    return out


def build_payload(
    *,
    roots: list[DecayState] | None = None,
    max_depth: int = 6,
    min_branch: float = 1e-6,
    q_policy: QPolicy = "mass_budget",
    include_hadron_demo: bool = True,
    qualify_em_tipping: bool = False,
) -> dict:
    if roots is None:
        roots = [
            NuclearState(A=1, Z=0, label="n"),
            NuclearState(A=3, Z=1, label="T"),
            NuclearState(A=4, Z=2, label="He4"),
        ]

    chains: list[dict] = []
    for root in roots:
        if isinstance(root, NuclearState):
            result = expand_chain(
                root,
                max_depth=max_depth,
                min_branch=min_branch,
                q_policy=q_policy,
                qualify_em_tipping=qualify_em_tipping,
            )
            root_node = result.nodes[0]
            chains.append(
                {
                    "root": _serialize_state(root),
                    "q_policy": q_policy,
                    "max_depth": max_depth,
                    "min_branch": min_branch,
                    "tree": _serialize_node(root_node),
                    "terminal_count": len(result.terminal),
                    "lean_modules": list(result.lean_modules),
                }
            )

    hadron_chains: list[dict] = []
    if include_hadron_demo:
        parent = HadronState(
            channel=tuft.TuftExcitationChannel.baryon(0, 1, pdg_key="Delta(1232)"),
            xi=lean.XI_LOCKIN,
        )
        daughters = [
            HadronState(
                channel=tuft.TuftExcitationChannel.baryon(0, 0, pdg_key="proton"),
                xi=lean.XI_LOCKIN,
            ),
        ]
        hres = expand_hadron_chain(parent, daughters, q_policy=q_policy)
        hadron_chains.append(
            {
                "root": _serialize_state(parent),
                "tree": _serialize_node(hres.nodes[0]),
                "lean_modules": list(hres.lean_modules),
            }
        )

    return {
        "source": "scripts/hqiv_decay_chain.py",
        "lean_mapping": LEAN_MAPPING,
        "referenceM": lean.REFERENCE_M,
        "xi_lockin": lean.XI_LOCKIN,
        "alpha": lean.ALPHA,
        "gamma": lean.GAMMA,
        "proton_anchor_mev": 938.272,
        "q_policy_default": q_policy,
        "nuclear_chains": chains,
        "hadron_chains": hadron_chains,
    }


def print_report(payload: dict) -> None:
    print("HQIV decay-chain readout")
    print("=" * 72)
    print(f"referenceM={payload['referenceM']}  xi_lock={payload['xi_lockin']}  q_policy={payload['q_policy_default']}")
    for chain in payload.get("nuclear_chains", []):
        root = chain["root"]
        print(f"\nRoot {root['label']}  A={root['A']} Z={root['Z']}  mass={root['mass_mev']:.3f} MeV")
        _print_tree(chain["tree"], indent=2)


def _print_tree(node: dict, indent: int = 0) -> None:
    st = node["state"]
    prefix = " " * indent
    line = f"{prefix}{st['label']}  w={node['cumulative_weight']:.4e}  t={node['cumulative_time_s']:.4e}s"
    if node.get("via"):
        via = node["via"]
        ch = via["channel"]
        line += f"  <- {ch['tag']}  BR={via['branching_ratio']:.4f}  Q={ch['endpoint_q_mev']:.4f} MeV"
    print(line)
    for child in node.get("children", []):
        _print_tree(child, indent + 2)


def main() -> None:
    parser = argparse.ArgumentParser(description="HQIV decay-chain calculator")
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    parser.add_argument("--max-depth", type=int, default=6)
    parser.add_argument("--min-branch", type=float, default=1e-6)
    parser.add_argument(
        "--q-policy",
        choices=("mass_budget", "nucleon_gap"),
        default="mass_budget",
    )
    parser.add_argument("--root", type=str, default=None, help="e.g. n, T, He4, or Z1A3")
    parser.add_argument(
        "--qualify-em-tipping",
        action="store_true",
        help="Use raw overlap residual for channel openness (stability-script rule)",
    )
    args = parser.parse_args()

    roots: list[DecayState] | None = None
    if args.root:
        label = args.root.strip()
        presets = {
            "n": NuclearState(1, 0, label="n"),
            "p": NuclearState(1, 1, label="p"),
            "T": NuclearState(3, 1, label="T"),
            "D": NuclearState(2, 1, label="D"),
            "He3": NuclearState(3, 2, label="He3"),
            "He4": NuclearState(4, 2, label="He4"),
        }
        if label in presets:
            roots = [presets[label]]
        else:
            a, z, _ = stability.parse_isotope_label(label)
            roots = [NuclearState(A=a, Z=z, label=label)]

    payload = build_payload(
        roots=roots,
        max_depth=args.max_depth,
        min_branch=args.min_branch,
        q_policy=args.q_policy,  # type: ignore[arg-type]
        qualify_em_tipping=args.qualify_em_tipping,
    )
    print_report(payload)
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(payload, indent=2) + "\n")
    print(f"\nWrote {args.json_out}")


if __name__ == "__main__":
    main()

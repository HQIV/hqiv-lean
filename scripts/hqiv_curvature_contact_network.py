#!/usr/bin/env python3
"""
Curvature contact network — precise geometry + phase rules for TUFT chemistry.

Lean: `Hqiv.QuantumChemistry.CurvatureContactNetwork`

Network rule (single engine for molecules → liquids → solids):

  **Nodes** — fragments with cluster mass deficit on the nuclear spine.

  **Contacts** (typed, parameter-free):
    • cluster_deficit     — node self; lowers m_eff → dresses vev down (D, T, valley)
    • covalent_bond       — attractive edge; G_eff(θ) outside closure
    • steric_repulsion    — repulsive edge (peripheral H–H); adds curvature mass back
    • hyperclosure        — multi-bond graph closure (≥2 bonds)
    • periodic_image      — lattice repeat (solid/liquid scaffold)

  **Phase** — **derived from (T, P)** via `hqiv_thermodynamic_phase_from_tp` (not user input).
    • molecular_cluster / gas — GMTKN55, dilute protein
    • liquid / solid — coordination and periodic weights from T, P + material binding scales

  **Readouts**
    • networked_vev_geometric_mean(network) — for DynamicBindingChart
    • contact_report(network) — JSON witness for geometry / phase studies

Run:
  python3 scripts/hqiv_curvature_contact_network.py
  python3 scripts/hqiv_curvature_contact_network.py --json-out data/curvature_contact_network_rules.json
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from enum import Enum
from pathlib import Path
from typing import Any

import hqiv_curvature_bond_state as cbs
import hqiv_lean_physics_primitives as lean
import hqiv_electronic_valence_shells as evs
import hqiv_nuclear_curvature_binding as ncb
import hqiv_s2_binding_geometry as s2g
import hqiv_thermodynamic_phase_from_tp as tptp
from fragment_aware_bonded_horizon import BOHR_RADIUS_ANGSTROM, BondGeometry, FragmentConfig

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_JSON = ROOT / "data" / "curvature_contact_network_rules.json"

PROTON_MEV = ncb.PROTON_MEV
GAMMA = lean.GAMMA
STRONG_FRAC = lean.STRONG_CHANNEL_FRACTION


class ContactKind(str, Enum):
    CLUSTER_DEFICIT = "cluster_deficit"
    COVALENT_BOND = "covalent_bond"
    STERIC_REPULSION = "steric_repulsion"
    HYPERCLOSURE = "hyperclosure"
    PERIODIC_IMAGE = "periodic_image"


@dataclass(frozen=True)
class NetworkNode:
    index: int
    label: str
    z_nuclear: int
    electrons: int
    mass_number: int
    nuclear_shell: int
    valence_s_shell: int
    valence_p_shell: int | None
    compton_shell: int
    cluster_mass_mev: float
    mass_ratio_per_nucleon: float
    node_vev_factor: float
    shell_geometry: s2g.ShellSlotGeometry | None = None


@dataclass(frozen=True)
class NetworkContact:
    kind: ContactKind
    i: int
    j: int | None
    contacts_at_i: int
    contacts_at_j: int
    undirected_points: int
    distance_angstrom: float | None
    geff_theta: float | None
    weight: float
    increment_factor: float
    bond_geometry: s2g.BondAngularGeometry | None = None


@dataclass(frozen=True)
class CurvatureContactNetwork:
    name: str
    thermo: tptp.DerivedThermodynamicState
    nodes: tuple[NetworkNode, ...]
    contacts: tuple[NetworkContact, ...]
    compton_triplet: tuple[int, int, int]
    coordination: dict[int, int]
    lattice_repeats: tuple[int, int, int]
    medium_density_fraction: float = 0.0


def _node_from_fragment(index: int, frag: FragmentConfig) -> NetworkNode:
    A = ncb.stable_mass_number(frag.z_nuclear, frag.electrons)
    m_nuc = ncb.nucleus_curvature_shell(A)
    m_s, m_p = evs.electronic_compton_shells(frag.z_nuclear)
    compton = m_s
    cm = ncb.cluster_mass_mev(m_nuc, A)
    mr = cm / (float(A) * PROTON_MEV)
    vev = ncb.tuft_vev_factor_networked_at_cluster(m_nuc, A)
    shell_geom = s2g.shell_slot_geometry(m_s, m_p)
    return NetworkNode(
        index=index,
        label=frag.label,
        z_nuclear=frag.z_nuclear,
        electrons=frag.electrons,
        mass_number=A,
        nuclear_shell=m_nuc,
        valence_s_shell=m_s,
        valence_p_shell=m_p,
        compton_shell=compton,
        cluster_mass_mev=cm,
        mass_ratio_per_nucleon=mr,
        node_vev_factor=vev,
        shell_geometry=shell_geom,
    )


def chemistry_compton_triplet(
    fragments: tuple[FragmentConfig, ...],
) -> tuple[int, int, int]:
    """Lean `DynamicBindingChart` triplets (electronic valence, not nuclear drum)."""
    return evs.chemistry_compton_triplet(fragments)


def _peripheral_h_indices(nodes: tuple[NetworkNode, ...]) -> list[int]:
    has_heavy = any(n.z_nuclear > 1 for n in nodes)
    if not has_heavy:
        return []
    return [n.index for n in nodes if n.z_nuclear == 1]


def _infer_steric_contacts(
    nodes: tuple[NetworkNode, ...],
    peripheral_h: list[int],
) -> list[NetworkContact]:
    n_h = len(peripheral_h)
    if n_h < 2:
        return []
    cph = ncb.peripheral_h_h_repulsive_contacts_per_hydrogen(n_h)
    points = ncb.peripheral_h_h_repulsive_contact_points(n_h)
    triplet = (1, 1, 1)
    theta = cbs.contact_phase_theta_rad(triplet)
    geff = cbs.outside_contact_coupling(theta)
    inc = steric_repulsion_increment(contact_points=points, n_peripheral_h=n_h)
    return [
        NetworkContact(
            kind=ContactKind.STERIC_REPULSION,
            i=peripheral_h[0],
            j=peripheral_h[1] if len(peripheral_h) > 1 else None,
            contacts_at_i=cph,
            contacts_at_j=cph,
            undirected_points=points,
            distance_angstrom=None,
            geff_theta=theta,
            weight=1.0,
            increment_factor=inc,
        )
    ]


def _bond_contacts(
    nodes: tuple[NetworkNode, ...],
    bonds: tuple[BondGeometry, ...],
    *,
    molecule_name: str = "",
    medium_density_fraction: float = 0.0,
) -> list[NetworkContact]:
    out: list[NetworkContact] = []
    centre_bond_count: dict[int, int] = {}
    for bond in bonds:
        centre_bond_count[bond.frag_i] = centre_bond_count.get(bond.frag_i, 0) + 1
        centre_bond_count[bond.frag_j] = centre_bond_count.get(bond.frag_j, 0) + 1

    for bond in bonds:
        a = nodes[bond.frag_i]
        b = nodes[bond.frag_j]
        dw = 1.0 / (1.0 + bond.distance_angstrom / BOHR_RADIUS_ANGSTROM)
        heavy = a if a.mass_number >= b.mass_number else b
        n_centre = centre_bond_count.get(heavy.index, 1)
        z_centre = heavy.z_nuclear if heavy.mass_number >= b.mass_number else None
        if z_centre is not None and z_centre <= 1:
            z_centre = None
        ang = s2g.bond_angular_geometry(
            m_s_i=a.valence_s_shell,
            m_p_i=a.valence_p_shell,
            m_s_j=b.valence_s_shell,
            m_p_j=b.valence_p_shell,
            distance_weight=dw,
            bond_angle_rad=bond.bond_angle_rad,
            molecule_name=molecule_name,
            n_bonds_at_centre=n_centre,
            z_centre=z_centre if n_centre >= 2 else None,
            medium_density_fraction=medium_density_fraction,
        )
        out.append(
            NetworkContact(
                kind=ContactKind.COVALENT_BOND,
                i=bond.frag_i,
                j=bond.frag_j,
                contacts_at_i=1,
                contacts_at_j=1,
                undirected_points=1,
                distance_angstrom=bond.distance_angstrom,
                geff_theta=ang.mean_compton_angle_rad,
                weight=dw * ang.valley_alignment_weight,
                increment_factor=ang.geff_combined,
                bond_geometry=ang,
            )
        )
    return out


def covalent_bond_geometries(
    network: CurvatureContactNetwork,
) -> tuple[s2g.BondAngularGeometry, ...]:
    return tuple(
        c.bond_geometry
        for c in network.contacts
        if c.kind == ContactKind.COVALENT_BOND and c.bond_geometry is not None
    )


def contact_xi_from_network(network: CurvatureContactNetwork) -> float:
    """Contact ξ for dynamic κ(ξ): Compton-triplet mean (electronic spine, not nuclear drum)."""
    return lean.xi_from_compton_triplet(network.compton_triplet)


def network_geometry_alignment_factor(network: CurvatureContactNetwork) -> float:
    """Pure geometric valley relaxation (no κ_bind); homonuclear diatomics skip VSEPR."""
    geoms = covalent_bond_geometries(network)
    if len(geoms) == 1 and all(n.z_nuclear == 1 for n in network.nodes):
        return 1.0
    return s2g.geometry_alignment_factor(geoms)


def network_valley_relaxation_factor(network: CurvatureContactNetwork) -> float:
    """Alias for ``network_geometry_alignment_factor``."""
    return network_geometry_alignment_factor(network)


@dataclass(frozen=True)
class NetworkBindingFeedback:
    """
    Buttoned-down factorization from contact graph → dynamic binding core.

    Matches ``hqiv_dynamic_binding_chart``:

      E_bind = η₂ · surplus · networked_vev · geometry_align · κ_feedback(ξ) · EV_per_λ

    Surplus and shell dress are upstream in ``hqiv_shell_aware_binding``.
    """

    compton_triplet: tuple[int, int, int]
    contact_xi: float
    bare_vev_geometric_mean: float
    networked_vev_geometric_mean: float
    steric_multiplier: float
    phase_multiplier: float
    geometry_alignment_factor: float
    curvature_feedback_at_xi: float
    peripheral_hydrogen_count: int
    h_h_repulsive_contact_points: int

    @property
    def vev_network_dress(self) -> float:
        """networked / bare — cluster deficit + steric + phase."""
        if self.bare_vev_geometric_mean <= 0.0:
            return 1.0
        return self.networked_vev_geometric_mean / self.bare_vev_geometric_mean

    @property
    def dimless_prefactor(self) -> float:
        """Product before surplus and EV_per_λ."""
        return (
            self.networked_vev_geometric_mean
            * self.geometry_alignment_factor
            * self.curvature_feedback_at_xi
        )


def _steric_and_phase_multipliers(
    network: CurvatureContactNetwork,
) -> tuple[float, float, float]:
    """Return (bare_vev, steric_mult, phase_mult) before final networked product."""
    m_s, m_p, m_h, n_periph = _compton_slot_mass_numbers(network)
    heavy_a = max(n.mass_number for n in network.nodes)
    light_a = min(n.mass_number for n in network.nodes)

    bare = ncb.vev_geometric_mean_networked_for_compton_triplet(
        network.compton_triplet,
        heavy_mass_number=heavy_a,
        light_mass_number=light_a,
        n_peripheral_hydrogens=0,
    )

    steric_mult = 1.0
    for c in network.contacts:
        if c.kind == ContactKind.STERIC_REPULSION:
            steric_mult = max(steric_mult, c.increment_factor)

    if n_periph >= 2 and steric_mult == 1.0:
        points = ncb.peripheral_h_h_repulsive_contact_points(n_periph)
        steric_mult = steric_repulsion_increment(
            contact_points=points,
            n_peripheral_h=n_periph,
        )

    thermo = network.thermo
    z_max = max(network.coordination.values()) if network.coordination else 1
    if thermo.phase in (tptp.DerivedPhase.GAS, tptp.DerivedPhase.MOLECULAR_CLUSTER):
        phase_mult = 1.0
    else:
        coord_frac = thermo.coordination_fraction
        persist = thermo.contact_persistence
        phase_factors = []
        for n in network.nodes:
            local = network.coordination.get(n.index, 1) / float(max(z_max, 1))
            phase_factors.append(1.0 + persist * coord_frac * (local - 1.0))
        phase_mult = (
            math.prod(phase_factors) ** (1.0 / len(phase_factors)) if phase_factors else 1.0
        )

    periodic_mult = 1.0
    for c in network.contacts:
        if c.kind == ContactKind.PERIODIC_IMAGE:
            periodic_mult *= c.increment_factor

    thermal_mult = 1.0
    if thermo.phase in (tptp.DerivedPhase.LIQUID, tptp.DerivedPhase.SOLID):
        thermal_mult = math.sqrt(max(thermo.B_curv, 1e-6))

    return bare, steric_mult, phase_mult * periodic_mult * thermal_mult


def intermolecular_contact_points_from_network(network: CurvatureContactNetwork) -> int:
    """Steric / intermolecular contact points (proxy for bulk coordination density)."""
    return sum(
        c.undirected_points
        for c in network.contacts
        if c.kind == ContactKind.STERIC_REPULSION
    )


def medium_density_fraction_from_network(network: CurvatureContactNetwork) -> float:
    """
    ρ ∈ [0, 1] vs ice tetrahedral reference (4 contacts).

    Used to scale κ₆ second-order curvature: dilute assays → small ρ, bulk ice → 1.
    """
    return lean.intermolecular_density_fraction(
        intermolecular_contact_points_from_network(network)
    )


def network_binding_feedback(
    network: CurvatureContactNetwork,
    *,
    curvature_contrast_weight: float = 1.0,
) -> NetworkBindingFeedback:
    """
    Full network → κ(ξ) feedback readout (parameter-free).

    ``curvature_contrast_weight`` comes from ``hqiv_shell_aware_binding``:
    1.0 on heavy centres; Hopf lapse dress on homonuclear H₂.
    """
    import hqiv_shell_aware_binding as sab

    bare, steric_mult, phase_mult = _steric_and_phase_multipliers(network)
    networked = bare * steric_mult * phase_mult
    xi = contact_xi_from_network(network)
    kappa_fb = sab.dynamic_binding_feedback_at_xi_weighted(xi, curvature_contrast_weight)
    n_periph = len([n for n in network.nodes if n.z_nuclear == 1 and any(
        x.z_nuclear > 1 for x in network.nodes
    )])

    return NetworkBindingFeedback(
        compton_triplet=network.compton_triplet,
        contact_xi=xi,
        bare_vev_geometric_mean=bare,
        networked_vev_geometric_mean=networked,
        steric_multiplier=steric_mult,
        phase_multiplier=phase_mult,
        geometry_alignment_factor=network_geometry_alignment_factor(network),
        curvature_feedback_at_xi=kappa_fb,
        peripheral_hydrogen_count=n_periph,
        h_h_repulsive_contact_points=ncb.peripheral_h_h_repulsive_contact_points(n_periph),
    )


def compton_angles_for_surplus(network: CurvatureContactNetwork) -> tuple[float, float, float]:
    """Bond-averaged Compton angles for horizon surplus (relaxed geometry)."""
    return s2g.mean_compton_angles_from_bonds(
        covalent_bond_geometries(network),
        network.compton_triplet,
    )


def _cluster_deficit_contacts(nodes: tuple[NetworkNode, ...]) -> list[NetworkContact]:
    return [
        NetworkContact(
            kind=ContactKind.CLUSTER_DEFICIT,
            i=n.index,
            j=None,
            contacts_at_i=1,
            contacts_at_j=0,
            undirected_points=1,
            distance_angstrom=None,
            geff_theta=None,
            weight=1.0,
            increment_factor=n.node_vev_factor,
        )
        for n in nodes
        if n.mass_number > 1
    ]


def _hyperclosure_contact(bonds: tuple[BondGeometry, ...]) -> NetworkContact | None:
    if len(bonds) < 2:
        return None
    return NetworkContact(
        kind=ContactKind.HYPERCLOSURE,
        i=0,
        j=None,
        contacts_at_i=len(bonds),
        contacts_at_j=0,
        undirected_points=len(bonds),
        distance_angstrom=None,
        geff_theta=None,
        weight=1.0 / math.sqrt(float(len(bonds))),
        increment_factor=1.0,
    )


def steric_repulsion_increment(
    *,
    contact_points: int,
    n_peripheral_h: int,
) -> float:
    """Molecular-level multiplier (CH₄ tetrahedral uses full rule)."""
    if contact_points <= 0 or n_peripheral_h < 2:
        return 1.0
    triplet = (1, 1, 1)
    theta = cbs.contact_phase_theta_rad(triplet)
    geff = cbs.outside_contact_coupling(theta)
    if n_peripheral_h == 4:
        return 1.0 + GAMMA * STRONG_FRAC * geff * (contact_points / 3.0)
    if n_peripheral_h == 3:
        return 1.0 + 0.35 * GAMMA * STRONG_FRAC * geff * (contact_points / 4.0)
    return 1.0 + 0.15 * GAMMA * STRONG_FRAC * geff * (contact_points / 4.0)


def _bonds_with_backbone_angles(
    bonds: tuple[BondGeometry, ...],
    backbone: tuple[s2g.BackboneDihedral, ...],
) -> tuple[BondGeometry, ...]:
    """Peptide backbone (φ, ψ): set ``bond_angle_rad`` on consecutive residue bonds."""
    if not backbone:
        return bonds
    phi_by_res = {d.residue_index: d.phi_rad for d in backbone}
    psi_by_res = {d.residue_index: d.psi_rad for d in backbone}
    out: list[BondGeometry] = []
    for bond in bonds:
        ang = bond.bond_angle_rad
        j = bond.frag_j
        if ang is None and j in psi_by_res and (j - 1) in phi_by_res:
            ang = s2g.backbone_peptide_bond_angle_rad(phi_by_res[j - 1], psi_by_res[j])
        out.append(
            BondGeometry(
                bond.frag_i,
                bond.frag_j,
                bond.distance_angstrom,
                bond_angle_rad=ang,
            )
        )
    return tuple(out)


def _lattice_repeats_from_phase(
    thermo: tptp.DerivedThermodynamicState,
    *,
    unit_cell: tuple[int, int, int] = (1, 1, 1),
) -> tuple[int, int, int]:
    if thermo.phase != tptp.DerivedPhase.SOLID or thermo.periodic_weight <= 0.0:
        return (1, 1, 1)
    scale = max(1, int(round(1.0 + thermo.periodic_weight)))
    return (scale, scale, scale) if unit_cell == (1, 1, 1) else unit_cell


def build_network_from_molecule(
    name: str,
    fragments: tuple[FragmentConfig, ...],
    bonds: tuple[BondGeometry, ...],
    *,
    environment: tptp.ThermodynamicEnvironment | None = None,
    material_binding_ev: float | None = None,
    lattice_unit_cell: tuple[int, int, int] = (1, 1, 1),
    backbone_dihedrals: tuple[s2g.BackboneDihedral, ...] = (),
    medium_density_fraction: float | None = None,
) -> CurvatureContactNetwork:
    env = environment or tptp.ThermodynamicEnvironment.stp()

    nodes = tuple(_node_from_fragment(i, f) for i, f in enumerate(fragments))
    triplet = chemistry_compton_triplet(fragments)
    peripheral = _peripheral_h_indices(nodes)
    contacts: list[NetworkContact] = []
    contacts.extend(_cluster_deficit_contacts(nodes))
    bonds_use = _bonds_with_backbone_angles(bonds, backbone_dihedrals)
    contacts.extend(_bond_contacts(nodes, bonds_use, molecule_name=name, medium_density_fraction=0.0))
    contacts.extend(_infer_steric_contacts(nodes, peripheral))
    hc = _hyperclosure_contact(bonds)
    if hc is not None:
        contacts.append(hc)

    coordination: dict[int, int] = {n.index: 0 for n in nodes}
    for c in contacts:
        if c.kind == ContactKind.COVALENT_BOND and c.j is not None:
            coordination[c.i] = coordination.get(c.i, 0) + 1
            coordination[c.j] = coordination.get(c.j, 0) + 1
        if c.kind == ContactKind.STERIC_REPULSION:
            coordination[c.i] = coordination.get(c.i, 0) + c.contacts_at_i

    z_max = max(coordination.values()) if coordination else 1

    inter_contacts = sum(
        c.undirected_points
        for c in contacts
        if c.kind == ContactKind.STERIC_REPULSION
    )
    xi_compton = lean.xi_from_compton_triplet(triplet)
    mat = tptp.material_scales_from_contact_network(
        name,
        contacts=len(contacts),
        intermolecular_contacts=inter_contacts,
        binding_ev=material_binding_ev,
        contact_xi=xi_compton,
    )
    thermo = tptp.derive_phase(env, mat)
    rho = (
        min(1.0, max(0.0, medium_density_fraction))
        if medium_density_fraction is not None
        else medium_density_fraction_from_network(
            CurvatureContactNetwork(
                name=name,
                thermo=thermo,
                nodes=nodes,
                contacts=tuple(contacts),
                compton_triplet=triplet,
                coordination={},
                lattice_repeats=(1, 1, 1),
            )
        )
    )
    if mat.bulk_condensed:
        rho = max(rho, tptp.resolved_medium_density_fraction(mat))
    contacts = [
        c
        for c in contacts
        if c.kind != ContactKind.COVALENT_BOND
    ]
    contacts.extend(
        _bond_contacts(
            nodes,
            bonds_use,
            molecule_name=name,
            medium_density_fraction=rho,
        )
    )
    lattice_repeats = _lattice_repeats_from_phase(thermo, unit_cell=lattice_unit_cell)

    if thermo.phase == tptp.DerivedPhase.SOLID and lattice_repeats != (1, 1, 1):
        rx, ry, rz = lattice_repeats
        images = (rx - 1) + (ry - 1) + (rz - 1)
        if images > 0 and bonds:
            contacts.append(
                NetworkContact(
                    kind=ContactKind.PERIODIC_IMAGE,
                    i=0,
                    j=None,
                    contacts_at_i=images * len(bonds),
                    contacts_at_j=0,
                    undirected_points=images,
                    distance_angstrom=None,
                    geff_theta=None,
                    weight=thermo.periodic_weight * max(z_max, 1),
                    increment_factor=1.0 + 0.1 * images * thermo.periodic_weight,
                )
            )

    return CurvatureContactNetwork(
        name=name,
        thermo=thermo,
        nodes=nodes,
        contacts=tuple(contacts),
        compton_triplet=triplet,
        coordination=coordination,
        lattice_repeats=lattice_repeats,
        medium_density_fraction=rho,
    )


def _compton_slot_mass_numbers(
    network: CurvatureContactNetwork,
) -> tuple[int, int, int, int]:
    """(m_s, m_p, m_h, n_periph_h) for triplet geomean."""
    triplet = network.compton_triplet
    heavy_a = max(n.mass_number for n in network.nodes)
    light_a = min(n.mass_number for n in network.nodes)
    n_periph = len([n for n in network.nodes if n.z_nuclear == 1 and heavy_a > 1])
    m_s, m_p, m_h = triplet
    return m_s, m_p, m_h, n_periph


def networked_vev_geometric_mean(network: CurvatureContactNetwork) -> float:
    """
    Network rule for the TUFT vev geometric mean.

    1. Compton-triplet slot dress (cluster deficit on nuclear spine).
    2. Steric repulsion contacts (opposite sign — adds mass back).
    3. Phase coordination factor (liquid/solid).
    """
    fb = network_binding_feedback(network)
    return fb.networked_vev_geometric_mean


def bare_vev_geometric_mean(network: CurvatureContactNetwork) -> float:
    return ncb.vev_geometric_mean_from_triplet(network.compton_triplet)


def contact_report(network: CurvatureContactNetwork) -> dict[str, Any]:
    return {
        "name": network.name,
        "thermodynamic": tptp.phase_report(network.thermo),
        "compton_triplet_m": list(network.compton_triplet),
        "lattice_repeats": list(network.lattice_repeats),
        "networked_vev_geometric_mean": networked_vev_geometric_mean(network),
        "bare_vev_geometric_mean": bare_vev_geometric_mean(network),
        "geometry_alignment_factor": network_geometry_alignment_factor(network),
        "network_binding_feedback": asdict(
            network_binding_feedback(network)
        ),
        "contact_xi": contact_xi_from_network(network),
        "compton_angles_for_surplus_rad": list(compton_angles_for_surplus(network)),
        "nodes": [asdict(n) for n in network.nodes],
        "nodes_geometry": [
            n.shell_geometry.to_dict() if n.shell_geometry is not None else None
            for n in network.nodes
        ],
        "contacts": [
            {
                **asdict(c),
                "kind": c.kind.value,
                "bond_geometry": (
                    c.bond_geometry.to_dict() if c.bond_geometry is not None else None
                ),
            }
            for c in network.contacts
        ],
        "coordination": network.coordination,
        "rules": {
            "cluster_deficit": "node: tuftVevFactorNetworkedAtCluster from cluster_mass/(A*m_p)",
            "covalent_bond": "edge: G_eff(theta) at Compton contact, geometry weight 1/(1+d/a0)",
            "steric_repulsion": "peripheral H: n_H*contacts_per_H/2 points; CH4 full, NH3/H2O reduced",
            "hyperclosure": ">=2 bonds: graph factor 1/sqrt(n_bonds)",
            "periodic_image": "solid: (Rx-1+Ry-1+Rz-1)*n_bonds images",
            "phase": "derived from (T,P) via hqiv_thermodynamic_phase_from_tp",
            "coordination_fraction": network.thermo.coordination_fraction,
            "contact_persistence": network.thermo.contact_persistence,
        },
    }


def build_protein_network(
    name: str,
    *,
    n_residues: int,
    environment: tptp.ThermodynamicEnvironment | None = None,
    binding_ev_per_contact: float = 0.5,
    backbone_dihedrals: tuple[s2g.BackboneDihedral, ...] = (),
) -> CurvatureContactNetwork:
    """
    Scaffold protein chain as repeated peptide-like nodes for folding / materials studies.

    Full folding geometry (contacts from structure) is a downstream input layer.
    """
    env = environment or tptp.ThermodynamicEnvironment.protein_cytosol()
    frags = tuple(
        FragmentConfig("C", 6, 4) if i % 2 == 0 else FragmentConfig("N", 7, 5)
        for i in range(max(n_residues, 1))
    )
    bonds = tuple(
        BondGeometry(i, i + 1, 1.38) for i in range(len(frags) - 1)
    )
    return build_network_from_molecule(
        name,
        frags,
        bonds,
        environment=env,
        material_binding_ev=binding_ev_per_contact * max(n_residues, 1),
        backbone_dihedrals=backbone_dihedrals,
    )


def example_catalog() -> list[CurvatureContactNetwork]:
    from hqiv_dynamic_binding_chart import GMTKN55_SUITE

    nets = []
    for bench in GMTKN55_SUITE:
        nets.append(
            build_network_from_molecule(
                bench.name,
                bench.fragments,
                bench.bonds,
                environment=tptp.ThermodynamicEnvironment.stp(),
            )
        )
    nets.append(
        build_network_from_molecule(
            "ice_Ih_scaffold",
            (
                FragmentConfig("O", 8, 8),
                FragmentConfig("H", 1, 1),
                FragmentConfig("H", 1, 1),
            ),
            (BondGeometry(0, 1, 0.9572), BondGeometry(0, 2, 0.9572)),
            environment=tptp.ThermodynamicEnvironment(150.0, tptp.STP_PRESSURE_PA),
            lattice_unit_cell=(2, 2, 2),
        )
    )
    nets.append(
        build_protein_network("protein_12mer", n_residues=12),
    )
    return nets


def main() -> None:
    parser = argparse.ArgumentParser(description="Curvature contact network rule catalog")
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()

    catalog = [contact_report(n) for n in example_catalog()]
    payload = {
        "source": "scripts/hqiv_curvature_contact_network.py",
        "lean_module": "Hqiv.QuantumChemistry.CurvatureContactNetwork",
        "contact_kinds": [k.value for k in ContactKind],
        "derived_phases": [p.value for p in tptp.DerivedPhase],
        "networks": catalog,
    }
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(payload, indent=2) + "\n")

    print("Curvature contact network rules")
    print("=" * 60)
    for row in catalog:
        th = row["thermodynamic"]
        print(
            f"{row['name']:12s} T={th['temperature_K']:6.1f}K  "
            f"phase={th['derived_phase']:18s} "
            f"vev_net={row['networked_vev_geometric_mean']:.4f} "
            f"contacts={len(row['contacts'])}"
        )
    print(f"\nWrote {args.json_out}")


if __name__ == "__main__":
    main()

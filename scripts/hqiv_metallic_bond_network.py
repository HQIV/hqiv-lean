#!/usr/bin/env python3
"""
Metallic bond network — parallel spine to ionic ``CurvatureContactNetwork``.

Lean mirrors:
  • ``Hqiv.Geometry.BondedHorizonCasimir`` — ``metallicPeelSurplus``
  • ``Hqiv.QuantumChemistry.MetallicContactSlot`` — peel surplus bridge
  • ``Hqiv.QuantumChemistry.CurvatureContactNetwork`` — ``metallicBond``

**Canonical pure API:** ``hqvmpy/src/pyhqiv/chemistry/metallic_contact.py`` (installable
``pyhqiv``). This script builds network witnesses + JSON for HQIV_LEAN integration.

No tabulated cohesive energies or fitted potentials:
  • ``MetalFragment`` — core (peel) vs valence (bulk) electron partition
  • Lattice binding from ``metallic_peel_surplus_ev`` + symmetric valence merge
  • Nearest-neighbor distance from nested-WF homonuclear ladder + γ/8 delocalization dress

Run:
  PYTHONPATH=scripts python3 scripts/hqiv_metallic_bond_network.py
  PYTHONPATH=scripts python3 scripts/hqiv_metallic_bond_network.py --metal Cu
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

import bonded_horizon_casimir_float as bhc
import hqiv_chemistry_tuft_dynamics as ctd
import hqiv_curvature_bond_state as cbs
import hqiv_derived_chemistry as hdc
import hqiv_electronic_valence_shells as evs
import hqiv_lean_physics_primitives as lean
from fragment_aware_bonded_horizon import BOHR_RADIUS_ANGSTROM, BondGeometry, FragmentConfig

import hqiv_curvature_contact_network as ccn

AVOGADRO = 6.02214076e23


def metallic_bonding_capacity(z: int) -> int:
    """Octet-side bonding capacity — Lean ``bondingCapacityOfValence`` pipeline."""
    import hqiv_particle_shell_structure as pss

    return int(pss.bonding_capacity(int(z)))


def metallic_valence_count(z: int) -> int:
    """Bonding valence for metal family keys (outer s+p / open-d residual)."""
    import hqiv_particle_shell_structure as pss

    return int(pss.bonding_valence_electron_count(int(z)))


def is_metallic_element(z: int) -> bool:
    """
    First-principles metal predicate (no Z-set):

    * left-side / p-block metals shed to close: ``1 ≤ cap ≤ 3`` and ``V = cap``;
    * transition / peel metals: ``cap = 0`` with ``Z > 2`` (d-block peel surplus).

    Nonmetals gain to close (``V > cap``): F has cap=1 but V=7 → not metal.
    Si/Ge have cap=4 → covalent network, not metallic.
    """
    z = int(z)
    if z <= 2:
        return False
    cap = metallic_bonding_capacity(z)
    if cap == 0:
        return True
    if 1 <= cap <= 3:
        return metallic_valence_count(z) == cap
    return False


def metallic_coordination(z: int) -> int:
    """
    Bravais coordination from shell capacity (replaces alkali Z-set):

    monovalent shed metals (``cap = V = 1``) → BCC CN=8;
    else close-pack CN=12.
    """
    if metallic_bonding_capacity(z) == 1 and metallic_valence_count(z) == 1:
        return 8
    return 12


@dataclass(frozen=True)
class MetalFragment:
    """Neutral metal atom: peel = inert core, bulk = conduction / outer-principal electrons."""

    label: str
    z_nuclear: int
    electrons: int

    @property
    def n_bulk(self) -> int:
        """
        Delocalized conduction electrons from the highest Madelung principal shell.

        Main-group alkali/alkaline recover the usual valence count.  Transition metals
        (e.g. Cu) expose only the outer ``ns`` electrons as bulk, with ``(n−1)d`` in the peel —
        not the noble-gas residual (which would count all of 3d+4s as “valence”).

        When ``(n−1)d`` is nearly filled (≥ 8 of 10), Madelung places 4s² before completing
        3d¹⁰; the conduction slot is the residual ``s`` capacity toward a closed ``d¹⁰ s¹``
        peel narrative (coinage / noble metals), capped at one bulk electron.
        """
        import hqiv_atom_construction as ac

        cfg = ac.electron_configuration(self.z_nuclear)
        if not cfg:
            return max(evs.valence_electron_count(self.z_nuclear), 1)
        top_n = max(n for n, _l in cfg)
        outer_s = sum(1 for n, l in cfg if n == top_n and l == 0)
        d_prev = sum(1 for n, l in cfg if n == top_n - 1 and l == 2)
        if d_prev >= 8:
            return max(min(outer_s, 1), 1) if outer_s else 1
        outer = sum(1 for n, _l in cfg if n == top_n)
        return max(outer, 1)

    @property
    def n_peel(self) -> int:
        """Localized core + d-band electrons."""
        return max(self.electrons - self.n_bulk, 0)

    @property
    def mass_amu(self) -> float:
        from hqiv_lab.crystal_geometry import closed_atomic_mass_amu

        return closed_atomic_mass_amu(self.z_nuclear)

    def to_fragment_config(self) -> FragmentConfig:
        return FragmentConfig(self.label, self.z_nuclear, self.electrons)


@dataclass(frozen=True)
class MetallicLattice:
    """Homonuclear metal lattice witness (nearest-neighbor contact)."""

    name: str
    metal: MetalFragment
    nearest_neighbor_angstrom: float
    coordination: int

    @property
    def formula_mass_amu(self) -> float:
        return self.metal.mass_amu


def metallic_nearest_neighbor_angstrom(z: int) -> float:
    """
    Unified nearest-neighbor distance: ``√(nested_wf · φ_pack)`` from ``crystal_geometry``.

    Replaces the standalone φ(m)/Z branch so network and Lean ``CrystalContactGeometry``
    share one canonical metallic nn readout.
    """
    from hqiv_lab.crystal_geometry import metallic_unified_nearest_neighbor_angstrom

    return metallic_unified_nearest_neighbor_angstrom(z, n_coord=metallic_coordination(z))


def metallic_peel_surplus_ev(metal: MetalFragment) -> float:
    """Intra-atomic ``metallicPeelSurplus`` on bulk vs core peel."""
    return bhc.metallic_peel_surplus_ev(metal.n_bulk, metal.n_peel)


def metallic_valence_merge_surplus_ev(metal: MetalFragment) -> float:
    """
    Inter-atomic symmetric valence merge: joint ``2·n_val`` sea vs two bulk fragments.

    Same ``bondHorizonSurplus`` slot as covalent dimer; electron partition is valence-only.
    """
    n = metal.n_bulk
    return bhc.bond_horizon_surplus_ev(2 * n, n, n)


def metallic_lattice_binding_ev_per_contact(
    metal: MetalFragment,
    *,
    distance_angstrom: float,
    coordination: int,
) -> float:
    """
    Contact binding from peel surplus × valence merge × lattice factor × coordination dress.

    Coordination dress ``1 + (4/8)/n_coord`` from shared Fermi-sea closure on the lattice graph.
    """
    peel = abs(metallic_peel_surplus_ev(metal))
    merge = abs(metallic_valence_merge_surplus_ev(metal))
    surplus = max(peel, merge * 0.5)
    d_lat = distance_angstrom / BOHR_RADIUS_ANGSTROM
    lattice_factor = 1.0 / (1.0 + d_lat)
    n_coord = max(coordination, 1)
    coord_dress = 1.0 + lean.STRONG_CHANNEL_FRACTION / float(n_coord)
    valence_frac = metal.n_bulk / max(metal.electrons, 1)
    return surplus * lattice_factor * coord_dress * valence_frac


def metallic_lattice_contact_weight(lattice: MetallicLattice) -> float:
    """Horizon contact weight ``1/(1+d/a₀)`` on the M–M bond."""
    return 1.0 / (1.0 + lattice.nearest_neighbor_angstrom / BOHR_RADIUS_ANGSTROM)


def metallic_lattice_contact_lock(lattice: MetallicLattice) -> float:
    """Binding / surplus dress on the metallic contact (network increment scale)."""
    bind = metallic_lattice_binding_ev_per_contact(
        lattice.metal,
        distance_angstrom=lattice.nearest_neighbor_angstrom,
        coordination=lattice.coordination,
    )
    ref = max(abs(metallic_peel_surplus_ev(lattice.metal)), 0.05)
    return min(1.0, bind / ref)


def metallic_melt_density_ratio(
    lattice: MetallicLattice,
    *,
    n_coord: int | None = None,
) -> float:
    """
    ρ_melt/ρ_solid (solid denser) from metallic periodic-image release on melt.

    Mirrors ionic ``ionic_melt_density_ratio`` with ``(γ/α)/n_coord`` motif ladder.
    """
    from hqiv_lab.coordination import IntermolecularMotif, melt_motif_relative_scale

    n = n_coord if n_coord is not None else lattice.coordination
    dw = metallic_lattice_contact_weight(lattice)
    contact_lock = metallic_lattice_contact_lock(lattice)
    motif_scale = melt_motif_relative_scale(
        IntermolecularMotif.METALLIC_LATTICE,
        max(n, 1),
        z_heavy=lattice.metal.z_nuclear,
    )
    return max(lean.GAMMA / 4.0, 1.0 - motif_scale * contact_lock * (1.0 - dw))


def classify_bond_kind(
    name: str,
    z_i: int,
    z_j: int,
) -> ccn.ContactKind:
    """Metallic vs covalent edge from homonuclear simple-metal pairs."""
    key = name.upper()
    if key in NAMED_METALLIC_LATTICES:
        return ccn.ContactKind.METALLIC_BOND
    if z_i == z_j and is_metallic_element(z_i):
        return ccn.ContactKind.METALLIC_BOND
    return ccn.ContactKind.COVALENT_BOND


def _node_from_metal_fragment(index: int, frag: MetalFragment) -> ccn.NetworkNode:
    return ccn._node_from_fragment(index, frag.to_fragment_config())


def _metallic_bond_contact(
    nodes: tuple[ccn.NetworkNode, ...],
    bond: BondGeometry,
    *,
    metal: MetalFragment,
    coordination: int,
) -> ccn.NetworkContact:
    a = nodes[bond.frag_i]
    b = nodes[bond.frag_j]
    dw = 1.0 / (1.0 + bond.distance_angstrom / BOHR_RADIUS_ANGSTROM)
    bind_ev = metallic_lattice_binding_ev_per_contact(
        metal,
        distance_angstrom=bond.distance_angstrom,
        coordination=coordination,
    )
    triplet = evs.chemistry_compton_triplet((metal.to_fragment_config(), metal.to_fragment_config()))
    theta = cbs.contact_phase_theta_rad(triplet)
    geff = cbs.outside_contact_coupling(theta)
    ref = max(abs(metallic_peel_surplus_ev(metal)), 0.05)
    inc = geff * (bind_ev / ref)
    return ccn.NetworkContact(
        kind=ccn.ContactKind.METALLIC_BOND,
        i=bond.frag_i,
        j=bond.frag_j,
        contacts_at_i=1,
        contacts_at_j=1,
        undirected_points=1,
        distance_angstrom=bond.distance_angstrom,
        geff_theta=theta,
        weight=dw,
        increment_factor=inc,
        bond_geometry=None,
    )


def build_metallic_lattice_network(
    lattice: MetallicLattice,
    *,
    environment: Any | None = None,
) -> ccn.CurvatureContactNetwork:
    """Homonuclear metal pair with ``metallicBond`` contact (lattice seed witness)."""
    import hqiv_thermodynamic_phase_from_tp as tptp

    frags = (lattice.metal.to_fragment_config(), lattice.metal.to_fragment_config())
    bonds = (BondGeometry(0, 1, lattice.nearest_neighbor_angstrom),)
    env = environment or tptp.ThermodynamicEnvironment.stp()
    nodes = tuple(_node_from_metal_fragment(i, lattice.metal) for i in range(2))
    triplet = evs.chemistry_compton_triplet(frags)
    contacts: list[ccn.NetworkContact] = []
    contacts.extend(ccn._cluster_deficit_contacts(nodes))
    contacts.append(
        _metallic_bond_contact(
            nodes,
            bonds[0],
            metal=lattice.metal,
            coordination=lattice.coordination,
        )
    )
    coordination = {0: 1, 1: 1}
    xi = lean.xi_from_compton_triplet(triplet)
    bind = metallic_lattice_binding_ev_per_contact(
        lattice.metal,
        distance_angstrom=lattice.nearest_neighbor_angstrom,
        coordination=lattice.coordination,
    )
    mat = tptp.material_scales_from_contact_network(
        lattice.name,
        contacts=len(contacts),
        intermolecular_contacts=lattice.coordination,
        binding_ev=bind,
        contact_xi=xi,
    )
    thermo = tptp.derive_phase(env, mat)
    return ccn.CurvatureContactNetwork(
        name=lattice.name,
        thermo=thermo,
        nodes=nodes,
        contacts=tuple(contacts),
        compton_triplet=triplet,
        coordination=coordination,
        lattice_repeats=(1, 1, 1),
    )


def metal_lattice_from_z(label: str, z: int) -> MetallicLattice:
    """Build lattice witness from atomic number."""
    return MetallicLattice(
        name=label,
        metal=MetalFragment(label, z, z),
        nearest_neighbor_angstrom=metallic_nearest_neighbor_angstrom(z),
        coordination=metallic_coordination(z),
    )


# Canonical metal witnesses.
LI_LATTICE = metal_lattice_from_z("Li", 3)
NA_LATTICE = metal_lattice_from_z("Na", 11)
AL_LATTICE = metal_lattice_from_z("Al", 13)
CU_LATTICE = metal_lattice_from_z("Cu", 29)

METALLIC_LATTICES: dict[str, MetallicLattice] = {
    "LI": LI_LATTICE,
    "NA": NA_LATTICE,
    "AL": AL_LATTICE,
    "CU": CU_LATTICE,
}

NAMED_METALLIC_LATTICES = frozenset(METALLIC_LATTICES.keys())


def metal_witness(lattice: MetallicLattice) -> dict[str, Any]:
    net = build_metallic_lattice_network(lattice)
    peel = metallic_peel_surplus_ev(lattice.metal)
    merge = metallic_valence_merge_surplus_ev(lattice.metal)
    bind = metallic_lattice_binding_ev_per_contact(
        lattice.metal,
        distance_angstrom=lattice.nearest_neighbor_angstrom,
        coordination=lattice.coordination,
    )
    return {
        "metal": lattice.name,
        "Z": lattice.metal.z_nuclear,
        "n_bulk": lattice.metal.n_bulk,
        "n_peel": lattice.metal.n_peel,
        "mass_amu": lattice.metal.mass_amu,
        "coordination": lattice.coordination,
        "nearest_neighbor_angstrom": lattice.nearest_neighbor_angstrom,
        "metallic_peel_surplus_ev": peel,
        "valence_merge_surplus_ev": merge,
        "lattice_binding_ev_per_contact": bind,
        "melt_density_ratio": metallic_melt_density_ratio(lattice),
        "contact_xi": net.compton_triplet,
        "network_contacts": [c.kind.value for c in net.contacts],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Metallic bond network witnesses.")
    parser.add_argument("--metal", default="Cu", choices=("Li", "Na", "Al", "Cu", "all"))
    parser.add_argument("--json-out", type=Path, default=None)
    args = parser.parse_args()
    keys = list(METALLIC_LATTICES) if args.metal.lower() == "all" else [args.metal.upper()]
    rows = [metal_witness(METALLIC_LATTICES[k]) for k in keys]
    payload = {"metals": rows}
    for row in rows:
        print(
            f"{row['metal']}: peel={row['metallic_peel_surplus_ev']:.4f} eV  "
            f"merge={row['valence_merge_surplus_ev']:.4f} eV  "
            f"bind/contact={row['lattice_binding_ev_per_contact']:.4f} eV  "
            f"nn={row['nearest_neighbor_angstrom']:.3f} Å  "
            f"Z_coord={row['coordination']}"
        )
    if args.json_out:
        args.json_out.write_text(json.dumps(payload, indent=2) + "\n")


if __name__ == "__main__":
    main()

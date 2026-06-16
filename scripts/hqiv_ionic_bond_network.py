#!/usr/bin/env python3
"""
Ionic bond network — parallel spine to covalent ``CurvatureContactNetwork``.

Lean mirrors:
  • ``Hqiv.Geometry.BondedHorizonCasimir`` — ``ionicBondSurplus``
  • ``Hqiv.QuantumChemistry.CurvatureContactNetwork`` — ``ionicBond``, ``ionSolvation``

No tabulated masses, hydration shells, or fitted potentials:
  • ``IonicFragment`` — formal charge from Z and electron count
  • Lattice binding from ``ionic_bond_surplus_ev``
  • Hydration contacts from ion–H₂O cluster geometry (VSEPR motif)
  • Mass from ``hqiv_derived_chemistry.derived_atomic_mass_amu``

Run:
  PYTHONPATH=scripts python3 scripts/hqiv_ionic_bond_network.py
  PYTHONPATH=scripts python3 scripts/hqiv_ionic_bond_network.py --salt NaCl
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
import hqiv_curvature_bond_state as cbs
import hqiv_derived_chemistry as hdc
import hqiv_electronic_valence_shells as evs
import hqiv_lean_physics_primitives as lean
import hqiv_nuclear_curvature_binding as ncb
from fragment_aware_bonded_horizon import BOHR_RADIUS_ANGSTROM, BondGeometry, FragmentConfig

import hqiv_curvature_contact_network as ccn
import hqiv_s2_binding_geometry as s2g

AVOGADRO = 6.02214076e23
EV_TO_J = 1.602176634e-19
K_B = 1.380649e-23
FARADAY = 96485.33212
HBAR_J_S = 1.054571817e-34
E_CHARGE = 1.602176634e-19


@dataclass(frozen=True)
class IonicFragment:
    """Charged fragment: electron count fixes formal charge (not a fit knob)."""

    label: str
    z_nuclear: int
    electrons: int

    @property
    def formal_charge(self) -> int:
        return self.z_nuclear - self.electrons

    @property
    def mass_amu(self) -> float:
        return hdc.derived_atomic_mass_amu(self.z_nuclear, self.electrons)

    def to_fragment_config(self) -> FragmentConfig:
        return FragmentConfig(self.label, self.z_nuclear, self.electrons)


@dataclass(frozen=True)
class IonicSalt:
    """1:1 salt from alkali–halogen electron transfer (+1 / −1)."""

    name: str
    cation: IonicFragment
    anion: IonicFragment
    lattice_bond_angstrom: float

    @property
    def formula_mass_amu(self) -> float:
        return self.cation.mass_amu + self.anion.mass_amu

    @property
    def dissolved_particles(self) -> int:
        return 2


def alkali_halide_fragments(
    cation_label: str,
    z_cation: int,
    anion_label: str,
    z_anion: int,
) -> tuple[IonicFragment, IonicFragment]:
    """M⁺ loses one valence e⁻; X⁻ gains one (alkali halide bookkeeping)."""
    cation = IonicFragment(cation_label, z_cation, z_cation - 1)
    anion = IonicFragment(anion_label, z_anion, z_anion + 1)
    return cation, anion


def ionic_bond_surplus_ev(cation: IonicFragment, anion: IonicFragment) -> float:
    """``ionicBondSurplus`` on separated electron seas."""
    return bhc.ionic_bond_surplus_ev(cation.electrons, anion.electrons)


def ionic_lattice_binding_ev_per_contact(
    cation: IonicFragment,
    anion: IonicFragment,
    *,
    distance_angstrom: float,
) -> float:
    """
    Contact binding from horizon surplus × bond lattice factor (same slot as covalent d/a₀).
    """
    surplus = abs(ionic_bond_surplus_ev(cation, anion))
    d_lat = distance_angstrom / BOHR_RADIUS_ANGSTROM
    lattice_factor = 1.0 / (1.0 + d_lat)
    z_vals = [cation.z_nuclear, anion.z_nuclear]
    delta_z = max(z_vals) - min(z_vals)
    z_total = sum(z_vals)
    ionic_dress = 1.0 + (delta_z / max(z_total, 1)) * lattice_factor
    return surplus * ionic_dress


def ionic_lattice_contact_weight(salt: IonicSalt) -> float:
    """Horizon contact weight ``1/(1+d/a₀)`` on the lattice M–X bond."""
    return 1.0 / (1.0 + salt.lattice_bond_angstrom / BOHR_RADIUS_ANGSTROM)


def ionic_lattice_contact_lock(salt: IonicSalt) -> float:
    """Binding / surplus dress on the ionic contact (network increment scale)."""
    bind = ionic_lattice_binding_ev_per_contact(
        salt.cation,
        salt.anion,
        distance_angstrom=salt.lattice_bond_angstrom,
    )
    surplus = abs(ionic_bond_surplus_ev(salt.cation, salt.anion))
    return min(1.0, bind / max(surplus, 1e-6))


def ionic_melt_density_ratio(
    salt: IonicSalt,
    *,
    n_coord: int,
) -> float:
    """
    ρ_melt/ρ_solid (solid denser) from ionic periodic-image release on melt.

    ``1 − melt_motif_scale · contact_lock · (1 − lattice_weight)`` — motif ladder
    and bond-length weight from the ionic network, not a fixed α·strongChannel slot.
    """
    from hqiv_lab.coordination import IntermolecularMotif, melt_motif_relative_scale

    dw = ionic_lattice_contact_weight(salt)
    contact_lock = ionic_lattice_contact_lock(salt)
    z_heavy = max(salt.cation.z_nuclear, salt.anion.z_nuclear)
    motif_scale = melt_motif_relative_scale(
        IntermolecularMotif.IONIC_LATTICE,
        max(n_coord, 1),
        z_heavy=z_heavy,
    )
    return max(lean.GAMMA / 4.0, 1.0 - motif_scale * contact_lock * (1.0 - dw))


_ALKALI_Z = frozenset({3, 11, 19})
_HALOGEN_Z = frozenset({9, 17, 35, 53})


def ionic_fragments_from_neutral_pair(
    label_i: str,
    z_i: int,
    e_i: int,
    label_j: str,
    z_j: int,
    e_j: int,
) -> tuple[IonicFragment, IonicFragment]:
    """Promote neutral GMTKN55 fragments to M⁺ / X⁻ electron counts for surplus."""
    _ = (e_i, e_j)
    # Metal hydride (LiH): metal cation, H⁻ anion.
    if z_i == 1 and z_j > 1:
        return IonicFragment(label_j, z_j, z_j - 1), IonicFragment(label_i, 1, 2)
    if z_j == 1 and z_i > 1:
        return IonicFragment(label_i, z_i, z_i - 1), IonicFragment(label_j, 1, 2)
    # Alkali halide.
    if z_i in _ALKALI_Z and z_j in _HALOGEN_Z:
        return IonicFragment(label_i, z_i, z_i - 1), IonicFragment(label_j, z_j, z_j + 1)
    if z_j in _ALKALI_Z and z_i in _HALOGEN_Z:
        return IonicFragment(label_j, z_j, z_j - 1), IonicFragment(label_i, z_i, z_i + 1)
    # Fallback: lower Z cation, higher Z anion (diagnostic only).
    if z_i <= z_j:
        return IonicFragment(label_i, z_i, max(z_i - 1, 1)), IonicFragment(label_j, z_j, z_j + 1)
    return IonicFragment(label_j, z_j, max(z_j - 1, 1)), IonicFragment(label_i, z_i, z_i + 1)


def classify_bond_kind(
    name: str,
    z_i: int,
    z_j: int,
) -> ccn.ContactKind:
    """Ionic vs covalent edge from named salts and alkali–halogen / metal–H pairs."""
    key = name.upper()
    if key in ("LIH", "NACL", "NACL_LATTICE"):
        return ccn.ContactKind.IONIC_BOND
    pair = frozenset((z_i, z_j))
    if pair & _ALKALI_Z and pair & _HALOGEN_Z:
        return ccn.ContactKind.IONIC_BOND
    if (z_i == 1) ^ (z_j == 1):
        metal_z = z_j if z_i == 1 else z_i
        if metal_z in _ALKALI_Z:
            return ccn.ContactKind.IONIC_BOND
    return ccn.ContactKind.COVALENT_BOND


def _node_from_ionic_fragment(index: int, frag: IonicFragment) -> ccn.NetworkNode:
    fc = frag.to_fragment_config()
    return ccn._node_from_fragment(index, fc)


def _ionic_bond_contact(
    nodes: tuple[ccn.NetworkNode, ...],
    bond: BondGeometry,
    *,
    cation: IonicFragment,
    anion: IonicFragment,
) -> ccn.NetworkContact:
    a = nodes[bond.frag_i]
    b = nodes[bond.frag_j]
    dw = 1.0 / (1.0 + bond.distance_angstrom / BOHR_RADIUS_ANGSTROM)
    bind_ev = ionic_lattice_binding_ev_per_contact(cation, anion, distance_angstrom=bond.distance_angstrom)
    triplet = evs.chemistry_compton_triplet((cation.to_fragment_config(), anion.to_fragment_config()))
    theta = cbs.contact_phase_theta_rad(triplet)
    geff = cbs.outside_contact_coupling(theta)
    inc = geff * (bind_ev / max(abs(bhc.ionic_bond_surplus_ev(1, 1)), 0.05))
    return ccn.NetworkContact(
        kind=ccn.ContactKind.IONIC_BOND,
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


def build_ionic_salt_network(
    salt: IonicSalt,
    *,
    environment: Any | None = None,
) -> ccn.CurvatureContactNetwork:
    """Ion pair network with ``ionicBond`` contact (gas-phase ion pair witness)."""
    import hqiv_thermodynamic_phase_from_tp as tptp

    frags = (salt.cation.to_fragment_config(), salt.anion.to_fragment_config())
    bonds = (BondGeometry(0, 1, salt.lattice_bond_angstrom),)
    env = environment or tptp.ThermodynamicEnvironment.stp()
    nodes = tuple(_node_from_ionic_fragment(i, f) for i, f in enumerate((salt.cation, salt.anion)))
    triplet = evs.chemistry_compton_triplet(frags)
    contacts: list[ccn.NetworkContact] = []
    contacts.extend(ccn._cluster_deficit_contacts(nodes))
    contacts.append(
        _ionic_bond_contact(
            nodes,
            bonds[0],
            cation=salt.cation,
            anion=salt.anion,
        )
    )
    coordination = {0: 1, 1: 1}
    xi = lean.xi_from_compton_triplet(triplet)
    mat = tptp.material_scales_from_contact_network(
        salt.name,
        contacts=len(contacts),
        intermolecular_contacts=1,
        binding_ev=ionic_lattice_binding_ev_per_contact(
            salt.cation, salt.anion, distance_angstrom=salt.lattice_bond_angstrom
        ),
        contact_xi=xi,
    )
    thermo = tptp.derive_phase(env, mat)
    return ccn.CurvatureContactNetwork(
        name=salt.name,
        thermo=thermo,
        nodes=nodes,
        contacts=tuple(contacts),
        compton_triplet=triplet,
        coordination=coordination,
        lattice_repeats=(1, 1, 1),
    )


def ion_hydration_cluster_spec(
    ion: IonicFragment,
    host: str = "H2O",
) -> tuple[FragmentConfig, ...]:
    """Ion + single H₂O for motif inference (first solvation shell seed)."""
    from hqiv_lab.spec import MoleculeSpec

    host_spec = MoleculeSpec.from_chart_name(host)
    host_frag = host_spec.fragments[0]
    return (ion.to_fragment_config(), host_frag)


def derived_hydration_contact_count(ion: IonicFragment, host: str = "H2O") -> int:
    """
    Hydration shell contacts from ion charge + host H-bond motif (no n=6 table).

    Tetrahedral water host: ``n_h ≈ 4 · (1 + γ·|q|)`` primary coordination sphere.
    Cross-check with ion–single-H₂O cluster VSEPR when that exceeds the charge slot.
    """
    from hqiv_lab.coordination import infer_monomer_geometry
    from hqiv_lab.spec import MoleculeSpec

    q = max(abs(ion.formal_charge), 1)
    if host.upper() == "H2O":
        charge_slot = int(round(4.0 * (1.0 + lean.GAMMA * float(q))))
    else:
        charge_slot = max(q + 1, 2)

    host_spec = MoleculeSpec.from_chart_name(host)
    ion_frag = ion.to_fragment_config()
    frags = (ion_frag,) + host_spec.fragments
    centre_bonds = (
        BondGeometry(0, 1, host_spec.bonds[0].distance_angstrom),
    )
    cluster = MoleculeSpec(
        name=f"{ion.label}+{host}",
        fragments=frags,
        bonds=centre_bonds,
    )
    mono = infer_monomer_geometry(cluster)
    vsepr_slot = max(mono.intermolecular_contacts, mono.n_bonds_at_heavy + mono.lone_pair_count)
    return max(charge_slot, vsepr_slot)


def ion_solvation_hopping_activation_ev(ion: IonicFragment, host: str = "H2O") -> float:
    """E_a,ion ≈ E_contact,host / (n_hydration · (1+α))."""
    import hqiv_phase_material_response as pmr

    n_h = max(derived_hydration_contact_count(ion, host), 1)
    return pmr.intermolecular_binding_ev_per_contact(host) / (n_h * (1.0 + lean.ALPHA))


def build_ion_solvation_contacts(
    ion: IonicFragment,
    host: str = "H2O",
) -> list[ccn.NetworkContact]:
    """``ionSolvation`` contacts: one per derived hydration shell slot."""
    import hqiv_phase_material_response as pmr
    from hqiv_lab.spec import MoleculeSpec

    host_spec = MoleculeSpec.from_chart_name(host)
    n_contacts = derived_hydration_contact_count(ion, host)
    triplet = evs.chemistry_compton_triplet(host_spec.fragments)
    theta = cbs.contact_phase_theta_rad(triplet)
    geff = cbs.outside_contact_coupling(theta)
    e_contact = ion_solvation_hopping_activation_ev(ion, host) * (1.0 + lean.ALPHA)
    e_host = pmr.intermolecular_binding_ev_per_contact(host)
    inc = geff * (e_contact / max(e_host, 0.05))
    span = host_spec.bonds[0].distance_angstrom
    contacts: list[ccn.NetworkContact] = []
    for k in range(n_contacts):
        contacts.append(
            ccn.NetworkContact(
                kind=ccn.ContactKind.ION_SOLVATION,
                i=0,
                j=k + 1,
                contacts_at_i=n_contacts,
                contacts_at_j=1,
                undirected_points=1,
                distance_angstrom=span,
                geff_theta=theta,
                weight=1.0 / (1.0 + span / BOHR_RADIUS_ANGSTROM),
                increment_factor=inc,
                bond_geometry=None,
            )
        )
    return contacts


def eyring_ion_mobility_m2_per_vs(
    ion: IonicFragment,
    *,
    host: str = "H2O",
    temperature_k: float,
    rho_curv: float,
) -> float:
    """μ from solvation-hop Eyring + Nernst–Einstein."""
    e_a = ion_solvation_hopping_activation_ev(ion, host)
    e_a_j = e_a * EV_TO_J
    z = abs(ion.formal_charge)
    span = 2.0 * BOHR_RADIUS_ANGSTROM * 1e-10 * (max(ion.z_nuclear, 1) ** (1.0 / 3.0))
    tau = (HBAR_J_S / (K_B * temperature_k)) * math.exp(e_a_j / (K_B * temperature_k))
    diff = (span**2) / max(tau, 1e-40)
    geff = cbs.g_eff(rho_curv)
    return z * E_CHARGE * diff * geff / (K_B * temperature_k)


# Canonical salts (geometry witness: bond length from ionic radii sum slot).
LIH_SALT = IonicSalt(
    name="LiH",
    cation=IonicFragment("Li", 3, 2),
    anion=IonicFragment("H", 1, 2),
    lattice_bond_angstrom=1.5956,
)
NACL_SALT = IonicSalt(
    name="NaCl",
    cation=alkali_halide_fragments("Na", 11, "Cl", 17)[0],
    anion=alkali_halide_fragments("Na", 11, "Cl", 17)[1],
    lattice_bond_angstrom=2.82,
)

SALTS: dict[str, IonicSalt] = {
    "LIH": LIH_SALT,
    "NACL": NACL_SALT,
}


def salt_witness(salt: IonicSalt) -> dict[str, Any]:
    net = build_ionic_salt_network(salt)
    surplus = ionic_bond_surplus_ev(salt.cation, salt.anion)
    bind = ionic_lattice_binding_ev_per_contact(
        salt.cation, salt.anion, distance_angstrom=salt.lattice_bond_angstrom
    )
    return {
        "salt": salt.name,
        "cation": {
            "label": salt.cation.label,
            "Z": salt.cation.z_nuclear,
            "electrons": salt.cation.electrons,
            "formal_charge": salt.cation.formal_charge,
            "mass_amu": salt.cation.mass_amu,
            "hydration_contacts": derived_hydration_contact_count(salt.cation),
            "solvation_E_a_ev": ion_solvation_hopping_activation_ev(salt.cation),
        },
        "anion": {
            "label": salt.anion.label,
            "Z": salt.anion.z_nuclear,
            "electrons": salt.anion.electrons,
            "formal_charge": salt.anion.formal_charge,
            "mass_amu": salt.anion.mass_amu,
            "hydration_contacts": derived_hydration_contact_count(salt.anion),
            "solvation_E_a_ev": ion_solvation_hopping_activation_ev(salt.anion),
        },
        "formula_mass_amu": salt.formula_mass_amu,
        "ionic_bond_surplus_ev": surplus,
        "lattice_binding_ev_per_contact": bind,
        "contact_xi": net.compton_triplet,
        "network_contacts": [c.kind.value for c in net.contacts],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Ionic bond network witnesses.")
    parser.add_argument("--salt", default="NaCl", choices=("LiH", "NaCl", "all"))
    parser.add_argument("--json-out", type=Path, default=None)
    args = parser.parse_args()
    keys = list(SALTS) if args.salt.lower() == "all" else [args.salt.upper()]
    rows = [salt_witness(SALTS[k]) for k in keys]
    payload = {"salts": rows}
    for row in rows:
        print(f"{row['salt']}: surplus={row['ionic_bond_surplus_ev']:.4f} eV  "
              f"bind/contact={row['lattice_binding_ev_per_contact']:.4f} eV  "
              f"formula={row['formula_mass_amu']:.3f} amu")
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2) + "\n")


if __name__ == "__main__":
    main()

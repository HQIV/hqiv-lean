#!/usr/bin/env python3
"""
Crystal lattice contact geometry witnesses.

Lean: ``Hqiv.QuantumChemistry.CrystalContactGeometry``.
Python mirror: ``hqiv_lab/crystal_geometry.py``.

Run:
  PYTHONPATH=scripts python3 scripts/hqiv_crystal_contact_geometry.py
  PYTHONPATH=scripts python3 scripts/hqiv_crystal_contact_geometry.py --json-out data/crystal_contact_witnesses.json
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

import hqiv_ionic_bond_network as ibn
import hqiv_metallic_bond_network as mbn
from hqiv_lab.crystal_geometry import (
    comparison_regime_for_species,
    covalent_network_em_packing_dress,
    diamond_cubic_lattice_parameter_angstrom,
    expected_contact_xi_for_crystal,
    fcc_lattice_parameter_angstrom,
    ionic_rocksalt_lattice_dress,
    metallic_lattice_nearest_neighbor_angstrom,
    metallic_phi_pack_nearest_neighbor_angstrom,
    metallic_unified_nearest_neighbor_angstrom,
    rocksalt_lattice_parameter_angstrom,
)
from hqiv_lab.species_panel import CONDENSED_SPECIES_PANEL

DEFAULT_JSON = _REPO_ROOT / "data" / "crystal_contact_witnesses.json"


def ionic_salt_witness(salt: ibn.IonicSalt) -> dict[str, Any]:
    z_i = salt.cation.z_nuclear
    z_j = salt.anion.z_nuclear
    nn = salt.lattice_bond_angstrom
    import hqiv_chemistry_tuft_dynamics as ctd

    outside_pair = ctd.outside_contact_geometry_target_angstrom(z_i, z_j)
    return {
        "name": salt.name,
        "crystal_kind": "ionic",
        "comparison_regime": comparison_regime_for_species(salt.name, z_i=z_i, z_j=z_j),
        "z_cation": z_i,
        "z_anion": z_j,
        "coordination": salt.coordination,
        "nearest_neighbor_angstrom": nn,
        "outside_contact_pair_angstrom": outside_pair,
        "ionic_rocksalt_lattice_dress": ionic_rocksalt_lattice_dress(salt.coordination),
        "lattice_parameter_angstrom": rocksalt_lattice_parameter_angstrom(nn),
        "geometry_route": "ionic_lattice_contact",
    }


def metallic_witness(lattice: mbn.MetallicLattice) -> dict[str, Any]:
    z = lattice.metal.z_nuclear
    nn_unified = metallic_unified_nearest_neighbor_angstrom(z, n_coord=lattice.coordination)
    return {
        "name": lattice.name,
        "crystal_kind": "metallic",
        "comparison_regime": "solid_lattice",
        "Z": z,
        "coordination": lattice.coordination,
        "nearest_neighbor_angstrom": nn_unified,
        "nested_wf_nearest_neighbor_angstrom": metallic_lattice_nearest_neighbor_angstrom(
            z, n_coord=lattice.coordination
        ),
        "phi_pack_nearest_neighbor_angstrom": metallic_phi_pack_nearest_neighbor_angstrom(
            z, n_coord=lattice.coordination
        ),
        "network_nearest_neighbor_angstrom": lattice.nearest_neighbor_angstrom,
        "expected_contact_xi": expected_contact_xi_for_crystal(
            crystal_kind="metallic", z_values=(z,)
        ),
        "lattice_parameter_angstrom": fcc_lattice_parameter_angstrom(nn_unified),
        "geometry_route": "metallic_unified_fcc_contact",
    }


def covalent_network_witness(z: int, name: str) -> dict[str, Any]:
    dress = covalent_network_em_packing_dress(z, coordination=4, em_feedback=True)
    bond = float(dress["bond_length_angstrom"])
    return {
        "name": name,
        "crystal_kind": "covalent_network",
        "comparison_regime": "solid_lattice",
        "Z": z,
        "coordination": 4,
        "nearest_neighbor_angstrom": bond,
        "nearest_neighbor_bare_angstrom": float(dress["bond_length_bare_angstrom"]),
        "lattice_parameter_angstrom": diamond_cubic_lattice_parameter_angstrom(bond),
        "length_reliable": dress["length_reliable"],
        "em_feedback_applied": dress["em_feedback_applied"],
        "network_open_channel_packing_scale": dress[
            "network_open_channel_packing_scale"
        ],
        "expected_contact_xi": expected_contact_xi_for_crystal(
            crystal_kind="covalent_network", z_values=(z,)
        ),
        "geometry_route": (
            "diamond_cubic_em_open_packing"
            if dress["em_feedback_applied"]
            else "diamond_cubic_allotrope_contact"
        ),
    }


def panel_crystal_witnesses() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for entry in CONDENSED_SPECIES_PANEL:
        if entry.crystal_kind == "ionic" and len(entry.z_values) >= 2:
            z_i, z_j = entry.z_values[0], entry.z_values[1]
            if entry.molecule.upper() == "NACL":
                rows.append(ionic_salt_witness(ibn.NACL_SALT))
            else:
                cation = ibn.IonicFragment("cat", z_i, z_i - 1)
                anion = ibn.IonicFragment("an", z_j, z_j + 1)
                rows.append(
                    ionic_salt_witness(
                        ibn.IonicSalt(entry.molecule, cation, anion)
                    )
                )
        elif entry.crystal_kind == "metallic" and entry.z_values:
            z = entry.z_values[0]
            label = entry.molecule
            lat = mbn.metal_lattice_from_z(label, z)
            rows.append(metallic_witness(lat))
        elif entry.crystal_kind == "covalent_network" and entry.z_values:
            rows.append(covalent_network_witness(entry.z_values[0], entry.molecule))
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description="Crystal contact geometry witnesses.")
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()
    rows = panel_crystal_witnesses()
    payload = {
        "lean_module": "Hqiv.QuantumChemistry.CrystalContactGeometry",
        "policy": "Lattice nn contacts derived upstream; NIST/CRC only in comparison audits",
        "witnesses": rows,
    }
    for row in rows:
        print(
            f"{row['name']:4s} {row['crystal_kind']:8s} "
            f"r_nn={row['nearest_neighbor_angstrom']:.3f} Å  "
            f"regime={row['comparison_regime']}"
        )
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(payload, indent=2) + "\n")
    print(f"Wrote {args.json_out}")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Molecular dipole moment from geometry — vector sum of bond dipoles on the VSEPR balanced frame.

The dipole is the next observable that falls out of the derived geometry with *no new rule*:

* each polar bond carries a dipole ``μ_bond = δ·e·r_e`` along its axis, with ``δ`` the already-derived
  native pull asymmetry (``hqiv_atom_construction.valence_electron_pull``) and ``r_e`` the derived
  equilibrium length;
* the bonds sit on the **balanced VSEPR frame** (``∑ v̂ = 0``, proven in ``VSEPRFromBalance``), so the
  molecular dipole is ``μ_bond · |∑_{bonds} v̂|``.

The resultant factor has a closed form from the frame's Gram identity:
``|∑_{k bonds} v̂|² = k(d−k)/(d−1)`` over ``d`` domains.  When every domain is a bond (``k=d``) it is
**zero** — CO₂, CH₄, BF₃, SF₆ are nonpolar by the *same* balance that sets their angles.  Lone pairs
(``k<d``) break the cancellation, giving H₂O, NH₃, SO₂ their dipoles.  See
``Hqiv/QuantumChemistry/MolecularDipoleBalance.lean``.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass

import hqiv_atom_construction as ac
import hqiv_chemistry_tuft_dynamics as ctd
import hqiv_particle_shell_structure as pss

# 1 e·Å expressed in debye (unit conversion, not a fit): 1 D = 0.2081943 e·Å.
DEBYE_PER_E_ANGSTROM = 4.803204


def bond_charge_asymmetry(z_i: int, z_j: int) -> float:
    """Linear charge-partition fraction `δ = |p_i − p_j|/(p_i + p_j)` displaced toward the more
    electronegative atom — the same native pull `p` behind the ionic character `w = δ²`."""
    p_i = ac.valence_electron_pull(z_i)
    p_j = ac.valence_electron_pull(z_j)
    if p_i + p_j <= 0.0:
        return 0.0
    return abs(p_i - p_j) / (p_i + p_j)


def bond_partial_charge(z_i: int, z_j: int) -> float:
    """Partial charge on the bond = the derived ionic character `w = δ²`.

    The dipole comes from the charge-transferred ionic resonance structure A⁺B⁻ (dipole `e·r_e`),
    which carries probability weight `c_ion² = δ²` in the VB superposition.  So the *effective*
    transferred charge is `w = δ²` — the same ionic character already used for the force-constant
    resonance, no new quantity.  Homonuclear `δ=0 ⇒ w=0`.
    """
    return bond_charge_asymmetry(z_i, z_j) ** 2


def bond_dipole_debye(z_i: int, z_j: int, bond_order: float = 1.0) -> float:
    """Single bond dipole `μ = w · e · r_e` (in debye), `w=δ²` the derived ionic character and `r_e`
    the derived equilibrium length; homonuclear `w=0 ⇒ μ=0`."""
    w = bond_partial_charge(z_i, z_j)
    r_e = ctd.bond_equilibrium_from_atomic_numbers(z_i, z_j)
    return w * r_e * DEBYE_PER_E_ANGSTROM


def resultant_factor(n_bonds: int, n_lone_pairs: int) -> float:
    """`|∑ of the bond unit vectors|` over `d = n_bonds + n_lone_pairs` balanced domains.

    DERIVED closed form from the balanced-frame Gram identity
    ``|∑_{i∈S} v̂_i|² = k + k(k−1)c`` with ``c = −1/(d−1)`` ⇒ ``k(d−k)/(d−1)`` (`k = n_bonds`).
    All-bonded (`k = d`) ⇒ 0 (nonpolar).  Lean: ``MolecularDipoleBalance.balanced_partial_resultant_sq``.
    """
    d = n_bonds + n_lone_pairs
    if d <= 1:
        return float(n_bonds)
    return math.sqrt(max(0.0, n_bonds * (d - n_bonds) / (d - 1)))


@dataclass(frozen=True)
class DipoleReadout:
    name: str
    z_center: int
    z_ligand: int
    n_sigma: int
    bond_order: int
    lone_pairs: int
    domains: int
    bond_dipole_debye: float
    resultant_factor: float
    dipole_debye: float
    polar: bool


def central_molecule_dipole(
    name: str, z_center: int, z_ligand: int, n_sigma: int, bond_order: int = 1
) -> DipoleReadout:
    """Dipole of an AXₙ centre: bond dipole × balanced-frame resultant factor.

    Lone pairs are the derived budget leftover ``(V − Σorder)/2`` (each multiple bond removes its full
    order from the electron budget but counts as one σ-domain).
    """
    total_order = n_sigma * bond_order
    n_lp = pss.lone_pair_count(z_center, total_order)
    mu_bond = bond_dipole_debye(z_center, z_ligand, bond_order)
    factor = resultant_factor(n_sigma, n_lp)
    mu = mu_bond * factor
    return DipoleReadout(
        name=name,
        z_center=z_center,
        z_ligand=z_ligand,
        n_sigma=n_sigma,
        bond_order=bond_order,
        lone_pairs=n_lp,
        domains=n_sigma + n_lp,
        bond_dipole_debye=mu_bond,
        resultant_factor=factor,
        dipole_debye=mu,
        polar=factor > 1e-9,
    )


# canonical AXₙEₘ panel: (name, Z_center, Z_ligand, n_sigma, bond_order)
PANEL = [
    ("H2O", 8, 1, 2, 1),
    ("NH3", 7, 1, 3, 1),
    ("CH4", 6, 1, 4, 1),
    ("HF", 9, 1, 1, 1),
    ("CO2", 6, 8, 2, 2),
    ("BF3", 5, 9, 3, 1),
    ("SO2", 16, 8, 2, 2),
    ("BeCl2", 4, 17, 2, 1),
]


def panel_readout() -> list[DipoleReadout]:
    return [central_molecule_dipole(*row) for row in PANEL]


def _payload() -> dict:
    return {
        "constants": {"debye_per_e_angstrom": DEBYE_PER_E_ANGSTROM},
        "molecules": [r.__dict__ for r in panel_readout()],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="emit JSON payload")
    args = parser.parse_args()
    if args.json:
        print(json.dumps(_payload(), indent=2))
        return
    print(f"{'molecule':8} {'domains':>7} {'lone':>4} {'factor':>7} {'mu_bond/D':>9} {'mu/D':>6} polar")
    for r in panel_readout():
        print(
            f"{r.name:8} {r.domains:>7} {r.lone_pairs:>4} {r.resultant_factor:>7.3f} "
            f"{r.bond_dipole_debye:>9.3f} {r.dipole_debye:>6.3f} {r.polar}"
        )


if __name__ == "__main__":
    main()

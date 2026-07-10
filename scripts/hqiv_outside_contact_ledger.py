#!/usr/bin/env python3
"""
Outside-contact G_eff ledger (multi-channel bookkeeping).

Lean: ``Hqiv.QuantumChemistry.OutsideContactLedger``

Channels (product dress M_out = grav · em · bulk · local · contact):

  grav    — Ricci / gravitational outside support
            ``outsideGravityGeffModulator(φ)``
  em      — electric / curvature-dielectric concentration
            ``1 + (4/8)·curvatureConcentrationWeight(n)``
  bulk    — medium density ρ
            ``scaleOutsideCouplingForMediumDensity(bulk_target, ρ_bulk)``
  local   — nucleation / wall / interface defect
            ``1 + localCurvatureDefectExcess(δ_coord)``
  contact — bond-summed outside G_eff participation
            ``outsideGeffSurplus(Σ G_eff, surplus)``  (legacy chart term)

Dilute-gas assay (φ=0, n=1, ρ=0, δ=0): grav=em=bulk=local=1, so
M_out = contact — recovers the previous single-scalar outside_geff dress.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
from typing import Any, Sequence

import hqiv_homogeneous_curvature_feedback as hcf
import hqiv_lean_physics_primitives as lean
import hqiv_molecular_spectroscopy as ms
import hqiv_nbody_second_order as nso
import hqiv_nuclear_outside_temperature_dynamics as notd

STRONG = lean.STRONG_CHANNEL_FRACTION


@dataclass(frozen=True)
class OutsideContactLedger:
    """Lean ``OutsideContactLedger``."""

    grav: float
    em: float
    bulk: float
    local_defect: float
    contact: float

    @property
    def dress(self) -> float:
        """Lean ``outsideContactLedgerDress``."""
        return self.grav * self.em * self.bulk * self.local_defect * self.contact

    def to_dict(self) -> dict[str, Any]:
        d = asdict(self)
        d["dress"] = self.dress
        d["channels"] = {
            "grav": "outsideGravityGeffModulator (Ricci / gravitational G_eff)",
            "em": "1+(4/8)·curvatureConcentrationWeight (electric / dielectric)",
            "bulk": "scaleOutsideCouplingForMediumDensity (medium density ρ)",
            "local_defect": "1+localCurvatureDefectExcess (nucleation / wall / interface)",
            "contact": "outsideGeffSurplus (bond-summed G_eff participation)",
        }
        return d


def scale_outside_coupling_for_medium_density(f: float, rho: float) -> float:
    """Lean ``scaleOutsideCouplingForMediumDensity``."""
    rho_c = max(0.0, min(1.0, float(rho)))
    return 1.0 + rho_c * (float(f) - 1.0)


def outside_em_channel(n_dielectric: float) -> float:
    """Lean ``outsideEmChannel``."""
    return 1.0 + STRONG * ms.concentration_weight(max(float(n_dielectric), 1.0))


def outside_bulk_channel(bulk_target: float, rho_bulk: float) -> float:
    """Lean ``outsideBulkChannel``."""
    return scale_outside_coupling_for_medium_density(bulk_target, rho_bulk)


def outside_local_channel(coordination_excess: float) -> float:
    """Lean ``outsideLocalDefectChannel``."""
    return 1.0 + hcf.local_curvature_defect_excess(coordination_excess)


def outside_contact_channel(geff_sum: float, surplus: float) -> float:
    """Lean ``outsideContactChannel`` / ``outsideGeffSurplus``."""
    return nso.outside_geff_surplus(geff_sum, surplus)


def dilute_gas_outside_contact_ledger(geff_sum: float, surplus: float) -> OutsideContactLedger:
    """Lean ``diluteGasOutsideContactLedger`` — environment channels at identity."""
    return OutsideContactLedger(
        grav=notd.outside_gravity_geff_modulator(0.0),
        em=outside_em_channel(1.0),
        bulk=outside_bulk_channel(1.0, 0.0),
        local_defect=outside_local_channel(0.0),
        contact=outside_contact_channel(geff_sum, surplus),
    )


def outside_contact_ledger_from_channels(
    *,
    phi_epsilon: float = 0.0,
    n_dielectric: float = 1.0,
    bulk_target: float = 1.0,
    rho_bulk: float = 0.0,
    coordination_excess: float = 0.0,
    geff_sum: float,
    surplus: float,
) -> OutsideContactLedger:
    """Lean ``outsideContactLedgerFromChannels``."""
    return OutsideContactLedger(
        grav=notd.outside_gravity_geff_modulator(phi_epsilon),
        em=outside_em_channel(n_dielectric),
        bulk=outside_bulk_channel(bulk_target, rho_bulk),
        local_defect=outside_local_channel(coordination_excess),
        contact=outside_contact_channel(geff_sum, surplus),
    )


def mean_dielectric_from_bonds(
    fragments: Sequence[object],
    bonds: Sequence[object],
) -> float:
    """Mean curvature-dielectric ratio over covalent bonds (n=1 if none)."""
    if not bonds:
        return 1.0
    ns: list[float] = []
    for b in bonds:
        i = getattr(b, "frag_i", None)
        j = getattr(b, "frag_j", None)
        if i is None or j is None:
            continue
        z_i = int(getattr(fragments[i], "z_nuclear"))
        z_j = int(getattr(fragments[j], "z_nuclear"))
        ns.append(ms.curvature_dielectric_ratio(z_i, z_j))
    return sum(ns) / len(ns) if ns else 1.0


def ledger_for_molecule(
    *,
    geff_thetas: Sequence[float],
    surplus: float,
    fragments: Sequence[object],
    bonds: Sequence[object],
    phi_epsilon: float = 0.0,
    rho_bulk: float = 0.0,
    coordination_excess: float = 0.0,
    contact_xi: float | None = None,
    dilute_gas_assay: bool = True,
) -> OutsideContactLedger:
    """
    Build the outside-contact ledger for one molecule.

    Dilute-gas assay (default for GMTKN chart): environment channels forced to
    identity; only ``contact`` carries the bond-summed G_eff participation.
    Condensed / interface: set ``dilute_gas_assay=False`` and supply ρ / δ / φ.
    """
    geff_sum = sum(float(g) for g in geff_thetas)
    if dilute_gas_assay:
        return dilute_gas_outside_contact_ledger(geff_sum, surplus)

    bulk_target = 1.0
    if contact_xi is not None and rho_bulk > 0.0:
        bulk_target = hcf.homogeneous_curvature_budget_at_xi(contact_xi, 1.0)
    n_diel = mean_dielectric_from_bonds(fragments, bonds)
    return outside_contact_ledger_from_channels(
        phi_epsilon=phi_epsilon,
        n_dielectric=n_diel,
        bulk_target=bulk_target,
        rho_bulk=rho_bulk,
        coordination_excess=coordination_excess,
        geff_sum=geff_sum,
        surplus=surplus,
    )

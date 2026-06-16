#!/usr/bin/env python3
"""
Faithful Python mirrors of Lean nucleon-binding identifiers.

Primary Lean sources:
  • ``Hqiv.Physics.DynamicBetaIsotope``
  • ``Hqiv.Physics.NeutronBindingStabilityScaffold``
  • ``Hqiv.Physics.SpinStatistics`` / ``Hqiv.Physics.HQIVNuclei``
  • ``Hqiv.Physics.NuclearAndAtomicSpectra``

Used by ``hqiv_nucleon_binding_integrator.py``; does not replace the lighter
witness scripts, but supplies the named ledger algebra they previously inlined.
"""

from __future__ import annotations

import math

# Lean ``hbar_MeV_s`` (SpinStatistics / HQIVNuclei).
HBAR_MEV_S = 6.582119569e-22
MIN_MEV = 1e-30
NUCLEON_ISOSPIN_GAP_MEV = 1.0


def curvature_mass_imprint(m_ref_mev: float, m_der_mev: float) -> float:
    """Lean ``curvatureMassImprint``."""
    return m_ref_mev / max(m_der_mev, MIN_MEV)


def imprinted_mass_budget(m_der_mev: float, kappa: float) -> float:
    """Lean ``imprintedMassBudget``."""
    return kappa * m_der_mev


def beta_minus_endpoint_q_from_budgets(
    m_parent_mev: float, m_daughter_mev: float, m_e_mev: float
) -> float:
    """Lean ``betaMinusEndpointQFromBudgets``."""
    return m_parent_mev - m_daughter_mev - m_e_mev


def beta_minus_endpoint_q_uniform_imprint(
    kappa: float,
    m_parent_der_mev: float,
    m_daughter_der_mev: float,
    m_e_mev: float,
) -> float:
    """Lean ``betaMinusEndpointQUniformImprint``."""
    return (
        imprinted_mass_budget(m_parent_der_mev, kappa)
        - imprinted_mass_budget(m_daughter_der_mev, kappa)
        - m_e_mev
    )


def beta_minus_endpoint_q_per_isotope_imprint(
    kappa_parent: float,
    m_parent_der_mev: float,
    kappa_daughter: float,
    m_daughter_der_mev: float,
    m_e_mev: float,
) -> float:
    """Lean ``betaMinusEndpointQPerIsotopeImprint``."""
    return (
        imprinted_mass_budget(m_parent_der_mev, kappa_parent)
        - imprinted_mass_budget(m_daughter_der_mev, kappa_daughter)
        - m_e_mev
    )


def beta_cluster_mass_well(cluster_total_mev: float, a: int) -> float:
    """Lean ``betaClusterMassWell``."""
    return cluster_total_mev / max(float(a), 1.0)


def beta_interior_partner_well(cluster_total_mev: float, partners: int) -> float:
    """Lean ``betaInteriorPartnerWell``."""
    return cluster_total_mev / max(float(partners), 1.0)


def beta_width_well_geometric_blend(
    mass_well_mev: float, interior_partner_mev: float, partners: int
) -> float:
    """Lean ``betaWidthWellGeometricBlend`` (literal blend exponent)."""
    blend = 1.0 / (2.0 * max(float(partners), 1.0))
    ratio = interior_partner_mev / max(mass_well_mev, MIN_MEV)
    return mass_well_mev * max(ratio, MIN_MEV) ** blend


def width_well_curvature_imprint(tau_ref_s: float, tau_pred_s: float, valley: int) -> float:
    """Lean ``widthWellCurvatureImprint``."""
    return (tau_ref_s / max(tau_pred_s, MIN_MEV)) ** (1.0 / max(float(valley + 1), 1.0))


def decay_width_per_s(delta_e_mev: float) -> float:
    """Lean ``decayWidth_per_s``: Γ = ΔE / ħ."""
    if delta_e_mev <= 0.0:
        return 0.0
    return delta_e_mev / HBAR_MEV_S


def half_life_from_width(gamma_per_s: float) -> float:
    """Lean ``half_life_from_width``."""
    if gamma_per_s <= 0.0:
        return math.inf
    return math.log(2.0) / gamma_per_s


def resonance_lifetime(delta_e_mev: float) -> float:
    """Lean ``resonance_lifetime``."""
    if delta_e_mev <= 0.0:
        return math.inf
    return HBAR_MEV_S / delta_e_mev


def resonance_half_life(delta_e_mev: float) -> float:
    """Lean ``resonance_half_life``."""
    return math.log(2.0) * resonance_lifetime(delta_e_mev)


def free_neutron_curvature_deficit(omega_readout: float) -> float:
    """Lean ``freeNeutronCurvatureDeficit``."""
    return max(0.0, 1.0 - omega_readout)


def free_neutron_overlap_energy(omega_readout: float) -> float:
    """Lean ``freeNeutronOverlapEnergy``."""
    return NUCLEON_ISOSPIN_GAP_MEV + free_neutron_curvature_deficit(omega_readout)


def free_neutron_strong_decay_width(omega_readout: float) -> float:
    """Lean ``freeNeutronStrongDecayWidth``."""
    return decay_width_per_s(free_neutron_overlap_energy(omega_readout))

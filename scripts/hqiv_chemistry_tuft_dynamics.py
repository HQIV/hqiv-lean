#!/usr/bin/env python3
"""
Lean-aligned TUFT chemistry dynamics (post-T12/T13).

Mirrors:
  - Hqiv.Physics.DynamicCentreGeometry
  - Hqiv.QuantumChemistry.ElectronicValenceFromTuftChart
  - Hqiv.QuantumChemistry.DynamicBindingChart
  - Hqiv.QuantumChemistry.ChemistryTuftDynamics

No tabulated bond angles (104.5°, 109.47°) or fitted κ_bind.
"""

from __future__ import annotations

import math

import hqiv_lean_physics_primitives as lean
import hqiv_dynamic_binding_chart as dbc

# TUFT chart shells (TuftShellChart / electronic valence)
TUFT_HEAVY_CHART_SHELL = 4
TUFT_STRONG_CHART_SHELL = 3
ELECTRONIC_H1S_SHELL = 1


def electronic_compton_shells(z: int) -> tuple[int, int | None, int]:
    """Centre (2s, 2p) + H 1s Compton slots for period-2 hydrides."""
    if z <= 2:
        return (ELECTRONIC_H1S_SHELL, None, ELECTRONIC_H1S_SHELL)
    return (TUFT_HEAVY_CHART_SHELL, TUFT_STRONG_CHART_SHELL, ELECTRONIC_H1S_SHELL)


def period2_valence_electron_count(z: int) -> int:
    if z <= 2:
        return z
    return min(z, 10) - 2


def centre_lone_pair_count(z: int, n_bonds: int) -> int:
    if z < 3 or z > 10 or n_bonds < 1:
        return 0
    valence = period2_valence_electron_count(z)
    bonding = 2 * n_bonds
    return max(0, (valence - bonding) // 2)


def steric_domain_count(n_bonds: int, n_lp: int) -> int:
    return n_bonds + n_lp


def centre_angle_rad_from_domains(n_domains: int) -> float:
    if n_domains <= 2:
        return math.pi
    return math.acos(-1.0 / (n_domains - 1))


def centre_angle_bent_dress(theta_tet: float, n_lp: int, n_domains: int) -> float:
    if n_domains == 0:
        return theta_tet
    return theta_tet - lean.STRONG_CHANNEL_FRACTION * (n_lp / n_domains) * (math.pi / 6.0)


def dynamic_centre_angle_rad(z: int, n_bonds: int) -> float:
    """H–X–H angle (rad) from VSEPR domains + (4/8) bent dress."""
    n_lp = centre_lone_pair_count(z, n_bonds)
    n_dom = steric_domain_count(n_bonds, n_lp)
    return centre_angle_bent_dress(centre_angle_rad_from_domains(n_dom), n_lp, n_dom)


def dynamic_contact_radius_dimless(m: int, z: int, c: float = 1.0) -> float:
    """R_m / (α_eff · Z) — Lean `dynamicContactRadiusDimless`."""
    import hqiv_excited_states as hes

    r_m = float(m + 1)
    return r_m / (hes.alpha_eff_at_shell(m, c) * max(float(z), 1.0))


def dynamic_bond_distance_weight(r_angstrom: float, m: int) -> float:
    """R_m / r contact weight (dimensionless ladder over supplied r)."""
    if r_angstrom <= 0:
        return 0.0
    return float(m + 1) / r_angstrom


def dynamic_atomization_surplus_dress(
    z_heavy: int,
    n_bonds: int,
    n_centre_bonds: int,
    eta_p: float,
) -> float:
    """Lean `dynamicAtomizationSurplusDress`."""
    n_lp = centre_lone_pair_count(z_heavy, n_bonds)
    lone = 1.0 + lean.STRONG_CHANNEL_FRACTION * float(n_lp) * eta_p
    bent = (
        1.0 + lean.STRONG_CHANNEL_FRACTION * 0.25
        if n_centre_bonds == 2
        else 1.0
    )
    return lone * bent


def heavy_hydride_compton_triplet() -> dbc.DynamicComptonTriplet:
    return dbc.DynamicComptonTriplet(
        m0=TUFT_HEAVY_CHART_SHELL,
        m1=TUFT_STRONG_CHART_SHELL,
        m2=ELECTRONIC_H1S_SHELL,
    )


def dynamic_contact_xi_heavy_hydride() -> float:
    t = heavy_hydride_compton_triplet()
    return dbc.dynamic_compton_xi_mean(t)


def dynamic_binding_participation_at_contact(eta_p: float) -> float:
    t = heavy_hydride_compton_triplet()
    return dbc.dynamic_compton_eta_second_order(
        eta_p, dbc.dynamic_compton_p_shell_active(t)
    ) * dbc.dynamic_binding_curvature_feedback_at_xi(dynamic_contact_xi_heavy_hydride())

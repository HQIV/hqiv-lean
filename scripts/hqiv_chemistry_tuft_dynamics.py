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
import hqiv_isotope_hydrogenic_scales as ihs

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
    """Period-2 centre lone pairs — Lean ``DynamicCentreGeometry.centreLonePairCount``."""
    if z < 3 or z > 10 or n_bonds < 1:
        return 0
    valence = period2_valence_electron_count(z)
    if valence < n_bonds:
        return 0
    return (valence - n_bonds) // 2


def period3_centre_lone_pair_count(z: int, n_bonds: int) -> int:
    """Period-3 VSEPR lone pairs: ``(V − X) / 2``."""
    if z < 11 or z > 18 or n_bonds < 1:
        return 0
    valence = min(z, 18) - 10
    return max(0, (valence - n_bonds) // 2)


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
    period = 3 if 11 <= z <= 18 else (2 if 3 <= z <= 10 else 0)
    if period == 3:
        n_lp = period3_centre_lone_pair_count(z, n_bonds)
    else:
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


# ---------------------------------------------------------------------------
# Bond geometry from nested shell-resolved wavefunctions (no diamond-node Θ)
# ---------------------------------------------------------------------------

BOHR_RADIUS_ANGSTROM = 0.529177210903

# ``1 − α/2`` — informational monogamy contracts shared-electron contact (H₂ witness).
INFORMATIONAL_MONOGAMY_LENGTH_FACTOR = 1.0 - lean.ALPHA / 2.0


def nested_wf_covalent_radius_bohr(m: int, z: int, c: float = 1.0) -> float:
    """
    Covalent radius (Bohr) from the shell-resolved hydrogenic ground state.

    Lean: ``dynamicContactRadiusDimless m z * alphaEffAtShell m = R_m m / z``
    (``CentreGeometryFromTuft`` / ``hydrogenGroundStateOfShell`` scale).
    """
    if z <= 0 or m <= 0:
        return float("nan")
    return dynamic_contact_radius_dimless(m, z, c) * ihs.alpha_eff_at_shell(m, c)


def bond_contact_compton_shell(z: int, z_partner: int) -> int:
    """
    Compton shell index on atom ``z`` for a bond to partner ``z_partner``.

    Hydrides use the heavy centre p slot when period-2; otherwise valence s.
    """
    import hqiv_electronic_valence_shells as evs

    if z <= 1:
        return ELECTRONIC_H1S_SHELL
    m_s, m_p = evs.electronic_compton_shells(z)
    if z_partner == 1 and m_p is not None and evs.chemical_period(z) == 2:
        return m_p
    return m_s


def period3_hydride_bond_length_scale(z_heavy: int) -> float:
    """
    Period-3 hydride elongation — inverse of the s–p σ-hole coupling dress
    on ``electronic_valence_shells.period3_hydride_surplus_dress`` (longer when
    coupling is weaker).
    """
    import hqiv_electronic_valence_shells as evs

    if evs.chemical_period(z_heavy) < 3:
        return 1.0
    m_s, m_p = evs.electronic_compton_shells(z_heavy)
    dress = float(TUFT_HEAVY_CHART_SHELL) / float(m_s)
    if m_p is not None:
        dress *= 1.0 - lean.STRONG_CHANNEL_FRACTION / float(m_s)
        dress *= 1.0 - lean.STRONG_CHANNEL_FRACTION / float(m_s + m_p)
    if dress <= 0.0:
        return 1.0
    return 1.0 / dress


def bond_equilibrium_radius_bohr(
    m_i: int,
    z_i: int,
    m_j: int,
    z_j: int,
    *,
    c: float = 1.0,
) -> float:
    """
    Equilibrium bond length (Bohr) from nested WF covalent radii + monogamy.

    Homonuclear dimers delegate to ``homonuclear_bond_equilibrium_bohr``.
    """
    if z_i == z_j:
        return homonuclear_bond_equilibrium_bohr(z_i, c=c)
    ri = nested_wf_covalent_radius_bohr(m_i, z_i, c)
    rj = nested_wf_covalent_radius_bohr(m_j, z_j, c)
    mono = INFORMATIONAL_MONOGAMY_LENGTH_FACTOR
    if min(z_i, z_j) == 1:
        r = (ri + rj) * mono
    else:
        r = 2.0 * math.sqrt(ri * rj) / mono
    if min(z_i, z_j) == 1 and max(z_i, z_j) > 1:
        z_h = max(z_i, z_j)
        r *= period3_hydride_bond_length_scale(z_h)
    return r


def homonuclear_bond_equilibrium_bohr(z: int, *, c: float = 1.0) -> float:
    """
    Homonuclear diatomic bond length (Bohr) from nested WF + bond-order routing.

    Mirrors dissociation surplus classes in ``hqiv_electronic_valence_shells``.
    """
    import hqiv_electronic_valence_shells as evs

    m_s, _ = evs.electronic_compton_shells(z)
    ri = nested_wf_covalent_radius_bohr(m_s, z, c)
    mono = INFORMATIONAL_MONOGAMY_LENGTH_FACTOR
    strong = lean.STRONG_CHANNEL_FRACTION
    cap = float(lean.CONSTRUCTIVE_VALLEY_CAP)
    period = evs.chemical_period(z)

    if z == 1:
        return 2.0 * ri * ri / (2.0 * ri) * mono

    base = 2.0 * ri / mono

    if evs.is_homonuclear_halogen(z):
        phi_m = 2.0 * (float(m_s) + 1.0)
        r_phi = 2.0 * phi_m / float(z) / mono
        r = math.sqrt(base * r_phi)
        chart_denom = float(evs.ELECTRONIC_M_S_PERIOD2 + max(period, 2) - 2)
        r /= 1.0 + strong / chart_denom
        if period >= 3:
            r /= period3_hydride_bond_length_scale(z)
        return r

    if evs.homonuclear_open_shell_dimer(z):
        return base * (1.0 + strong / 2.0)

    if evs.homonuclear_bond_order(z) >= 2:
        return base

    return base * (1.0 + strong / cap)


def bond_order_length_scale(z_i: int, z_j: int) -> float:
    """Contract equilibrium length for σ+π bond order > 1 (C≡C, C≡N, …)."""
    import hqiv_electronic_valence_shells as evs

    bo = evs.covalent_bond_order(z_i, z_j)
    if bo <= 1:
        return 1.0
    return 1.0 / (1.0 + (float(bo) - 1.0) * lean.STRONG_CHANNEL_FRACTION / 4.0)


def bond_equilibrium_radius_angstrom(
    m_i: int,
    z_i: int,
    m_j: int,
    z_j: int,
    *,
    c: float = 1.0,
) -> float:
    """SI export: Bohr × ``BOHR_RADIUS_ANGSTROM``."""
    return bond_equilibrium_radius_bohr(m_i, z_i, m_j, z_j, c=c) * BOHR_RADIUS_ANGSTROM


def bond_equilibrium_from_atomic_numbers(z_i: int, z_j: int, *, c: float = 1.0) -> float:
    """Bond length (Å) from atomic numbers only (Compton slots from TUFT chart)."""
    m_i = bond_contact_compton_shell(z_i, z_j)
    m_j = bond_contact_compton_shell(z_j, z_i)
    return bond_equilibrium_radius_angstrom(m_i, z_i, m_j, z_j, c=c)

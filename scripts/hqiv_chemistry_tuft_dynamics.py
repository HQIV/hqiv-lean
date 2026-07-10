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
import hqiv_particle_shell_structure as pss

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
    """Period-2 centre lone pairs from the derived electron budget.

    Delegates to :func:`hqiv_particle_shell_structure.lone_pair_count` — the leftover ``(V − X)/2``
    electrons paired up, with conservation proven in ``LonePairPartition.electron_budget_closes``.
    """
    if z < 3 or z > 10 or n_bonds < 1:
        return 0
    return pss.lone_pair_count(z, n_bonds)


def period3_centre_lone_pair_count(z: int, n_bonds: int) -> int:
    """Period-3 lone pairs from the same derived budget (one rule, no period special-case)."""
    if z < 11 or z > 18 or n_bonds < 1:
        return 0
    return pss.lone_pair_count(z, n_bonds)


def steric_domain_count(n_bonds: int, n_lp: int) -> int:
    return n_bonds + n_lp


def centre_angle_rad_from_domains(n_domains: int) -> float:
    """Steric-domain angle = `arccos(−1/(d−1))`.

    This is NOT an injected VSEPR rule.  The σ-domains are unit informational-monogamy contacts; at
    equilibrium their directions sum to zero (Kirchhoff node law) and, being equivalent, share one
    pairwise cosine `c`, forcing `0 = d·(1 + (d−1)c)` ⇒ `c = −1/(d−1)`.  The derivation and its
    numerical check live in ``hqiv_allotrope_network.balanced_unit_contact_cos`` and the Lean proof
    ``Hqiv/QuantumChemistry/VSEPRFromBalance.lean``.
    """
    if n_domains <= 2:
        return math.pi
    return math.acos(-1.0 / (n_domains - 1))


def centre_angle_bent_dress(theta_tet: float, n_lp: int, n_domains: int) -> float:
    if n_domains == 0:
        return theta_tet
    n_bonds = max(n_domains - n_lp, 0)
    torque_sites = max(n_domains + n_bonds, 1)
    return theta_tet - lean.STRONG_CHANNEL_FRACTION * (n_lp / torque_sites) * (math.pi / 6.0)


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

    # Period-2: unified carrier+network law (replaces the per-bond-order class routing).
    # The two nested-WF carriers contact at `base`; each *open* (unsaturated) p-shell
    # channel then pushes them apart by one informational-monogamy step `1 + strong/2`.
    # The open-channel count is the antibonding-pair number — the SAME monogamy channel
    # defect that stiffens the spectroscopy curvature (filled π* density): it adds well
    # curvature *and* elongates the bond.  N₂ (triple, no open channel) sits at the bare
    # carrier contact; O₂ (one π* pair) is one step out; F₂ (two π* pairs) is two.
    if period == 2:
        channel_cap = 3 if evs.valence_electron_count(z) >= 3 else 1
        antibond_pairs = max(0, channel_cap - evs.homonuclear_bond_order(z))
        return base * (1.0 + strong / 2.0) ** antibond_pairs

    # Period ≥ 3 homonuclear halogens: same open-channel carrier law as period-2.
    if period >= 3 and evs.is_homonuclear_halogen(z):
        return period3_halogen_bond_length_bohr(z, c=c)

    if evs.homonuclear_open_shell_dimer(z):
        return base * (1.0 + strong / 2.0)

    if evs.homonuclear_bond_order(z) >= 2:
        return base

    return base * (1.0 + strong / cap)


def ionic_charge_asymmetry(z_i: int, z_j: int) -> float:
    """Lean ``ionicChargeAsymmetry``: ``|Z_i − Z_j| / (Z_i + Z_j)``."""
    if z_i + z_j == 0:
        return 0.0
    return abs(z_i - z_j) / (z_i + z_j)


def ionic_outside_contact_dress(z_i: int, z_j: int) -> float:
    """Lean ``ionicOutsideContactDress``."""
    return 1.0 + ionic_charge_asymmetry(z_i, z_j) * lean.STRONG_CHANNEL_FRACTION * lean.GAMMA


def period3_inert_core_lattice_dress() -> float:
    """Lean ``period3InertCoreLatticeDress``."""
    return math.sqrt(1.0 + lean.STRONG_CHANNEL_FRACTION)


def ionic_inert_core_length_elongation(z_i: int, z_j: int) -> float:
    """Lean ``ionicInertCoreLengthElongation`` (outer ``valenceElectronCount``)."""
    import hqiv_electronic_valence_shells as evs

    period = max(evs.chemical_period(z_i), evs.chemical_period(z_j))
    if period <= 2 or z_i + z_j == 0:
        return 1.0
    n_val = max(
        evs.valence_electron_count(z_i) + evs.valence_electron_count(z_j),
        1,
    )
    return (z_i + z_j) / n_val


def ionic_gas_phase_em_dress() -> float:
    """Lean ``ionicGasPhaseEmDress``: ``1 + α = 8/5``."""
    return 1.0 + lean.ALPHA


def ionic_gas_outside_contact_bond_length_bohr(
    m_i: int,
    z_i: int,
    m_j: int,
    z_j: int,
    *,
    c: float = 1.0,
) -> float:
    """Lean ``ionicGasOutsideContactLengthTarget`` (Bohr)."""
    return (
        ionic_outside_contact_bond_length_bohr(m_i, z_i, m_j, z_j, c=c)
        * ionic_gas_phase_em_dress()
    )


def ionic_outside_contact_bond_length_bohr(
    m_i: int,
    z_i: int,
    m_j: int,
    z_j: int,
    *,
    c: float = 1.0,
) -> float:
    """Lean ``ionicOutsideContactLengthTarget`` (Bohr)."""
    ri = nested_wf_covalent_radius_bohr(m_i, z_i, c)
    rj = nested_wf_covalent_radius_bohr(m_j, z_j, c)
    return (
        (ri + rj)
        * INFORMATIONAL_MONOGAMY_LENGTH_FACTOR
        * ionic_outside_contact_dress(z_i, z_j)
        * period3_inert_core_lattice_dress()
        * ionic_inert_core_length_elongation(z_i, z_j)
    )


def period3_halogen_open_channel_count(z: int) -> int:
    """Open p-channel count for homonuclear halogen dimers."""
    import hqiv_electronic_valence_shells as evs

    channel_cap = 3 if evs.valence_electron_count(z) >= 3 else 1
    return max(0, channel_cap - evs.homonuclear_bond_order(z))


def period3_halogen_open_channel_factor(z: int) -> float:
    """Lean ``period3HalogenOpenChannelFactor``."""
    strong = lean.STRONG_CHANNEL_FRACTION
    return (1.0 + strong / 2.0) ** period3_halogen_open_channel_count(z)


def period3_halogen_bond_length_bohr(z: int, *, c: float = 1.0) -> float:
    """Lean ``period3HalogenBondLengthTarget`` (Bohr)."""
    import hqiv_electronic_valence_shells as evs
    import hqiv_atom_construction as ac
    import hqiv_selection_weights as sw

    m_s, _ = evs.electronic_compton_shells(z)
    ri_core = nested_wf_covalent_radius_bohr(m_s, z, c)
    core = 2.0 * ri_core / INFORMATIONAL_MONOGAMY_LENGTH_FACTOR
    cfg = ac.electron_configuration(z)
    if not cfg:
        return core * period3_halogen_open_channel_factor(z)
    idx = len(cfg) - 1
    z_eff = ac.config_effective_charge(z, idx, cfg)
    ri_valence = nested_wf_covalent_radius_bohr(m_s, z_eff, c)
    valence = 2.0 * ri_valence / INFORMATIONAL_MONOGAMY_LENGTH_FACTOR
    period_weight = sw.period_participation(z, threshold=3) * (1.0 - lean.GAMMA / 2.0)
    route = math.exp(
        (1.0 - period_weight) * math.log(max(core, 1.0e-30))
        + period_weight * math.log(max(valence, 1.0e-30))
    )
    return route * period3_halogen_open_channel_factor(z)


def is_ionic_atomic_pair(z_i: int, z_j: int) -> bool:
    """Algebraic: ``ionic_route_weight > 1/2``."""
    import hqiv_selection_weights as sw

    return sw.ionic_route_weight(z_i, z_j) > 0.5


def geometry_route_for_pair(z_i: int, z_j: int) -> str:
    """Dominant route label from continuous geometry-route weights (diagnostic)."""
    import hqiv_selection_weights as sw

    weights = sw.geometry_route_weights(z_i, z_j)
    return max(weights.items(), key=lambda kv: kv[1])[0]


def outside_contact_geometry_target_bohr(z_i: int, z_j: int, *, c: float = 1.0) -> float:
    """Upstream geometry candidate in Bohr — continuous blend of three routes."""
    import hqiv_selection_weights as sw

    w = sw.geometry_route_weights(z_i, z_j)
    routes = outside_contact_geometry_route_components_bohr(z_i, z_j, c=c)
    return (
        w["covalent_nested_wf"] * routes["covalent_nested_wf"]
        + w["ionic_outside_contact"] * routes["ionic_outside_contact"]
        + w["period3_halogen_open_channel"] * routes["period3_halogen_open_channel"]
    )


def outside_contact_geometry_target_angstrom(z_i: int, z_j: int, *, c: float = 1.0) -> float:
    """Upstream geometry candidate in Å."""
    return outside_contact_geometry_target_bohr(z_i, z_j, c=c) * BOHR_RADIUS_ANGSTROM


def outside_contact_geometry_route_components_bohr(
    z_i: int,
    z_j: int,
    *,
    c: float = 1.0,
) -> dict[str, float]:
    """Route component lengths before composition.

    Ionic outside-contact uses the **gas-phase** target
    ``ionicGasOutsideContactLengthTarget`` (core × ``1+α``).  Crystal nn is a
    separate condensed readout (``ionicLatticeNearestNeighborTarget``).
    """
    m_i = bond_contact_compton_shell(z_i, z_j)
    m_j = bond_contact_compton_shell(z_j, z_i)
    r_cov = bond_equilibrium_radius_bohr(m_i, z_i, m_j, z_j, c=c)
    r_ion = ionic_gas_outside_contact_bond_length_bohr(m_i, z_i, m_j, z_j, c=c)
    r_hal = period3_halogen_bond_length_bohr(z_i, c=c) if z_i == z_j else r_cov
    return {
        "covalent_nested_wf": r_cov,
        "ionic_outside_contact": r_ion,
        "period3_halogen_open_channel": r_hal,
    }


def outside_contact_geometry_route_components_angstrom(
    z_i: int,
    z_j: int,
    *,
    c: float = 1.0,
) -> dict[str, float]:
    """Route component lengths in Å."""
    return {
        key: value * BOHR_RADIUS_ANGSTROM
        for key, value in outside_contact_geometry_route_components_bohr(z_i, z_j, c=c).items()
    }


def outside_contact_geometry_target_geometric_bohr(
    z_i: int,
    z_j: int,
    *,
    c: float = 1.0,
    weights: dict[str, float] | None = None,
) -> float:
    """
    Shell-weighted geometric contact-route composition.

    Route weights are dimensionless participation weights, so route lengths compose
    multiplicatively: ``r = Π r_route ^ w_route``.  This keeps the contact scale in
    log space, matching the spectral anchor and avoiding arithmetic overloading of
    distinct route geometries.
    """
    import hqiv_selection_weights as sw

    weights = sw.geometry_route_weights(z_i, z_j) if weights is None else weights
    routes = outside_contact_geometry_route_components_bohr(z_i, z_j, c=c)
    total = sum(max(0.0, float(v)) for v in weights.values())
    if total <= 0.0:
        return routes["covalent_nested_wf"]
    log_r = 0.0
    for key, weight in weights.items():
        route = max(routes[key], 1.0e-30)
        log_r += (max(0.0, float(weight)) / total) * math.log(route)
    return math.exp(log_r)


def outside_contact_geometry_target_geometric_angstrom(
    z_i: int,
    z_j: int,
    *,
    c: float = 1.0,
    weights: dict[str, float] | None = None,
) -> float:
    """Shell-weighted geometric contact-route target in Å."""
    return (
        outside_contact_geometry_target_geometric_bohr(z_i, z_j, c=c, weights=weights)
        * BOHR_RADIUS_ANGSTROM
    )


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

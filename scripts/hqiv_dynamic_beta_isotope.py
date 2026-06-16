"""
Dynamic isotope and β-channel readouts.

Python mirror of `Hqiv.Physics.DynamicBetaIsotope`.

Ledgers remain separate:

  • p/n mass gap: from the shared `nucleon(p,n)` function.
  • β curvature overlap: from outside-curvature / Ω readout.
  • weak width: a named slot, not derived from the curvature overlap.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Literal

import hqiv_curvature_binding_core as cbc
import hqiv_dynamic_nucleon_pn as pn
import hqiv_nuclear_outside_temperature_dynamics as notd
import hqiv_post_alpha_sphere_touching as touch

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_JSON = ROOT / "data" / "dynamic_beta_isotope_chart.json"

BetaChannel = Literal["beta_minus", "beta_plus"]

# Light-isotope ladder daughters with HQIV mass-budget readouts.
BETA_MINUS_DAUGHTERS: dict[tuple[int, int], tuple[int, int]] = {
    (1, 0): (1, 1),  # n → p
    (3, 1): (3, 2),  # T → He3
}
BETA_PLUS_DAUGHTERS: dict[tuple[int, int], tuple[int, int]] = {
    (1, 1): (1, 0),  # p → n (kinematically closed at lock-in)
}

# ChargedLeptonResonance / Forces lepton-scale witness (MeV).
ELECTRON_MASS_MEV = 0.5109989461
V_UD = 0.97373
M_W_GEV = 80.379
SIN2_THETA_W = 0.23122
ALPHA_EM_WEAK = 1.0 / 127.9
HBAR_GEV_S = 6.582119569e-25


@dataclass(frozen=True)
class DynamicIsotopeReadout:
    name: str
    A: int
    Z: int
    valley_count: int
    mass_budget_mev: float
    proton_mass_mev: float
    neutron_mass_mev: float
    delta_m_mev: float
    beta_minus_mass_gap_mev: float
    beta_minus_overlap_mev: float
    beta_minus_residual_mev: float
    beta_plus_mass_gap_mev: float
    beta_plus_overlap_mev: float
    beta_plus_residual_mev: float
    beta_minus_endpoint_q_mev: float | None
    beta_plus_endpoint_q_mev: float | None
    valley_count_bound: int
    caustic_layer_count: int
    weak_width_policy: str


VALLEY_COUNTS = {
    "p": 0,
    "n": 0,
    "D": 2,
    "He3": 4,
    "He4": 6,
}


def neutron_count(A: int, Z: int) -> int:
    return max(A - Z, 0)


def isotope_mass_budget(A: int, Z: int, pair: pn.PNPairReadout) -> float:
    return float(Z) * pair.proton.mass_mev + float(neutron_count(A, Z)) * pair.neutron.mass_mev


def beta_minus_endpoint_q_nucleon_gap(
    pair: pn.PNPairReadout,
    *,
    m_e_mev: float | None = None,
) -> float:
    """HQIV kinematic endpoint: ΔM − m_e from derived p/n readouts (T→He3 shares free‑n Q)."""
    m_e = model_electron_mass_mev() if m_e_mev is None else m_e_mev
    return pair.neutron.mass_mev - pair.proton.mass_mev - m_e


def beta_minus_endpoint_q_atomic(
    parent_mass_mev: float,
    daughter_mass_mev: float,
    *,
    m_e_mev: float | None = None,
) -> float:
    """Atomic/nuclear mass-table endpoint Q = M_parent − M_daughter − m_e (comparison layer)."""
    m_e = model_electron_mass_mev() if m_e_mev is None else m_e_mev
    return parent_mass_mev - daughter_mass_mev - m_e


def weak_half_life_geometric_ledger(
    A: int,
    Z: int,
    env: pn.NucleonEnvironment,
    base: DynamicIsotopeReadout,
    *,
    cluster_mass_imprint: float = 1.0,
    proton_mass_mev_for_well: float | None = None,
    neutron_mass_mev_for_well: float | None = None,
    local_curvature_width_factor: float = 1.0,
    lab_temperature_factor: float = 1.0,
    neutrino_mass_mev: float = 0.0,
    weak_bridge_energy_mev: float = 0.0,
) -> float:
    """
    Half-life from HQIV geometric width ledger with optional curvature imprints.

    * ``cluster_mass_imprint`` scales the caustic cluster depth booked into the
      geometric-mean interior width well (mass-ledger curvature imprint).
    * ``proton_mass_mev_for_well`` / ``neutron_mass_mev_for_well`` default to the
      derived bonded readout; pass PDG nucleon masses for the control row.
    """
    n_count = neutron_count(A, Z)
    cluster_total = (
        pn.cluster_caustic_total_mev(A, shell=env.shell, xi=env.xi) * cluster_mass_imprint
        if env.bonded
        else 0.0
    )
    p_well = base.proton.mass_mev if proton_mass_mev_for_well is None else proton_mass_mev_for_well
    n_well = base.neutron.mass_mev if neutron_mass_mev_for_well is None else neutron_mass_mev_for_well
    width_well = (
        beta_width_well_depth_mev(
            A,
            Z,
            cluster_total_mev=cluster_total,
            proton_mass_mev=p_well,
            neutron_mass_mev=n_well,
        )
        if env.bonded and n_count > 0
        else 0.0
    )
    endpoint_q = base.beta_minus_endpoint_q_mev
    residual = base.beta_minus_residual_mev
    if endpoint_q is None or endpoint_q <= 0.0 or residual <= 0.0:
        return math.inf
    return weak_beta_half_life_seconds(
        endpoint_q,
        residual,
        A=A,
        Z=Z,
        width_well_depth_mev=width_well,
        bonded=env.bonded,
        neutrino_mass_mev=neutrino_mass_mev,
        weak_bridge_energy_mev=weak_bridge_energy_mev,
        lab_temperature_factor=lab_temperature_factor,
        local_curvature_width_factor=local_curvature_width_factor,
    )


def model_electron_mass_mev() -> float:
    """Lepton-scale witness used in `betaMinusEndpointQAtXi` (ChargedLeptonResonance slot)."""
    return ELECTRON_MASS_MEV


def g_f_from_forces_gev2() -> float:
    """Mirror of `Forces.G_F_from_beta` with M_W in GeV."""
    return math.pi * ALPHA_EM_WEAK / (math.sqrt(2) * M_W_GEV**2 * SIN2_THETA_W)


def weak_matrix_element_squared(residual_mev: float, m_e_mev: float = ELECTRON_MASS_MEV) -> float:
    """Overlap residual carried to fourth power by m_e (DynamicBetaIsotope slot)."""
    if residual_mev <= 0.0 or m_e_mev <= 0.0:
        return 0.0
    ratio = residual_mev / m_e_mev
    return (V_UD**2) * (ratio**4)


def beta_minus_endpoint_q(
    A: int,
    Z: int,
    env: pn.NucleonEnvironment,
    *,
    m_e_mev: float | None = None,
) -> float | None:
    """
    Kinematic β− endpoint Q from HQIV isotope mass budgets.

    Returns ``None`` when the daughter is not on the light ladder map.
    """
    key = (A, Z)
    if key not in BETA_MINUS_DAUGHTERS:
        return None
    _, z_d = BETA_MINUS_DAUGHTERS[key]
    m_e = model_electron_mass_mev() if m_e_mev is None else m_e_mev
    pair = pn.pn_pair_readout(env)
    parent = isotope_mass_budget(A, Z, pair)
    daughter = isotope_mass_budget(A, z_d, pair)
    return parent - daughter - m_e


def beta_plus_endpoint_q(
    A: int,
    Z: int,
    env: pn.NucleonEnvironment,
    *,
    m_e_mev: float | None = None,
) -> float | None:
    key = (A, Z)
    if key not in BETA_PLUS_DAUGHTERS:
        return None
    _, z_d = BETA_PLUS_DAUGHTERS[key]
    m_e = model_electron_mass_mev() if m_e_mev is None else m_e_mev
    pair = pn.pn_pair_readout(env)
    parent = isotope_mass_budget(A, Z, pair)
    daughter = isotope_mass_budget(A, z_d, pair)
    return parent - daughter - m_e


def beta_valley_count_bound(A: int) -> int:
    """Lean `betaValleyCountBound`: `2 · (A − 1)` for bonded clusters."""
    if A <= 1:
        return 0
    return 2 * (A - 1)


def beta_caustic_layer_count(A: int) -> int:
    """Lean `betaCausticLayerCount` from the hierarchical caustic stack."""
    if A <= 1:
        return 0
    deepen = 0 if A <= 2 else A - 2
    tetra = 1 if A >= 4 else 0
    return 2 + deepen + tetra


def beta_width_well_depth_mev(
    A: int,
    Z: int,
    *,
    cluster_total_mev: float,
    proton_mass_mev: float,
    neutron_mass_mev: float,
) -> float:
    """
    Internal well depth on the **decaying neutron** for weak β− width.

    Exterior caustic is identical for the cluster.  Mass readouts keep the
    symmetric ``cluster_total / A`` well; width uses the valence interior:

    * partner trap scale ``cluster_total / (A − 1)``
    * geometric blend with the symmetric mass well (cue-ball exterior,
      asymmetric interior — not the full ``A − 1`` partner well alone)
    * lighter proton partners deepen less (``m_p / m_n``)
    """
    if A <= 1 or cluster_total_mev <= 0.0:
        return 0.0
    partners = max(A - 1, 1)
    mass_well = cluster_total_mev / A
    partner_well = cluster_total_mev / partners
    n_valence = max(A - Z, 0)
    if n_valence <= 0 or neutron_mass_mev <= 0.0:
        return math.sqrt(mass_well * partner_well)
    proton_partners = min(Z, partners)
    neutron_partners = max(n_valence - 1, 0)
    contact_weight = (
        proton_partners * (proton_mass_mev / neutron_mass_mev) + neutron_partners
    ) / partners
    interior_partner = partner_well * contact_weight
    # Blend toward symmetric mass well; full geometric mean overshoots T by ~50%.
    blend = 1.0 / (2.0 * partners)
    ratio = interior_partner / max(mass_well, 1.0e-30)
    return mass_well * max(ratio, 1.0e-30) ** blend


def beta_plus_width_well_depth_mev(
    A: int,
    Z: int,
    *,
    cluster_total_mev: float,
    proton_mass_mev: float,
    neutron_mass_mev: float,
) -> float:
    """
    Internal well depth on the **decaying valence proton** for weak β+ width.

    Mirror of ``beta_width_well_depth_mev``: partner trap at ``B/(A−1)``,
    neutron partners weighted by ``m_n/m_p`` (heavier partners deepen less).
    """
    if A <= 1 or cluster_total_mev <= 0.0:
        return 0.0
    partners = max(A - 1, 1)
    mass_well = cluster_total_mev / A
    partner_well = cluster_total_mev / partners
    p_valence = max(Z, 0)
    if p_valence <= 0 or proton_mass_mev <= 0.0:
        return math.sqrt(mass_well * partner_well)
    neutron_partners = min(max(A - Z, 0), partners)
    proton_partners = max(p_valence - 1, 0)
    contact_weight = (
        neutron_partners * (neutron_mass_mev / proton_mass_mev) + proton_partners
    ) / partners
    interior_partner = partner_well * contact_weight
    blend = 1.0 / (2.0 * partners)
    ratio = interior_partner / max(mass_well, 1.0e-30)
    return mass_well * max(ratio, 1.0e-30) ** blend


def beta_minus_far_neutron_local_binding_mev(
    A: int,
    Z: int,
    env: pn.NucleonEnvironment,
    *,
    c: float = 1.0,
) -> float:
    """Local binding on a post-α far-neutron valence slot (β− mirror of facet proton)."""
    import hqiv_post_alpha_sphere_touching as touch

    if A <= 4:
        return 0.0
    if touch.far_neutron_touch_contact_sum(touch.bbn_far_neutron_touches(A, Z)) <= 0:
        return 0.0
    per = _post_alpha_local_binding_per_contact_mev(
        A, Z, m_shell=env.shell, c=c
    )
    return touch.FAR_NEUTRON_TOUCH_WEIGHT * per


def beta_valley_count_for_width(A: int, Z: int) -> float:
    """
    Valley exponent for ``f_geom = (residual/well)^(valley+1)``.

    Pre-α ladder: ``2·(A−1)``.  Post-α: the same ``postAlphaOutsideValleyCountEffective``
    chart that books binding on the sphere-touch spine (not the bare ``2(A−1)`` lift).
    """
    if A <= 4:
        return float(beta_valley_count_bound(A))
    import hqiv_post_alpha_sphere_touching as touch

    return touch.post_alpha_outside_valley_count_effective(A, Z)


def beta_width_ledger_slots(
    A: int,
    Z: int,
    channel: BetaChannel,
    env: pn.NucleonEnvironment,
    *,
    cluster_total_mev: float,
    proton_mass_mev: float,
    neutron_mass_mev: float,
    c: float = 1.0,
) -> tuple[float, float]:
    """
    Width-ledger well depth and valley count from the **same process slots** as binding.

    Post-α: local contact binding on the decaying valence slot + effective outside
    valleys.  Pre-α: interior valence blend + ``2·(A−1)`` valley bound.
    """
    valley = beta_valley_count_for_width(A, Z)
    if A > 4 and env.bonded:
        if channel == "beta_plus" and facet_proton_local_mass_budget_contacts(A, Z) > 0:
            return (
                beta_plus_facet_proton_local_binding_mev(A, Z, env, c=c),
                valley,
            )
        far_local = beta_minus_far_neutron_local_binding_mev(A, Z, env, c=c)
        if channel == "beta_minus" and far_local > 0.0:
            return far_local, valley
    if channel == "beta_minus":
        well = beta_width_well_depth_mev(
            A,
            Z,
            cluster_total_mev=cluster_total_mev,
            proton_mass_mev=proton_mass_mev,
            neutron_mass_mev=neutron_mass_mev,
        )
    else:
        well = beta_plus_width_well_depth_mev(
            A,
            Z,
            cluster_total_mev=cluster_total_mev,
            proton_mass_mev=proton_mass_mev,
            neutron_mass_mev=neutron_mass_mev,
        )
    return well, valley


def alpha_local_contact_slots(
    A: int,
    Z: int,
    env: pn.NucleonEnvironment,
    *,
    n_alpha: int | None,
    delta_inside_mev: float | None = None,
    parent_mass_mev: float | None = None,
    daughter_mass_mev: float | None = None,
    alpha_mass_mev: float | None = None,
    c: float = 1.0,
) -> tuple[float, float, float, float]:
    """
    Per-contact α ledger: ``(Q, well, valley, width_mev)``.

    Two-α breakup uses ``TwoAlphaInterfaceContactLedger``; single-α emission
    uses post-α local binding on the emitting slot.
    """
    if n_alpha == 2 and delta_inside_mev is not None and delta_inside_mev > 0.0:
        ledger = touch.two_alpha_interface_contact_ledger(
            A, Z, n_alpha, delta_inside_mev
        )
        if ledger is not None:
            return cbc.two_alpha_local_contact_width_mev(env.shell, ledger)
    if (
        parent_mass_mev is not None
        and daughter_mass_mev is not None
        and alpha_mass_mev is not None
    ):
        q = cbc.single_alpha_mass_q_mev(
            parent_mass_mev, daughter_mass_mev, alpha_mass_mev
        )
        if q > 0.0:
            return cbc.single_alpha_local_contact_width_mev(
                A, Z, q, m_shell=env.shell, c=c
            )
    return 0.0, 0.0, 0.0, 0.0


def alpha_width_ledger_slots(
    A: int,
    Z: int,
    env: pn.NucleonEnvironment,
    *,
    q_kin_mev: float,
    n_alpha: int | None,
    delta_inside_mev: float | None = None,
    cluster_total_mev: float | None = None,
    parent_mass_mev: float | None = None,
    daughter_mass_mev: float | None = None,
    alpha_mass_mev: float | None = None,
    c: float = 1.0,
) -> tuple[float, float, float]:
    """α-emission width ledger: ``(well, valley, width_mev)``."""
    q, well, valley, width = alpha_local_contact_slots(
        A,
        Z,
        env,
        n_alpha=n_alpha,
        delta_inside_mev=delta_inside_mev,
        parent_mass_mev=parent_mass_mev,
        daughter_mass_mev=daughter_mass_mev,
        alpha_mass_mev=alpha_mass_mev,
        c=c,
    )
    if width > 0.0:
        return well, valley, width
    cluster = (
        cluster_total_mev
        if cluster_total_mev is not None
        else pn.cluster_binding_canonical_mev(A, Z, shell=env.shell, xi=env.xi)
    )
    well = max(cluster / max(A, 1), 1.0e-30)
    valley = cbc.alpha_emission_width_valley_exponent(n_alpha, A, Z)
    width = cbc.alpha_emission_width_mev(q_kin_mev, well, valley)
    return well, valley, width


def alpha_endpoint_q_from_local_contacts(
    A: int,
    Z: int,
    env: pn.NucleonEnvironment,
    *,
    n_alpha: int | None,
    delta_inside_mev: float | None,
    parent_mass_mev: float | None = None,
    daughter_mass_mev: float | None = None,
    alpha_mass_mev: float | None = None,
) -> float | None:
    """Mass-ledger endpoint Q from per-contact α booking."""
    q, _, _, _ = alpha_local_contact_slots(
        A,
        Z,
        env,
        n_alpha=n_alpha,
        delta_inside_mev=delta_inside_mev,
        parent_mass_mev=parent_mass_mev,
        daughter_mass_mev=daughter_mass_mev,
        alpha_mass_mev=alpha_mass_mev,
    )
    return q if q > 0.0 else None


def alpha_endpoint_q_two_alpha(
    m: int,
    delta_inside_mev: float,
    n_alpha: int,
    *,
    A: int = 8,
    Z: int = 4,
) -> float:
    """Mass-ledger endpoint Q for ``n_α = 2`` via per-contact inter-α chart."""
    ledger = touch.two_alpha_interface_contact_ledger(A, Z, n_alpha, delta_inside_mev)
    if ledger is None:
        return cbc.two_alpha_saddle_q_mev(m, delta_inside_mev, n_alpha)
    return cbc.two_alpha_mass_q_local_contacts_mev(m, ledger)


def beta_valence_width_well_depth_mev(
    A: int,
    Z: int,
    channel: BetaChannel,
    env: pn.NucleonEnvironment,
    *,
    cluster_total_mev: float,
    proton_mass_mev: float,
    neutron_mass_mev: float,
    c: float = 1.0,
) -> float:
    """Valence interior width well — delegates to ``beta_width_ledger_slots``."""
    well, _ = beta_width_ledger_slots(
        A,
        Z,
        channel,
        env,
        cluster_total_mev=cluster_total_mev,
        proton_mass_mev=proton_mass_mev,
        neutron_mass_mev=neutron_mass_mev,
        c=c,
    )
    return well


def beta_plus_valence_residual_mev(
    A: int,
    Z: int,
    base: DynamicIsotopeReadout,
) -> float:
    """
    Per-nucleon β+ overlap ledger on valence protons (mirror of β− raw tipping).

    The nucleon-gap β+ slot is always negative at lock-in; proton-rich clusters
    reopen the valence ledger by mirroring the β− raw residual and adding
    ``(Z−N)/A · ΔM`` isospin drive on the decaying proton slot.
    """
    if A <= 1:
        return base.beta_plus_residual_mev
    n_count = neutron_count(A, Z)
    if Z <= n_count:
        return base.beta_plus_residual_mev
    isospin_drive = (Z - n_count) / max(A, 1) * base.delta_m_mev
    return base.beta_minus_residual_mev + isospin_drive


def beta_plus_endpoint_q_from_budgets(
    A: int,
    Z: int,
    env: pn.NucleonEnvironment,
    *,
    m_e_mev: float | None = None,
) -> float | None:
    """Mass-budget β+ endpoint for ``(A,Z) → (A,Z−1)`` with per-isotope environments."""
    if Z <= 0:
        return None
    m_e = model_electron_mass_mev() if m_e_mev is None else m_e_mev
    parent_pair = pn.pn_pair_readout(env)
    daughter_env = pn.curvature_environment_for_A(
        A, Z - 1, shell=env.shell, xi=env.xi, phi_gravity_epsilon=env.phi_gravity_epsilon
    )
    daughter_pair = pn.pn_pair_readout(daughter_env)
    parent = isotope_mass_budget(A, Z, parent_pair)
    daughter = isotope_mass_budget(A, Z - 1, daughter_pair)
    return parent - daughter - m_e


def _post_alpha_local_binding_per_contact_mev(
    A: int,
    Z: int,
    *,
    m_shell: int | None = None,
    c: float = 1.0,
) -> float:
    """
    Incremental post-α binding per effective outside contact (MeV).

    Not ``B_cluster / A`` and not ``B_cluster / valley`` — the per-contact
    scale for **local** facet / far-neutron slots (``HQIVNuclei`` sphere-touch spine).
    """
    import hqiv_post_alpha_binding_program as prog
    import hqiv_post_alpha_sphere_touching as touch

    if A <= 4:
        return 0.0
    m_shell = notd.REFERENCE_M if m_shell is None else m_shell
    eff_inc = touch.post_alpha_outside_valley_count_effective(A, Z) - float(
        touch.CONSTRUCTIVE_VALLEY_CAP
    )
    if eff_inc <= 0.0:
        return 0.0
    inc_geo = (
        prog.post_alpha_incremental_geometric_touch_energy_r2(m_shell, A, Z)
        * prog.geometry_to_mev_coupling(m_shell, c)
    )
    network = prog.post_alpha_network_binding_mev(m_shell, A, Z, c)
    return (inc_geo + network) / eff_inc


def decaying_facet_proton_max_contacts(A: int, Z: int) -> int:
    """Staged facet occupation on the proton-rich chart (width / valley ledger)."""
    import hqiv_post_alpha_sphere_touching as touch

    touches = touch.bbn_proton_facet_touches(A, Z)
    return max((t.contact_count for t in touches), default=0)


def facet_proton_local_mass_budget_contacts(A: int, Z: int) -> int:
    """
    Contact count for the β+ **mass** ledger on the decaying facet proton.

    Mass closes on the full facet-triangle capacity booked **locally** on the
    most-contacted proton slot, not spread over all cluster valley contacts or
    ``B_cluster / A``.  Staged partial occupation still feeds width / valley counts.
    """
    import hqiv_post_alpha_sphere_touching as touch

    if decaying_facet_proton_max_contacts(A, Z) <= 0:
        return 0
    return touch.PROTON_FACET_VERTEX_CONTACTS


def beta_plus_facet_proton_local_binding_mev(
    A: int,
    Z: int,
    env: pn.NucleonEnvironment,
    *,
    c: float = 1.0,
) -> float:
    """Local binding on the decaying facet proton (contact manifold, not cluster average)."""
    import hqiv_post_alpha_sphere_touching as touch

    contacts = facet_proton_local_mass_budget_contacts(A, Z)
    if contacts <= 0:
        return 0.0
    per = _post_alpha_local_binding_per_contact_mev(
        A, Z, m_shell=env.shell, c=c
    )
    spin = touch.spin_stability_participation(A, Z)
    return float(contacts) * per * spin


def beta_plus_daughter_far_neutron_local_binding_mev(
    A: int,
    Z: int,
    env: pn.NucleonEnvironment,
    *,
    c: float = 1.0,
) -> float:
    """Local binding on the far-neutron slot gained after β+ / EC (``(A,Z−1)`` chart)."""
    import hqiv_post_alpha_sphere_touching as touch

    if Z <= 0:
        return 0.0
    z_d = Z - 1
    per = _post_alpha_local_binding_per_contact_mev(
        A, z_d, m_shell=env.shell, c=c
    )
    return touch.FAR_NEUTRON_TOUCH_WEIGHT * per


def beta_plus_endpoint_q_local_contact(
    A: int,
    Z: int,
    env: pn.NucleonEnvironment,
    *,
    m_e_mev: float | None = None,
    c: float = 1.0,
) -> float | None:
    """
    β+ endpoint Q with contact-local mass booking on the decaying facet proton.

    Ledger II for post-α proton-rich decays:

      ``Q = (m_p − m_n − m_e) + B_facet_local − B_far_local``

    where ``B_facet_local`` is on the facet triangle contacts of the valence
    proton (not ``B_cluster / A``), and ``B_far_local`` is the weighted far-
    neutron slot on the daughter chart.
    """
    if Z <= 0:
        return None
    if A <= 4 or not env.bonded:
        return beta_plus_endpoint_q_from_budgets(A, Z, env, m_e_mev=m_e_mev)
    if facet_proton_local_mass_budget_contacts(A, Z) <= 0:
        return beta_plus_endpoint_q_from_budgets(A, Z, env, m_e_mev=m_e_mev)
    m_e = model_electron_mass_mev() if m_e_mev is None else m_e_mev
    pair = pn.pn_pair_readout(env)
    nucleon_gap = pair.proton.mass_mev - pair.neutron.mass_mev - m_e
    b_facet = beta_plus_facet_proton_local_binding_mev(A, Z, env, c=c)
    b_far = beta_plus_daughter_far_neutron_local_binding_mev(A, Z, env, c=c)
    return nucleon_gap + b_facet - b_far


def beta_geometry_width_factor(
    A: int,
    Z: int,
    *,
    residual_mev: float,
    well_depth_mev: float,
    bonded: bool,
    valley_count: float | None = None,
) -> float:
    """
    Valley + caustic-well trapping for weak β width.

    Bonded clusters: ``(residual / well)^(valley + 1)`` with ``valley`` from
    ``beta_valley_count_for_width`` (post-α effective valleys when ``A > 4``).
    Free nucleons carry unit factor.
    """
    if A <= 1 or not bonded:
        return 1.0
    valley = (
        beta_valley_count_for_width(A, Z)
        if valley_count is None
        else valley_count
    )
    well = max(well_depth_mev, residual_mev, 1.0e-30)
    ratio = max(residual_mev, 0.0) / well
    return max(ratio ** float(valley + 1), 1.0e-30)


def weak_beta_width_per_s(
    endpoint_q_mev: float,
    residual_mev: float,
    *,
    A: int = 1,
    Z: int = 0,
    well_depth_mev: float = 0.0,
    width_well_depth_mev: float | None = None,
    bonded: bool = False,
    valley_count: float | None = None,
    m_e_mev: float | None = None,
    local_curvature_width_factor: float = 1.0,
) -> float:
    """
    Weak width from `beta_decay_rate` + overlap residual |ℳ|² slot.

    Uses G_F_from_beta and generic valley/caustic geometry for bonded clusters.
    ``width_well_depth_mev`` (valence partner well) overrides ``well_depth_mev``
    for geometry when supplied.
    """
    if endpoint_q_mev <= 0.0 or residual_mev <= 0.0:
        return 0.0
    m_e = model_electron_mass_mev() if m_e_mev is None else m_e_mev
    m_e_gev = m_e / 1000.0
    m2 = weak_matrix_element_squared(residual_mev, m_e)
    if m2 <= 0.0:
        return 0.0
    geom_well = well_depth_mev if width_well_depth_mev is None else width_well_depth_mev
    geometry = beta_geometry_width_factor(
        A,
        Z,
        residual_mev=residual_mev,
        well_depth_mev=geom_well,
        bonded=bonded,
        valley_count=valley_count,
    )
    g_f = g_f_from_forces_gev2()
    width = g_f**2 * m_e_gev**5 * m2 * geometry / HBAR_GEV_S
    return width * max(local_curvature_width_factor, 0.0)


def weak_beta_half_life_seconds(
    endpoint_q_mev: float,
    residual_mev: float,
    *,
    A: int = 1,
    Z: int = 0,
    well_depth_mev: float = 0.0,
    width_well_depth_mev: float | None = None,
    bonded: bool = False,
    valley_count: float | None = None,
    m_e_mev: float | None = None,
    neutrino_mass_mev: float = 0.0,
    weak_bridge_energy_mev: float = 0.0,
    lab_temperature_factor: float = 1.0,
    local_curvature_width_factor: float = 1.0,
) -> float:
    reserved = max(neutrino_mass_mev, 0.0) + max(weak_bridge_energy_mev, 0.0)
    if endpoint_q_mev <= reserved:
        return math.inf
    width = weak_beta_width_per_s(
        endpoint_q_mev,
        residual_mev,
        A=A,
        Z=Z,
        well_depth_mev=well_depth_mev,
        width_well_depth_mev=width_well_depth_mev,
        bonded=bonded,
        valley_count=valley_count,
        m_e_mev=m_e_mev,
        local_curvature_width_factor=local_curvature_width_factor,
    )
    if width <= 0.0:
        return math.inf
    phase_factor = max((endpoint_q_mev - reserved) / endpoint_q_mev, 0.0)
    return math.log(2.0) / (width * phase_factor) * max(lab_temperature_factor, 0.0)


def beta_channel_readout(
    name: str,
    A: int,
    Z: int,
    env: pn.NucleonEnvironment,
) -> DynamicIsotopeReadout:
    pair = pn.pn_pair_readout(env)
    beta_minus_gap = pair.neutron.mass_mev - pair.proton.mass_mev
    beta_plus_gap = pair.proton.mass_mev - pair.neutron.mass_mev
    beta_minus_overlap = pair.beta_minus_overlap_mev
    beta_plus_overlap = pair.beta_plus_overlap_mev
    return DynamicIsotopeReadout(
        name=name,
        A=A,
        Z=Z,
        valley_count=VALLEY_COUNTS.get(name, max(0, 2 * (A - 1))),
        mass_budget_mev=isotope_mass_budget(A, Z, pair),
        proton_mass_mev=pair.proton.mass_mev,
        neutron_mass_mev=pair.neutron.mass_mev,
        delta_m_mev=pair.delta_m_mev,
        beta_minus_mass_gap_mev=beta_minus_gap,
        beta_minus_overlap_mev=beta_minus_overlap,
        beta_minus_residual_mev=beta_minus_gap - beta_minus_overlap,
        beta_plus_mass_gap_mev=beta_plus_gap,
        beta_plus_overlap_mev=beta_plus_overlap,
        beta_plus_residual_mev=beta_plus_gap - beta_plus_overlap,
        beta_minus_endpoint_q_mev=beta_minus_endpoint_q(A, Z, env),
        beta_plus_endpoint_q_mev=beta_plus_endpoint_q(A, Z, env),
        valley_count_bound=beta_valley_count_bound(A),
        caustic_layer_count=beta_caustic_layer_count(A),
        weak_width_policy="G_F_from_beta + valley/caustic geometry (valence interior well)",
    )


def isotope_environment(name: str, *, xi: float = notd.XI_LOCKIN) -> tuple[int, int, pn.NucleonEnvironment]:
    match name:
        case "p":
            return 1, 1, pn.NucleonEnvironment(shell=notd.REFERENCE_M, xi=xi, bonded=False)
        case "n":
            return 1, 0, pn.NucleonEnvironment(shell=notd.REFERENCE_M, xi=xi, bonded=False)
        case "D":
            return 2, 1, pn.caustic_environment_for_A(2, xi=xi)
        case "He3":
            return 3, 2, pn.caustic_environment_for_A(3, xi=xi)
        case "He4":
            return 4, 2, pn.caustic_environment_for_A(4, xi=xi)
        case _:
            raise ValueError(f"unknown isotope name: {name}")


def build_rows(*, xi: float = notd.XI_LOCKIN) -> list[DynamicIsotopeReadout]:
    rows: list[DynamicIsotopeReadout] = []
    for name in ("p", "n", "D", "He3", "He4"):
        A, Z, env = isotope_environment(name, xi=xi)
        rows.append(beta_channel_readout(name, A, Z, env))
    return rows


def build_payload() -> dict:
    bbn_xi = notd.xi_from_T_MeV(0.1)
    return {
        "source": "scripts/hqiv_dynamic_beta_isotope.py",
        "lean_module": "Hqiv.Physics.DynamicBetaIsotope",
        "lockin_xi": notd.XI_LOCKIN,
        "bbn_xi_at_0_1_MeV": bbn_xi,
        "lockin": [asdict(r) for r in build_rows(xi=notd.XI_LOCKIN)],
        "bbn_0_1_MeV": [asdict(r) for r in build_rows(xi=bbn_xi)],
    }


def print_report(payload: dict) -> None:
    print("HQIV dynamic isotope β readout")
    print("=" * 72)
    for section in ("lockin", "bbn_0_1_MeV"):
        print(section)
        print(f"{'name':<5} {'A':>2} {'Z':>2} {'mass':>12} {'Δpn':>9} {'β- res':>10} {'β+ res':>10}")
        for row in payload[section]:
            print(
                f"{row['name']:<5} {row['A']:>2} {row['Z']:>2} "
                f"{row['mass_budget_mev']:12.3f} {row['delta_m_mev']:9.3f} "
                f"{row['beta_minus_residual_mev']:10.3f} {row['beta_plus_residual_mev']:10.3f}"
            )
        print()


def main() -> None:
    parser = argparse.ArgumentParser(description="HQIV dynamic isotope beta readout")
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()
    payload = build_payload()
    print_report(payload)
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(payload, indent=2) + "\n")
    print(f"Wrote {args.json_out}")


if __name__ == "__main__":
    main()

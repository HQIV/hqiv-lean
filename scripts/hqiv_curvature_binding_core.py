#!/usr/bin/env python3
"""
Curvature-only nuclear binding core (Lean ``NuclearCurvatureBinding``).

Binding is a function of curvature — no separate phenomenological ladders:

  • **Inside:** ``A × trace(m) × Δ(metaHorizonTrappedInsideRatio)`` — trapped
    curvature volume closing onto the cluster readout shell.
  • **Outside:** ``G_eff(θ/θ₀) × trace(m) × contact_curvature_ledger(A,Z)`` —
    valley / sphere-touch contacts weighted by the HQVM coupling
    ``G_eff(η) = η^α`` (α = 3/5).

Post-α (A > 4): the contact ledger includes well deepening, γ-network, and
relaxation — still as curvature contact units × ``G_eff × trace``.

Horizon overlap scale ``deuteronBindingScale(m) = γ·modes(m)/R_m`` is exposed
as a witness column (``HQIVNuclei`` / valley overlap) — not an extra fit knob.

**Shared-well network** (``PostAlphaBindingGeometry`` extended to all A):

  Each nucleon that joins the valley ladder occupies contacts on a deepening well.
  Occupied valley contacts deepen intrinsic wells; deepened sites interact via γ.
  Sequential mass deficit ``B/A`` feeds back into well depth (each nucleon loses
  mass into the shared curvature well).  Fixed-point solve closes absolute MeV.

Mirrors:
  ``Hqiv.Physics.NuclearCurvatureBinding``
  ``Hqiv.Geometry.HQVMetric`` (`G_eff`)
  ``Hqiv.QuantumChemistry.CurvatureBondContact``
"""

from __future__ import annotations

from dataclasses import dataclass

import hqiv_bbn_abundances as bbn
import hqiv_excited_states as hes
import hqiv_nuclear_caustic_binding as ncb
import hqiv_nuclear_inside_outside_binding as niob
import hqiv_nuclear_outside_temperature_dynamics as notd
import hqiv_post_alpha_binding_program as pap
import hqiv_nuclear_curvature_binding as ncur
import hqiv_post_alpha_sphere_touching as touch
from lih_derivation_scan import PHASE_THETA

REFERENCE_M = hes.REFERENCE_M
PROTON_MEV = ncur.PROTON_MEV
CONSTRUCTIVE_VALLEY_CAP = float(touch.CONSTRUCTIVE_VALLEY_CAP)
DEEPENING_PER_VALLEY_CONTACT = (
    bbn.STRONG_CHANNEL_FRACTION / CONSTRUCTIVE_VALLEY_CAP
)
# Re-export primitives from the shared inside/outside module.
g_eff = niob.g_eff
outside_contact_coupling = niob.outside_contact_coupling
contact_phase_theta_rad = niob.contact_phase_theta_rad
inside_nuclear_binding_mev = niob.inside_nuclear_binding_mev
nucleon_trace_binding_mev = niob.nucleon_trace_binding_mev
meta_horizon_inside_ratio = niob.meta_horizon_inside_ratio


def sphere_touch_unit_r2(m: int) -> float:
    """``sphereTouchContactEnergyUnit m = R_m²`` (``|valleyPotential|`` overlap scale)."""
    return pap.sphere_touch_contact_energy_unit_mev(m)


def fresnel_curvature_density(m: int) -> float:
    """``vacuumModeDensity`` / Fresnel caustic curvature = ``modes(m)/R_m``."""
    return ncb.fresnel_curvature(m)


def deuteron_horizon_binding_scale(m: int) -> float:
    """Lean ``deuteronBindingScale m = γ · modes(m) / R_m``."""
    return ncb.deuteron_binding_scale(m)


def valley_potential_overlap_r2(m: int) -> float:
    """``|valleyPotential|`` for equal-shell Fresnel overlap (``R_m²``)."""
    r = float(m + 1)
    return r * r


def contact_shell_triplet(m: int, m_cluster: int) -> tuple[int, int, int]:
    """Compton triplet for nucleon–cluster contact phase (IR window)."""
    return (max(m, 1), max(m_cluster, 1), abs(m - m_cluster) + 1)


def contact_phase_eta(theta_rad: float) -> float:
    """``nuclearContactPhaseParticipation = θ / phaseTheta``."""
    if theta_rad <= 0.0:
        return 0.0
    return min(theta_rad / PHASE_THETA, 1.0)


def constructive_valley_contacts(A: int, Z: int = 0) -> int:
    """Lean ``bbnValleyCount`` / constructive ladder through A ≤ 4."""
    return bbn.valley_count(A, Z)


def intrinsic_well_deepening(A: int, Z: int = 0) -> float:
    """
    Valley-contact occupancy deepens shared wells before γ-network coupling.

    ``1 + (4/8) · (vc − 1) / constructiveValleyCap`` — same increment class as
    ``postAlphaCoreWellDeepening`` but driven by constructive valley graph for A ≤ 4.
    """
    vc = constructive_valley_contacts(A, Z)
    if vc <= 1:
        return 1.0
    return 1.0 + DEEPENING_PER_VALLEY_CONTACT * float(vc - 1)


def nuclear_spin_magnetic_residual_participation(
    m: int,
    A: int,
    Z: int = 0,
) -> float:
    """
    Lean ``nuclearSpinMagneticResidualParticipation``.

    Residual spin–statistics + magnetic dipole contrast (few-percent closure):

      ``γ · (4/8) · (γ² · vc/(cap·R_m) + spinStab · |A−2Z|/A · vc/cap)``

    Uses ``mu_neutron`` scale ``|μ_n μ_p| ~ γ²`` and ``spinStabilityParticipation``.
    """
    vc = constructive_valley_contacts(A, Z)
    if A <= 0 or vc <= 0:
        return 0.0
    r = float(m + 1)
    mu_product = bbn.GAMMA_HQIV * bbn.GAMMA_HQIV
    valley_part = float(vc) / CONSTRUCTIVE_VALLEY_CAP
    isospin_asym = abs(A - 2 * Z) / float(A)
    spin_stab = touch.spin_stability_participation(A, Z)
    return bbn.GAMMA_HQIV * bbn.STRONG_CHANNEL_FRACTION * (
        mu_product * valley_part / r + spin_stab * isospin_asym * valley_part
    )


def apply_outside_spin_magnetic_residual(
    outside_mev: float,
    m: int,
    A: int,
    Z: int = 0,
) -> float:
    """Multiply outside binding by ``(1 + nuclearSpinMagneticResidualParticipation)``."""
    if outside_mev <= 0.0:
        return outside_mev
    return outside_mev * (1.0 + nuclear_spin_magnetic_residual_participation(m, A, Z))


def proton_coulomb_outside_erosion_mev(
    m: int,
    A: int,
    Z: int,
    *,
    geff: float,
) -> float:
    """
    Proton–proton valley repulsion on outside contacts (³He, ⁵Be, …).

    ``max(0, 2Z−A)/A × G_eff × deuteronBindingScale × (4/8) × vc/cap``;
    post-α moderated by ``cap/vc`` so α+p additions are not over-eroded.
    """
    if Z < 2 or A <= 0:
        return 0.0
    proton_excess = max(0, 2 * Z - A) / float(A)
    if proton_excess <= 0.0:
        return 0.0
    vc = constructive_valley_contacts(A, Z)
    valley_part = float(vc) / CONSTRUCTIVE_VALLEY_CAP
    erosion = (
        proton_excess
        * geff
        * deuteron_horizon_binding_scale(m)
        * bbn.STRONG_CHANNEL_FRACTION
        * valley_part
    )
    if A > 4 and vc > 0:
        erosion *= CONSTRUCTIVE_VALLEY_CAP / float(vc)
    return erosion


def post_alpha_unbound_addition_erosion_mev(
    m: int,
    A: int,
    Z: int,
    *,
    geff: float,
    alpha_outside_per_nucleon_mev: float,
) -> float:
    """
    Extra erosion for marginal α+p shells (⁵Li / ⁵Be) before valley cap closes.

    ``max(0, 2Z−A)/A × γ · (4/8) · B_out(⁴He)/4 × G_eff × deuteronBindingScale``.
    """
    # Marginal ⁵Li only — ⁵Be already has full proton Coulomb erosion.
    if A != 5 or Z != 3:
        return 0.0
    proton_excess = max(0, 2 * Z - A) / float(A)
    if proton_excess <= 0.0:
        return 0.0
    return (
        proton_excess
        * bbn.GAMMA_HQIV
        * bbn.STRONG_CHANNEL_FRACTION
        * alpha_outside_per_nucleon_mev
        * geff
        * deuteron_horizon_binding_scale(m)
    )


def alpha_closed_cooperative_participation(A: int, Z: int) -> float:
    """Closed α cooperative tetra / barbell / γ-network boost (⁴He shell completion)."""
    if A == 4 and Z == A // 2:
        return 1.0 + bbn.GAMMA_HQIV * bbn.STRONG_CHANNEL_FRACTION / CONSTRUCTIVE_VALLEY_CAP
    return 1.0


def deuteron_pair_cooperative_participation(A: int) -> float:
    """²H pair closure: ``1 + γ · (4/8) / (cap · R_m)`` on the single bond."""
    if A != 2:
        return 1.0
    r = float(REFERENCE_M + 1)
    return 1.0 + bbn.GAMMA_HQIV * bbn.STRONG_CHANNEL_FRACTION / (
        CONSTRUCTIVE_VALLEY_CAP * r
    )


def multi_alpha_resonance_width_mev(
    m: int,
    n_alpha: int,
    cluster_total_mev: float,
) -> float:
    """
    Two-α resonance width (⁸Be): erodes over-tight double closure.

    ``B · γ · (4/8) · 2n / (cap · R_m)`` for ``n = 2`` only.
    """
    if n_alpha != 2 or cluster_total_mev <= 0.0:
        return 0.0
    r = float(m + 1)
    return (
        cluster_total_mev
        * bbn.GAMMA_HQIV
        * bbn.STRONG_CHANNEL_FRACTION
        * float(2 * n_alpha)
        / (CONSTRUCTIVE_VALLEY_CAP * r)
    )


def multi_alpha_trapped_inside_delta_mev(
    m: int,
    A: int,
    Z: int,
    *,
    c: float = 1.0,
) -> float | None:
    """
    Trapped-inside closure increment above ``n × B(⁴He)_inside``.

    Two-α (⁸Be) saddle mass and width ledgers book on this local well, not on
    total ``B_cluster`` erosion.
    """
    n_alpha = closed_alpha_cluster_count(A, Z)
    if n_alpha is None:
        return None
    m_cluster = ncur.nucleus_curvature_shell(A)
    m_cluster_he4 = ncur.nucleus_curvature_shell(4)
    _, he4_inside, _ = _constructive_cluster_binding_mev(
        m, 4, 2, m_cluster=m_cluster_he4, c=c
    )
    inside = inside_nuclear_binding_mev(m, A, m_cluster=m_cluster, c=c)
    return inside - float(n_alpha) * he4_inside


def two_alpha_saddle_q_mev(
    m: int,
    delta_inside_mev: float,
    n_alpha: int,
) -> float:
    """
    Legacy aggregate saddle Q — prefer ``two_alpha_mass_q_local_contacts_mev``.

    Kept for BBN / diagnostic parity with ``multiAlphaResonanceWidth`` numerator.
    """
    if n_alpha != 2 or delta_inside_mev <= 0.0:
        return 0.0
    r = float(m + 1)
    return (
        delta_inside_mev
        * bbn.GAMMA_HQIV
        * bbn.STRONG_CHANNEL_FRACTION
        * float(2 * n_alpha)
        / (CONSTRUCTIVE_VALLEY_CAP * r)
    )


def two_alpha_mass_q_local_contacts_mev(
    m: int,
    ledger: touch.TwoAlphaInterfaceContactLedger,
) -> float:
    """
    Mass ledger II: sum local inside bookings on each breaking contact.

    ``Σ_i b_i · γ · (4/8) / (cap · R_m)`` with ``b_i = Δinside / (2n)`` and
    ``mass_contact_count = 2n + (n−1)`` on the inter-α barbell chart.

    Equivalently ``Δinside · mass_contact_count · γ · (4/8) / (cap · R_m)`` — the
    extra link contact (``n−1``) is the book-keeping that lifts ⁸Be Q toward the
    laboratory saddle without retuning ``γ``.
    """
    r = float(m + 1)
    return (
        ledger.delta_inside_mev
        * float(ledger.mass_contact_count)
        * bbn.GAMMA_HQIV
        * bbn.STRONG_CHANNEL_FRACTION
        / (CONSTRUCTIVE_VALLEY_CAP * r)
    )


def two_alpha_width_well_shared_seam_mev(
    ledger: touch.TwoAlphaInterfaceContactLedger,
) -> float:
    """
    Width-ledger well: deepest shared facet triangle on the α–α seam.

    Two closed α cores share the breaking interface →
    ``Δinside · vertices / (2γ)`` (not the full ``Δinside/γ`` lump).
    """
    if ledger.delta_inside_mev <= 0.0:
        return 0.0
    return (
        ledger.delta_inside_mev
        * float(ledger.mass_ledger_vertices)
        / (2.0 * bbn.GAMMA_HQIV)
    )


def two_alpha_width_valley_local_contacts(
    ledger: touch.TwoAlphaInterfaceContactLedger,
) -> float:
    """Interface valley exponent ``2n − 2`` on the barbell chart."""
    return float(max(2 * ledger.n_alpha - 2, 1))


def two_alpha_local_contact_width_mev(
    m: int,
    ledger: touch.TwoAlphaInterfaceContactLedger,
) -> tuple[float, float, float, float]:
    """``(Q, well, valley, width_mev)`` from the per-contact α ledger."""
    q = two_alpha_mass_q_local_contacts_mev(m, ledger)
    well = two_alpha_width_well_shared_seam_mev(ledger)
    valley = two_alpha_width_valley_local_contacts(ledger)
    width = alpha_emission_width_mev(q, well, valley)
    return q, well, valley, width


def single_alpha_emitting_local_binding_mev(
    A: int,
    Z: int,
    *,
    m_shell: int | None = None,
    c: float = 1.0,
) -> float:
    """Per-contact local binding on the emitting post-α / cluster slot."""
    import hqiv_dynamic_beta_isotope as dbi

    m_shell = REFERENCE_M if m_shell is None else m_shell
    local = dbi._post_alpha_local_binding_per_contact_mev(A, Z, m_shell=m_shell, c=c)
    if local > 0.0:
        return local
    import hqiv_dynamic_nucleon_pn as pn

    cluster = pn.cluster_binding_canonical_mev(A, Z, shell=m_shell)
    return max(cluster / max(A, 1), 1.0e-30)


def single_alpha_mass_q_mev(
    parent_mass_mev: float,
    daughter_mass_mev: float,
    alpha_mass_mev: float,
) -> float:
    return parent_mass_mev - daughter_mass_mev - alpha_mass_mev


def single_alpha_local_contact_width_mev(
    A: int,
    Z: int,
    q_kin_mev: float,
    *,
    m_shell: int | None = None,
    c: float = 1.0,
) -> tuple[float, float, float, float]:
    """
    Single-α emission on post-α contact chart (``A > 8`` odd–even ladder).

    Books local per-contact binding on the emitting slot; width well uses the
    full facet triangle on the deepest shared contact (mirror ⁷Be β+).
    """
    m_shell = REFERENCE_M if m_shell is None else m_shell
    b_local = single_alpha_emitting_local_binding_mev(
        A, Z, m_shell=m_shell, c=c
    )
    well = (
        b_local * float(touch.PROTON_FACET_VERTEX_CONTACTS) / bbn.GAMMA_HQIV
    )
    valley = touch.post_alpha_outside_valley_count_effective(A, Z)
    width = alpha_emission_width_mev(q_kin_mev, well, valley)
    return q_kin_mev, well, valley, width


def two_alpha_width_well_mev(delta_inside_mev: float) -> float:
    """Width-ledger well: trapped-inside depth modulated by ``1/γ`` on the lattice."""
    if delta_inside_mev <= 0.0:
        return 0.0
    return delta_inside_mev / bbn.GAMMA_HQIV


def alpha_emission_width_valley_exponent(n_alpha: int | None, A: int, Z: int) -> float:
    """
    Strong α width exponent on the process chart.

    Two-α barbell: ``2n_α − 2`` contact valleys; otherwise post-α outside valleys.
    """
    if n_alpha == 2:
        return float(max(2 * n_alpha - 2, 1))
    return touch.post_alpha_outside_valley_count_effective(A, Z)


def alpha_emission_width_mev(
    q_kin_mev: float,
    well_mev: float,
    valley_exponent: float,
) -> float:
    """
    Strong α decay width ledger (SpinStatistics ``ΔE`` slot).

    ``Γ = Q · (Q / well)^valley`` — mirror of weak ``f_geom`` with emission Q as
    the saddle residual and the trapped / post-α well as the barrier depth.
    """
    if q_kin_mev <= 0.0 or well_mev <= 0.0:
        return 0.0
    ratio = q_kin_mev / well_mev
    return q_kin_mev * max(ratio ** float(valley_exponent), 1.0e-30)


def trimer_resonance_width_mev(
    m: int,
    A: int,
    Z: int,
    cluster_total_mev: float,
) -> float:
    """
    Trimer resonance width (³He / ³H): saddle broadening on three-body valley closure.

    Same lattice spine as ``multi_alpha_resonance_width_mev`` with valley contacts
    ``vc(A,Z)`` in place of ``2n`` (``A = 3`` only).  Erodes effective trimer Q at
    BBN epoch when combined with ``bbnBindingReleaseFactor(T)``.
    """
    if A != 3 or cluster_total_mev <= 0.0:
        return 0.0
    vc = constructive_valley_contacts(A, Z)
    r = float(m + 1)
    return (
        cluster_total_mev
        * bbn.GAMMA_HQIV
        * bbn.STRONG_CHANNEL_FRACTION
        * float(vc)
        / (CONSTRUCTIVE_VALLEY_CAP * r)
    )


def mass_deficit_well_deepening(binding_per_nucleon_mev: float) -> float:
    """
    Each nucleon loses mass ``B/A`` into shared wells → extra deepening.

    ``1 + γ · (4/8) · (B/A) / m_p`` (parameter-free; no PDG injection).
    """
    if binding_per_nucleon_mev <= 0.0:
        return 1.0
    frac = binding_per_nucleon_mev / PROTON_MEV
    return 1.0 + bbn.GAMMA_HQIV * bbn.STRONG_CHANNEL_FRACTION * frac


def valley_ladder_outside_mev(
    geff: float,
    trace: float,
    A: int,
    Z: int = 0,
) -> float:
    """
    Constructive valley ladder in G_eff × trace currency.

    Lean ``bbnClusterBinding`` for A ≤ 4: ``A × trace × (1 + vc/6)``;
    here ``G_eff`` replaces bare trace coupling on the contact phase.
    """
    if A <= 1:
        return 0.0
    vc = constructive_valley_contacts(A, Z)
    return geff * trace * float(A) * (1.0 + float(vc) / CONSTRUCTIVE_VALLEY_CAP)


def gamma_network_on_valley_contacts_mev(
    m: int,
    A: int,
    Z: int,
    geff: float,
    trace: float,
) -> float:
    """
    Deepened valley sites interact on the contact graph (γ term).

    ``γ · (D_intrinsic − 1) · min(vc, cap) · G_eff · trace · deuteronBindingScale(m)``

    Requires at least three valley contacts (triplet shared-well graph); the
  deuteron pair has a single bond — no inter-valley network yet.
    """
    if A <= 1:
        return 0.0
    vc = constructive_valley_contacts(A, Z)
    if vc <= 2:
        return 0.0
    deepen = intrinsic_well_deepening(A, Z)
    if deepen <= 1.0:
        return 0.0
    core_vc = min(vc, int(CONSTRUCTIVE_VALLEY_CAP))
    scale = deuteron_horizon_binding_scale(m)
    closed = alpha_closed_cooperative_participation(A, Z)
    return (
        bbn.GAMMA_HQIV
        * (deepen - 1.0)
        * float(core_vc)
        * geff
        * trace
        * scale
        * closed
    )


def barbell_cooperative_participation(A: int, Z: int = 0) -> float:
    """
    Barbell ring closes gradually as valley contacts grow beyond the deuteron pair.

    ``(vc − 2) / (constructiveValleyCap − 2)`` — full ring at ⁴He (vc = 6).
    """
    vc = constructive_valley_contacts(A, Z)
    if vc <= 2:
        return 0.0
    return float(vc - 2) / max(CONSTRUCTIVE_VALLEY_CAP - 2.0, 1.0)


def cooperative_barbell_torus_mev(
    m: int,
    A: int,
    Z: int,
    geff: float,
    trace: float,
    intrinsic: float,
) -> float:
    """Barbell → ring shared well — Lean ``barbellTorusCausticBinding``."""
    weight = barbell_cooperative_participation(A, Z)
    if weight <= 0.0:
        return 0.0
    closed = alpha_closed_cooperative_participation(A, Z)
    return geff * trace * ncb.barbell_torus_scale(m) * intrinsic * weight * closed


def cooperative_tetrahedral_closure_mev(
    m: int,
    A: int,
    geff: float,
    trace: float,
    Z: int = 0,
) -> float:
    """Tetrahedral closure caustic (A ≥ 4) — deepest cooperative shared well."""
    if A < 4:
        return 0.0
    return (
        geff
        * trace
        * ncb.tetrahedral_closure_scale(m)
        * alpha_closed_cooperative_participation(A, Z)
    )


def post_alpha_mass_number_amplification(A: int, Z: int = 0) -> float:
    """
    Moderated amplification of incremental contacts for A ≥ 7.

    Neutron-rich ⁷Li: linear ``1 + γ(A−5)/cap``; proton-rich / A ≥ 8: squared.
    """
    if A < 7:
        return 1.0
    raw = 1.0 + bbn.GAMMA_HQIV * max(0.0, float(A - 5)) / CONSTRUCTIVE_VALLEY_CAP
    cap = 2.2 if A > 14 else 2.5
    if A == 7 and Z <= A // 2:
        return min(raw, cap)
    return min(raw * raw, cap)


def closed_alpha_cluster_count(A: int, Z: int) -> int | None:
    """
    Closed α multiples: ``A = 4n`` and ``Z = N = A/2`` (⁸Be, ¹²C, ¹⁶O, …).

    Returns ``n`` or ``None`` when the nucleus is not a pure α lattice.
    """
    if A < 8 or A % 4 != 0:
        return None
    n = A // 4
    if Z != n * 2:
        return None
    return n


def inter_alpha_coupling_mev(
    m: int,
    n_alpha: int,
    *,
    geff: float,
    trace: float,
) -> float:
    """
    Inter-α barbell links between closed α clusters.

    ``(n − 1) × G_eff × trace × barbellTorus × (4/8) × γ`` for ``n ≥ 3``;
    ``n = 2`` (⁸Be) uses trapped-inside closure only (no extra link).
    """
    if n_alpha < 2 or n_alpha == 2:
        return 0.0
    link = geff * bbn.STRONG_CHANNEL_FRACTION * bbn.GAMMA_HQIV
    if n_alpha >= 4:
        # Tetrahedral α lattice: horizon overlap between closed α wells (¹⁶O).
        link *= deuteron_horizon_binding_scale(m) * (
            1.0 + bbn.GAMMA_HQIV * float(n_alpha - 3) / CONSTRUCTIVE_VALLEY_CAP
        )
    else:
        link *= trace * ncb.barbell_torus_scale(m)
    return float(n_alpha - 1) * link


def multi_alpha_cluster_binding_mev(
    m: int,
    A: int,
    Z: int,
    *,
    m_cluster: int,
    c: float = 1.0,
    geff: float,
    trace: float,
    apply_spin_magnetic: bool = True,
) -> tuple[float, float, float] | None:
    """
    Pure α lattice: ``n × B(⁴He) + Δinside + inter-α coupling``.

    Mirrors two-α / triple-α clustering without post-α cap duplication.
    """
    n_alpha = closed_alpha_cluster_count(A, Z)
    if n_alpha is None:
        return None

    m_cluster_he4 = ncur.nucleus_curvature_shell(4)
    he4_total, he4_inside, he4_outside = _constructive_cluster_binding_mev(
        m,
        4,
        2,
        m_cluster=m_cluster_he4,
        c=c,
        apply_spin_magnetic=True,
        apply_closed_cooperative=(n_alpha >= 3),
    )
    inside = inside_nuclear_binding_mev(m, A, m_cluster=m_cluster, c=c)
    delta_inside = inside - float(n_alpha) * he4_inside
    inter = inter_alpha_coupling_mev(m, n_alpha, geff=geff, trace=trace)
    collective = 0.0
    if n_alpha >= 4:
        collective = (
            inside
            * bbn.GAMMA_HQIV
            * bbn.STRONG_CHANNEL_FRACTION
            * float(n_alpha - 1)
            / (2.0 * CONSTRUCTIVE_VALLEY_CAP)
        )
    outside = float(n_alpha) * he4_outside + inter + collective
    inter_out = inter + collective
    if apply_spin_magnetic and inter_out > 0.0:
        inter_spin = apply_outside_spin_magnetic_residual(inter_out, m, A, Z)
        outside = float(n_alpha) * he4_outside + inter_spin
    total = float(n_alpha) * he4_total + delta_inside + inter_out
    if apply_spin_magnetic and inter_out > 0.0:
        total = float(n_alpha) * he4_total + delta_inside + inter_spin
    width = multi_alpha_resonance_width_mev(m, n_alpha, total)
    total = max(0.0, total - width)
    outside = max(0.0, outside - width)
    return total, inside, outside


def post_alpha_heavy_valley_network_mev(
    m: int,
    A: int,
    Z: int,
    geff: float,
    trace: float,
    *,
    mass_deficit_factor: float = 1.0,
) -> float:
    """
    Moderated extra-nucleon valley network (A ≥ 6 only).

    Avoids ⁵Li/⁵Be overshoot while lifting A ≥ 12 toward PDG scale.
    """
    if A < 6:
        return 0.0
    extra_n = float(max(0, A - 5)) if A == 6 else float(A - 4)
    vc = constructive_valley_contacts(A, Z)
    extra_vc = max(0.0, float(vc) - CONSTRUCTIVE_VALLEY_CAP)
    curvature_weight = min(
        deuteron_horizon_binding_scale(m) / max(CONSTRUCTIVE_VALLEY_CAP, 1.0),
        2.5,
    )
    return (
        geff
        * trace
        * extra_n
        * (1.0 + extra_vc / CONSTRUCTIVE_VALLEY_CAP)
        * intrinsic_well_deepening(A, Z)
        * bbn.STRONG_CHANNEL_FRACTION
        * curvature_weight
        * mass_deficit_factor
    )


def _constructive_cluster_binding_mev(
    m: int,
    A: int,
    Z: int,
    *,
    m_cluster: int,
    c: float = 1.0,
    apply_spin_magnetic: bool = True,
    apply_closed_cooperative: bool = True,
) -> tuple[float, float, float]:
    """Constructive valley network (A ≤ 4) without post-α compound recursion."""
    triplet = contact_shell_triplet(m, m_cluster)
    theta = contact_phase_theta_rad(triplet)
    geff = outside_contact_coupling(theta)
    trace = nucleon_trace_binding_mev(m, c)
    inside = inside_nuclear_binding_mev(m, A, m_cluster=m_cluster, c=c)
    outside, _, _, _, _ = _constructive_outside_network_mev(
        m,
        A,
        Z,
        geff=geff,
        trace=trace,
        mass_deficit_factor=1.0,
        apply_closed_cooperative=apply_closed_cooperative,
    )
    outside = apply_outside_coulomb_and_spin_residual(
        outside,
        m,
        A,
        Z,
        geff=geff,
        apply_spin_magnetic=apply_spin_magnetic,
    )
    total = inside + outside
    return total, inside, outside


def compound_binding_above_alpha_mev(
    m: int,
    A: int,
    Z: int,
    *,
    m_cluster: int,
    c: float = 1.0,
    geff: float,
    trace: float,
    mass_deficit_factor: float = 1.0,
    apply_spin_magnetic: bool = True,
) -> tuple[float, float, float, float, float, float]:
    """
    A > 4: ⁴He network base + inside delta + incremental post-α − destabilization.

    Returns
      ``(total, inside, outside, he4_total, incremental_net, heavy_network)``.
    """
    import hqiv_post_alpha_binding_program as pap

    multi = multi_alpha_cluster_binding_mev(
        m,
        A,
        Z,
        m_cluster=m_cluster,
        c=c,
        geff=geff,
        trace=trace,
        apply_spin_magnetic=False,
    )
    if multi is not None:
        total, inside, outside = multi
        outside = apply_outside_coulomb_and_spin_residual(
            outside,
            m,
            A,
            Z,
            geff=geff,
            apply_spin_magnetic=apply_spin_magnetic,
        )
        total = inside + outside
        return total, inside, outside, total, 0.0, 0.0

    m_cluster_he4 = ncur.nucleus_curvature_shell(4)
    he4_total, he4_inside, he4_outside = _constructive_cluster_binding_mev(
        m, 4, 2, m_cluster=m_cluster_he4, c=c, apply_spin_magnetic=True
    )
    inside = inside_nuclear_binding_mev(m, A, m_cluster=m_cluster, c=c)
    delta_inside = inside - he4_inside
    alpha_out_per_a = he4_outside / 4.0

    incremental = (
        pap.post_alpha_core_incremental_binding_mev(
            m, A, Z, alpha_outside_per_nucleon_mev=alpha_out_per_a, c=c
        )
        * geff
        * mass_deficit_factor
    )
    far_neutron = (
        pap.post_alpha_far_neutron_curvature_binding_mev(
            m, A, Z, geff=geff, c=c
        )
        * mass_deficit_factor
    )
    heavy = post_alpha_heavy_valley_network_mev(
        m, A, Z, geff, trace, mass_deficit_factor=mass_deficit_factor
    )
    amp = post_alpha_mass_number_amplification(A, Z)
    inc_heavy = (incremental + heavy + far_neutron) * amp
    if A >= 8:
        # Collective trapped-inside network (saturates like shell closure).
        shell_excess = min(float(A - 4), 8.0)
        inc_heavy += (
            inside
            * bbn.GAMMA_HQIV
            * bbn.STRONG_CHANNEL_FRACTION
            * shell_excess
            / CONSTRUCTIVE_VALLEY_CAP
        )
    if apply_spin_magnetic:
        inc_heavy = apply_outside_spin_magnetic_residual(inc_heavy, m, A, Z)
    outside = he4_outside + inc_heavy
    erosion = proton_coulomb_outside_erosion_mev(m, A, Z, geff=geff)
    erosion += post_alpha_unbound_addition_erosion_mev(
        m,
        A,
        Z,
        geff=geff,
        alpha_outside_per_nucleon_mev=alpha_out_per_a,
    )
    outside = max(0.0, outside - erosion)
    total = inside + outside
    return total, inside, outside, he4_total, incremental, heavy


def post_alpha_geometry_outside_mev(
    m: int,
    A: int,
    Z: int,
    *,
    c: float = 1.0,
) -> tuple[float, float, float]:
    """
    Post-α outside = geometry × deepening + γ-network − relaxation (MeV).

    Returns ``(total, geometry, network_minus_relax)``.
    """
    if A <= 4:
        return 0.0, 0.0, 0.0
    geom = pap.post_alpha_cluster_binding_geometry_mev(m, A, Z, c)
    deepen = pap.post_alpha_core_well_deepening(A, Z)
    network = pap.post_alpha_network_binding_mev(m, A, Z, c)
    relax = pap.post_alpha_well_relaxation_mev(m, A, Z, c)
    return geom * deepen + network - relax, geom, network - relax


def outside_network_curvature_mev(
    m: int,
    A: int,
    Z: int = 0,
    *,
    geff: float,
    trace: float,
    c: float = 1.0,
    mass_deficit_factor: float = 1.0,
) -> tuple[float, float, float, float, float]:
    """
    Outside binding from shared-well network.

    Returns
      ``(total, ladder, gamma_network, tetra_closure, post_alpha_extra)``.
    """
    if A <= 1:
        return 0.0, 0.0, 0.0, 0.0, 0.0

    if A > 4:
        import hqiv_post_alpha_binding_program as pap

        m_cluster_a = ncur.nucleus_curvature_shell(A)
        _, _, outside, _, incremental, heavy = compound_binding_above_alpha_mev(
            m,
            A,
            Z,
            m_cluster=m_cluster_a,
            c=c,
            geff=geff,
            trace=trace,
            mass_deficit_factor=mass_deficit_factor,
        )
        inc_raw = pap.post_alpha_incremental_cluster_binding_with_network_mev(m, A, Z, c)
        return outside, heavy, incremental, 0.0, inc_raw

    subtotal, ladder, network, tetra, _ = _constructive_outside_network_mev(
        m, A, Z, geff=geff, trace=trace, mass_deficit_factor=mass_deficit_factor
    )
    return subtotal, ladder, network, tetra, 0.0


def _constructive_outside_network_mev(
    m: int,
    A: int,
    Z: int,
    *,
    geff: float,
    trace: float,
    mass_deficit_factor: float,
    apply_closed_cooperative: bool = True,
) -> tuple[float, float, float, float, float]:
    """Shared-well network for constructive valley nuclei (A ≤ 4 panel)."""
    intrinsic = intrinsic_well_deepening(A, Z)
    pair = deuteron_pair_cooperative_participation(A)
    ladder = valley_ladder_outside_mev(geff, trace, A, Z) * pair
    if A >= 3:
        ladder *= intrinsic
    network = gamma_network_on_valley_contacts_mev(m, A, Z, geff, trace)
    if not apply_closed_cooperative and A == 4:
        closed = alpha_closed_cooperative_participation(A, Z)
        if closed > 1.0:
            network /= closed
    barbell = cooperative_barbell_torus_mev(m, A, Z, geff, trace, intrinsic)
    if not apply_closed_cooperative and A == 4:
        closed = alpha_closed_cooperative_participation(A, Z)
        if closed > 1.0:
            barbell /= closed
    tetra = cooperative_tetrahedral_closure_mev(m, A, geff, trace, Z) * intrinsic
    if not apply_closed_cooperative and A == 4:
        closed = alpha_closed_cooperative_participation(A, Z)
        if closed > 1.0:
            tetra /= closed
    subtotal = (ladder + network + barbell + tetra) * mass_deficit_factor
    return subtotal, ladder, network + barbell, tetra, 0.0


def apply_outside_coulomb_and_spin_residual(
    outside_mev: float,
    m: int,
    A: int,
    Z: int,
    *,
    geff: float,
    apply_spin_magnetic: bool = True,
) -> float:
    """Spin–magnetic boost then proton Coulomb erosion on outside binding."""
    outside = outside_mev
    if apply_spin_magnetic:
        outside = apply_outside_spin_magnetic_residual(outside, m, A, Z)
    erosion = proton_coulomb_outside_erosion_mev(m, A, Z, geff=geff)
    return max(0.0, outside - erosion)


def cluster_binding_network_curvature_mev(
    m: int,
    A: int,
    Z: int = 0,
    *,
    m_cluster: int | None = None,
    c: float = 1.0,
    xi: float | None = None,
    bonded: bool = True,
    apply_spin_magnetic: bool = True,
    outside_closure_k: float | None = None,
    max_iter: int = 40,
    tol: float = 1e-9,
) -> tuple[float, float, float, float, float, float, float, float, float, float]:
    """
    Curvature + shared-well network (fixed-point mass deficit).

    Returns
      ``(total, inside, outside, G_eff, η, ladder, network, tetra, post_alpha, mass_factor)``.
    """
    if m_cluster is None:
        m_cluster = m if A <= 1 else ncur.nucleus_curvature_shell(A)

    triplet = contact_shell_triplet(m, m_cluster)
    theta = contact_phase_theta_rad(triplet)
    geff = outside_contact_coupling(theta)
    trace = nucleon_trace_binding_mev(m, c)

    outside = 0.0
    ladder = network = tetra = post_alpha = 0.0
    mass_factor = 1.0
    inside = inside_nuclear_binding_mev(m, A, m_cluster=m_cluster, c=c)
    total = inside

    for _ in range(max_iter):
        prev_total = total
        mass_factor = mass_deficit_well_deepening(
            max(0.0, prev_total / float(A)) if A > 0 else 0.0
        )
        inside = inside_nuclear_binding_mev(m, A, m_cluster=m_cluster, c=c)
        if A > 4:
            total, inside, outside, _, incremental, heavy = (
                compound_binding_above_alpha_mev(
                    m,
                    A,
                    Z,
                    m_cluster=m_cluster,
                    c=c,
                    geff=geff,
                    trace=trace,
                    mass_deficit_factor=mass_factor,
                    apply_spin_magnetic=apply_spin_magnetic,
                )
            )
            ladder = heavy
            network = incremental
            post_alpha = incremental
        else:
            (
                outside,
                ladder,
                network,
                tetra,
                post_alpha,
            ) = outside_network_curvature_mev(
                m, A, Z, geff=geff, trace=trace, c=c, mass_deficit_factor=mass_factor
            )
            outside = apply_outside_coulomb_and_spin_residual(
                outside,
                m,
                A,
                Z,
                geff=geff,
                apply_spin_magnetic=apply_spin_magnetic,
            )
            total = inside + outside
        if xi is not None:
            mod = notd.outside_curvature_binding_modulator(xi, bonded=bonded)
            outside *= mod
            total = inside + outside
        if outside_closure_k is not None:
            outside *= outside_closure_k
            total = inside + outside
        if abs(total - prev_total) < tol:
            break

    return (
        total,
        inside,
        outside,
        geff,
        contact_phase_eta(theta),
        ladder,
        network,
        tetra,
        post_alpha,
        mass_factor,
    )


def cluster_binding_network_mev(
    m: int,
    A: int,
    Z: int = 0,
    *,
    m_cluster: int | None = None,
    c: float = 1.0,
    xi: float | None = None,
    bonded: bool = True,
    apply_spin_magnetic: bool = True,
    outside_closure_k: float | None = None,
) -> float:
    """BBN / integrator entry: total binding on the network + residual spine."""
    total, *_ = cluster_binding_network_curvature_mev(
        m,
        A,
        Z,
        m_cluster=m_cluster,
        c=c,
        xi=xi,
        bonded=bonded,
        apply_spin_magnetic=apply_spin_magnetic,
        outside_closure_k=outside_closure_k,
    )
    return total


def post_alpha_curvature_contact_units(A: int, Z: int) -> float:
    """
    Effective curvature-contact units for A > 4 (sphere-touch ledger + network).

    Same contact arithmetic as ``postAlphaClusterBindingWithNetwork``, expressed
    as a dimensionless valley count before ``× G_eff × trace``.
    """
    if A <= 4:
        return float(constructive_valley_contacts(A, Z))

    cap = float(touch.CONSTRUCTIVE_VALLEY_CAP)
    ledger = touch.post_alpha_outside_valley_count_effective(A, Z)
    deepening = pap.post_alpha_core_well_deepening(A, Z)
    network_units = (
        bbn.GAMMA_HQIV * (deepening - 1.0) * cap
    )
    relax_units = (
        float(A - 4)
        * pap.post_alpha_light_contact_fraction(A, Z)
        * bbn.STRONG_CHANNEL_FRACTION
        * bbn.GAMMA_HQIV
    )
    return ledger * deepening + network_units - relax_units


def outside_curvature_contact_ledger(A: int, Z: int = 0) -> float:
    """Unified contact ledger: constructive valleys (A ≤ 4) or post-α units (A > 4)."""
    if A <= 4:
        return float(constructive_valley_contacts(A, Z))
    return post_alpha_curvature_contact_units(A, Z)


def outside_nuclear_binding_curvature_mev(
    m: int,
    A: int,
    Z: int = 0,
    *,
    m_cluster: int,
    c: float = 1.0,
    theta_rad: float | None = None,
    xi: float | None = None,
    bonded: bool = True,
) -> tuple[float, float, float, float]:
    """
    Lean ``nuclearOutsideBindingAtShell`` (+ post-α ledger for A > 4).

    Returns ``(B_out, G_eff(η), η, contact_units)``.
    """
    if A <= 1:
        return 0.0, 0.0, 0.0, 0.0

    if theta_rad is None:
        theta_rad = contact_phase_theta_rad(contact_shell_triplet(m, m_cluster))

    geff = outside_contact_coupling(theta_rad)
    eta = contact_phase_eta(theta_rad)
    trace = nucleon_trace_binding_mev(m, c)
    units = outside_curvature_contact_ledger(A, Z)
    binding = geff * trace * units

    if xi is not None:
        binding *= notd.outside_curvature_binding_modulator(xi, bonded=bonded)

    return binding, geff, eta, units


def cluster_binding_curvature_mev(
    m: int,
    A: int,
    Z: int = 0,
    *,
    m_cluster: int | None = None,
    c: float = 1.0,
    xi: float | None = None,
    bonded: bool = True,
) -> tuple[float, float, float, float, float, float]:
    """
    Lean ``nuclearClusterBindingCurvature``.

    Returns
      ``(total, inside, outside, G_eff, η, contact_units)``.
    """
    if m_cluster is None:
        m_cluster = m if A <= 1 else m

    inside = inside_nuclear_binding_mev(m, A, m_cluster=m_cluster, c=c)
    outside, geff, eta, units = outside_nuclear_binding_curvature_mev(
        m, A, Z, m_cluster=m_cluster, c=c, xi=xi, bonded=bonded
    )
    return inside + outside, inside, outside, geff, eta, units


def horizon_scale_outside_witness_mev(
    m: int,
    A: int,
    Z: int = 0,
    *,
    m_cluster: int,
    c: float = 1.0,
    theta_rad: float | None = None,
) -> float:
    """
    Diagnostic witness: ``Σ_contacts G_eff × deuteronBindingScale(m) × trace``.

    Uses constructive valley count as contact multiplicity.  Not the Lean
    definition (which is ``vc × G_eff × trace``); kept to compare horizon
    curvature density vs PDG without injecting fits.
    """
    if A <= 1:
        return 0.0
    if theta_rad is None:
        theta_rad = contact_phase_theta_rad(contact_shell_triplet(m, m_cluster))
    geff = outside_contact_coupling(theta_rad)
    trace = nucleon_trace_binding_mev(m, c)
    scale = deuteron_horizon_binding_scale(m)
    vc = constructive_valley_contacts(A, Z) if A <= 4 else int(
        round(touch.post_alpha_outside_valley_count_effective(A, Z))
    )
    return float(vc) * geff * scale * trace


@dataclass(frozen=True)
class CurvatureBindingBreakdown:
    A: int
    Z: int
    m: int
    m_cluster: int
    theta_rad: float
    eta: float
    g_eff_contact: float
    trace_mev: float
    inside_mev: float
    outside_mev: float
    total_mev: float
    contact_units: float
    intrinsic_well_deepening: float
    mass_deficit_factor: float
    outside_ladder_mev: float
    outside_gamma_network_mev: float
    outside_tetra_closure_mev: float
    outside_post_alpha_mev: float
    fresnel_curvature: float
    valley_overlap_r2: float
    deuteron_horizon_scale: float
    horizon_scale_outside_witness_mev: float
    inside_ratio_free: float
    inside_ratio_cluster: float
    xi: float | None
    outside_modulator: float | None
    outside_closure_k: float | None = None
    outside_mev_chart: float | None = None
    total_mev_chart: float | None = None


def curvature_binding_breakdown(
    m: int,
    A: int,
    Z: int = 0,
    *,
    m_cluster: int | None = None,
    c: float = 1.0,
    xi: float | None = None,
    bonded: bool = True,
    outside_closure_k: float | None = None,
) -> CurvatureBindingBreakdown:
    if m_cluster is None:
        import hqiv_nuclear_curvature_binding as ncur

        m_cluster = ncur.nucleus_curvature_shell(A) if A > 1 else m

    triplet = contact_shell_triplet(m, m_cluster)
    theta = contact_phase_theta_rad(triplet)
    eta = contact_phase_eta(theta)
    geff = outside_contact_coupling(theta)
    trace = nucleon_trace_binding_mev(m, c)

    (
        total,
        inside,
        outside,
        _,
        _,
        ladder,
        gamma_net,
        tetra,
        post_alpha,
        mass_factor,
    ) = cluster_binding_network_curvature_mev(
        m, A, Z, m_cluster=m_cluster, c=c, xi=xi, bonded=bonded,
        outside_closure_k=outside_closure_k,
    )
    units = outside_curvature_contact_ledger(A, Z)

    modulator: float | None = None
    if xi is not None:
        modulator = notd.outside_curvature_binding_modulator(xi, bonded=bonded)

    outside_chart = outside
    total_chart = total
    if outside_closure_k is not None and outside_closure_k != 0.0:
        outside_chart = outside / outside_closure_k
        total_chart = inside + outside_chart

    return CurvatureBindingBreakdown(
        A=A,
        Z=Z,
        m=m,
        m_cluster=m_cluster,
        theta_rad=theta,
        eta=eta,
        g_eff_contact=geff,
        trace_mev=trace,
        inside_mev=inside,
        outside_mev=outside,
        total_mev=total,
        contact_units=units,
        intrinsic_well_deepening=intrinsic_well_deepening(A, Z),
        mass_deficit_factor=mass_factor,
        outside_ladder_mev=ladder,
        outside_gamma_network_mev=gamma_net,
        outside_tetra_closure_mev=tetra,
        outside_post_alpha_mev=post_alpha,
        fresnel_curvature=fresnel_curvature_density(m),
        valley_overlap_r2=valley_potential_overlap_r2(m),
        deuteron_horizon_scale=deuteron_horizon_binding_scale(m),
        horizon_scale_outside_witness_mev=horizon_scale_outside_witness_mev(
            m, A, Z, m_cluster=m_cluster, c=c, theta_rad=theta
        ),
        inside_ratio_free=meta_horizon_inside_ratio(m, REFERENCE_M),
        inside_ratio_cluster=meta_horizon_inside_ratio(m_cluster, REFERENCE_M),
        xi=xi,
        outside_modulator=modulator,
        outside_closure_k=outside_closure_k,
        outside_mev_chart=outside_chart,
        total_mev_chart=total_chart,
    )

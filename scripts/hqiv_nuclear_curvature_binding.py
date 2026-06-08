#!/usr/bin/env python3
"""
Per-nucleus curvature / binding readouts for HQIV nuclear physics.

Mirrors:
  • `Hqiv.Physics.NuclearCurvatureBinding` — inside/outside curvature cluster binding
  • `Hqiv.Physics.BBNNetworkFromWeights` — valley ladder / composite trace
  • `Hqiv.Physics.MetaHorizonTrappedPlanckMass` — trapped inside ratio
  • `Hqiv.Geometry.HQVMetric` — `G_eff` contact coupling at nucleon contact points

Nuclear binding energy lives in the same curvature slot as the proton:

  **inside** trapped ratio × nucleon composite trace
  **outside** `G_eff(θ)` at isotope-valley contact points (α = 3/5)

Also supplies per-nucleus shell readouts used by molecular chemistry charts (downstream).
"""

from __future__ import annotations

import math
from dataclasses import dataclass

import hqiv_bbn_abundances as bbn
import hqiv_excited_states as hes
import hqiv_lean_physics_primitives as lean
import hqiv_nuclear_inside_outside_binding as niob
from hqiv_continuous_shell_mass import inside_ratio_discrete
from lih_derivation_scan import (
    HBAR_EV_S,
    PHASE_THETA,
    compton_window_angles_from_detuning_lapse,
    detuning_lapse_fraction_from_hqiv_scalars,
    lattice_full_mode_energy,
    omega_compton_from_energy_ev,
    t_ir_from_omega,
)

REFERENCE_M = hes.REFERENCE_M
PROTON_MEV = 938.27208816
PHASE_THETA_RAD = PHASE_THETA

# Stable main-isotope mass numbers (chemistry benchmark bookkeeping, not fitted parameters).
STABLE_MASS_NUMBER: dict[int, int] = {
    1: 1,   # H
    3: 7,   # Li
    6: 12,  # C
    7: 14,  # N
    8: 16,  # O
    9: 19,  # F
}


@dataclass(frozen=True)
class NucleusCurvatureRow:
    Z: int
    A: int
    m_nuclear: int
    xi_nuclear: float
    per_nucleon_binding_mev: float
    cluster_binding_mev: float
    inside_binding_mev: float
    outside_binding_mev: float
    cluster_mass_mev: float
    inside_ratio: float
    tuft_vev_factor: float
    eta_nuclear: float
    valence_s_shell: int
    valence_p_shell: int | None


def stable_mass_number(z: int, electrons: int | None = None) -> int:
    """Stable A for light chemistry elements; fallback to electrons if Z unknown."""
    if z in STABLE_MASS_NUMBER:
        return STABLE_MASS_NUMBER[z]
    if electrons is not None and electrons > 0:
        return max(z, electrons)
    return max(z, 1)


def cluster_binding_mev_legacy(m: int, A: int, c: float = 1.0) -> float:
    """Legacy scalar: A × trace × valley factor (BBN witness path)."""
    try:
        return bbn.cluster_binding_mev(m, A, c)
    except KeyError:
        return float(A) * hes.e_bind_from_nucleon_trace_mev(m, c)


def cluster_binding_mev_safe(m: int, A: int, c: float = 1.0) -> float:
    """Inside + outside curvature cluster binding (primary nuclear readout)."""
    m_cluster = nucleus_curvature_shell(A) if A > 1 else m
    total, _, _ = niob.nuclear_cluster_binding_mev(m, A, m_cluster=m_cluster, c=c)
    return total


def cluster_binding_breakdown_mev(
    m: int, A: int, c: float = 1.0
) -> tuple[float, float, float]:
    m_cluster = nucleus_curvature_shell(A) if A > 1 else m
    return niob.nuclear_cluster_binding_mev(m, A, m_cluster=m_cluster, c=c)


def cluster_mass_mev(m: int, A: int, m_nucleon: float = PROTON_MEV, c: float = 1.0) -> float:
    return float(A) * m_nucleon - cluster_binding_mev_safe(m, A, c)


def per_nucleon_binding_mev(m: int, A: int, c: float = 1.0) -> float:
    if A <= 0:
        raise ValueError("mass number A must be positive")
    return cluster_binding_mev_safe(m, A, c) / float(A)


def nucleus_curvature_shell(A: int) -> int:
    """
    Nuclear readout shell from trapped inside-ratio vs mass-number volume scale.

    Target inside ratio = A^(1/3) (same curvature primitive as meta-horizon mass readout,
    parameter-free).  H (A=1) sits at the proton lock-in drum `referenceM`.
    """
    if A <= 1:
        return REFERENCE_M
    target = float(A) ** (1.0 / 3.0)
    return min(
        range(0, REFERENCE_M + 8),
        key=lambda m: abs(nucleus_inside_ratio(m) - target),
    )


def per_nucleon_trace_binding_at_shell(m: int, c: float = 1.0) -> float:
    """Raw composite-trace binding at shell m (identical spine for every nucleus)."""
    return hes.e_bind_from_nucleon_trace_mev(m, c)


def nucleus_inside_ratio(m_nuclear: int) -> float:
    return inside_ratio_discrete(float(m_nuclear))


def valence_shells_for_nucleus(z: int, m_nuclear: int) -> tuple[int, int | None]:
    """Electronic valence readout shells tied to the nuclear drum, not universal m=4."""
    if z == 1:
        return 1, None
    return m_nuclear, m_nuclear - 1 if z >= 3 else None


def _compton_eta_from_energy_ev(energy_ev: float, lapse_fraction: float) -> float:
    if energy_ev <= 0.0:
        return 0.0
    omega = omega_compton_from_energy_ev(energy_ev, HBAR_EV_S)
    t_ir = t_ir_from_omega(omega)
    shared = lapse_fraction * t_ir
    angle = omega * shared
    return angle / PHASE_THETA_RAD


def nuclear_phase_participation_eta(m_nuclear: int, A: int, *, lapse_fraction: float) -> float:
    """
    Per-nucleus η from the Compton IR window on the **electronic ladder site energy**
    evaluated at the nuclear readout shell m_nuc(A) (curvature-linked, not universal m=4).

    Uses the same detuning-lapse shared-time construction as LiH, but with shell m_nuc.
    """
    _ = A
    triplet = (max(m_nuclear, 1), max(m_nuclear, 1), max(m_nuclear, 1))
    return electronic_compton_eta_from_triplet(triplet, lapse_fraction=lapse_fraction)


def molecule_phase_participation_eta(
    fragments: tuple[tuple[int, int], ...],
    *,
    lapse_fraction: float | None = None,
) -> tuple[float, list[NucleusCurvatureRow]]:
    """
    Geometric mean of per-fragment nuclear η.

    `fragments`: iterable of (Z, electrons) pairs.
    """
    if lapse_fraction is None:
        lapse_fraction = detuning_lapse_fraction_from_hqiv_scalars().lapse_fraction

    rows: list[NucleusCurvatureRow] = []
    etas: list[float] = []
    for z, electrons in fragments:
        A = stable_mass_number(z, electrons)
        m_nuc = nucleus_curvature_shell(A)
        xi = float(m_nuc + 1)
        bind_a = per_nucleon_binding_mev(m_nuc, A)
        bind_tot, bind_in, bind_out = cluster_binding_breakdown_mev(m_nuc, A)
        m_s, m_p = valence_shells_for_nucleus(z, m_nuc)
        eta = nuclear_phase_participation_eta(m_nuc, A, lapse_fraction=lapse_fraction)
        rows.append(
            NucleusCurvatureRow(
                Z=z,
                A=A,
                m_nuclear=m_nuc,
                xi_nuclear=xi,
                per_nucleon_binding_mev=bind_a,
                cluster_binding_mev=bind_tot,
                inside_binding_mev=bind_in,
                outside_binding_mev=bind_out,
                cluster_mass_mev=cluster_mass_mev(m_nuc, A),
                inside_ratio=nucleus_inside_ratio(m_nuc),
                tuft_vev_factor=lean.tuft_vev_factor_at_xi(xi),
                eta_nuclear=eta,
                valence_s_shell=m_s,
                valence_p_shell=m_p,
            )
        )
        if eta > 0.0:
            etas.append(eta)
    if not etas:
        return 0.0, rows
    return math.prod(etas) ** (1.0 / len(etas)), rows


def compton_triplet_from_nuclei(rows: list[NucleusCurvatureRow]) -> tuple[int, int, int]:
    """
    Build a three-shell Compton triplet from nuclear-derived valence shells.

    Prefer heavy-atom (s, p) + light H s=1; homonuclear H₂ uses (1,1,1).
    """
    zs = [r.Z for r in rows]
    if all(z == 1 for z in zs):
        return (1, 1, 1)
    heavy = max(rows, key=lambda r: r.A)
    light = min(rows, key=lambda r: r.A)
    m_h = light.valence_s_shell
    m_s = heavy.valence_s_shell
    m_p = heavy.valence_p_shell if heavy.valence_p_shell is not None else heavy.valence_s_shell
    return (m_s, m_p, m_h)


def vev_geometric_mean_from_triplet(triplet: tuple[int, int, int]) -> float:
    """Bare shell-ladder geomean (no cluster-mass feedback)."""
    factors = [lean.tuft_vev_factor_at_xi(float(m + 1)) for m in triplet]
    return math.prod(factors) ** (1.0 / len(factors))


def tuft_vev_factor_networked_at_cluster(
    m: int,
    A: int,
    *,
    m_proton: float = PROTON_MEV,
    xi_lock: float | None = None,
) -> float:
    """
    Mass-networked TUFT vev factor for a bound cluster.

    After binding, the cluster carries ``cluster_mass_mev = A·m_p − B``; the effective
    per-nucleon mass ``m_eff = cluster_mass / A`` is lower than the proton anchor.
    Map that deficit back onto the lock-in ξ ladder:

      ξ_eff = ξ_lock · (m_eff / m_proton)

    then read ``heavy_lepton_gap_at_xi(ξ_eff) / heavy_lepton_gap_at_xi(ξ_lock)``.

    D is the first non-trivial step (A = 2); T and heavier isotopes inherit the same
    networked scale when their geometric means are taken over fragments or along the
    BBN valley chain — not independent bare ``tuft_vev_factor_at_xi(ξ_shell)``.
    """
    if A <= 0:
        raise ValueError("mass number A must be positive")
    xi_lock = xi_lock if xi_lock is not None else lean.XI_LOCKIN
    m_eff = cluster_mass_mev(m, A, m_proton) / float(A)
    xi_eff = xi_lock * (m_eff / m_proton)
    gap_eff = lean.heavy_lepton_gap_at_xi(xi_eff)
    gap_lock = lean.heavy_lepton_gap_at_xi(xi_lock)
    return gap_eff / max(gap_lock, 1e-30)


def valley_network_vev_factor(A: int, *, m_proton: float = PROTON_MEV) -> float:
    """
    BBN-valley networked geomean: ∏_{a=1..A} vev_networked(a) ^ (1/A).

    Light nuclei composed in sequence (H → D → T → He) share mass-deficit memory;
    D sits closest to unity; T and He feel the accumulated lower-mass scale.
    """
    if A <= 0:
        raise ValueError("mass number A must be positive")
    factors = [
        tuft_vev_factor_networked_at_cluster(nucleus_curvature_shell(a), a, m_proton=m_proton)
        for a in range(1, A + 1)
    ]
    return math.prod(factors) ** (1.0 / len(factors))


def vev_geometric_mean_networked_from_fragments(
    fragments: tuple[tuple[int, int], ...],
) -> float:
    """Geomean of per-fragment mass-networked vev factors (molecular readout)."""
    factors: list[float] = []
    for z, electrons in fragments:
        A = stable_mass_number(z, electrons)
        m = nucleus_curvature_shell(A)
        factors.append(tuft_vev_factor_networked_at_cluster(m, A))
    if not factors:
        return 1.0
    return math.prod(factors) ** (1.0 / len(factors))


def peripheral_h_h_repulsive_contacts_per_hydrogen(n_peripheral_h: int) -> int:
    """
    Steric H–H contacts per peripheral proton (tetrahedral / trigonal outer H).

    CH₄: four H, **two** repulsive contacts each → four undirected contact points total.
    NH₃: three H, two each → three contact points.  H₂O: two H, one each → one contact.
    """
    if n_peripheral_h < 2:
        return 0
    if n_peripheral_h >= 4:
        return 2
    if n_peripheral_h == 3:
        return 2
    return 1


def peripheral_h_h_repulsive_contact_points(n_peripheral_h: int) -> int:
    """Undirected H–H repulsive contact count (``n_H · contacts_per_H / 2``)."""
    cph = peripheral_h_h_repulsive_contacts_per_hydrogen(n_peripheral_h)
    return n_peripheral_h * cph // 2


def hydrogen_repulsive_curvature_mass_boost(
    n_peripheral_hydrogens: int,
    *,
    m_compton_h: int = 1,
) -> float:
    """Delegate to `hqiv_curvature_contact_network.steric_repulsion_increment`."""
    import hqiv_curvature_contact_network as ccn

    _ = m_compton_h
    points = peripheral_h_h_repulsive_contact_points(n_peripheral_hydrogens)
    return ccn.steric_repulsion_increment(
        contact_points=points,
        n_peripheral_h=n_peripheral_hydrogens,
    )


def tuft_vev_networked_at_compton_shell(
    m_compton: int,
    A: int,
    *,
    m_proton: float = PROTON_MEV,
) -> float:
    """
    Compton-shell vev dressed by the fragment's bound cluster mass.

    Electronic readout stays on shell ``m_compton``; the deficit factor comes from
    ``cluster_mass_mev(m_nuc(A), A) / (A·m_p)`` on the nuclear spine.
    """
    m_nuc = nucleus_curvature_shell(A)
    bare = lean.tuft_vev_factor_at_xi(float(m_compton + 1))
    mass_ratio = cluster_mass_mev(m_nuc, A, m_proton) / (float(A) * m_proton)
    return bare * mass_ratio ** (1.0 / 3.0)


def vev_geometric_mean_networked_for_compton_triplet(
    triplet: tuple[int, int, int],
    *,
    heavy_mass_number: int,
    light_mass_number: int = 1,
    n_peripheral_hydrogens: int = 0,
) -> float:
    """
    Compton-triplet geomean with per-slot cluster-mass dress.

    • ``(1, 1, 1)`` (H₂): bare electronic geomean (proton anchor).
    • ``(4, 3, 1)``: heavy slots use ``A = heavy_mass_number``, H slot uses ``A = 1``.
    • homonuclear ``(m, m, m)``, ``A > 1``: valley-networked geomean on heavy ``A``.
    • Multi-H hydrides (CH₄, NH₃, H₂O): H leg gets repulsive H–H contact boost (opposite
      of cluster deficit); CH₄ uses four contact points at two per H.
    """
    m_s, m_p, m_h = triplet
    if triplet == (1, 1, 1):
        return vev_geometric_mean_from_triplet(triplet)

    if m_s == m_p == m_h and heavy_mass_number == light_mass_number and heavy_mass_number > 1:
        return valley_network_vev_factor(heavy_mass_number)

    factors = [
        tuft_vev_networked_at_compton_shell(m_s, heavy_mass_number),
        tuft_vev_networked_at_compton_shell(m_p, heavy_mass_number),
        tuft_vev_networked_at_compton_shell(m_h, light_mass_number),
    ]
    base = math.prod(factors) ** (1.0 / len(factors))
    if n_peripheral_hydrogens == 4:
        base *= hydrogen_repulsive_curvature_mass_boost(
            n_peripheral_hydrogens,
            m_compton_h=m_h,
        )
    return base


def electronic_compton_eta_from_triplet(triplet: tuple[int, int, int], *, lapse_fraction: float) -> float:
    """Electronic-site Compton η on lattice site energies (legacy comparison path)."""
    compton, _ = compton_window_angles_from_detuning_lapse(triplet)
    mean_angle = sum(compton.angles_rad) / len(compton.angles_rad)
    return mean_angle / PHASE_THETA_RAD


def binding_uniformity_report(rows: list[NucleusCurvatureRow]) -> dict[str, float]:
    """
    HQIV composite-trace binding spread across nuclei at their respective m_nuc.

    The **procedure** is identical (`e_bind_from_nucleon_trace`); values cluster when
    valley-enhanced clusters sit near the same network shell.
    """
    vals = [per_nucleon_trace_binding_at_shell(r.m_nuclear) for r in rows]
    cluster_vals = [r.per_nucleon_binding_mev for r in rows]
    if not vals:
        return {"count": 0.0, "trace_spread_pct": 0.0, "cluster_spread_pct": 0.0}
    t_mean = sum(vals) / len(vals)
    c_mean = sum(cluster_vals) / len(cluster_vals)
    t_spread = (max(vals) - min(vals)) / t_mean * 100.0 if t_mean > 0 else 0.0
    c_spread = (max(cluster_vals) - min(cluster_vals)) / c_mean * 100.0 if c_mean > 0 else 0.0
    return {
        "count": float(len(vals)),
        "trace_mean_mev": t_mean,
        "trace_min_mev": min(vals),
        "trace_max_mev": max(vals),
        "trace_spread_pct": t_spread,
        "cluster_mean_mev_per_A": c_mean,
        "cluster_spread_pct": c_spread,
    }


def dynamic_site_energy_dimless(m: int) -> float:
    return lattice_full_mode_energy(m) * lean.tuft_vev_factor_at_xi(float(m + 1))

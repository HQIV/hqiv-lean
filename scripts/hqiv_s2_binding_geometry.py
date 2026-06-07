#!/usr/bin/env python3
"""
S² binding geometry for valence contacts (s and p shells).

Lean spine:
  `Hqiv.Geometry.SphericalHarmonicsBridge` — degeneracy ``2ℓ+1`` on S²
  `Hqiv.Physics.ComptonIRWindow` — ``phaseParticipationEta = x/θ₀``
  `Hqiv.Physics.HQIVAtoms` — dihedral budget ``κ(1 - cos θ)`` minimized at θ = 0
  `Hqiv.Algebra.OctonionAxisAngles` — axis angles ``π/(2k)``

Python consumers: `hqiv_curvature_contact_network`, `hqiv_dynamic_binding_chart`.

Run:
  python3 scripts/hqiv_s2_binding_geometry.py
"""

from __future__ import annotations

import math
from dataclasses import asdict, dataclass
from typing import Any

import hqiv_curvature_bond_state as cbs
import hqiv_lean_physics_primitives as lean
from lih_derivation_scan import (
    PHASE_THETA,
    compton_window_angles_from_detuning_lapse,
    compton_window_angles_from_shells,
    detuning_lapse_fraction_from_hqiv_scalars,
)

ALPHA = lean.ALPHA
GAMMA = lean.GAMMA


def s2_degeneracy(ell: int) -> int:
    """Cumulative mode count for ℓ on S²: ``2ℓ+1``."""
    if ell < 0:
        return 0
    return 2 * ell + 1


def axis_angle_rad(k: int) -> float:
    """Lean ``axisAngle k = π/(2k)`` for k ≥ 1."""
    if k < 1:
        return PHASE_THETA
    return math.pi / (2.0 * float(k))


def shell_axis_angle_rad(m_shell: int) -> float:
    """
    Intrinsic polar angle from shell index (Ω proxy: use ``m+1`` as ladder rung).

    Primes at π/2; deeper shells open smaller axes — same narrative as
    ``intrinsicShellAxisAngle`` without importing Mathlib Ω.
    """
    k = max(m_shell, 1)
    return axis_angle_rad(k)


def phase_participation_eta(angle_rad: float) -> float:
    """Lean ``phaseParticipationEta x = x / phaseTheta``."""
    if angle_rad <= 0.0:
        return 0.0
    return min(angle_rad / PHASE_THETA, 1.0)


def dihedral_budget_factor(binding_angle_rad: float) -> float:
    """
    HQIV torque-tree dihedral: ``κ(1 - cos θ)`` is minimal at θ = 0.

    Attractive contact weight: ``(1 + cos θ)/2`` ∈ [0, 1], unity at aligned poles.
    """
    return max(0.0, (1.0 + math.cos(binding_angle_rad)) / 2.0)


def polar_angle_from_compton_triplet(
    triplet: tuple[int, int, int],
    slot_index: int,
) -> float:
    """Polar angle for Compton triplet slot (0=s, 1=p, 2=light)."""
    compton, _ = compton_window_angles_from_detuning_lapse(triplet)
    idx = max(0, min(slot_index, 2))
    return compton.angles_rad[idx]


def polar_angle_for_valence(
    m_s: int,
    m_p: int | None,
    *,
    use_p: bool,
    m_light: int = 1,
) -> float:
    """IR-window polar angle for s or p valence on the heavy-centre triplet."""
    triplet = bond_compton_triplet(m_s, m_p, m_light)
    return polar_angle_from_compton_triplet(triplet, 1 if use_p and m_p is not None else 0)


def shell_direction_on_s2(
    polar_rad: float,
    *,
    ell: int,
    magnetic_slot: int = 0,
) -> tuple[float, float, float]:
    """
    Unit direction at S² harmonic slot ``m_slot`` (0 … 2ℓ).

    ``polar_rad`` is the Compton IR-window angle for that slot (not repeated per m).
    """
    deg = s2_degeneracy(ell)
    slot = magnetic_slot % max(deg, 1)
    if ell == 0:
        return (
            math.sin(polar_rad),
            0.0,
            math.cos(polar_rad),
        )
    phi = 2.0 * math.pi * float(slot) / float(deg)
    return (
        math.sin(polar_rad) * math.cos(phi),
        math.sin(polar_rad) * math.sin(phi),
        math.cos(polar_rad),
    )


def s2_binding_angle_rad(
    m_a: int,
    m_b: int,
    *,
    m_p_a: int | None = None,
    m_p_b: int | None = None,
    ell_a: int = 1,
    ell_b: int = 1,
    slot_a: int = 0,
    slot_b: int = 0,
) -> float:
    """Angle between two shell directions on S² (radians)."""
    pol_a = polar_angle_for_valence(m_a, m_p_a, use_p=(ell_a == 1 and m_p_a is not None))
    pol_b = polar_angle_for_valence(m_b, m_p_b, use_p=(ell_b == 1 and m_p_b is not None))
    va = shell_direction_on_s2(pol_a, ell=ell_a, magnetic_slot=slot_a)
    vb = shell_direction_on_s2(pol_b, ell=ell_b, magnetic_slot=slot_b)
    dot = max(-1.0, min(1.0, sum(a * b for a, b in zip(va, vb))))
    return math.acos(dot)


def valence_ell(node_has_p: bool) -> int:
    return 1 if node_has_p else 0


@dataclass(frozen=True)
class ShellSlotGeometry:
    """Per-node S² / Compton geometry on valence slots."""

    m_s: int
    m_p: int | None
    ell_s: int
    ell_p: int | None
    angle_s_rad: float
    angle_p_rad: float | None
    eta_s: float
    eta_p: float | None
    s2_deg_s: int
    s2_deg_p: int | None

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class BondAngularGeometry:
    """Bond-level angular readout for one covalent contact."""

    compton_triplet_m: tuple[int, int, int]
    compton_angles_rad: tuple[float, float, float]
    mean_compton_angle_rad: float
    eta_contact: float
    bond_angle_rad: float
    ideal_bond_angle_rad: float
    s2_binding_angle_rad: float
    valley_alignment_weight: float
    dihedral_weight: float
    geff_theta: float
    geff_combined: float
    p_shell_active: bool

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class BackboneDihedral:
    """Protein backbone (φ, ψ) per residue — drives peptide contact angles."""

    residue_index: int
    phi_rad: float
    psi_rad: float


def valley_alignment_weight(
    bond_angle_rad: float,
    ideal_bond_angle_rad: float,
) -> float:
    """
    HQIV valley minimum at **zero deviation** from the native centre angle.

    Uses ``κ(1 - cos θ)`` on ``θ = bond - ideal`` (torque-tree dihedral), not on raw θ.
    """
    delta = bond_angle_rad - ideal_bond_angle_rad
    return dihedral_budget_factor(delta)


def backbone_peptide_bond_angle_rad(phi_rad: float, psi_rad: float) -> float:
    """
    Contact angle from sequential (φ, ψ): folds map to smaller dihedral spread → deeper valley.

    Parameter-free: uses |φ − ψ| wrapped on the circle as the effective bend angle.
    """
    d = abs(phi_rad - psi_rad) % (2.0 * math.pi)
    if d > math.pi:
        d = 2.0 * math.pi - d
    return d


def bond_geometry_weight(bg: BondAngularGeometry) -> float:
    """VSEPR / valley misalignment only — Compton η_p is applied once in the chart core."""
    return bg.valley_alignment_weight


def geometry_alignment_factor(bond_geoms: tuple[BondAngularGeometry, ...]) -> float:
    """
    Geometric mean valley relaxation — **no κ_bind**.

    Bonds in native geometry sit at w → 1; misalignment lowers w and binding readout.
    """
    if not bond_geoms:
        return 1.0
    weights = [max(bond_geometry_weight(bg), 1e-12) for bg in bond_geoms]
    return math.prod(weights) ** (1.0 / len(weights))


def valley_relaxation_factor(bond_geoms: tuple[BondAngularGeometry, ...]) -> float:
    """Alias for ``geometry_alignment_factor`` (legacy name)."""
    return geometry_alignment_factor(bond_geoms)


def mean_compton_angles_from_bonds(
    bond_geoms: tuple[BondAngularGeometry, ...],
    fallback_triplet: tuple[int, int, int],
) -> tuple[float, float, float]:
    """Average per-slot Compton angles across covalent contacts (surplus witness)."""
    if not bond_geoms:
        compton, _ = compton_window_angles_from_detuning_lapse(fallback_triplet)
        return compton.angles_rad
    return tuple(
        sum(bg.compton_angles_rad[i] for bg in bond_geoms) / len(bond_geoms) for i in range(3)
    )


def shell_slot_geometry(
    m_s: int,
    m_p: int | None,
    *,
    lapse_fraction: float | None = None,
) -> ShellSlotGeometry:
    lapse = lapse_fraction
    if lapse is None:
        lapse = detuning_lapse_fraction_from_hqiv_scalars().lapse_fraction
    triplet_s = (max(m_s, 1), max(m_s, 1), max(m_s, 1))
    rep_s, _ = compton_window_angles_from_detuning_lapse(triplet_s)
    ang_s = rep_s.angles_rad[0]
    eta_s = phase_participation_eta(ang_s)
    ell_p = 1 if m_p is not None else None
    ang_p = eta_p = s2_deg_p = None
    if m_p is not None:
        triplet_p = (max(m_s, 1), max(m_p, 1), max(m_s, 1))
        rep_p, _ = compton_window_angles_from_detuning_lapse(triplet_p)
        ang_p = rep_p.angles_rad[1]
        eta_p = phase_participation_eta(ang_p)
        s2_deg_p = s2_degeneracy(1)
    return ShellSlotGeometry(
        m_s=m_s,
        m_p=m_p,
        ell_s=0,
        ell_p=ell_p,
        angle_s_rad=ang_s,
        angle_p_rad=ang_p,
        eta_s=eta_s,
        eta_p=eta_p,
        s2_deg_s=s2_degeneracy(0),
        s2_deg_p=s2_deg_p,
    )


def bond_compton_triplet(
    m_s_heavy: int,
    m_p_heavy: int | None,
    m_s_light: int,
) -> tuple[int, int, int]:
    """Heavy-centre Compton triplet (s, p, light) — Lean LiH / hydride pattern."""
    m_p = m_p_heavy if m_p_heavy is not None else m_s_heavy
    return (max(m_s_heavy, 1), max(m_p, 1), max(m_s_light, 1))


def infer_centre_bond_angle_rad(
    molecule_name: str,
    n_bonds_at_centre: int,
    *,
    z_centre: int | None = None,
) -> float:
    """
    Dynamic centre angle (radians) from TUFT steric geometry.

    When ``z_centre`` is supplied (period-2 atom), uses
    ``hqiv_chemistry_tuft_dynamics.dynamic_centre_angle_rad``.
    """
    import hqiv_chemistry_tuft_dynamics as ctd

    if z_centre is not None and 3 <= z_centre <= 10:
        return ctd.dynamic_centre_angle_rad(z_centre, n_bonds_at_centre)
    if n_bonds_at_centre <= 1:
        return math.pi
    if n_bonds_at_centre == 2:
        return math.pi
    if n_bonds_at_centre == 3:
        return ctd.centre_angle_rad_from_domains(3)
    if n_bonds_at_centre >= 4:
        return ctd.centre_angle_rad_from_domains(n_bonds_at_centre)
    return math.pi


def bond_angular_geometry(
    *,
    m_s_i: int,
    m_p_i: int | None,
    m_s_j: int,
    m_p_j: int | None,
    distance_weight: float,
    bond_angle_rad: float | None = None,
    molecule_name: str = "",
    n_bonds_at_centre: int = 1,
    z_centre: int | None = None,
    medium_density_fraction: float = 0.0,
) -> BondAngularGeometry:
    """
    Full angular contact readout for one covalent bond.

    Combines Compton IR ``G_eff(θ)`` with S² dihedral alignment on p shells.
    """
    heavy_s = max(m_s_i, m_s_j)
    heavy_p = m_p_i if m_p_i is not None else m_p_j
    light_s = min(m_s_i, m_s_j)
    triplet = bond_compton_triplet(heavy_s, heavy_p, light_s)
    compton, _ = compton_window_angles_from_detuning_lapse(triplet)
    mean_ang = sum(compton.angles_rad) / len(compton.angles_rad)
    eta_c = phase_participation_eta(mean_ang)
    geff = cbs.outside_contact_coupling_scaled(mean_ang, medium_density_fraction)

    p_active = m_p_i is not None or m_p_j is not None
    ell_i = valence_ell(m_p_i is not None)
    ell_j = valence_ell(m_p_j is not None)
    m_contact_i = m_p_i if m_p_i is not None else m_s_i
    m_contact_j = m_p_j if m_p_j is not None else m_s_j
    s2_ang = s2_binding_angle_rad(
        m_s_i,
        m_s_j,
        m_p_a=m_p_i,
        m_p_b=m_p_j,
        ell_a=ell_i,
        ell_b=ell_j,
    )

    ideal = (
        infer_centre_bond_angle_rad(
            molecule_name,
            n_bonds_at_centre,
            z_centre=z_centre,
        )
        if molecule_name or z_centre is not None
        else (bond_angle_rad if bond_angle_rad is not None else s2_ang)
    )
    if bond_angle_rad is None and molecule_name:
        theta_bond = ideal
    else:
        theta_bond = bond_angle_rad if bond_angle_rad is not None else s2_ang

    valley_align = valley_alignment_weight(theta_bond, ideal)
    dihedral_w = dihedral_budget_factor(theta_bond)
    geff_combined = geff * valley_align * distance_weight

    return BondAngularGeometry(
        compton_triplet_m=triplet,
        compton_angles_rad=compton.angles_rad,
        mean_compton_angle_rad=mean_ang,
        eta_contact=eta_c,
        bond_angle_rad=theta_bond,
        ideal_bond_angle_rad=ideal,
        s2_binding_angle_rad=s2_ang,
        valley_alignment_weight=valley_align,
        dihedral_weight=dihedral_w,
        geff_theta=geff,
        geff_combined=geff_combined,
        p_shell_active=p_active,
    )


def main() -> None:
    print("S² binding geometry (p-shell contacts)")
    print("=" * 60)
    for name, angle_deg in [("H2O", 104.5), ("CH4", 109.47), ("LiH", 180.0)]:
        ang = math.radians(angle_deg)
        geo = bond_angular_geometry(
            m_s_i=4,
            m_p_i=3,
            m_s_j=1,
            m_p_j=None,
            distance_weight=1.0,
            bond_angle_rad=ang,
            molecule_name=name,
        )
        print(
            f"{name:4s}  θ={math.degrees(geo.bond_angle_rad):6.1f}°  "
            f"ideal={math.degrees(geo.ideal_bond_angle_rad):6.1f}°  "
            f"valley={geo.valley_alignment_weight:.3f}  η={geo.eta_contact:.3f}"
        )
    triplet = (4, 3, 1)
    rep, _ = compton_window_angles_from_detuning_lapse(triplet)
    print(f"\nLiH Compton triplet {triplet} angles (rad): {rep.angles_rad}")
    print(f"p-slot S² degeneracy: {s2_degeneracy(1)}  s-slot: {s2_degeneracy(0)}")


if __name__ == "__main__":
    main()

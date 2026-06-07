#!/usr/bin/env python3
"""
Shell-aware binding readout — routes surplus angles, η, ξ, and curvature feedback
by Compton triplet class and nuclear shell assignment (not ad hoc per molecule).

Lean spine:
  • ``BondedHorizonCasimir.covalentDimerTwoElectronSurplusDimless`` — UUD torus angles
  • ``DynamicBindingChart.dynamicComptonTriplet*`` — electronic (m_s, m_p, m_h)
  • ``LiHDynamicBinding`` — heavy-hydride (4,3,1) with detuning Compton η
  • Cluster binding contrast on ``dynamicBindingCurvatureFeedbackAtXi`` — heavy centres only

Consumers: ``hqiv_dynamic_binding_chart``, contact network witnesses.
"""

from __future__ import annotations

import math
from dataclasses import asdict, dataclass
from enum import Enum
from typing import Any, Literal

import hqiv_electronic_valence_shells as evs
import hqiv_lean_physics_primitives as lean
import hqiv_nuclear_curvature_binding as ncb
from bonded_horizon_casimir_float import DEFAULT_UUD_ANGLES_RAD
from fragment_aware_bonded_horizon import FragmentConfig
from lih_derivation_scan import (
    PHASE_THETA,
    compton_window_angles_from_detuning_lapse,
)

BindingKind = Literal["dissociation", "atomization"]


class ComptonTripletClass(str, Enum):
    """Electronic Compton slot pattern (Lean ``DynamicComptonTriplet``)."""

    H2_LADDER = "dynamicComptonTripletH2"  # (1, 1, 1)
    HEAVY_HYDRIDE = "dynamicComptonTripletHeavyHydride"  # (4, 3, 1)
    HOMONUCLEAR_PERIOD2 = "dynamicComptonTripletHomonuclearPeriod2"  # (4, 4, 4)
    GENERAL = "general"


class SurplusAnglePolicy(str, Enum):
    """Which torus / Compton angles feed ``bond_horizon_surplus``."""

    COVALENT_DIMER_UUD = "covalent_dimer_uud"
    BOND_AVERAGED_COMPTON = "bond_averaged_compton"
    ELECTRONIC_COMPTON_TRIPLET = "electronic_compton_triplet"
    DETUNING_COMPTON_TRIPLET = "detuning_compton_triplet"


@dataclass(frozen=True)
class ShellAwareBindingReadout:
    """Per-molecule shell routing witness (serialised in chart JSON)."""

    compton_triplet_m: tuple[int, int, int]
    compton_triplet_class: str
    surplus_angle_policy: str
    surplus_angles_rad: tuple[float, float, float]
    eta_angles_rad: tuple[float, float, float]
    eta_p_linear: float
    contact_xi: float
    curvature_feedback_weight: float
    has_heavy_nucleus: bool
    electron_split: tuple[int, ...]
    electronic_shell_slots: tuple[str, str, str]
    surplus_dress_factor: float

    def to_dict(self) -> dict[str, Any]:
        d = asdict(self)
        d["surplus_angles_rad"] = list(self.surplus_angles_rad)
        d["eta_angles_rad"] = list(self.eta_angles_rad)
        d["compton_triplet_m"] = list(self.compton_triplet_m)
        d["electron_split"] = list(self.electron_split)
        d["electronic_shell_slots"] = list(self.electronic_shell_slots)
        return d


def classify_compton_triplet(triplet: tuple[int, int, int]) -> ComptonTripletClass:
    if triplet == (1, 1, 1):
        return ComptonTripletClass.H2_LADDER
    if triplet == (4, 3, 1):
        return ComptonTripletClass.HEAVY_HYDRIDE
    if triplet[0] == triplet[1] == triplet[2] and triplet[0] >= 4:
        return ComptonTripletClass.HOMONUCLEAR_PERIOD2
    return ComptonTripletClass.GENERAL


def phase_participation_eta(angle_rad: float) -> float:
    if angle_rad <= 0.0:
        return 0.0
    return min(angle_rad / PHASE_THETA, 1.0)


def eta_p_from_compton_angles(
    angles: tuple[float, float, float],
    triplet: tuple[int, int, int] | None = None,
) -> float:
    """IR-window participation with S² weights on the p slot when active."""
    if triplet is not None:
        return evs.eta_p_s2_weighted(angles, triplet, phase_theta=PHASE_THETA)
    mean_angle = sum(angles) / float(len(angles))
    return phase_participation_eta(mean_angle)


def surplus_angle_policy(
    *,
    kind: BindingKind,
    triplet_class: ComptonTripletClass,
    fragments: tuple[FragmentConfig, ...],
) -> SurplusAnglePolicy:
    """
    Route surplus torus angles by shell class.

    H₂ covalent dimer → UUD (Lean default nuclear torus for 2e shared sea).
    Atomization / heavy hydrides → bond-averaged Compton (geometry-relaxed).
    """
    if triplet_class == ComptonTripletClass.H2_LADDER and kind == "dissociation":
        return SurplusAnglePolicy.COVALENT_DIMER_UUD
    if triplet_class == ComptonTripletClass.HEAVY_HYDRIDE and kind == "dissociation":
        return SurplusAnglePolicy.BOND_AVERAGED_COMPTON
    if kind == "atomization" and triplet_class == ComptonTripletClass.HEAVY_HYDRIDE:
        return SurplusAnglePolicy.ELECTRONIC_COMPTON_TRIPLET
    if kind == "atomization":
        return SurplusAnglePolicy.ELECTRONIC_COMPTON_TRIPLET
    return SurplusAnglePolicy.DETUNING_COMPTON_TRIPLET


def curvature_feedback_weight(
    *,
    has_heavy_nucleus: bool,
    kind: BindingKind,
    triplet_class: ComptonTripletClass,
    compton_triplet: tuple[int, int, int],
) -> float:
    """
    Weight on ``dynamicBindingCurvatureCorrectionAtXi``.

    Heavy centres: full BBN cluster contrast (lock-in vs QCD).

    Homonuclear electronic dissociation (H₂): no heavy cluster spine — dress
    contrast with the Hopf second-order lapse ratio at the Compton ξ:

      w = 1 − (4/8) · (1 − C₂(ξ)/C₂(ξ_lock))

    At ξ_lock this is unity; at electronic ξ it reduces spurious over-counting
    that would compound on larger molecules.
    """
    if has_heavy_nucleus:
        return 1.0
    xi = lean.xi_from_compton_triplet(compton_triplet)
    c2 = lean.tuft_lapse_concentration_at_xi(xi)
    c2_lock = lean.tuft_lapse_concentration_at_xi(lean.XI_LOCKIN)
    lapse_ratio = c2 / max(c2_lock, 1e-30)
    return 1.0 - lean.STRONG_CHANNEL_FRACTION * (1.0 - lapse_ratio)


def dynamic_binding_feedback_at_xi_weighted(xi: float, contrast_weight: float) -> float:
    correction = lean.dynamic_binding_curvature_correction_at_xi(xi)
    return 1.0 + contrast_weight * correction


def contact_xi_for_readout(
    triplet: tuple[int, int, int],
    *,
    has_heavy_nucleus: bool,
) -> float:
    """Contact ξ for κ(ξ): Compton mean; heavy systems share the electronic spine."""
    xi_compton = lean.xi_from_compton_triplet(triplet)
    if not has_heavy_nucleus:
        return xi_compton
    return xi_compton


def resolve_shell_aware_readout(
    *,
    kind: BindingKind,
    fragments: tuple[FragmentConfig, ...],
    compton_triplet: tuple[int, int, int],
    net: Any,
    molecule_name: str = "",
) -> ShellAwareBindingReadout:
    """
    Build full shell-aware witness for one molecule/network.
    """
    import hqiv_curvature_contact_network as ccn

    triplet_class = classify_compton_triplet(compton_triplet)
    policy = surplus_angle_policy(
        kind=kind,
        triplet_class=triplet_class,
        fragments=fragments,
    )
    compton_det, _ = compton_window_angles_from_detuning_lapse(compton_triplet)
    eta_angles = compton_det.angles_rad

    if policy == SurplusAnglePolicy.COVALENT_DIMER_UUD:
        surplus_angles = DEFAULT_UUD_ANGLES_RAD
    elif policy == SurplusAnglePolicy.BOND_AVERAGED_COMPTON:
        surplus_angles = ccn.compton_angles_for_surplus(net)
    else:
        surplus_angles = eta_angles

    has_heavy = any(f.z_nuclear > 1 for f in fragments)
    electrons = tuple(max(f.electrons, 0) for f in fragments)
    if kind == "dissociation" and len(electrons) == 2:
        electron_split = (sum(electrons), electrons[0], electrons[1])
    elif kind == "atomization":
        lean_split = evs.lean_atomization_horizon_split(
            molecule_name or getattr(net, "name", ""),
            fragments,
        )
        if lean_split is None:
            electron_split = electrons
        else:
            electron_split = lean_split
    else:
        electron_split = electrons

    eta_linear = eta_p_from_compton_angles(eta_angles, compton_triplet)
    xi = contact_xi_for_readout(compton_triplet, has_heavy_nucleus=has_heavy)
    fb_weight = curvature_feedback_weight(
        has_heavy_nucleus=has_heavy,
        kind=kind,
        triplet_class=triplet_class,
        compton_triplet=compton_triplet,
    )

    heavy = next((f for f in fragments if f.z_nuclear > 1), None)
    n_centre_bonds = sum(
        1
        for c in net.contacts
        if c.kind == ccn.ContactKind.COVALENT_BOND
        and heavy is not None
        and c.i == 0
    )
    if n_centre_bonds == 0 and heavy is not None:
        n_centre_bonds = sum(1 for f in fragments if f.z_nuclear == 1)

    dress = 1.0
    if kind == "atomization" and heavy is not None:
        dress *= evs.centre_lone_pair_surplus_dress(
            heavy.z_nuclear,
            n_centre_bonds,
            eta_linear,
        )
        dress *= evs.hyperclosure_surplus_dress(n_centre_bonds)

    m_s, m_p, m_h = compton_triplet
    slot_labels = (
        evs.electronic_shell_label(heavy.z_nuclear if heavy else 1, slot="s")
        if heavy
        else "1s",
        evs.electronic_shell_label(heavy.z_nuclear, slot="p")
        if heavy and m_p > 1
        else "1s",
        "1s",
    )

    return ShellAwareBindingReadout(
        compton_triplet_m=compton_triplet,
        compton_triplet_class=triplet_class.value,
        surplus_angle_policy=policy.value,
        surplus_angles_rad=surplus_angles,
        eta_angles_rad=eta_angles,
        eta_p_linear=eta_linear,
        contact_xi=xi,
        curvature_feedback_weight=fb_weight,
        has_heavy_nucleus=has_heavy,
        electron_split=electron_split,
        electronic_shell_slots=slot_labels,
        surplus_dress_factor=dress,
    )

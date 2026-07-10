#!/usr/bin/env python3
"""
Reusable two-way feedback dynamics for HQIV chemistry/material readouts.

These helpers are deliberately small:

* scale anchors set a yardstick;
* feedback channels update the yardstick or state;
* bounded iteration records convergence instead of silently fitting.

Lean mirrors for the EM length/density pieces live in
``Hqiv.QuantumChemistry.OutsideContactReducedDeltas``.
"""

from __future__ import annotations

import math
from dataclasses import asdict, dataclass
from typing import Callable, Iterable

import hqiv_lean_physics_primitives as lean
import hqiv_outside_contact_ledger as ocl


@dataclass(frozen=True)
class EmLengthFeedback:
    """EM/BE feedback into contact scale, with mass held as scale anchor."""

    em: float
    alpha: float = lean.ALPHA

    @property
    def length_scale(self) -> float:
        """Lean ``contactLengthFromEmFeedback`` scale: ``em^alpha``."""
        return max(float(self.em), 1.0e-30) ** float(self.alpha)

    @property
    def volumetric_density_scale(self) -> float:
        """Density scales as ``1/r^3``."""
        return self.length_scale ** -3.0

    @property
    def areal_density_scale(self) -> float:
        """Sheet density scales as ``1/r^2``."""
        return self.length_scale ** -2.0

    @property
    def inverse_length_binding_scale(self) -> float:
        """First contact-energy proxy for Coulombic/elastic ``E ~ 1/r`` slots."""
        return self.length_scale ** -1.0

    @property
    def stiffness_scale(self) -> float:
        """Contact stiffness proxy ``E/r^3`` with ``E ~ 1/r`` => ``1/r^4``."""
        return self.length_scale ** -4.0

    def dress_length(self, r_bare: float) -> float:
        return float(r_bare) * self.length_scale

    def dress_volumetric_density(self, rho_bare: float) -> float:
        return float(rho_bare) * self.volumetric_density_scale

    def dress_areal_density(self, sigma_bare: float) -> float:
        return float(sigma_bare) * self.areal_density_scale

    def to_dict(self) -> dict[str, float]:
        return asdict(self) | {
            "length_scale": self.length_scale,
            "volumetric_density_scale": self.volumetric_density_scale,
            "areal_density_scale": self.areal_density_scale,
            "inverse_length_binding_scale": self.inverse_length_binding_scale,
            "stiffness_scale": self.stiffness_scale,
        }


def em_feedback_from_dielectric(n_dielectric: float) -> EmLengthFeedback:
    """Build EM length feedback from Lean/Python ``outsideEmChannel``."""
    return EmLengthFeedback(ocl.outside_em_channel(n_dielectric))


def spectral_contact_share() -> float:
    """Default log-space share for spectral anchors: shared strong contact × γ."""
    return clamp01(lean.STRONG_CHANNEL_FRACTION * lean.GAMMA)


@dataclass(frozen=True)
class ShellAnchorProjection:
    """
    Shell equation for projecting one spectral anchor onto bond observables.

    No bond-type labels enter.  The share is assembled from:

    * filled shared-channel occupancy ``bond_order / capacity``;
    * open-channel stress ``1 - occupancy``;
    * polar/ionic character ``δ²``;
    * phase/contact-route mismatch weight.

    The base contact share is the lattice factor ``γ · strong``.  Shell factors
    then allocate that same anchor differently into length and energy slots.
    """

    capacity: float
    bond_order: float
    ionic_character: float
    phase_contact_weight: float = 0.0
    ionic_route_weight: float = 0.0
    gas_alkali_halide_weight: float = 0.0
    metal_hydride_weight: float = 0.0
    hydrogen_acceptor_weight: float = 0.0
    halogen_open_channel_weight: float = 0.0
    period3_weight: float = 0.0
    anchor_share: float = lean.GAMMA * lean.STRONG_CHANNEL_FRACTION
    gamma: float = lean.GAMMA
    strong: float = lean.STRONG_CHANNEL_FRACTION

    @property
    def occupancy(self) -> float:
        return clamp01(float(self.bond_order) / max(float(self.capacity), 1.0e-30))

    @property
    def open_channel_fraction(self) -> float:
        return clamp01(1.0 - self.occupancy)

    @property
    def polarity(self) -> float:
        return clamp01(self.ionic_character)

    @property
    def polarity_amplitude(self) -> float:
        """Charge-transfer amplitude δ from ionic character δ²."""
        return math.sqrt(self.polarity)

    @property
    def base_share(self) -> float:
        return clamp01(self.anchor_share)

    @property
    def length_share(self) -> float:
        """
        Shell projection into contact length.

        Filled channels transmit the shared anchor; open channels and phase/contact
        mismatch add unsaturated length response.  Polarity softens length response
        because part of the anchor belongs in the energy partition.
        """
        open_lift = 1.0 + self.strong * self.open_channel_fraction
        phase_lift = 1.0 + self.gamma * clamp01(self.phase_contact_weight)
        polar_soften = 1.0 - self.strong * self.polarity
        ionic_lift = 1.0 + clamp01(self.ionic_route_weight) * self.polarity_amplitude
        return clamp01(self.base_share * open_lift * phase_lift * polar_soften * ionic_lift)

    @property
    def gas_polar_separation_scale(self) -> float:
        """
        Gas-phase donor-acceptor separation lift.

        This is not the condensed ionic outside-contact route.  It only activates
        through the period-2 alkali-halide shell weight and uses the charge-transfer
        amplitude δ with the shared strong channel.
        """
        return 1.0 + (
            clamp01(self.gas_alkali_halide_weight)
            * self.base_share
            * self.strong
            * self.polarity_amplitude
        )

    @property
    def gas_metal_hydride_length_scale(self) -> float:
        """
        Gas-phase metal-hydride elongation from covalent contact.

        Condensed ionic outside-contact overshoots the gas hydride.  The missing
        length is the charge-transfer amplitude δ, reduced by the already-shared
        spectral contact share through the strong channel:
        ``1 + δ · (1 − base · strong)``.
        """
        return 1.0 + (
            clamp01(self.metal_hydride_weight)
            * self.polarity_amplitude
            * (1.0 - self.base_share * self.strong)
        )

    @property
    def halogen_open_channel_length_scale(self) -> float:
        """
        Open-channel halogen length lift.

        Unsaturated halogen dimers need a soft open-channel elongation of the
        nested-WF contact.  The soft factor ``(1 − γ/2)`` is the same monogamy
        remnant used in the period-3 valence/core geometric blend.
        """
        return 1.0 + (
            clamp01(self.halogen_open_channel_weight)
            * self.base_share
            * self.strong
            * (1.0 - self.gamma / 2.0)
        )

    @property
    def period3_hydrogen_acceptor_length_soft(self) -> float:
        """
        Period-3 hydrogen-acceptor soft against spectral length overshoot.

        Period≥3 hydrides already carry an upstream s–p elongation.  The spectral
        EM length dress should not fully re-apply that same polar amplitude, so
        the shared contact share is reduced by ``base · γ · period · h · δ``.
        """
        return 1.0 - (
            clamp01(self.period3_weight)
            * clamp01(self.hydrogen_acceptor_weight)
            * self.base_share
            * self.gamma
            * self.polarity_amplitude
        )

    @property
    def network_open_channel_packing_scale(self) -> float:
        """
        Two-sided open-channel packing elongation.

        In a covalent network both contact ends contribute open-channel stress, so
        the unsaturated fraction enters as ``open²``.  Multiplied by the shared
        spectral contact share this is the missing packing dress beyond bare
        ``em^α`` length feedback.
        """
        open_f = self.open_channel_fraction
        return 1.0 + self.base_share * open_f * open_f

    @property
    def contact_length_dress_scale(self) -> float:
        """Compose gas-phase shell length dresses before spectral EM feedback."""
        return (
            self.gas_polar_separation_scale
            * self.gas_metal_hydride_length_scale
            * self.halogen_open_channel_length_scale
            * self.period3_hydrogen_acceptor_length_soft
        )

    @property
    def energy_share(self) -> float:
        """
        Shell projection into binding energy.

        Ionic/polar contacts get extra energy-channel activation; open-channel
        covalent contacts are softened because the missing channel is geometric.
        """
        polar_lift = 1.0 + self.polarity
        open_soften = 1.0 - self.strong * self.open_channel_fraction
        return clamp01(self.base_share * polar_lift * open_soften)

    @property
    def hydrogen_acceptor_energy_scale(self) -> float:
        """Hydrogen-1s to acceptor p-shell charge-transfer energy lift."""
        return 1.0 + (
            clamp01(self.hydrogen_acceptor_weight)
            * self.base_share
            * self.strong
            * self.polarity_amplitude
        )

    @property
    def energy_exponent_share(self) -> float:
        """
        Signed shell projection for well depth.

        The VB resonance uses ionic character δ² as a probability.  The spectral
        anchor couples to the charge-transfer amplitude δ.  The baseline sign
        ``2δ - 1`` rotates covalent wells toward inverse-length scaling and
        polar wells toward concentration deepening.  A two-sided polar surplus
        ``2γδ`` accounts for charge-transfer response on both ends of the contact
        without adding a molecule-type branch.
        """
        delta = self.polarity_amplitude
        return self.base_share * (2.0 * delta - 1.0 + 2.0 * self.gamma * delta)

    @property
    def stiffness_share(self) -> float:
        """Intermediate shell share for stiffness-like readouts."""
        return geometric_mean_positive((self.length_share, self.energy_share))

    def energy_scale_from_em(self, em: float) -> float:
        """Well-depth scale ``em^(alpha · signed_shell_energy_share)``."""
        return (
            max(float(em), 1.0e-30) ** (lean.ALPHA * self.energy_exponent_share)
            * self.hydrogen_acceptor_energy_scale
        )

    def to_dict(self) -> dict[str, float]:
        return asdict(self) | {
            "occupancy": self.occupancy,
            "open_channel_fraction": self.open_channel_fraction,
            "polarity": self.polarity,
            "polarity_amplitude": self.polarity_amplitude,
            "ionic_route_weight": clamp01(self.ionic_route_weight),
            "gas_alkali_halide_weight": clamp01(self.gas_alkali_halide_weight),
            "metal_hydride_weight": clamp01(self.metal_hydride_weight),
            "hydrogen_acceptor_weight": clamp01(self.hydrogen_acceptor_weight),
            "halogen_open_channel_weight": clamp01(self.halogen_open_channel_weight),
            "period3_weight": clamp01(self.period3_weight),
            "base_share": self.base_share,
            "length_share": self.length_share,
            "gas_polar_separation_scale": self.gas_polar_separation_scale,
            "gas_metal_hydride_length_scale": self.gas_metal_hydride_length_scale,
            "halogen_open_channel_length_scale": self.halogen_open_channel_length_scale,
            "period3_hydrogen_acceptor_length_soft": self.period3_hydrogen_acceptor_length_soft,
            "network_open_channel_packing_scale": self.network_open_channel_packing_scale,
            "contact_length_dress_scale": self.contact_length_dress_scale,
            "energy_share": self.energy_share,
            "hydrogen_acceptor_energy_scale": self.hydrogen_acceptor_energy_scale,
            "energy_exponent_share": self.energy_exponent_share,
            "stiffness_share": self.stiffness_share,
        }


def shell_anchor_projection(
    *,
    capacity: float,
    bond_order: float,
    ionic_character: float,
    phase_contact_weight: float = 0.0,
    ionic_route_weight: float = 0.0,
    gas_alkali_halide_weight: float = 0.0,
    metal_hydride_weight: float = 0.0,
    hydrogen_acceptor_weight: float = 0.0,
    halogen_open_channel_weight: float = 0.0,
    period3_weight: float = 0.0,
    anchor_share: float | None = None,
) -> ShellAnchorProjection:
    """Build the shell-equation projection for a bond contact."""
    return ShellAnchorProjection(
        capacity=capacity,
        bond_order=bond_order,
        ionic_character=ionic_character,
        phase_contact_weight=phase_contact_weight,
        ionic_route_weight=ionic_route_weight,
        gas_alkali_halide_weight=gas_alkali_halide_weight,
        metal_hydride_weight=metal_hydride_weight,
        hydrogen_acceptor_weight=hydrogen_acceptor_weight,
        halogen_open_channel_weight=halogen_open_channel_weight,
        period3_weight=period3_weight,
        anchor_share=spectral_contact_share() if anchor_share is None else clamp01(anchor_share),
    )


def em_feedback_from_concentration_weight(
    s: float,
    *,
    contact_share: float = 1.0,
) -> EmLengthFeedback:
    """Build EM length feedback directly from Clausius-Mossotti weight ``s``."""
    sc = max(0.0, min(1.0, float(s)))
    return EmLengthFeedback(
        1.0 + lean.STRONG_CHANNEL_FRACTION * sc,
        alpha=lean.ALPHA * clamp01(contact_share),
    )


@dataclass(frozen=True)
class FixedPointStep:
    index: int
    state: float
    next_state: float
    delta: float


@dataclass(frozen=True)
class FixedPointTrace:
    initial_state: float
    final_state: float
    converged: bool
    tolerance: float
    steps: tuple[FixedPointStep, ...]

    def to_dict(self) -> dict[str, object]:
        return {
            "initial_state": self.initial_state,
            "final_state": self.final_state,
            "converged": self.converged,
            "tolerance": self.tolerance,
            "steps": [asdict(s) for s in self.steps],
        }


def clamp01(x: float) -> float:
    return max(0.0, min(1.0, float(x)))


def geometric_mean_positive(values: Iterable[float]) -> float:
    """Geometric mean for positive scale factors."""
    vals = [float(v) for v in values if math.isfinite(float(v)) and float(v) > 0.0]
    if not vals:
        return 0.0
    return math.exp(sum(math.log(v) for v in vals) / len(vals))


def multiplicative_error_factor(pred: float, ref: float | None) -> float | None:
    """
    Symmetric multiplicative error factor.

    ``1`` is exact; ``1.10`` means either 10% high or 9.09% low.  This is the
    right aggregation unit for scale-anchor witnesses.
    """
    if ref in (None, 0.0):
        return None
    p = float(pred)
    r = float(ref)
    if not (math.isfinite(p) and math.isfinite(r)) or p <= 0.0 or r <= 0.0:
        return None
    ratio = p / r
    return max(ratio, 1.0 / ratio)


def multiplicative_error_pct(pred: float, ref: float | None) -> float | None:
    factor = multiplicative_error_factor(pred, ref)
    return None if factor is None else 100.0 * (factor - 1.0)


def bounded_fixed_point(
    initial: float,
    step_fn: Callable[[float], float],
    *,
    clamp: Callable[[float], float] = clamp01,
    max_steps: int = 5,
    tolerance: float = 1.0e-6,
    damping: float = 1.0,
) -> FixedPointTrace:
    """
    Bounded fixed-point iterator.

    ``damping=1`` means full update; lower values under-relax the update.  Every
    state is clamped, which keeps material/phase fractions physical.
    """
    state = clamp(initial)
    steps: list[FixedPointStep] = []
    converged = False
    damp = max(0.0, min(1.0, float(damping)))
    for idx in range(max_steps):
        raw_next = clamp(step_fn(state))
        next_state = clamp((1.0 - damp) * state + damp * raw_next)
        delta = abs(next_state - state)
        steps.append(FixedPointStep(idx, state, next_state, delta))
        state = next_state
        if delta <= tolerance:
            converged = True
            break
    return FixedPointTrace(
        initial_state=clamp(initial),
        final_state=state,
        converged=converged,
        tolerance=tolerance,
        steps=tuple(steps),
    )


def summarize_traces(traces: Iterable[FixedPointTrace]) -> dict[str, float | int]:
    traces = tuple(traces)
    if not traces:
        return {"count": 0, "converged": 0, "mean_abs_shift": 0.0, "max_abs_shift": 0.0}
    shifts = [abs(t.final_state - t.initial_state) for t in traces]
    return {
        "count": len(traces),
        "converged": sum(1 for t in traces if t.converged),
        "mean_abs_shift": sum(shifts) / len(shifts),
        "max_abs_shift": max(shifts),
    }

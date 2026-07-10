#!/usr/bin/env python3
"""Coupled relaxation helpers mirrored by Lean `CoupledRelaxation`.

These helpers do not fit residuals.  They implement finite one-step relaxation from a
feed-forward readout toward a coupled target, with the activation supplied by derived
structural flags in the caller.
"""

from __future__ import annotations


def clamp01(x: float) -> float:
    return min(1.0, max(0.0, x))


def coupled_relaxation_step(feed_forward: float, coupled_target: float, lam: float) -> float:
    """Lean `coupledRelaxationStep`: x + λ·(target − x)."""
    return feed_forward + lam * (coupled_target - feed_forward)


def structural_coupling_weight(missing_coupling: float, response_fraction: float) -> float:
    """Lean `structuralCouplingWeight`: clamp01(missing · response)."""
    return clamp01(missing_coupling * response_fraction)


def two_slot_coupled_relaxation(x: float, y: float, lam: float) -> tuple[float, float]:
    """Symmetric two-slot update; conserves x+y."""
    return (
        coupled_relaxation_step(x, y, lam),
        coupled_relaxation_step(y, x, lam),
    )


def branch_fraction_coupled_step(feed_forward: float, coupled_target: float, lam: float) -> float:
    """Lean `branchFractionCoupledStep`: relax and clamp to [0, 1]."""
    return clamp01(coupled_relaxation_step(feed_forward, coupled_target, lam))


def cage_limited_transport(diffusion: float, cage: float) -> float:
    """Lean `cageLimitedTransport`: D_eff = D·(1-cage)."""
    return diffusion * (1.0 - cage)


def activation_rate_slot(contact_rate: float, barrier_transmission: float) -> float:
    """Lean `activationRateSlot`: rate = contact_rate·barrier."""
    return contact_rate * barrier_transmission


def barrier_transmission_from_gate(barrier_ev: float, scale_ev: float) -> float:
    """
    Lean ``barrierTransmissionFromGate``:
    ``T = 1 / (1 + B / max(strong · D_scale, ε))``.
    Zero barrier recovers identity.
    """
    import hqiv_lean_physics_primitives as lean

    denom = lean.STRONG_CHANNEL_FRACTION * max(float(scale_ev), 0.0)
    return 1.0 / (1.0 + float(barrier_ev) / max(denom, 1e-30))


def activation_rate_from_saddle(
    contact_rate: float, barrier_ev: float, scale_ev: float
) -> float:
    """Lean ``activationRateFromSaddle``."""
    return activation_rate_slot(
        contact_rate, barrier_transmission_from_gate(barrier_ev, scale_ev)
    )


def network_propagation_step(local_slot: float, neighbour_mean: float, lam: float) -> float:
    """Lean `networkPropagationStep`: local register relaxes toward neighbour mean."""
    return coupled_relaxation_step(local_slot, neighbour_mean, lam)


def geometry_binding_relaxed_length(
    one_way_length: float, target_length: float, lam: float
) -> float:
    """Lean `geometryBindingRelaxedLength`: bond geometry relaxes toward contact target."""
    return coupled_relaxation_step(one_way_length, target_length, lam)


def coupling_level_from_weight(lam: float) -> str:
    if lam <= 0.0:
        return "feed_forward"
    if lam >= 1.0:
        return "coupled_relaxed"
    return "feedback_factorized_partial"


if __name__ == "__main__":
    x, y, lam = 1.0, 3.0, 0.5
    xp, yp = two_slot_coupled_relaxation(x, y, lam)
    assert abs((xp + yp) - (x + y)) < 1.0e-12
    assert branch_fraction_coupled_step(-1.0, 0.5, 1.0) == 0.5
    assert cage_limited_transport(2.0, 1.0) == 0.0
    assert activation_rate_slot(2.0, 0.0) == 0.0
    print("hqiv_chemistry_coupled_readout: OK")

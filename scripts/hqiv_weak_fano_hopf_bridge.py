#!/usr/bin/env python3
"""
Weak Fano/Hopf bridge energy.

Mirror of `Hqiv.Physics.WeakFanoHopfBridge`.

The bridge is the topological hump between β endpoints:

  Fano rotation shape × Hopf fibration shape × phase-lift shape × endpoint scale.

By default the endpoint scale is the model electron-neutrino mass used by the β
phase-space code, keeping this as a small weak-channel correction.
"""

from __future__ import annotations

from dataclasses import dataclass

import hqiv_lean_physics_primitives as lean

REFERENCE_M = lean.REFERENCE_M


@dataclass(frozen=True)
class WeakFanoHopfBridge:
    source_vertex: int = 0
    target_vertex: int = 1
    shell: int = REFERENCE_M
    hopf_winding: int = 1


def fano_vertex_distance(a: int, b: int) -> int:
    if not (0 <= a <= 6 and 0 <= b <= 6):
        raise ValueError("Fano vertices must be in 0..6")
    return abs(b - a)


def fano_rotation_shape(a: int, b: int) -> float:
    return fano_vertex_distance(a, b) / 6.0


def hopf_fibration_shape(winding: int) -> float:
    if winding < 0:
        raise ValueError("winding must be nonnegative")
    return float(winding) / float(winding + 2)


def phase_lift_coeff(shell: int) -> float:
    # Lean `phaseLiftCoeff m = phi(m)/6`, with phi(m)=2(m+1).
    return (2.0 * float(shell + 1)) / 6.0


def phase_lift_shape(shell: int, reference_shell: int = REFERENCE_M) -> float:
    return phase_lift_coeff(shell) / phase_lift_coeff(reference_shell)


def weak_bridge_shape(bridge: WeakFanoHopfBridge = WeakFanoHopfBridge()) -> float:
    return (
        fano_rotation_shape(bridge.source_vertex, bridge.target_vertex)
        * hopf_fibration_shape(bridge.hopf_winding)
        * phase_lift_shape(bridge.shell)
    )


def weak_bridge_energy_mev(
    endpoint_scale_mev: float,
    bridge: WeakFanoHopfBridge = WeakFanoHopfBridge(),
) -> float:
    return max(endpoint_scale_mev, 0.0) * weak_bridge_shape(bridge)


def default_beta_bridge() -> WeakFanoHopfBridge:
    return WeakFanoHopfBridge()

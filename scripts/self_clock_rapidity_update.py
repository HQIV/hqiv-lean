#!/usr/bin/env python3
"""Mirror of `Hqiv.Physics.SurfaceWaveSelfClock.selfClock_rapidity_update` (quarter-turn + φ·Δt)."""

import math


def compton_quarter_turn(m: int) -> float:
    """Matches Lean `comptonAngularFrequency m * (π/2)` with `comptonAngularFrequency m = m + 1`."""
    return float(m + 1) * (math.pi / 2.0)


def self_clock_phase(m: int, cumulative_rapidity: float) -> float:
    return compton_quarter_turn(m) + cumulative_rapidity


def self_clock_rapidity_update(
    m: int, cumulative_rapidity: float, phi: float, dt: float
) -> float:
    return self_clock_phase(m, cumulative_rapidity + phi * dt)


if __name__ == "__main__":
    m = 4
    r0 = 0.0
    phi = 0.7
    dt = 0.01
    lhs = self_clock_phase(m, r0 + phi * dt)
    rhs = self_clock_phase(m, r0) + phi * dt
    assert abs(lhs - rhs) < 1e-15
    expected = compton_quarter_turn(m) + phi * dt
    assert abs(self_clock_rapidity_update(m, r0, phi, dt) - expected) < 1e-15
    print("self_clock_rapidity_update round-trip OK")

# SPDX-License-Identifier: Apache-2.0
"""
Chart-level F2 alignment: continuum scalars φ_F, dot_F on ℝ^{1+3} ↔ fluid inputs.

This mirrors the **Prop** bundle `OMaxwellFluidChartHypothesis` in
`Hqiv/Physics/HQIVFluidClosureScaffold.lean` (same repository):

  - phi_fluid = φ_F(c)                    (`phi_pointwise`)
  - grad_phi (Fin 3) = spatial part of ∇φ_F at c   (`chartSpatialPhiGradient` / `grad_phi_spatial`)
  - dot_theta = delta_theta_prime(Eprime)         (`dotTheta_bridge`; tipping-from-E′, not ∂_t)
  - grad_dot (Fin 3) = spatial ∇(dot_F) at c      (`chartSpatialDotGradient` / `grad_dot_spatial`)

Vacuum momentum source (matches `hqivVacuumMomentumSource3` / pyhqiv `g_vac_vector`):

  g_vac[i] = -(γ/6) * (phi * grad_dot[i] + dot * grad_phi[i]),  γ = 2/5.

When the reference implementation `hqvmpy` / `pyhqiv.fluid` is on PYTHONPATH, pass the same tuples into
`vacuum_momentum_source3` there; this module stays dependency-free for CI smoke imports.

See: AGENTS/FLUID_OMAXWELL_ROADMAP.md §F2, paper/HQIV_OMaxwell_fluid_chart.tex
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

# Chart point c : Fin 4 → ℝ represented as (t, x, y, z).
ChartPoint = tuple[float, float, float, float]
Spatial3 = tuple[float, float, float]


def _as_spatial3(g4: Sequence[float]) -> Spatial3:
    """Take ν = 1,2,3 from a length-4 coordinate gradient list."""
    if len(g4) != 4:
        raise ValueError("expected 4 components (time + space)")
    return (float(g4[1]), float(g4[2]), float(g4[3]))


def chart_spatial_phi_gradient(
    coords_gradient_phi_f: Sequence[float],
) -> Spatial3:
    """Alias for `chartSpatialPhiGradient` once `coordsGradientComponents φF c` is computed (ν=0..3)."""
    return _as_spatial3(coords_gradient_phi_f)


def chart_spatial_dot_gradient(
    coords_gradient_dot_f: Sequence[float],
) -> Spatial3:
    """Alias for `chartSpatialDotGradient` for a scalar dot_F."""
    return _as_spatial3(coords_gradient_dot_f)


def vacuum_momentum_source3(
    gamma: float,
    phi: float,
    dot: float,
    grad_phi: Spatial3,
    grad_dot: Spatial3,
) -> Spatial3:
    """Python mirror of `hqivVacuumMomentumSource3` (componentwise)."""
    return tuple(
        (-gamma / 6.0) * (phi * grad_dot[i] + dot * grad_phi[i]) for i in range(3)
    )


@dataclass(frozen=True)
class OMaxwellFluidChartHypothesisData:
    """Numeric snapshot: check equalities that Lean states as `Prop` hypotheses."""

    phi_f_at_c: float
    phi_fluid: float
    dot_theta: float
    delta_theta_prime_e_prime: float
    grad_phi3: Spatial3
    chart_grad_phi3: Spatial3
    grad_dot3: Spatial3
    chart_grad_dot3: Spatial3

    def holds_algebraically(self, *, tol: float = 1e-9) -> bool:
        def close(a: float, b: float) -> bool:
            return abs(a - b) <= tol

        if not close(self.phi_fluid, self.phi_f_at_c):
            return False
        if not close(self.dot_theta, self.delta_theta_prime_e_prime):
            return False
        for i in range(3):
            if not close(self.grad_phi3[i], self.chart_grad_phi3[i]):
                return False
            if not close(self.grad_dot3[i], self.chart_grad_dot3[i]):
                return False
        return True


__all__ = [
    "ChartPoint",
    "Spatial3",
    "chart_spatial_phi_gradient",
    "chart_spatial_dot_gradient",
    "vacuum_momentum_source3",
    "OMaxwellFluidChartHypothesisData",
]

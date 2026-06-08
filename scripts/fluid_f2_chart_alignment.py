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

Longitudinal stress extension (matches `hqivLongitudinalStressTensor3`):

  τ_L[i,j] = κ_L * rho * coupling_log * grad_phi_along * direction[i] * direction[j]

The mesh/discretization layer should compute div(τ_L); this module carries that vector as
`longitudinal_stress_force3` so RANS/LES residuals can keep it separate from pressure.

Action-mined force bundle (matches `HQIVActionMinedForcePointData`):

  f_action = f_long + f_F + f_metric_phi + f_plaquette + f_current_coherence

SST extension (matches `HQIVSSTPointData` residual slots):

  R_k = N*rho*f(a,phi)*(k_dot + conv_k) - (P_k - D_k + Diff_k + S_k^HQIV)
  R_omega = N*rho*f(a,phi)*(omega_dot + conv_omega)
            - (P_omega - D_omega + Diff_omega + CrossDiff_omega + S_omega^HQIV)
  a_HQIV = clamp(|tau_action|/(rho*k)) or clamp((betaStar*omega - S_k^HQIV/(rho*k))/|S|)

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
Matrix33 = tuple[Spatial3, Spatial3, Spatial3]


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


def longitudinal_stress_tensor3(
    kappa_l: float,
    density: float,
    coupling_log: float,
    grad_phi_along: float,
    direction: Spatial3,
) -> Matrix33:
    """Python mirror of `hqivLongitudinalStressTensor3`.

    `direction` should be supplied by the simulator, e.g. flow-aligned, vorticity-aligned,
    or shear-layer aligned. This helper does not normalize it implicitly.
    """
    coeff = float(kappa_l) * float(density) * float(coupling_log) * float(grad_phi_along)
    d = tuple(float(v) for v in direction)
    return (
        (coeff * d[0] * d[0], coeff * d[0] * d[1], coeff * d[0] * d[2]),
        (coeff * d[1] * d[0], coeff * d[1] * d[1], coeff * d[1] * d[2]),
        (coeff * d[2] * d[0], coeff * d[2] * d[1], coeff * d[2] * d[2]),
    )


def longitudinal_stress_force3(stress_divergence: Sequence[float]) -> Spatial3:
    """Force density contribution `div(τ_L)` supplied by the discretization layer."""
    if len(stress_divergence) != 3:
        raise ValueError("expected 3 stress-divergence components")
    return (float(stress_divergence[0]), float(stress_divergence[1]), float(stress_divergence[2]))


def add_longitudinal_force3(base_rhs: Spatial3, stress_divergence: Sequence[float]) -> Spatial3:
    """RANS/LES RHS extension: keep longitudinal stress separate from pressure/body force."""
    f_long = longitudinal_stress_force3(stress_divergence)
    return tuple(float(base_rhs[i]) + f_long[i] for i in range(3))


def _as_force3(v: Sequence[float], *, name: str) -> Spatial3:
    if len(v) != 3:
        raise ValueError(f"expected 3 {name} components")
    return (float(v[0]), float(v[1]), float(v[2]))


@dataclass(frozen=True)
class ActionMinedForcePointData:
    """Python mirror of Lean `HQIVActionMinedForcePointData`."""

    longitudinal_stress_divergence: Spatial3
    field_stress_divergence: Spatial3
    metric_phi_force: Spatial3
    plaquette_force: Spatial3
    current_coherence_force: Spatial3

    def force(self) -> Spatial3:
        """Total additional action-mined force density."""
        return tuple(
            self.longitudinal_stress_divergence[i]
            + self.field_stress_divergence[i]
            + self.metric_phi_force[i]
            + self.plaquette_force[i]
            + self.current_coherence_force[i]
            for i in range(3)
        )


def action_mined_force3(
    longitudinal_stress_divergence: Sequence[float],
    field_stress_divergence: Sequence[float],
    metric_phi_force: Sequence[float],
    plaquette_force: Sequence[float],
    current_coherence_force: Sequence[float],
) -> Spatial3:
    """Compute `f_action = f_long + f_F + f_metric_phi + f_plaquette + f_current_coherence`."""
    data = ActionMinedForcePointData(
        longitudinal_stress_divergence=_as_force3(longitudinal_stress_divergence, name="longitudinal"),
        field_stress_divergence=_as_force3(field_stress_divergence, name="field-stress"),
        metric_phi_force=_as_force3(metric_phi_force, name="metric-phi"),
        plaquette_force=_as_force3(plaquette_force, name="plaquette"),
        current_coherence_force=_as_force3(current_coherence_force, name="current-coherence"),
    )
    return data.force()


def add_action_mined_forces3(base_rhs: Spatial3, force_data: ActionMinedForcePointData) -> Spatial3:
    """RANS/LES RHS extension for the full action-mined force certificate."""
    f_action = force_data.force()
    return tuple(float(base_rhs[i]) + f_action[i] for i in range(3))


def hqiv_inertia_factor(a_loc: float, phi: float) -> float:
    """Mirror of `hqivFluidInertiaFactor`; caller must avoid a zero denominator."""
    return float(a_loc) / (float(a_loc) + float(phi) / 6.0)


def clamp(lo: float, hi: float, value: float) -> float:
    """Mirror of Lean `hqivClamp`."""
    return min(float(hi), max(float(lo), float(value)))


def dynamic_bradshaw_from_stress(
    density: float,
    k: float,
    action_stress_norm: float,
    lo: float,
    hi: float,
) -> float:
    """Dynamic Bradshaw coefficient `clamp(|tau_action|/(rho*k))`."""
    return clamp(lo, hi, float(action_stress_norm) / (float(density) * float(k)))


def dynamic_bradshaw_from_equilibrium(
    density: float,
    k: float,
    omega: float,
    beta_star: float,
    strain_norm: float,
    action_k_source: float,
    lo: float,
    hi: float,
) -> float:
    """Dynamic Bradshaw coefficient from local k-equilibrium."""
    raw = (float(beta_star) * float(omega) - float(action_k_source) / (float(density) * float(k))) / float(
        strain_norm
    )
    return clamp(lo, hi, raw)


@dataclass(frozen=True)
class SSTTransportPointData:
    """Python mirror of Lean `HQIVSSTPointData` transport fields."""

    lapse: float
    rho: float
    inertia_factor: float
    k: float
    omega: float
    action_stress_norm: float
    strain_norm: float
    beta_star: float
    bradshaw_min: float
    bradshaw_max: float
    k_dot: float
    omega_dot: float
    convective_k: float
    convective_omega: float
    production_k: float
    destruction_k: float
    diffusion_k: float
    production_omega: float
    destruction_omega: float
    diffusion_omega: float
    cross_diffusion_omega: float
    action_k_source: float
    action_omega_source: float

    def dynamic_bradshaw_stress(self) -> float:
        return dynamic_bradshaw_from_stress(
            self.rho, self.k, self.action_stress_norm, self.bradshaw_min, self.bradshaw_max
        )

    def dynamic_bradshaw_equilibrium(self) -> float:
        return dynamic_bradshaw_from_equilibrium(
            self.rho,
            self.k,
            self.omega,
            self.beta_star,
            self.strain_norm,
            self.action_k_source,
            self.bradshaw_min,
            self.bradshaw_max,
        )


def sst_k_residual(data: SSTTransportPointData) -> float:
    """HQIV lapse/action-modified SST k residual."""
    lhs = data.lapse * data.rho * data.inertia_factor * (data.k_dot + data.convective_k)
    rhs = data.production_k - data.destruction_k + data.diffusion_k + data.action_k_source
    return lhs - rhs


def sst_omega_residual(data: SSTTransportPointData) -> float:
    """HQIV lapse/action-modified SST omega residual."""
    lhs = data.lapse * data.rho * data.inertia_factor * (data.omega_dot + data.convective_omega)
    rhs = (
        data.production_omega
        - data.destruction_omega
        + data.diffusion_omega
        + data.cross_diffusion_omega
        + data.action_omega_source
    )
    return lhs - rhs


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
    "Matrix33",
    "chart_spatial_phi_gradient",
    "chart_spatial_dot_gradient",
    "vacuum_momentum_source3",
    "longitudinal_stress_tensor3",
    "longitudinal_stress_force3",
    "add_longitudinal_force3",
    "ActionMinedForcePointData",
    "action_mined_force3",
    "add_action_mined_forces3",
    "hqiv_inertia_factor",
    "clamp",
    "dynamic_bradshaw_from_stress",
    "dynamic_bradshaw_from_equilibrium",
    "SSTTransportPointData",
    "sst_k_residual",
    "sst_omega_residual",
    "OMaxwellFluidChartHypothesisData",
]

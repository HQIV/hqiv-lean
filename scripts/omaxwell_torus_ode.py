"""
O-Maxwell torus ODE prototype on S^7 metahorizon.

Numerical mirror of the Lean scaffold:
- Potential = associator channel + phi(m)*bond_surplus + S^7 norm penalty
- Force from finite-difference gradient
- RK4 integration with S^7 projection
"""

from __future__ import annotations

from dataclasses import dataclass
import math
from typing import Iterable, Optional

from bonded_horizon_casimir_float import bond_horizon_surplus_ev
from fragment_aware_bonded_horizon import (
    BondGeometry,
    FragmentConfig,
    MoleculeConfig,
)
from nuclear_torus_casimir_float import (
    EV_PER_LAMBDA_UNIT,
    octonion_associator_norm_sq,
    nuclear_torus_x,
    nuclear_torus_l,
    DEFAULT_UUD_ANGLES_RAD,
    occupation_list,
)


Vec8 = list[float]


@dataclass(frozen=True)
class ODESettings:
    dt: float = 0.01
    steps: int = 1200
    eps: float = 1e-4
    damping: float = 0.03
    m_shell: int = 4
    s7_penalty: float = 1.0
    potential_mode: str = "nuclear_only"  # "nuclear_only" | "joint_horizon"
    uncertainty_coeff: float = 1.0
    equilibrium_tol: float = 1e-4
    force_tol: float = 1e-4
    #: Looser bound for reporting “plateau” stationarity under coarse V (optional).
    force_tol_practical: float = 8.5
    #: Symmetric FD step for equilibrium `∇V` only; `None` ⇒ use `eps`.
    equilibrium_eps: Optional[float] = None
    adaptive_damping: bool = True
    # Armijo backtracking (steepest descent on ℝ⁸ with S⁷ reprojection per trial).
    # Force from `_force` equals −∇V (finite-difference); step x ← proj(x + α·force).
    armijo_c: float = 1e-4
    armijo_rho: float = 0.5
    line_search_max_iter: int = 28
    line_search_alpha0: float = 0.5


def _norm(v: Vec8) -> float:
    return math.sqrt(sum(x * x for x in v))


def _project_s7(v: Vec8) -> Vec8:
    n = _norm(v)
    if n <= 0.0:
        out = [0.0] * 8
        out[0] = 1.0
        return out
    return [x / n for x in v]


def _phi_of_shell(m: int) -> float:
    return 2.0 * (float(m) + 1.0)


def _seed_state(molecule: MoleculeConfig) -> Vec8:
    z_sum = sum(max(f.z_nuclear, 1) for f in molecule.fragments)
    e_sum = sum(max(f.electrons, 1) for f in molecule.fragments)
    raw = [
        1.0,
        float(z_sum),
        float(e_sum),
        float(len(molecule.fragments)),
        float(len(molecule.bonds) + 1),
        0.5 * float(z_sum + e_sum),
        1.0 + float(z_sum - e_sum),
        2.0,
    ]
    return _project_s7(raw)


def _bond_distance_factor(bonds: Iterable[BondGeometry]) -> float:
    # Same Bohr conversion as fragment-aware script.
    a0 = 0.529177210903
    vals = []
    for b in bonds:
        vals.append(1.0 / (1.0 + b.distance_angstrom / a0))
    if not vals:
        return 1.0
    return sum(vals) / float(len(vals))


def _bond_distance_lattice(bond: BondGeometry) -> float:
    a0 = 0.529177210903
    return bond.distance_angstrom / a0


def _bond_lookup(molecule: MoleculeConfig) -> dict[tuple[int, int], float]:
    out: dict[tuple[int, int], float] = {}
    for b in molecule.bonds:
        i, j = sorted((b.frag_i, b.frag_j))
        out[(i, j)] = _bond_distance_lattice(b)
    return out


def _occupation_shell_overlap_weight(n_a: int, n_b: int) -> float:
    """
    Weighted shell overlap from occupation lists.
    Weights shell `ell` by `(ell+1)` to preserve shell structure influence.
    """
    from collections import Counter

    oa = Counter(occupation_list(max(n_a, 0)))
    ob = Counter(occupation_list(max(n_b, 0)))
    keys = set(oa) | set(ob)
    if not keys:
        return 1.0
    numer = 0.0
    denom = 0.0
    for ell in keys:
        w = float(ell + 1)
        numer += w * float(min(oa[ell], ob[ell]))
        denom += w * float(max(oa[ell], ob[ell]))
    return numer / denom if denom > 0.0 else 1.0


def molecule_bond_surplus_ev(molecule: MoleculeConfig, x: Vec8 | None = None) -> float:
    """
    Multi-fragment pair ledger:
      For each pair (i,j), use joint-vs-separated surplus on (N_i + N_j, N_i, N_j),
      weighted by bond geometry and (optionally) state-coupled radial mismatch.
    """
    frags = molecule.fragments
    if len(frags) < 2:
        return 0.0
    bonds = _bond_lookup(molecule)
    r = _radial_scale(x) if x is not None else None
    num = 0.0
    den = 0.0
    for i in range(len(frags)):
        for j in range(i + 1, len(frags)):
            ni, nj = frags[i].electrons, frags[j].electrons
            raw = bond_horizon_surplus_ev(ni + nj, ni, nj)
            d = bonds.get((i, j), 2.0)
            geom_w = 1.0 / (1.0 + d)
            if r is None:
                state_w = 1.0
            else:
                state_w = 1.0 / (1.0 + abs(r - d))
            w = geom_w * state_w
            num += raw * w
            den += w
    return num / den if den > 0.0 else 0.0


def _associator_channel(x: Vec8, molecule: MoleculeConfig) -> float:
    x_ref = nuclear_torus_x(DEFAULT_UUD_ANGLES_RAD)
    l_ref = nuclear_torus_l(DEFAULT_UUD_ANGLES_RAD)
    z_vals = [max(f.z_nuclear, 1) for f in molecule.fragments]
    z_total = float(sum(z_vals))
    delta_z = float(max(z_vals) - min(z_vals)) if z_vals else 0.0
    charge_mod = 1.0 + (delta_z / z_total if z_total > 0.0 else 0.0) * _bond_distance_factor(molecule.bonds)
    return charge_mod * octonion_associator_norm_sq(x, x_ref, l_ref)


def _occupation_mismatch_ratio(n_joint: int, n_frag: int) -> float:
    return abs(float(n_joint - n_frag)) / (float(n_joint + n_frag) + 1.0)


def _nuclear_channel(x: Vec8, molecule: MoleculeConfig) -> float:
    x_ref = nuclear_torus_x(DEFAULT_UUD_ANGLES_RAD)
    l_ref = nuclear_torus_l(DEFAULT_UUD_ANGLES_RAD)
    return octonion_associator_norm_sq(x, x_ref, l_ref)


def _joint_horizon_split_channels(x: Vec8, molecule: MoleculeConfig) -> tuple[float, float, float]:
    n_joint = sum(f.electrons for f in molecule.fragments)
    n_nuclear = sum(max(f.z_nuclear, 1) for f in molecule.fragments)
    electron_counts = [max(f.electrons, 0) for f in molecule.fragments]
    v_nuclear = _nuclear_channel(x, molecule)
    # Shell-resolved overlap between joint electronic occupancy and nuclear-charge proxy occupancy.
    w_en = _occupation_shell_overlap_weight(n_joint, n_nuclear)
    # Electron-electron channel from pairwise shell overlap average.
    pair_weights: list[float] = []
    for i in range(len(electron_counts)):
        for j in range(i + 1, len(electron_counts)):
            pair_weights.append(_occupation_shell_overlap_weight(electron_counts[i], electron_counts[j]))
    w_ee = (sum(pair_weights) / float(len(pair_weights))) if pair_weights else 0.0
    v_en = w_en * v_nuclear
    v_ee = w_ee * v_nuclear
    return v_nuclear, v_en, v_ee


def _radial_scale(x: Vec8) -> float:
    return math.sqrt(x[1] * x[1] + x[2] * x[2] + x[3] * x[3])


def _potential(x: Vec8, molecule: MoleculeConfig, settings: ODESettings) -> float:
    bond_surplus_ev = molecule_bond_surplus_ev(molecule, x)
    bond_surplus_lambda = bond_surplus_ev / EV_PER_LAMBDA_UNIT
    norm_sq = sum(t * t for t in x)
    uncertainty_term = settings.uncertainty_coeff * _phi_of_shell(settings.m_shell) / (_radial_scale(x) + 1e-3)
    if settings.potential_mode == "joint_horizon":
        v_nuclear, v_en, v_ee = _joint_horizon_split_channels(x, molecule)
        channel_term = v_nuclear + v_en + v_ee
    else:
        channel_term = _associator_channel(x, molecule)
    return (
        channel_term
        + uncertainty_term
        + _phi_of_shell(settings.m_shell) * bond_surplus_lambda
        + settings.s7_penalty * (norm_sq - 1.0) ** 2
    )


def _equilibrium_fd_eps(settings: ODESettings) -> float:
    return settings.equilibrium_eps if settings.equilibrium_eps is not None else settings.eps


def _force(
    x: Vec8,
    molecule: MoleculeConfig,
    settings: ODESettings,
    *,
    fd_eps: Optional[float] = None,
) -> Vec8:
    eps = fd_eps if fd_eps is not None else settings.eps
    out = [0.0] * 8
    for i in range(8):
        xp = x.copy()
        xm = x.copy()
        xp[i] += eps
        xm[i] -= eps
        vp = _potential(xp, molecule, settings)
        vm = _potential(xm, molecule, settings)
        out[i] = -((vp - vm) / (2.0 * eps))
    return out


def _add(a: Vec8, b: Vec8, scale: float = 1.0) -> Vec8:
    return [x + scale * y for x, y in zip(a, b)]


def _dot(a: Vec8, b: Vec8) -> float:
    return sum(x * y for x, y in zip(a, b))


def _riemannian_grad_s7(x: Vec8, force: Vec8) -> Vec8:
    """
    Ambient `force` = −∇V (componentwise finite difference).
    Euclidean gradient g = −force. Riemannian (tangent) gradient on S⁷ embedded in ℝ⁸:

      h = g − ⟨g,x⟩ x = −force + ⟨force,x⟩ x

    Descent direction on the sphere is −h = force − ⟨force,x⟩ x.
    """
    xf = _dot(x, force)
    return [fi - xf * xi for xi, fi in zip(x, force)]


def backtracking_line_search(
    x: Vec8,
    force: Vec8,
    potential_fn,
    *,
    alpha0: float,
    c: float,
    rho: float,
    max_iter: int,
) -> tuple[Vec8, float, bool]:
    """
    Armijo on S⁷ with Riemannian steepest descent.

    Let `desc = force − ⟨force,x⟩ x` (ambient descent direction tangent to S⁷).
    Trial: `x' = normalize(x + α desc)`.

    Armijo (matching tangential gradient norm):

      V(x') ≤ V(x) − c α ‖desc‖²

    (`‖desc‖²` agrees with ⟨∇_S V, −desc⟩ in the embedded picture for this retraction at first order.)
    """
    v0 = potential_fn(x)
    desc = _riemannian_grad_s7(x, force)
    dsq = _dot(desc, desc)
    if dsq < 1e-28:
        return list(x), 0.0, True
    alpha = alpha0
    for _ in range(max_iter):
        x_trial = _project_s7([xi + alpha * di for xi, di in zip(x, desc)])
        v1 = potential_fn(x_trial)
        if v1 <= v0 - c * alpha * dsq:
            return x_trial, alpha, True
        alpha *= rho
    return list(x), alpha, False


def integrate_molecule(molecule: MoleculeConfig, settings: ODESettings = ODESettings()) -> dict[str, float]:
    x = _seed_state(molecule)
    v = [0.0] * 8

    dt = settings.dt
    damp = settings.damping

    for _ in range(settings.steps):
        # RK4 on (x, v) with dv/dt = F(x) - damp*v
        def accel(xx: Vec8, vv: Vec8) -> Vec8:
            f = _force(xx, molecule, settings)
            return [fi - damp * vi for fi, vi in zip(f, vv)]

        k1x = v
        k1v = accel(x, v)

        x2 = _project_s7(_add(x, k1x, dt / 2.0))
        v2 = _add(v, k1v, dt / 2.0)
        k2x = v2
        k2v = accel(x2, v2)

        x3 = _project_s7(_add(x, k2x, dt / 2.0))
        v3 = _add(v, k2v, dt / 2.0)
        k3x = v3
        k3v = accel(x3, v3)

        x4 = _project_s7(_add(x, k3x, dt))
        v4 = _add(v, k3v, dt)
        k4x = v4
        k4v = accel(x4, v4)

        x = _project_s7(
            [
                xi + (dt / 6.0) * (a + 2.0 * b + 2.0 * c + d)
                for xi, a, b, c, d in zip(x, k1x, k2x, k3x, k4x)
            ]
        )
        v = [
            vi + (dt / 6.0) * (a + 2.0 * b + 2.0 * c + d)
            for vi, a, b, c, d in zip(v, k1v, k2v, k3v, k4v)
        ]

    pot = _potential(x, molecule, settings)
    kinetic = 0.5 * sum(t * t for t in v)
    energy_lambda = pot + kinetic
    return {
        "final_energy_lambda": energy_lambda,
        "final_energy_ev": energy_lambda * EV_PER_LAMBDA_UNIT,
        "radial_scale": _radial_scale(x),
        "speed": _norm(v),
    }


def solve_equilibrium_radius(
    molecule: MoleculeConfig,
    settings: ODESettings = ODESettings(),
    max_steps: int = 400,
) -> dict[str, float | bool]:
    """
    Equilibrium via monotone Armijo backtracking on V on S⁷ (Riemannian tangent
    descent + normalize). Uses `equilibrium_eps` for a finer FD gradient when set.
    """
    x = _seed_state(molecule)
    v = [0.0] * 8  # unused for Armijo path; kept for API compatibility
    fd_eps = _equilibrium_fd_eps(settings)

    def V_state(xx: Vec8) -> float:
        return _potential(xx, molecule, settings)

    converged = False
    converged_practical = False
    last_alpha = 0.0
    armijo_fail_streak = 0
    alpha0_scale = 1.0
    f0 = _norm(_force(x, molecule, settings, fd_eps=fd_eps))
    last_step = 0

    for step in range(max_steps):
        last_step = step + 1
        f = _force(x, molecule, settings, fd_eps=fd_eps)
        f_norm = _norm(f)
        if f_norm < settings.force_tol:
            converged = True
            converged_practical = True
            break
        if f_norm < settings.force_tol_practical:
            converged_practical = True

        x_new, alpha_used, accepted = backtracking_line_search(
            x,
            f,
            V_state,
            alpha0=settings.line_search_alpha0 * alpha0_scale,
            c=settings.armijo_c,
            rho=settings.armijo_rho,
            max_iter=settings.line_search_max_iter,
        )
        last_alpha = alpha_used
        if accepted:
            armijo_fail_streak = 0
            alpha0_scale = min(1.0, alpha0_scale * 1.03)
            x = x_new
        else:
            armijo_fail_streak += 1
            alpha0_scale *= 0.72
            if armijo_fail_streak >= 20:
                break

    r = _radial_scale(x)
    f_final = _force(x, molecule, settings, fd_eps=fd_eps)
    fn_final = _norm(f_final)
    v_final = V_state(x)
    if not converged_practical and fn_final < settings.force_tol_practical:
        converged_practical = True
    return {
        "x_eq_lattice": r,
        "speed": _norm(v),
        "force_norm": fn_final,
        "eq_force_norm_after_backtrack": fn_final,
        "potential_at_eq": v_final,
        "last_line_search_alpha": last_alpha,
        "outer_steps": float(last_step),
        "force_norm_initial": f0,
        "equilibrium_fd_eps": fd_eps,
        "converged": converged,
        "converged_practical": converged_practical,
    }


__all__ = [
    "ODESettings",
    "integrate_molecule",
    "solve_equilibrium_radius",
    "backtracking_line_search",
    "MoleculeConfig",
    "FragmentConfig",
    "BondGeometry",
]

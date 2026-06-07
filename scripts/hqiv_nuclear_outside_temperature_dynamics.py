#!/usr/bin/env python3
"""
Outside-curvature environment dynamics for nuclear binding and β± decay.

The structural caustic stack (sphere → barbell torus → tetra closure) is evaluated
at lock-in; **outside curvature in the lab** is set by effective temperature *and*
local gravity through `G_eff`:

  • **Temperature** — `T(ξ) = T_Pl/ξ` weakens or deepens outside response.
  • **Gravity** — weak-field potential stack ``ε = Σ GM/(Rc²)`` (Earth + Sun @ 1 AU +
    Galactic circular support ``v_c²/c²``) adds outside support through
    `G_eff(1+ε)/G_eff(1) = (1+ε)^α` (α = 3/5, `HQVMetric.G_eff`).

β decay channels (before any full `nucleon(p,n)` function):

  • **β−** — free / sub-lock-in branch: outside weakens binding; overlap energy
    mirrors `freeNeutronOverlapEnergy` in `NeutronBindingStabilityScaffold`.
  • **β+** — proton-rich mirror slot (structural; weak width separate).

Lean: `Hqiv.Physics.NuclearOutsideTemperatureDynamics`.
"""

from __future__ import annotations

import math
from dataclasses import asdict, dataclass
from typing import Literal

import hqiv_bbn_abundances as bbn
import hqiv_excited_states as hes
import hqiv_lean_physics_primitives as lean
import hqiv_nuclear_caustic_binding as ncb
import hqiv_nuclear_inside_outside_binding as niob

REFERENCE_M = hes.REFERENCE_M
XI_LOCKIN = lean.XI_LOCKIN
GAMMA = lean.GAMMA
T_PL_MEV = bbn.T_PL_MEV

# Lean `nucleonIsospinGap_MeV = 1` (hypercharge bookkeeping unit).
NUCLEON_ISOSPIN_GAP_MEV = 1.0

# Lean `outerHorizonNeutrinoSuppression = γ / S(referenceM+2) = 1/140`.
OUTER_NEUTRINO_SUPPRESSION = 1.0 / 140.0
STRONG_CHANNEL_FRACTION = lean.STRONG_CHANNEL_FRACTION

# Earth surface defaults (SI; same as `hqiv_orbital_flyby_omaxwell.py`).
GM_EARTH_M3_S2 = 3.986004418e14
R_EARTH_M = 6.378137e6
GM_SUN_M3_S2 = 1.32712440018e20
AU_M = 1.495978707e11
GALACTIC_VC_M_S = 233_000.0  # circular speed at the Sun (local Milky-Way disk)
C_LIGHT_M_S = 299792458.0

GravityBindingTier = Literal["none", "earth", "solar_system", "full"]


@dataclass(frozen=True)
class GravitationalBindingStack:
    """Additive weak-field outside-potential ledger (dimensionless ε = Φ/c²)."""

    earth: float
    sun: float
    galaxy: float
    molecular: float = 0.0

    @property
    def total(self) -> float:
        return self.earth + self.sun + self.galaxy + self.molecular

    @property
    def total_gravity(self) -> float:
        return self.earth + self.sun + self.galaxy

    def as_dict(self) -> dict[str, float]:
        row = asdict(self)
        row["total"] = self.total
        row["total_gravity"] = self.total_gravity
        return row


def gravitational_phi_epsilon(
    gm_m3_s2: float,
    radius_m: float,
    *,
    c_m_s: float = C_LIGHT_M_S,
) -> float:
    """Dimensionless gravitational potential ``ε = GM/(Rc²)``."""
    if gm_m3_s2 <= 0.0 or radius_m <= 0.0 or c_m_s <= 0.0:
        return 0.0
    return gm_m3_s2 / (radius_m * c_m_s * c_m_s)


def earth_surface_phi_epsilon(
    *,
    gm_m3_s2: float = GM_EARTH_M3_S2,
    radius_m: float = R_EARTH_M,
    c_m_s: float = C_LIGHT_M_S,
) -> float:
    """
    Earth surface slot of the binding stack: ``ε_⊕ = GM_⊕/(R_⊕ c²) ≈ 6.96×10⁻¹⁰``.
    """
    return gravitational_phi_epsilon(gm_m3_s2, radius_m, c_m_s=c_m_s)


def solar_phi_epsilon_at_distance(
    distance_m: float = AU_M,
    *,
    gm_m3_s2: float = GM_SUN_M3_S2,
    c_m_s: float = C_LIGHT_M_S,
) -> float:
    """Sun's exterior potential at Earth's orbital radius: ``ε_☉ ≈ 10⁻⁸`` at 1 AU."""
    return gravitational_phi_epsilon(gm_m3_s2, distance_m, c_m_s=c_m_s)


def galactic_circular_phi_epsilon(
    v_c_m_s: float = GALACTIC_VC_M_S,
    *,
    c_m_s: float = C_LIGHT_M_S,
) -> float:
    """
    Local Milky-Way disk circular-support slot: ``ε_gal ≈ v_c²/c² ≈ 6×10⁻⁷``.

    Same comoving disk support used in the flyby galactic Rindler denominator; here we
    book the baseline lapse that co-moves with the Solar System (not the seasonal residual).
    """
    if v_c_m_s <= 0.0 or c_m_s <= 0.0:
        return 0.0
    return (v_c_m_s / c_m_s) ** 2


def local_lab_gravity_binding_stack(
    tier: GravityBindingTier = "full",
) -> GravitationalBindingStack:
    """
    Cumulative outside binding for a lab on Earth's surface in the Solar System.

    Weak-field potentials add: Earth surface + Sun @ 1 AU + Galactic disk support.
    """
    earth = earth_surface_phi_epsilon() if tier in ("earth", "solar_system", "full") else 0.0
    sun = solar_phi_epsilon_at_distance() if tier in ("solar_system", "full") else 0.0
    galaxy = galactic_circular_phi_epsilon() if tier == "full" else 0.0
    return GravitationalBindingStack(earth=earth, sun=sun, galaxy=galaxy)


def local_lab_gravity_phi_epsilon(tier: GravityBindingTier = "full") -> float:
    """Total outside gravitational potential ε for a surface lab (default: full stack)."""
    return local_lab_gravity_binding_stack(tier).total_gravity


def local_outside_binding_stack(
    tier: GravityBindingTier = "full",
    *,
    molecular_host: str | None = None,
    molecular_nucleus_label: str | None = None,
) -> GravitationalBindingStack:
    """Gravity stack plus optional molecular host curvature (``T2``, ``T2O``, …)."""
    gravity = local_lab_gravity_binding_stack(tier)
    molecular = 0.0
    if molecular_host:
        import hqiv_bond_state_network as bsn

        molecular = bsn.molecular_host_phi_epsilon(
            molecular_host,
            nucleus_label=molecular_nucleus_label,
        )
    return GravitationalBindingStack(
        earth=gravity.earth,
        sun=gravity.sun,
        galaxy=gravity.galaxy,
        molecular=molecular,
    )


def local_outside_phi_epsilon(
    tier: GravityBindingTier = "full",
    *,
    molecular_host: str | None = None,
    molecular_nucleus_label: str | None = None,
) -> float:
    return local_outside_binding_stack(
        tier,
        molecular_host=molecular_host,
        molecular_nucleus_label=molecular_nucleus_label,
    ).total


def xi_from_T_MeV(T_MeV: float) -> float:
    return lean.xi_from_T_MeV(T_MeV)


K_B_MEV_PER_K = 8.617333262e-11


def xi_from_temperature_K(T_K: float) -> float:
    if T_K <= 0.0:
        raise ValueError("temperature must be positive")
    return T_PL_MEV / (K_B_MEV_PER_K * T_K)


def T_MeV_from_xi(xi: float) -> float:
    return T_PL_MEV / xi


def effective_inside_temperature(xi: float) -> float:
    """Background T / inner trapping (bulk_v2 / T12 contact surfaces)."""
    t_bg = 1.0 / max(xi, 1e-30)
    trap = lean.trapping_selection_heavy(lean.ALPHA_HEAVY, lean.omega_k_xi(xi))
    return t_bg / max(trap, 1e-30)


def effective_outside_temperature(xi: float) -> float:
    """Background T × outer T13 suppression — outside curvature channel."""
    t_bg = 1.0 / max(xi, 1e-30)
    return t_bg * lean.t13_outer_suppression_at_xi(xi)


def outside_inside_temperature_ratio(xi: float) -> float:
    t_out = effective_outside_temperature(xi)
    t_in = effective_inside_temperature(xi)
    if t_in <= 0.0:
        return 1.0
    return t_out / t_in


def outside_curvature_release_factor(xi: float) -> float:
    """Lean `bbnBindingReleaseFactor` at T(ξ) = T_Pl/ξ."""
    if abs(xi - XI_LOCKIN) < 1e-12:
        return 1.0
    return lean.bbn_binding_release_factor(T_MeV_from_xi(xi))


def omega_readout_at_xi(xi: float) -> float:
    return lean.omega_k_xi(xi)


def free_neutron_curvature_deficit(omega_readout: float) -> float:
    """Lean `freeNeutronCurvatureDeficit`."""
    return max(0.0, 1.0 - omega_readout)


def outside_curvature_binding_modulator(xi: float, *, bonded: bool) -> float:
    """
    Weakens or deepens nucleon own binding + outside caustic stack.

    • **Bonded** (closed ledger, nuclear well): outside can *deepen* when inside/outside
      temperature balance favors closure (`log T_in/T_out > 0`).
    • **Free** (β− branch): outside *weakens* when Ω readout drops below lock-in.
    """
    if abs(xi - XI_LOCKIN) < 1e-12:
        return 1.0

    release = outside_curvature_release_factor(xi)
    omega = omega_readout_at_xi(xi)
    omega_lock = omega_readout_at_xi(XI_LOCKIN)
    omega_norm = omega / max(omega_lock, 1e-30)

    t_in = effective_inside_temperature(xi)
    t_out = effective_outside_temperature(xi)
    balance = math.log(max(t_in, 1e-30) / max(t_out, 1e-30))

    if bonded:
        deepen = 1.0 + GAMMA * max(0.0, balance) * omega_norm
        return release * deepen

    deficit = max(0.0, 1.0 - omega_norm)
    # Free branch: no nuclear well → outside temperature releases cooperativity;
    # sub-lock-in Ω adds further weakening (β− slot).
    hot_release_penalty = GAMMA * (1.0 - release)
    sub_lock_penalty = GAMMA * deficit
    weaken = 1.0 - hot_release_penalty - sub_lock_penalty
    return release * max(weaken, 0.0)


def outside_gravity_geff_modulator(phi_epsilon: float) -> float:
    """
    Outside support from local gravity via `G_eff(1+ε)/G_eff(1)`.

    Uses the lattice α = 3/5 and monogamy γ = 2/5 to fold the tiny lapse bump into
    the outside-curvature channel (not a separate fit parameter).
    """
    if phi_epsilon <= 0.0:
        return 1.0
    geff_ratio = (1.0 + phi_epsilon) ** lean.ALPHA
    return 1.0 + GAMMA * (geff_ratio - 1.0)


def outside_environment_modulator(
    xi: float,
    *,
    bonded: bool,
    phi_gravity_epsilon: float = 0.0,
) -> float:
    """Temperature + gravity outside support for the free or bonded branch."""
    temp = outside_curvature_binding_modulator(xi, bonded=bonded)
    gravity = outside_gravity_geff_modulator(phi_gravity_epsilon)
    return temp * gravity


def local_curvature_neutrino_opacity_barn(
    xi: float,
    phi_gravity_epsilon: float = 0.0,
) -> float:
    """
    Effective relic-neutrino opacity (barn) from local ``B_curv(ξ)`` × outer T13 dressing.

    OOM witness at lock-in: ``(1/s)⁴ ≈ 3.8×10⁸`` barn — the same curvature budget that
    feeds bound-state ``κ(ξ)``, contact networks, and melt readouts.
    """
    s = OUTER_NEUTRINO_SUPPRESSION
    return (
        (1.0 / s) ** 4
        * lean.curvature_budget_at_xi(xi)
        * outside_gravity_geff_modulator(phi_gravity_epsilon)
    )


def local_curvature_weak_width_catalysis(
    xi: float,
    phi_gravity_epsilon: float = 0.0,
) -> float:
    """
    Additive catalysis fraction booked onto weak β width (central estimate).

    Participation uses only lattice rationals (γ, strong channel) and the outer
    suppression unwind on four weak legs; environment imprint scales with the same
    ``B_curv × G_eff`` stack as bound-state calculations.
    """
    s = OUTER_NEUTRINO_SUPPRESSION
    b_curv = lean.curvature_budget_at_xi(xi)
    geff = outside_gravity_geff_modulator(phi_gravity_epsilon)
    env_imprint = max(b_curv * geff - 1.0, 0.0)
    lockin = GAMMA**2 * (1.0 - s) * (1.0 - GAMMA / 5.0) * STRONG_CHANNEL_FRACTION
    return lockin * (1.0 + env_imprint / max(lockin, 1e-30))


def local_curvature_weak_width_factor(
    xi: float,
    phi_gravity_epsilon: float = 0.0,
) -> float:
    """Multiplicative weak-width factor from the dressed local neutrino bath."""
    return 1.0 + local_curvature_weak_width_catalysis(xi, phi_gravity_epsilon)


def local_curvature_weak_width_factor_band(
    xi: float,
    phi_gravity_epsilon: float = 0.0,
    *,
    A: int = 1,
    bonded: bool = False,
) -> tuple[float, float, float]:
    """
    ``(low, central, high)`` width factors — monogamy envelope ``±γ/5`` on catalysis.

    Bonded valence decays (``A > 1``): interior well shields the relic-bath catalysis
    (same exterior/interior split as valley width geometry).
    """
    if bonded and A > 1:
        return (1.0, 1.0, 1.0)
    low, central, high = _local_curvature_weak_width_factor_band_raw(xi, phi_gravity_epsilon)
    return low, central, high


def _local_curvature_weak_width_factor_band_raw(
    xi: float,
    phi_gravity_epsilon: float = 0.0,
) -> tuple[float, float, float]:
    central = local_curvature_weak_width_factor(xi, phi_gravity_epsilon)
    catalysis = central - 1.0
    envelope = 1.0 + GAMMA / 5.0
    return (
        1.0 + catalysis / envelope,
        central,
        1.0 + catalysis * envelope,
    )


def local_curvature_neutrino_width_witness(
    *,
    bbn_temperatures_mev: tuple[float, ...] = (10.0, 1.0, 0.1, 0.01),
    xi_lock: float = XI_LOCKIN,
    lab_temperature_K: float = 300.0,
    gravity_tier: GravityBindingTier = "full",
) -> dict[str, object]:
    """
    Export local ν-opacity and weak-width catalysis for BBN integrator + paper witnesses.

    Uses the same ``B_curv(ξ)`` stack as bound-state feedback; free-branch catalysis
    only (bonded clusters shield the interior well).
    """
    lab_xi = xi_from_temperature_K(lab_temperature_K)
    lab_gravity = local_lab_gravity_phi_epsilon(gravity_tier)
    lab_low, lab_central, lab_high = local_curvature_weak_width_factor_band(
        lab_xi,
        lab_gravity,
        A=1,
        bonded=False,
    )
    epoch_rows: list[dict[str, float]] = []
    for t_mev in bbn_temperatures_mev:
        xi = xi_from_T_MeV(t_mev)
        epoch_rows.append(
            {
                "T_MeV": t_mev,
                "xi": xi,
                "B_curv": lean.curvature_budget_at_xi(xi, xi_lock),
                "neutrino_opacity_barn": local_curvature_neutrino_opacity_barn(xi, 0.0),
                "free_branch_width_factor": local_curvature_weak_width_factor(xi, 0.0),
                "free_branch_width_factor_low": local_curvature_weak_width_factor_band(
                    xi, 0.0, A=1, bonded=False
                )[0],
                "free_branch_width_factor_high": local_curvature_weak_width_factor_band(
                    xi, 0.0, A=1, bonded=False
                )[2],
                "outside_release_factor": outside_curvature_release_factor(xi),
                "free_outside_modulator": outside_curvature_binding_modulator(xi, bonded=False),
            }
        )
    return {
        "lean_module": "Hqiv.Physics.NuclearOutsideTemperatureDynamics",
        "outer_neutrino_suppression": OUTER_NEUTRINO_SUPPRESSION,
        "opacity_oom_at_lockin_barn": (1.0 / OUTER_NEUTRINO_SUPPRESSION) ** 4,
        "lab_readout": {
            "lab_temperature_K": lab_temperature_K,
            "lab_xi": lab_xi,
            "lab_gravity_phi_epsilon": lab_gravity,
            "neutrino_opacity_barn": local_curvature_neutrino_opacity_barn(lab_xi, lab_gravity),
            "width_factor": lab_central,
            "width_factor_band": {"low": lab_low, "central": lab_central, "high": lab_high},
        },
        "bbn_epochs": epoch_rows,
        "bonded_cluster_policy": "A>1 interior well shields relic-bath catalysis (valley width ledger)",
    }


def lab_outside_support_lifetime_factor(
    T_K: float,
    *,
    phi_gravity_epsilon: float = 0.0,
    reference_K: float = 2.725,
    reference_phi_gravity_epsilon: float = 0.0,
) -> float:
    """
    Relative outside-support correction for a lab environment vs a reference.

    Default reference is CMB-like 2.725 K with zero gravitational potential (deep space).
    Earth-surface bottle/beam experiments supply the full binding stack by default
    (Earth + Sun @ 1 AU + Galactic ``v_c²/c²``).
    """
    lab_mod = outside_environment_modulator(
        xi_from_temperature_K(T_K),
        bonded=False,
        phi_gravity_epsilon=phi_gravity_epsilon,
    )
    ref_mod = outside_environment_modulator(
        xi_from_temperature_K(reference_K),
        bonded=False,
        phi_gravity_epsilon=reference_phi_gravity_epsilon,
    )
    if lab_mod <= 0.0:
        return math.inf
    return ref_mod / lab_mod


def nucleon_own_binding_mev(
    m: int,
    xi: float,
    *,
    bonded: bool,
    c: float = 1.0,
) -> float:
    """Per-nucleon composite trace binding modulated by outside curvature at ξ."""
    trace = niob.nucleon_trace_binding_mev(m, c)
    return trace * outside_curvature_binding_modulator(xi, bonded=bonded)


def caustic_outside_binding_at_xi(
    m: int,
    A: int,
    *,
    m_cluster: int,
    xi: float,
    bonded: bool,
    c: float = 1.0,
) -> tuple[float, tuple[ncb.CausticLayer, ...]]:
    """Outside caustic stack at horizon ξ (structural layers × temperature modulator)."""
    base, layers = ncb.cumulative_caustic_binding_mev(m, A, m_cluster=m_cluster, c=c)
    mod = outside_curvature_binding_modulator(xi, bonded=bonded)
    scaled = tuple(
        ncb.CausticLayer(layer.name, layer.depth_mev * mod) for layer in layers
    )
    return base * mod, scaled


def nuclear_cluster_binding_at_xi(
    m: int,
    A: int,
    *,
    m_cluster: int | None = None,
    xi: float = XI_LOCKIN,
    bonded: bool = True,
    c: float = 1.0,
) -> tuple[float, float, float, float, tuple[ncb.CausticLayer, ...]]:
    """
    Full cluster binding at ξ.

    Returns `(total, inside, outside, nucleon_own_modulated, caustic_layers)`.
    Inside trapped ratio stays structural; outside + own trace get temperature dynamics.
    """
    if m_cluster is None:
        m_cluster = m if A <= 1 else m
    inside = niob.inside_nuclear_binding_mev(m, A, m_cluster=m_cluster, c=c)
    outside, layers = caustic_outside_binding_at_xi(
        m, A, m_cluster=m_cluster, xi=xi, bonded=bonded, c=c
    )
    own = nucleon_own_binding_mev(m, xi, bonded=bonded, c=c)
    return inside + outside, inside, outside, own, layers


BetaChannel = Literal["beta_minus", "beta_plus"]


@dataclass(frozen=True)
class BetaDecayReadout:
    channel: BetaChannel
    xi: float
    omega_readout: float
    outside_modulator: float
    overlap_mev: float
    mass_gap_mev: float
    stable_bonded: bool
    notes: str


def beta_decay_readout(
    channel: BetaChannel,
    *,
    xi: float = XI_LOCKIN,
    well_depth_mev: float = 0.0,
    bonded: bool = True,
) -> BetaDecayReadout:
    """
    β± channel readout before a full `nucleon(p,n)` function.

    β− mirrors `freeNeutronOverlapEnergy`; β+ is the proton-rich structural mirror.
    Weak width (`G_F`, 880 s) stays a separate slot (`NeutronBindingStabilityScaffold`).
    """
    omega = omega_readout_at_xi(xi)
    omega_lock = omega_readout_at_xi(XI_LOCKIN)
    mod = outside_curvature_binding_modulator(xi, bonded=bonded)
    mass_gap = float(hes.e_bind_from_nucleon_trace_mev(REFERENCE_M))  # placeholder scale
    # Use witness-derived ΔM when available
    try:
        import json
        from pathlib import Path

        wpath = Path(__file__).resolve().parents[1] / "data" / "hqiv_witnesses.json"
        if wpath.is_file():
            mass_gap = float(json.loads(wpath.read_text()).get("derivedDeltaM_MeV", 1.293))
    except Exception:
        mass_gap = 1.293

    if channel == "beta_minus":
        overlap = NUCLEON_ISOSPIN_GAP_MEV + free_neutron_curvature_deficit(
            min(omega, omega_lock)
        )
        stable = bonded and (well_depth_mev + niob.nucleon_trace_binding_mev(REFERENCE_M) * mod > 0)
        notes = "free branch: isospin gap + Ω deficit; outside temperature weakens own binding"
    else:
        overlap = NUCLEON_ISOSPIN_GAP_MEV * mod
        stable = bonded and well_depth_mev > overlap
        notes = "proton-rich mirror slot; weak tipping not identified with overlap energy"

    return BetaDecayReadout(
        channel=channel,
        xi=xi,
        omega_readout=omega,
        outside_modulator=mod,
        overlap_mev=overlap,
        mass_gap_mev=mass_gap,
        stable_bonded=stable,
        notes=notes,
    )


def cluster_mass_mev_nuclear(
    m: int,
    A: int,
    m_nucleon: float,
    xi: float,
    *,
    c: float = 1.0,
) -> float:
    """Cluster mass after inside + outside nuclear binding at horizon ξ."""
    import hqiv_nuclear_curvature_binding as ncur

    m_cluster = ncur.nucleus_curvature_shell(A)
    total, _, _, _, _ = nuclear_cluster_binding_at_xi(
        m, A, m_cluster=m_cluster, xi=xi, bonded=True, c=c
    )
    return float(A) * m_nucleon - total


def binding_q_hybrid_at_xi(
    m_shell: int,
    m_nucleon: float,
    xi: float,
    *,
    xi_lock: float = XI_LOCKIN,
    c: float = 1.0,
) -> tuple[float, float, float]:
    """
    Nuclear inside/outside shape at ξ with lock-in amplitudes anchored to the
    legacy BBN valley witness at ``ξ_lock`` (proton anchor unchanged).
    """
    Q_n = binding_q_nuclear_at_xi(m_shell, m_nucleon, xi, c=c)
    Q_nl = binding_q_nuclear_at_xi(m_shell, m_nucleon, xi_lock, c=c)
    Q_ll = bbn.lockin_binding_q(m_nucleon, m_shell, c)[:3]
    out: list[float] = []
    for qn, qnl, qll in zip(Q_n, Q_nl, Q_ll):
        if abs(qnl) < 1e-30:
            out.append(qll)
        else:
            out.append(qll * (qn / qnl))
    return out[0], out[1], out[2]


def binding_q_nuclear_at_xi(
    m_shell: int,
    m_nucleon: float,
    xi: float,
    *,
    c: float = 1.0,
) -> tuple[float, float, float]:
    """
    Light-nucleus binding Q (MeV) from composite trace + inside/outside caustics.

    Same ledger as ``hqiv_bbn_abundances.lockin_binding_q`` at ξ = ξ_lock, with
    outside-curvature temperature dynamics at other horizons.
    """
    import hqiv_nuclear_curvature_binding as ncur

    Q_D = 2.0 * m_nucleon - cluster_mass_mev_nuclear(m_shell, 2, m_nucleon, xi, c=c)
    Q_4 = 4.0 * m_nucleon - cluster_mass_mev_nuclear(m_shell, 4, m_nucleon, xi, c=c)
    m_c3 = ncur.nucleus_curvature_shell(3)
    bind3, _, _, _, _ = nuclear_cluster_binding_at_xi(
        m_shell, 3, m_cluster=m_c3, xi=xi, bonded=True, c=c
    )
    return Q_D, Q_4, bind3


def shell_nuclear_binding_row(
    m: int,
    xi: float,
    *,
    xi_lock: float = XI_LOCKIN,
    m_shell_lock: int = REFERENCE_M,
    c: float = 1.0,
) -> dict[str, float | int]:
    """Per-shell nuclear binding witness for the bulk integrator."""
    import hqiv_nuclear_curvature_binding as ncur

    m_c4 = ncur.nucleus_curvature_shell(4)
    total, inside, outside, own, _ = nuclear_cluster_binding_at_xi(
        m, 4, m_cluster=m_c4, xi=xi, bonded=True, c=c
    )
    lock_total, lock_in, lock_out, _, _ = nuclear_cluster_binding_at_xi(
        m_shell_lock, 4, m_cluster=m_c4, xi=xi_lock, bonded=True, c=c
    )
    trace = niob.nucleon_trace_binding_mev(m, c)
    trace_lock = niob.nucleon_trace_binding_mev(m_shell_lock, c)
    return {
        "m": m,
        "xi": xi,
        "cluster_A": 4,
        "cluster_binding_mev": total,
        "inside_binding_mev": inside,
        "outside_binding_mev": outside,
        "nucleon_own_modulated_mev": own,
        "trace_binding_mev": trace,
        "outside_release_factor": outside_curvature_release_factor(xi),
        "outside_modulator_bonded": outside_curvature_binding_modulator(xi, bonded=True),
        "cluster_ratio_to_lockin": total / max(lock_total, 1e-30),
        "trace_ratio_to_lockin": trace / max(trace_lock, 1e-30),
        "lockin_cluster_binding_mev": lock_total,
    }


def nuclear_binding_conditions_witness(
    *,
    m_start: int = 1,
    m_lock: int = REFERENCE_M,
    xi_lock: float = XI_LOCKIN,
    bbn_T_MeV: float = 0.1,
) -> dict[str, object]:
    """
    Witness block for ``papers/nucleon_binding`` consumed by the dynamic bulk integrator.
    """
    xi_bbn = xi_from_T_MeV(bbn_T_MeV)
    m_p = niob.PROTON_MEV  # lock-in anchor comparison
    Q_lock = binding_q_nuclear_at_xi(m_lock, m_p, xi_lock)
    Q_bbn = binding_q_nuclear_at_xi(m_lock, m_p, xi_bbn)
    Q_legacy = bbn.lockin_binding_q(m_p, m_lock)
    return {
        "paper": "papers/nucleon_binding/hqiv_nucleon_binding_from_composite_trace.tex",
        "lean_modules": [
            "Hqiv.Physics.NuclearCurvatureBinding",
            "Hqiv.Physics.NuclearCausticBinding",
            "Hqiv.Physics.NuclearOutsideTemperatureDynamics",
            "Hqiv.Physics.DynamicBBNBaryogenesis",
        ],
        "shell_rows": [
            shell_nuclear_binding_row(m, float(m + 1), xi_lock=xi_lock, m_shell_lock=m_lock)
            for m in range(m_start, m_lock + 1)
        ],
        "light_nuclei_lockin_vs_bbn": {
            "T_MeV_bbn": bbn_T_MeV,
            "xi_bbn": xi_bbn,
            "Q_D_lockin_MeV": Q_lock[0],
            "Q_4He_lockin_MeV": Q_lock[1],
            "Q_3He_lockin_MeV": Q_lock[2],
            "Q_D_bbn_MeV": Q_bbn[0],
            "Q_4He_bbn_MeV": Q_bbn[1],
            "Q_3He_bbn_MeV": Q_bbn[2],
            "Q_D_legacy_lockin_MeV": Q_legacy[0],
            "Q_4He_legacy_lockin_MeV": Q_legacy[1],
            "Q_3He_legacy_lockin_MeV": Q_legacy[2],
        },
        "bbn_cluster_reports": {
            f"A={A}": lockin_binding_report(A, m=m_lock) for A in (2, 3, 4)
        },
        "outside_at_bbn": {
            "free_modulator": outside_curvature_binding_modulator(xi_bbn, bonded=False),
            "bonded_modulator": outside_curvature_binding_modulator(xi_bbn, bonded=True),
            "release_factor": outside_curvature_release_factor(xi_bbn),
        },
        "local_curvature_neutrino_width": local_curvature_neutrino_width_witness(
            xi_lock=xi_lock
        ),
    }


def lockin_binding_report(A: int, m: int = REFERENCE_M) -> dict[str, float]:
    """Lock-in structural binding vs BBN-weakened outside at T ≈ 0.1 MeV."""
    import hqiv_nuclear_curvature_binding as ncur

    m_c = ncur.nucleus_curvature_shell(A)
    lock_total, lock_in, lock_out, _, _ = nuclear_cluster_binding_at_xi(
        m, A, m_cluster=m_c, xi=XI_LOCKIN, bonded=True
    )
    bbn_xi = xi_from_T_MeV(0.1)
    bbn_total, _, bbn_out, _, _ = nuclear_cluster_binding_at_xi(
        m, A, m_cluster=m_c, xi=bbn_xi, bonded=True
    )
    free_mod = outside_curvature_binding_modulator(bbn_xi, bonded=False)
    return {
        "A": float(A),
        "lockin_total_mev": lock_total,
        "lockin_outside_mev": lock_out,
        "bbn_xi": bbn_xi,
        "bbn_total_mev": bbn_total,
        "bbn_outside_mev": bbn_out,
        "free_outside_modulator_at_bbn": free_mod,
    }

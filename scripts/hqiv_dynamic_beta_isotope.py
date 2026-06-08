"""
Dynamic isotope and β-channel readouts.

Python mirror of `Hqiv.Physics.DynamicBetaIsotope`.

Ledgers remain separate:

  • p/n mass gap: from the shared `nucleon(p,n)` function.
  • β curvature overlap: from outside-curvature / Ω readout.
  • weak width: a named slot, not derived from the curvature overlap.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Literal

import hqiv_dynamic_nucleon_pn as pn
import hqiv_nuclear_outside_temperature_dynamics as notd

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_JSON = ROOT / "data" / "dynamic_beta_isotope_chart.json"

BetaChannel = Literal["beta_minus", "beta_plus"]

# Light-isotope ladder daughters with HQIV mass-budget readouts.
BETA_MINUS_DAUGHTERS: dict[tuple[int, int], tuple[int, int]] = {
    (1, 0): (1, 1),  # n → p
    (3, 1): (3, 2),  # T → He3
}
BETA_PLUS_DAUGHTERS: dict[tuple[int, int], tuple[int, int]] = {
    (1, 1): (1, 0),  # p → n (kinematically closed at lock-in)
}

# ChargedLeptonResonance / Forces lepton-scale witness (MeV).
ELECTRON_MASS_MEV = 0.5109989461
V_UD = 0.97373
M_W_GEV = 80.379
SIN2_THETA_W = 0.23122
ALPHA_EM_WEAK = 1.0 / 127.9
HBAR_GEV_S = 6.582119569e-25


@dataclass(frozen=True)
class DynamicIsotopeReadout:
    name: str
    A: int
    Z: int
    valley_count: int
    mass_budget_mev: float
    proton_mass_mev: float
    neutron_mass_mev: float
    delta_m_mev: float
    beta_minus_mass_gap_mev: float
    beta_minus_overlap_mev: float
    beta_minus_residual_mev: float
    beta_plus_mass_gap_mev: float
    beta_plus_overlap_mev: float
    beta_plus_residual_mev: float
    beta_minus_endpoint_q_mev: float | None
    beta_plus_endpoint_q_mev: float | None
    valley_count_bound: int
    caustic_layer_count: int
    weak_width_policy: str


VALLEY_COUNTS = {
    "p": 0,
    "n": 0,
    "D": 2,
    "He3": 4,
    "He4": 6,
}


def neutron_count(A: int, Z: int) -> int:
    return max(A - Z, 0)


def isotope_mass_budget(A: int, Z: int, pair: pn.PNPairReadout) -> float:
    return float(Z) * pair.proton.mass_mev + float(neutron_count(A, Z)) * pair.neutron.mass_mev


def beta_minus_endpoint_q_nucleon_gap(
    pair: pn.PNPairReadout,
    *,
    m_e_mev: float | None = None,
) -> float:
    """HQIV kinematic endpoint: ΔM − m_e from derived p/n readouts (T→He3 shares free‑n Q)."""
    m_e = model_electron_mass_mev() if m_e_mev is None else m_e_mev
    return pair.neutron.mass_mev - pair.proton.mass_mev - m_e


def beta_minus_endpoint_q_atomic(
    parent_mass_mev: float,
    daughter_mass_mev: float,
    *,
    m_e_mev: float | None = None,
) -> float:
    """Atomic/nuclear mass-table endpoint Q = M_parent − M_daughter − m_e (comparison layer)."""
    m_e = model_electron_mass_mev() if m_e_mev is None else m_e_mev
    return parent_mass_mev - daughter_mass_mev - m_e


def weak_half_life_geometric_ledger(
    A: int,
    Z: int,
    env: pn.NucleonEnvironment,
    base: DynamicIsotopeReadout,
    *,
    cluster_mass_imprint: float = 1.0,
    proton_mass_mev_for_well: float | None = None,
    neutron_mass_mev_for_well: float | None = None,
    local_curvature_width_factor: float = 1.0,
    lab_temperature_factor: float = 1.0,
    neutrino_mass_mev: float = 0.0,
    weak_bridge_energy_mev: float = 0.0,
) -> float:
    """
    Half-life from HQIV geometric width ledger with optional curvature imprints.

    * ``cluster_mass_imprint`` scales the caustic cluster depth booked into the
      geometric-mean interior width well (mass-ledger curvature imprint).
    * ``proton_mass_mev_for_well`` / ``neutron_mass_mev_for_well`` default to the
      derived bonded readout; pass PDG nucleon masses for the control row.
    """
    n_count = neutron_count(A, Z)
    cluster_total = (
        pn.cluster_caustic_total_mev(A, shell=env.shell, xi=env.xi) * cluster_mass_imprint
        if env.bonded
        else 0.0
    )
    p_well = base.proton.mass_mev if proton_mass_mev_for_well is None else proton_mass_mev_for_well
    n_well = base.neutron.mass_mev if neutron_mass_mev_for_well is None else neutron_mass_mev_for_well
    width_well = (
        beta_width_well_depth_mev(
            A,
            Z,
            cluster_total_mev=cluster_total,
            proton_mass_mev=p_well,
            neutron_mass_mev=n_well,
        )
        if env.bonded and n_count > 0
        else 0.0
    )
    endpoint_q = base.beta_minus_endpoint_q_mev
    residual = base.beta_minus_residual_mev
    if endpoint_q is None or endpoint_q <= 0.0 or residual <= 0.0:
        return math.inf
    return weak_beta_half_life_seconds(
        endpoint_q,
        residual,
        A=A,
        width_well_depth_mev=width_well,
        bonded=env.bonded,
        neutrino_mass_mev=neutrino_mass_mev,
        weak_bridge_energy_mev=weak_bridge_energy_mev,
        lab_temperature_factor=lab_temperature_factor,
        local_curvature_width_factor=local_curvature_width_factor,
    )


def model_electron_mass_mev() -> float:
    """Lepton-scale witness used in `betaMinusEndpointQAtXi` (ChargedLeptonResonance slot)."""
    return ELECTRON_MASS_MEV


def g_f_from_forces_gev2() -> float:
    """Mirror of `Forces.G_F_from_beta` with M_W in GeV."""
    return math.pi * ALPHA_EM_WEAK / (math.sqrt(2) * M_W_GEV**2 * SIN2_THETA_W)


def weak_matrix_element_squared(residual_mev: float, m_e_mev: float = ELECTRON_MASS_MEV) -> float:
    """Overlap residual carried to fourth power by m_e (DynamicBetaIsotope slot)."""
    if residual_mev <= 0.0 or m_e_mev <= 0.0:
        return 0.0
    ratio = residual_mev / m_e_mev
    return (V_UD**2) * (ratio**4)


def beta_minus_endpoint_q(
    A: int,
    Z: int,
    env: pn.NucleonEnvironment,
    *,
    m_e_mev: float | None = None,
) -> float | None:
    """
    Kinematic β− endpoint Q from HQIV isotope mass budgets.

    Returns ``None`` when the daughter is not on the light ladder map.
    """
    key = (A, Z)
    if key not in BETA_MINUS_DAUGHTERS:
        return None
    _, z_d = BETA_MINUS_DAUGHTERS[key]
    m_e = model_electron_mass_mev() if m_e_mev is None else m_e_mev
    pair = pn.pn_pair_readout(env)
    parent = isotope_mass_budget(A, Z, pair)
    daughter = isotope_mass_budget(A, z_d, pair)
    return parent - daughter - m_e


def beta_plus_endpoint_q(
    A: int,
    Z: int,
    env: pn.NucleonEnvironment,
    *,
    m_e_mev: float | None = None,
) -> float | None:
    key = (A, Z)
    if key not in BETA_PLUS_DAUGHTERS:
        return None
    _, z_d = BETA_PLUS_DAUGHTERS[key]
    m_e = model_electron_mass_mev() if m_e_mev is None else m_e_mev
    pair = pn.pn_pair_readout(env)
    parent = isotope_mass_budget(A, Z, pair)
    daughter = isotope_mass_budget(A, z_d, pair)
    return parent - daughter - m_e


def beta_valley_count_bound(A: int) -> int:
    """Lean `betaValleyCountBound`: `2 · (A − 1)` for bonded clusters."""
    if A <= 1:
        return 0
    return 2 * (A - 1)


def beta_caustic_layer_count(A: int) -> int:
    """Lean `betaCausticLayerCount` from the hierarchical caustic stack."""
    if A <= 1:
        return 0
    deepen = 0 if A <= 2 else A - 2
    tetra = 1 if A >= 4 else 0
    return 2 + deepen + tetra


def beta_width_well_depth_mev(
    A: int,
    Z: int,
    *,
    cluster_total_mev: float,
    proton_mass_mev: float,
    neutron_mass_mev: float,
) -> float:
    """
    Internal well depth on the **decaying neutron** for weak β− width.

    Exterior caustic is identical for the cluster.  Mass readouts keep the
    symmetric ``cluster_total / A`` well; width uses the valence interior:

    * partner trap scale ``cluster_total / (A − 1)``
    * geometric blend with the symmetric mass well (cue-ball exterior,
      asymmetric interior — not the full ``A − 1`` partner well alone)
    * lighter proton partners deepen less (``m_p / m_n``)
    """
    if A <= 1 or cluster_total_mev <= 0.0:
        return 0.0
    partners = max(A - 1, 1)
    mass_well = cluster_total_mev / A
    partner_well = cluster_total_mev / partners
    n_valence = max(A - Z, 0)
    if n_valence <= 0 or neutron_mass_mev <= 0.0:
        return math.sqrt(mass_well * partner_well)
    proton_partners = min(Z, partners)
    neutron_partners = max(n_valence - 1, 0)
    contact_weight = (
        proton_partners * (proton_mass_mev / neutron_mass_mev) + neutron_partners
    ) / partners
    interior_partner = partner_well * contact_weight
    # Blend toward symmetric mass well; full geometric mean overshoots T by ~50%.
    blend = 1.0 / (2.0 * partners)
    ratio = interior_partner / max(mass_well, 1.0e-30)
    return mass_well * max(ratio, 1.0e-30) ** blend


def beta_geometry_width_factor(
    A: int,
    *,
    residual_mev: float,
    well_depth_mev: float,
    bonded: bool,
) -> float:
    """
    Valley + caustic-well trapping for weak β width.

    Bonded clusters: `(residual / well)^(valley + 1)` with valley = 2·(A−1).
    Free nucleons carry unit factor.
    """
    if A <= 1 or not bonded:
        return 1.0
    valley = beta_valley_count_bound(A)
    well = max(well_depth_mev, residual_mev, 1.0e-30)
    ratio = max(residual_mev, 0.0) / well
    return max(ratio ** float(valley + 1), 1.0e-30)


def weak_beta_width_per_s(
    endpoint_q_mev: float,
    residual_mev: float,
    *,
    A: int = 1,
    well_depth_mev: float = 0.0,
    width_well_depth_mev: float | None = None,
    bonded: bool = False,
    m_e_mev: float | None = None,
    local_curvature_width_factor: float = 1.0,
) -> float:
    """
    Weak width from `beta_decay_rate` + overlap residual |ℳ|² slot.

    Uses G_F_from_beta and generic valley/caustic geometry for bonded clusters.
    ``width_well_depth_mev`` (valence partner well) overrides ``well_depth_mev``
    for geometry when supplied.
    """
    if endpoint_q_mev <= 0.0 or residual_mev <= 0.0:
        return 0.0
    m_e = model_electron_mass_mev() if m_e_mev is None else m_e_mev
    m_e_gev = m_e / 1000.0
    m2 = weak_matrix_element_squared(residual_mev, m_e)
    if m2 <= 0.0:
        return 0.0
    geom_well = well_depth_mev if width_well_depth_mev is None else width_well_depth_mev
    geometry = beta_geometry_width_factor(
        A,
        residual_mev=residual_mev,
        well_depth_mev=geom_well,
        bonded=bonded,
    )
    g_f = g_f_from_forces_gev2()
    width = g_f**2 * m_e_gev**5 * m2 * geometry / HBAR_GEV_S
    return width * max(local_curvature_width_factor, 0.0)


def weak_beta_half_life_seconds(
    endpoint_q_mev: float,
    residual_mev: float,
    *,
    A: int = 1,
    well_depth_mev: float = 0.0,
    width_well_depth_mev: float | None = None,
    bonded: bool = False,
    m_e_mev: float | None = None,
    neutrino_mass_mev: float = 0.0,
    weak_bridge_energy_mev: float = 0.0,
    lab_temperature_factor: float = 1.0,
    local_curvature_width_factor: float = 1.0,
) -> float:
    reserved = max(neutrino_mass_mev, 0.0) + max(weak_bridge_energy_mev, 0.0)
    if endpoint_q_mev <= reserved:
        return math.inf
    width = weak_beta_width_per_s(
        endpoint_q_mev,
        residual_mev,
        A=A,
        well_depth_mev=well_depth_mev,
        width_well_depth_mev=width_well_depth_mev,
        bonded=bonded,
        m_e_mev=m_e_mev,
        local_curvature_width_factor=local_curvature_width_factor,
    )
    if width <= 0.0:
        return math.inf
    phase_factor = max((endpoint_q_mev - reserved) / endpoint_q_mev, 0.0)
    return math.log(2.0) / (width * phase_factor) * max(lab_temperature_factor, 0.0)


def beta_channel_readout(
    name: str,
    A: int,
    Z: int,
    env: pn.NucleonEnvironment,
) -> DynamicIsotopeReadout:
    pair = pn.pn_pair_readout(env)
    beta_minus_gap = pair.neutron.mass_mev - pair.proton.mass_mev
    beta_plus_gap = pair.proton.mass_mev - pair.neutron.mass_mev
    beta_minus_overlap = pair.beta_minus_overlap_mev
    beta_plus_overlap = pair.beta_plus_overlap_mev
    return DynamicIsotopeReadout(
        name=name,
        A=A,
        Z=Z,
        valley_count=VALLEY_COUNTS.get(name, max(0, 2 * (A - 1))),
        mass_budget_mev=isotope_mass_budget(A, Z, pair),
        proton_mass_mev=pair.proton.mass_mev,
        neutron_mass_mev=pair.neutron.mass_mev,
        delta_m_mev=pair.delta_m_mev,
        beta_minus_mass_gap_mev=beta_minus_gap,
        beta_minus_overlap_mev=beta_minus_overlap,
        beta_minus_residual_mev=beta_minus_gap - beta_minus_overlap,
        beta_plus_mass_gap_mev=beta_plus_gap,
        beta_plus_overlap_mev=beta_plus_overlap,
        beta_plus_residual_mev=beta_plus_gap - beta_plus_overlap,
        beta_minus_endpoint_q_mev=beta_minus_endpoint_q(A, Z, env),
        beta_plus_endpoint_q_mev=beta_plus_endpoint_q(A, Z, env),
        valley_count_bound=beta_valley_count_bound(A),
        caustic_layer_count=beta_caustic_layer_count(A),
        weak_width_policy="G_F_from_beta + valley/caustic geometry (valence interior well)",
    )


def isotope_environment(name: str, *, xi: float = notd.XI_LOCKIN) -> tuple[int, int, pn.NucleonEnvironment]:
    match name:
        case "p":
            return 1, 1, pn.NucleonEnvironment(shell=notd.REFERENCE_M, xi=xi, bonded=False)
        case "n":
            return 1, 0, pn.NucleonEnvironment(shell=notd.REFERENCE_M, xi=xi, bonded=False)
        case "D":
            return 2, 1, pn.caustic_environment_for_A(2, xi=xi)
        case "He3":
            return 3, 2, pn.caustic_environment_for_A(3, xi=xi)
        case "He4":
            return 4, 2, pn.caustic_environment_for_A(4, xi=xi)
        case _:
            raise ValueError(f"unknown isotope name: {name}")


def build_rows(*, xi: float = notd.XI_LOCKIN) -> list[DynamicIsotopeReadout]:
    rows: list[DynamicIsotopeReadout] = []
    for name in ("p", "n", "D", "He3", "He4"):
        A, Z, env = isotope_environment(name, xi=xi)
        rows.append(beta_channel_readout(name, A, Z, env))
    return rows


def build_payload() -> dict:
    bbn_xi = notd.xi_from_T_MeV(0.1)
    return {
        "source": "scripts/hqiv_dynamic_beta_isotope.py",
        "lean_module": "Hqiv.Physics.DynamicBetaIsotope",
        "lockin_xi": notd.XI_LOCKIN,
        "bbn_xi_at_0_1_MeV": bbn_xi,
        "lockin": [asdict(r) for r in build_rows(xi=notd.XI_LOCKIN)],
        "bbn_0_1_MeV": [asdict(r) for r in build_rows(xi=bbn_xi)],
    }


def print_report(payload: dict) -> None:
    print("HQIV dynamic isotope β readout")
    print("=" * 72)
    for section in ("lockin", "bbn_0_1_MeV"):
        print(section)
        print(f"{'name':<5} {'A':>2} {'Z':>2} {'mass':>12} {'Δpn':>9} {'β- res':>10} {'β+ res':>10}")
        for row in payload[section]:
            print(
                f"{row['name']:<5} {row['A']:>2} {row['Z']:>2} "
                f"{row['mass_budget_mev']:12.3f} {row['delta_m_mev']:9.3f} "
                f"{row['beta_minus_residual_mev']:10.3f} {row['beta_plus_residual_mev']:10.3f}"
            )
        print()


def main() -> None:
    parser = argparse.ArgumentParser(description="HQIV dynamic isotope beta readout")
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()
    payload = build_payload()
    print_report(payload)
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(payload, indent=2) + "\n")
    print(f"Wrote {args.json_out}")


if __name__ == "__main__":
    main()

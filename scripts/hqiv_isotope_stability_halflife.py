#!/usr/bin/env python3
"""
HQIV isotope stability and half-life readout.

Ledgers remain separate:

  • structural overlap residual: curvature / isospin overlap after the nuclear well
  • weak endpoint Q: literal HQIV mass-budget gap minus the lepton mass slot
  • weak width: ``G_F_from_beta`` with overlap residual in the |ℳ|² slot

Without ``--qualify-em-tipping`` the output is a residual / endpoint report only.
"""

from __future__ import annotations

import argparse
import json
import math
import re
from dataclasses import asdict, dataclass
from pathlib import Path

import hqiv_dynamic_beta_isotope as dbi
import hqiv_dynamic_nucleon_pn as pn
import hqiv_nuclear_outside_temperature_dynamics as notd
import hqiv_weak_fano_hopf_bridge as weak_bridge

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_JSON = ROOT / "data" / "isotope_stability_halflife.json"

K_B_MEV_PER_K = 8.617333262e-11
CMB_TEMPERATURE_K = 2.725
WITNESS_JSON = ROOT / "data" / "hqiv_witnesses.json"


@dataclass(frozen=True)
class StabilityReadout:
    label: str
    A: int
    Z: int
    N: int
    xi: float
    well_shield_mev: float
    width_well_shield_mev: float
    cluster_caustic_total_mev: float
    own_binding_mev: float
    beta_minus_raw_residual_mev: float
    beta_plus_raw_residual_mev: float
    beta_minus_endpoint_q_mev: float | None
    beta_plus_endpoint_q_mev: float | None
    neutron_excess_drive_mev: float
    proton_excess_drive_mev: float
    beta_minus_effective_residual_mev: float
    beta_plus_effective_residual_mev: float
    structurally_shielded: bool
    em_tipping_qualified: bool
    active_channel: str
    dynamically_stable: bool
    lab_temperature_K: float
    lab_gravity_phi_epsilon: float
    lab_gravity_binding_stack: dict[str, float]
    lab_molecular_host: str | None
    lab_outside_gravity_factor: float
    lab_outside_curvature_factor: float
    local_curvature_neutrino_opacity_barn: float
    local_curvature_weak_width_factor: float
    local_curvature_weak_width_factor_low: float
    local_curvature_weak_width_factor_high: float
    neutrino_mass_mev: float
    weak_bridge_energy_mev: float
    beta_phase_space_q_mev: float | None
    half_life_seconds: float | None
    half_life_label: str
    notes: str


def parse_isotope_label(label: str) -> tuple[int, int, str]:
    """
    Parse a compact isotope label.

    Default HQIV convention here:
      P120 = proton-count-120 candidate, A = 2Z = 240.
    """
    s = label.strip()
    m = re.fullmatch(r"[Pp](\d+)", s)
    if m:
        z = int(m.group(1))
        return 2 * z, z, f"P{z}"
    m = re.fullmatch(r"[Zz](\d+)[Aa](\d+)", s)
    if m:
        z = int(m.group(1))
        a = int(m.group(2))
        return a, z, f"Z{z}A{a}"
    m = re.fullmatch(r"[Aa](\d+)[Zz](\d+)", s)
    if m:
        a = int(m.group(1))
        z = int(m.group(2))
        return a, z, f"Z{z}A{a}"
    raise ValueError(f"cannot parse isotope label {label!r}; use --A and --Z")


def xi_from_temperature_K(T_K: float) -> float:
    if T_K <= 0.0:
        raise ValueError("temperature must be positive")
    return notd.T_PL_MEV / (K_B_MEV_PER_K * T_K)


def lab_outside_curvature_lifetime_factor(
    T_K: float,
    reference_K: float = CMB_TEMPERATURE_K,
    *,
    phi_gravity_epsilon: float = 0.0,
    reference_phi_gravity_epsilon: float = 0.0,
) -> float:
    """Relative outside-support correction: temperature + gravity vs reference."""
    return notd.lab_outside_support_lifetime_factor(
        T_K,
        phi_gravity_epsilon=phi_gravity_epsilon,
        reference_K=reference_K,
        reference_phi_gravity_epsilon=reference_phi_gravity_epsilon,
    )


def default_lab_gravity_phi_epsilon(
    *,
    tier: notd.GravityBindingTier = "full",
) -> float:
    return notd.local_lab_gravity_phi_epsilon(tier)


def default_molecular_host(A: int, Z: int) -> str | None:
    """Tritium lab samples are rarely bare atoms; default molecular host is T2."""
    if A == 3 and Z == 1:
        return "T2"
    return None


def resolve_lab_outside_binding(
    lab_gravity_phi_epsilon: float | None,
    *,
    gravity_tier: notd.GravityBindingTier,
    molecular_host: str | None = None,
    molecular_nucleus_label: str | None = None,
) -> tuple[float, notd.GravitationalBindingStack]:
    if lab_gravity_phi_epsilon is not None:
        stack = notd.GravitationalBindingStack(
            earth=lab_gravity_phi_epsilon,
            sun=0.0,
            galaxy=0.0,
            molecular=0.0,
        )
        return lab_gravity_phi_epsilon, stack
    stack = notd.local_outside_binding_stack(
        gravity_tier,
        molecular_host=molecular_host,
        molecular_nucleus_label=molecular_nucleus_label,
    )
    return stack.total, stack


def resolve_lab_gravity(
    lab_gravity_phi_epsilon: float | None,
    *,
    gravity_tier: notd.GravityBindingTier,
    molecular_host: str | None = None,
    molecular_nucleus_label: str | None = None,
) -> tuple[float, notd.GravitationalBindingStack]:
    return resolve_lab_outside_binding(
        lab_gravity_phi_epsilon,
        gravity_tier=gravity_tier,
        molecular_host=molecular_host,
        molecular_nucleus_label=molecular_nucleus_label,
    )


def model_electron_neutrino_mass_mev() -> float:
    try:
        raw = json.loads(WITNESS_JSON.read_text())
        if "nu_m1_MeV" in raw:
            return abs(float(raw["nu_m1_MeV"]))
        return abs(float(raw.get("m_nu_e", 0.0))) * abs(float(raw.get("geV_per_MeV", 1.0e-3)))
    except Exception:
        return 0.0


def weak_tipping_half_life_seconds(
    endpoint_q_mev: float,
    residual_mev: float,
    *,
    A: int = 1,
    well_depth_mev: float = 0.0,
    width_well_depth_mev: float | None = None,
    bonded: bool = False,
    lab_temperature_K: float = CMB_TEMPERATURE_K,
    lab_gravity_phi_epsilon: float | None = None,
    gravity_tier: notd.GravityBindingTier = "full",
    molecular_host: str | None = None,
    neutrino_mass_mev: float = 0.0,
    weak_bridge_energy_mev: float = 0.0,
    local_curvature_width_factor: float = 1.0,
) -> float:
    """Backward-compatible wrapper around the G_F weak-width readout."""
    gravity_eps, _ = resolve_lab_outside_binding(
        lab_gravity_phi_epsilon,
        gravity_tier=gravity_tier,
        molecular_host=molecular_host,
    )
    support_factor = lab_outside_curvature_lifetime_factor(
        lab_temperature_K,
        phi_gravity_epsilon=gravity_eps,
    )
    return dbi.weak_beta_half_life_seconds(
        endpoint_q_mev,
        residual_mev,
        A=A,
        well_depth_mev=well_depth_mev,
        width_well_depth_mev=width_well_depth_mev,
        bonded=bonded,
        neutrino_mass_mev=neutrino_mass_mev,
        weak_bridge_energy_mev=weak_bridge_energy_mev,
        lab_temperature_factor=support_factor,
        local_curvature_width_factor=local_curvature_width_factor,
    )


def isotope_environment(A: int, Z: int, *, xi: float) -> pn.NucleonEnvironment:
    if A <= 1:
        return pn.NucleonEnvironment(shell=notd.REFERENCE_M, xi=xi, bonded=False)
    return pn.caustic_environment_for_A(A, xi=xi)


def imbalance_drive(A: int, Z: int, n_count: int, own_binding_mev: float) -> tuple[float, float]:
    """Cluster imbalance drive applies only to multi-nucleon isotopes."""
    if A <= 1:
        return 0.0, 0.0
    neutron_excess = max(0.0, (n_count - Z) / max(A, 1))
    proton_excess = max(0.0, (Z - n_count) / max(A, 1))
    return neutron_excess * own_binding_mev, proton_excess * own_binding_mev


def stability_readout(
    A: int,
    Z: int,
    *,
    xi: float = notd.XI_LOCKIN,
    label: str | None = None,
    em_tipping_qualified: bool = False,
    lab_temperature_K: float = CMB_TEMPERATURE_K,
    lab_gravity_phi_epsilon: float | None = None,
    gravity_tier: notd.GravityBindingTier = "full",
    molecular_host: str | None = None,
    neutrino_mass_mev: float | None = None,
) -> StabilityReadout:
    if A <= 0 or Z < 0 or Z > A:
        raise ValueError("require A > 0 and 0 ≤ Z ≤ A")
    label = label or f"Z{Z}A{A}"
    env = isotope_environment(A, Z, xi=xi)
    base = dbi.beta_channel_readout(label, A, Z, env)
    n_count = dbi.neutron_count(A, Z)
    own = notd.nucleon_own_binding_mev(env.shell, env.xi, bonded=env.bonded)
    shield = max(env.well_depth_mev, 0.0) if env.bonded else 0.0
    cluster_total = (
        pn.cluster_caustic_total_mev(A, shell=env.shell, xi=env.xi) if env.bonded else 0.0
    )
    width_well = (
        dbi.beta_width_well_depth_mev(
            A,
            Z,
            cluster_total_mev=cluster_total,
            proton_mass_mev=base.proton_mass_mev,
            neutron_mass_mev=base.neutron_mass_mev,
        )
        if env.bonded and n_count > 0
        else 0.0
    )
    host = default_molecular_host(A, Z) if molecular_host is None else molecular_host
    if host == "":
        host = None
    gravity_eps, gravity_stack = resolve_lab_outside_binding(
        lab_gravity_phi_epsilon,
        gravity_tier=gravity_tier,
        molecular_host=host,
        molecular_nucleus_label="T" if host in ("T2", "T2O") else None,
    )
    outside_gravity_factor = notd.outside_gravity_geff_modulator(gravity_eps)
    outside_support_factor = lab_outside_curvature_lifetime_factor(
        lab_temperature_K,
        phi_gravity_epsilon=gravity_eps,
    )
    lab_xi = xi_from_temperature_K(lab_temperature_K)
    width_low, width_central, width_high = notd.local_curvature_weak_width_factor_band(
        lab_xi,
        gravity_eps,
        A=A,
        bonded=env.bonded,
    )

    neutron_drive, proton_drive = imbalance_drive(A, Z, n_count, own)

    beta_minus_eff = base.beta_minus_residual_mev + neutron_drive - shield
    beta_plus_eff = base.beta_plus_residual_mev + proton_drive - shield

    structurally_shielded = beta_minus_eff <= 0.0 and beta_plus_eff <= 0.0

    active: list[tuple[str, float, float]] = []
    if (
        n_count > 0
        and base.beta_minus_endpoint_q_mev is not None
        and base.beta_minus_endpoint_q_mev > 0.0
        and base.beta_minus_residual_mev > 0.0
    ):
        active.append(
            (
                "beta_minus",
                base.beta_minus_endpoint_q_mev,
                base.beta_minus_residual_mev,
            )
        )
    if (
        Z > 0
        and base.beta_plus_endpoint_q_mev is not None
        and base.beta_plus_endpoint_q_mev > 0.0
        and base.beta_plus_residual_mev > 0.0
    ):
        active.append(
            (
                "beta_plus",
                base.beta_plus_endpoint_q_mev,
                base.beta_plus_residual_mev,
            )
        )

    if not em_tipping_qualified:
        channel = "unqualified"
        half_life = None
        half_label = "unqualified: EM tipping not locked"
        dynamically_stable = False
        q_phase = None
    elif not active:
        channel = "stable"
        half_life = None
        half_label = "stable (∞ after EM-tipping qualification)"
        dynamically_stable = True
        q_phase = None
    else:
        nu_mev = model_electron_neutrino_mass_mev() if neutrino_mass_mev is None else neutrino_mass_mev
        bridge_mev = weak_bridge.weak_bridge_energy_mev(nu_mev)
        channel, endpoint_q, residual_q = min(
            active,
            key=lambda item: weak_tipping_half_life_seconds(
                item[1],
                item[2],
                A=A,
                well_depth_mev=shield,
                width_well_depth_mev=width_well if item[0] == "beta_minus" else None,
                bonded=env.bonded,
                lab_temperature_K=lab_temperature_K,
                lab_gravity_phi_epsilon=gravity_eps,
                gravity_tier=gravity_tier,
                molecular_host=host,
                neutrino_mass_mev=nu_mev,
                weak_bridge_energy_mev=bridge_mev,
                local_curvature_width_factor=width_central,
            ),
        )
        q_phase = max(endpoint_q - max(nu_mev, 0.0) - max(bridge_mev, 0.0), 0.0)
        half_life = weak_tipping_half_life_seconds(
            endpoint_q,
            residual_q,
            A=A,
            well_depth_mev=shield,
            width_well_depth_mev=width_well if channel == "beta_minus" else None,
            bonded=env.bonded,
            lab_temperature_K=lab_temperature_K,
            lab_gravity_phi_epsilon=gravity_eps,
            gravity_tier=gravity_tier,
            molecular_host=host,
            neutrino_mass_mev=nu_mev,
            weak_bridge_energy_mev=bridge_mev,
            local_curvature_width_factor=width_central,
        )
        half_label = f"{half_life:.6e} s"
        dynamically_stable = False

    nu_mev_out = model_electron_neutrino_mass_mev() if neutrino_mass_mev is None else neutrino_mass_mev
    weak_bridge_mev_out = weak_bridge.weak_bridge_energy_mev(nu_mev_out)

    return StabilityReadout(
        label=label,
        A=A,
        Z=Z,
        N=n_count,
        xi=xi,
        well_shield_mev=shield,
        width_well_shield_mev=width_well,
        cluster_caustic_total_mev=cluster_total,
        own_binding_mev=own,
        beta_minus_raw_residual_mev=base.beta_minus_residual_mev,
        beta_plus_raw_residual_mev=base.beta_plus_residual_mev,
        beta_minus_endpoint_q_mev=base.beta_minus_endpoint_q_mev,
        beta_plus_endpoint_q_mev=base.beta_plus_endpoint_q_mev,
        neutron_excess_drive_mev=neutron_drive,
        proton_excess_drive_mev=proton_drive,
        beta_minus_effective_residual_mev=beta_minus_eff,
        beta_plus_effective_residual_mev=beta_plus_eff,
        structurally_shielded=structurally_shielded,
        em_tipping_qualified=em_tipping_qualified,
        active_channel=channel,
        dynamically_stable=dynamically_stable,
        lab_temperature_K=lab_temperature_K,
        lab_gravity_phi_epsilon=gravity_eps,
        lab_gravity_binding_stack=gravity_stack.as_dict(),
        lab_molecular_host=host,
        lab_outside_gravity_factor=outside_gravity_factor,
        lab_outside_curvature_factor=outside_support_factor,
        local_curvature_neutrino_opacity_barn=notd.local_curvature_neutrino_opacity_barn(
            lab_xi,
            gravity_eps,
        ),
        local_curvature_weak_width_factor=width_central,
        local_curvature_weak_width_factor_low=width_low,
        local_curvature_weak_width_factor_high=width_high,
        neutrino_mass_mev=nu_mev_out,
        weak_bridge_energy_mev=weak_bridge_mev_out,
        beta_phase_space_q_mev=q_phase,
        half_life_seconds=half_life,
        half_life_label=half_label,
        notes=(
            "endpoint Q + valley geometry; outside support = temperature + "
            f"gravity stack ({gravity_tier}); local ν opacity width × "
            f"{width_central:.6f} ({width_low:.6f}–{width_high:.6f})"
        ),
    )


def build_payload(
    A: int,
    Z: int,
    label: str,
    *,
    em_tipping_qualified: bool = False,
    lab_temperature_K: float = CMB_TEMPERATURE_K,
    lab_gravity_phi_epsilon: float | None = None,
    gravity_tier: notd.GravityBindingTier = "full",
    molecular_host: str | None = None,
    neutrino_mass_mev: float | None = None,
) -> dict:
    bbn_xi = notd.xi_from_T_MeV(0.1)
    return {
        "source": "scripts/hqiv_isotope_stability_halflife.py",
        "lean_module": "Hqiv.Physics.DynamicIsotopeStability",
        "label_policy": "P120 means proton-count 120 with default A=2Z; pass --A/--Z to override",
        "em_tipping_qualified": em_tipping_qualified,
        "lab_temperature_K": lab_temperature_K,
        "neutrino_mass_mev": model_electron_neutrino_mass_mev()
        if neutrino_mass_mev is None
        else neutrino_mass_mev,
        "lab_gravity_phi_epsilon_default": default_lab_gravity_phi_epsilon(tier=gravity_tier),
        "lab_gravity_binding_stack_default": notd.local_lab_gravity_binding_stack(
            gravity_tier
        ).as_dict(),
        "earth_surface_phi_epsilon": notd.earth_surface_phi_epsilon(),
        "solar_phi_epsilon_at_1au": notd.solar_phi_epsilon_at_distance(),
        "galactic_circular_phi_epsilon": notd.galactic_circular_phi_epsilon(),
        "electron_mass_mev": dbi.model_electron_mass_mev(),
        "weak_bridge_shape": weak_bridge.weak_bridge_shape(),
        "lockin": asdict(
            stability_readout(
                A,
                Z,
                xi=notd.XI_LOCKIN,
                label=label,
                em_tipping_qualified=em_tipping_qualified,
                lab_temperature_K=lab_temperature_K,
                lab_gravity_phi_epsilon=lab_gravity_phi_epsilon,
                gravity_tier=gravity_tier,
                molecular_host=molecular_host,
                neutrino_mass_mev=neutrino_mass_mev,
            )
        ),
        "bbn_0_1_MeV": asdict(
            stability_readout(
                A,
                Z,
                xi=bbn_xi,
                label=label,
                em_tipping_qualified=em_tipping_qualified,
                lab_temperature_K=lab_temperature_K,
                lab_gravity_phi_epsilon=lab_gravity_phi_epsilon,
                gravity_tier=gravity_tier,
                molecular_host=molecular_host,
                neutrino_mass_mev=neutrino_mass_mev,
            )
        ),
    }


def print_report(payload: dict) -> None:
    print("HQIV isotope stability / half-life")
    print("=" * 72)
    for section in ("lockin", "bbn_0_1_MeV"):
        row = payload[section]
        print(
            f"{section:<14} {row['label']} A={row['A']} Z={row['Z']} N={row['N']} "
            f"shielded={row['structurally_shielded']} stable={row['dynamically_stable']} "
            f"channel={row['active_channel']} "
            f"t1/2={row['half_life_label']}"
        )
        print(
            f"  endpoint Qβ-={row['beta_minus_endpoint_q_mev']} MeV, "
            f"residual={row['beta_minus_raw_residual_mev']:.6f} MeV, "
            f"shield={row['well_shield_mev']:.6f} MeV"
        )
        print(
            f"  mν={row['neutrino_mass_mev']:.6e} MeV, "
            f"ε_g={row['lab_gravity_phi_epsilon']:.6e} "
            f"(⊕={row['lab_gravity_binding_stack']['earth']:.3e}, "
            f"☉={row['lab_gravity_binding_stack']['sun']:.3e}, "
            f"gal={row['lab_gravity_binding_stack']['galaxy']:.3e}, "
            f"mol={row['lab_gravity_binding_stack'].get('molecular', 0.0):.3e}), "
            f"host={row.get('lab_molecular_host')}, "
            f"G_eff={row['lab_outside_gravity_factor']:.12f}, "
            f"outside support={row['lab_outside_curvature_factor']:.9f}, "
            f"nu_opacity={row['local_curvature_neutrino_opacity_barn']:.3e} barn, "
            f"width×={row['local_curvature_weak_width_factor']:.6f} "
            f"({row['local_curvature_weak_width_factor_low']:.6f}–"
            f"{row['local_curvature_weak_width_factor_high']:.6f}), "
            f"Q_phase={row['beta_phase_space_q_mev']}"
        )


def main() -> None:
    parser = argparse.ArgumentParser(description="HQIV isotope stability and half-life")
    parser.add_argument("label", nargs="?", default="P120")
    parser.add_argument("--A", type=int)
    parser.add_argument("--Z", type=int)
    parser.add_argument(
        "--qualify-em-tipping",
        action="store_true",
        help="allow stability/half-life claims from the residual readout",
    )
    parser.add_argument(
        "--lab-temperature-K",
        type=float,
        default=CMB_TEMPERATURE_K,
        help="temperature for outside-curvature half-life correction (default: 2.725 K)",
    )
    parser.add_argument(
        "--neutrino-mass-mev",
        type=float,
        default=None,
        help="electron-neutrino mass used in beta endpoint phase space; default from HQIV witness",
    )
    parser.add_argument(
        "--molecular-host",
        default=None,
        help="molecular binding host for outside ε (T2, T2O, H2, …); tritium defaults to T2",
    )
    parser.add_argument(
        "--isolated-atom",
        action="store_true",
        help="disable default molecular host even for tritium",
    )
    parser.add_argument(
        "--gravity-stack",
        choices=("none", "earth", "solar_system", "full"),
        default="full",
        help="outside binding tiers: none | earth | earth+sun | earth+sun+galaxy (default)",
    )
    parser.add_argument(
        "--no-earth-gravity",
        action="store_true",
        help="alias for --gravity-stack none",
    )
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()

    if args.A is not None or args.Z is not None:
        if args.A is None or args.Z is None:
            raise SystemExit("provide both --A and --Z")
        A, Z, label = args.A, args.Z, f"Z{args.Z}A{args.A}"
    else:
        A, Z, label = parse_isotope_label(args.label)

    gravity_tier: notd.GravityBindingTier = "none" if args.no_earth_gravity else args.gravity_stack
    mol_host = "" if args.isolated_atom else args.molecular_host
    payload = build_payload(
        A,
        Z,
        label,
        em_tipping_qualified=args.qualify_em_tipping,
        lab_temperature_K=args.lab_temperature_K,
        gravity_tier=gravity_tier,
        molecular_host=mol_host,
        neutrino_mass_mev=args.neutrino_mass_mev,
    )
    print_report(payload)
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(payload, indent=2) + "\n")
    print(f"Wrote {args.json_out}")


if __name__ == "__main__":
    main()

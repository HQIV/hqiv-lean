#!/usr/bin/env python3
"""
Dynamic `nucleon(p,n)` readout.

This is the executable mirror of `Hqiv.Physics.DynamicNucleonPN`.

The rule is intentionally conservative:

  mass(flavor, env) =
      constituent(flavor)
    − own_binding(shell, ξ, bonded/free)
    − bonded_well_depth

The ξ-dependent own-binding is the outside-curvature temperature layer from
`hqiv_nuclear_outside_temperature_dynamics.py`.  The nuclear well can be supplied
from the caustic stack.  Since the binding and well are shared by p and n, the
p–n gap stays the derived constituent/isospin gap until an explicit weak/EM tipping
layer is added.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Literal

import hqiv_nuclear_curvature_binding as ncur
import hqiv_nuclear_outside_temperature_dynamics as notd

ROOT = Path(__file__).resolve().parents[1]
WITNESS_JSON = ROOT / "data" / "hqiv_witnesses.json"

NucleonFlavor = Literal["p", "n"]


@dataclass(frozen=True)
class NucleonEnvironment:
    shell: int
    xi: float
    well_depth_mev: float = 0.0
    bonded: bool = False


@dataclass(frozen=True)
class NucleonReadout:
    flavor: NucleonFlavor
    mass_mev: float
    constituent_mev: float
    own_binding_mev: float
    well_contribution_mev: float
    xi: float
    shell: int
    bonded: bool


@dataclass(frozen=True)
class PNPairReadout:
    proton: NucleonReadout
    neutron: NucleonReadout
    delta_m_mev: float
    beta_minus_overlap_mev: float
    beta_plus_overlap_mev: float
    notes: str


def _load_witness() -> dict[str, float]:
    if WITNESS_JSON.is_file():
        return json.loads(WITNESS_JSON.read_text())
    return {
        "derivedProtonMass_MeV": 938.272,
        "derivedNeutronMass_MeV": 939.565,
        "derivedDeltaM_MeV": 1.293,
    }


def shared_binding_mev(shell: int = notd.REFERENCE_M) -> float:
    return notd.niob.nucleon_trace_binding_mev(shell)


def constituent_masses(shell: int = notd.REFERENCE_M) -> tuple[float, float]:
    witness = _load_witness()
    shared = shared_binding_mev(shell)
    return (
        float(witness["derivedProtonMass_MeV"]) + shared,
        float(witness["derivedNeutronMass_MeV"]) + shared,
    )


def constituent_energy(flavor: NucleonFlavor, shell: int = notd.REFERENCE_M) -> float:
    p, n = constituent_masses(shell)
    return p if flavor == "p" else n


def well_contribution(env: NucleonEnvironment) -> float:
    return max(env.well_depth_mev, 0.0) if env.bonded else 0.0


def nucleon_readout(flavor: NucleonFlavor, env: NucleonEnvironment) -> NucleonReadout:
    constituent = constituent_energy(flavor, env.shell)
    own = notd.nucleon_own_binding_mev(env.shell, env.xi, bonded=env.bonded)
    well = well_contribution(env)
    return NucleonReadout(
        flavor=flavor,
        mass_mev=constituent - own - well,
        constituent_mev=constituent,
        own_binding_mev=own,
        well_contribution_mev=well,
        xi=env.xi,
        shell=env.shell,
        bonded=env.bonded,
    )


def pn_pair_readout(env: NucleonEnvironment) -> PNPairReadout:
    p = nucleon_readout("p", env)
    n = nucleon_readout("n", env)
    beta_minus = notd.beta_decay_readout(
        "beta_minus", xi=env.xi, well_depth_mev=env.well_depth_mev, bonded=env.bonded
    )
    beta_plus = notd.beta_decay_readout(
        "beta_plus", xi=env.xi, well_depth_mev=env.well_depth_mev, bonded=env.bonded
    )
    return PNPairReadout(
        proton=p,
        neutron=n,
        delta_m_mev=n.mass_mev - p.mass_mev,
        beta_minus_overlap_mev=beta_minus.overlap_mev,
        beta_plus_overlap_mev=beta_plus.overlap_mev,
        notes="shared outside-temperature binding preserves p-n gap; beta widths remain separate",
    )


def cluster_caustic_total_mev(
    A: int,
    *,
    shell: int = notd.REFERENCE_M,
    xi: float = notd.XI_LOCKIN,
) -> float:
    """Outside caustic stack for mass number ``A`` at horizon ``xi`` (MeV)."""
    m_cluster = ncur.nucleus_curvature_shell(A)
    total, _, _, _, _ = notd.nuclear_cluster_binding_at_xi(
        shell, A, m_cluster=m_cluster, xi=xi, bonded=True
    )
    return total


def caustic_environment_for_A(
    A: int,
    *,
    shell: int = notd.REFERENCE_M,
    xi: float = notd.XI_LOCKIN,
) -> NucleonEnvironment:
    total = cluster_caustic_total_mev(A, shell=shell, xi=xi)
    # Mass readout: symmetric per-nucleon well (preserves proved ΔM bookkeeping).
    well = total / max(A, 1)
    return NucleonEnvironment(shell=shell, xi=xi, well_depth_mev=well, bonded=True)


def build_payload() -> dict:
    free = pn_pair_readout(
        NucleonEnvironment(shell=notd.REFERENCE_M, xi=notd.XI_LOCKIN, bonded=False)
    )
    he4_env = caustic_environment_for_A(4)
    he4 = pn_pair_readout(he4_env)
    bbn_xi = notd.xi_from_T_MeV(0.1)
    he4_bbn = pn_pair_readout(caustic_environment_for_A(4, xi=bbn_xi))
    return {
        "source": "scripts/hqiv_dynamic_nucleon_pn.py",
        "lean_module": "Hqiv.Physics.DynamicNucleonPN",
        "policy": "no fitted nucleon masses; uses witness-derived masses plus shared binding",
        "free_lockin": asdict(free),
        "he4_lockin_environment": asdict(he4),
        "he4_bbn_temperature_environment": asdict(he4_bbn),
    }


def print_report(payload: dict) -> None:
    print("HQIV dynamic nucleon(p,n) readout")
    print("=" * 72)
    for label in ("free_lockin", "he4_lockin_environment", "he4_bbn_temperature_environment"):
        row = payload[label]
        print(
            f"{label:<34} "
            f"p={row['proton']['mass_mev']:.6f} MeV "
            f"n={row['neutron']['mass_mev']:.6f} MeV "
            f"Δ={row['delta_m_mev']:.6f} MeV "
            f"β-={row['beta_minus_overlap_mev']:.6f}"
        )


def main() -> None:
    parser = argparse.ArgumentParser(description="HQIV dynamic nucleon(p,n) readout")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    payload = build_payload()
    print_report(payload)
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2) + "\n")
        print(f"Wrote {args.json_out}")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
Meta-horizon excited-state readouts (Lean: MetaHorizonExcitedStates.lean).

Ground hadron mass comes from the witness / coupling / informational-energy stack;
excitations add ΔM from internal radial (n) or orbital (ℓ) modes on the lock-in drum:

  totalModeMass(n, ℓ) = protonConstituent − E_bind(composite_trace @ referenceM + n + ℓ)
  ΔM(n, ℓ) = totalModeMass(n, ℓ) − derivedProtonMass

Python mirrors E_bind_from_composite_trace with the nucleon 3-channel trace witness.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from pathlib import Path
from typing import Literal

import cubic_phase_relax_probe as cpr

REFERENCE_M = cpr.REFERENCE_M
ALPHA = cpr.ALPHA
GAMMA = cpr.GAMMA
INV_ALPHA_GUT = 42.0
PHI_COEFF = cpr.PHI_TEMPERATURE_COEFF

# Nucleon composite trace: three active carrier slots on one generator family.
NUCLEON_TRACE_GENERATOR_WEIGHT = 3.0

ExcitationTag = Literal["", "decuplet", "vector"]


def phi_of_shell(m: int) -> float:
    return PHI_COEFF * float(m + 1)


def lattice_simplex_count(m: int) -> int:
    return (m + 2) * (m + 1)


def alpha_eff_at_shell(m: int, c: float = 1.0) -> float:
    inv = INV_ALPHA_GUT * (1.0 + c * ALPHA * math.log(phi_of_shell(m) + 1.0))
    return 1.0 / inv


def binding_coupling_at_shell(m: int, c: float = 1.0) -> float:
    """Lean `bindingCouplingAtShell`: latticeSimplexCount · α_eff(m)."""
    return float(lattice_simplex_count(m)) * alpha_eff_at_shell(m, c)


def e_bind_from_nucleon_trace_mev(m: int, c: float = 1.0) -> float:
    """Lean `E_bind_from_composite_trace` with nucleonTraceDiagonal / nucleonTraceState."""
    return NUCLEON_TRACE_GENERATOR_WEIGHT * binding_coupling_at_shell(m, c)


def total_mode_shell(n: int, ell: int) -> int:
    return REFERENCE_M + n + ell


def total_mode_binding_mev(n: int, ell: int, c: float = 1.0) -> float:
    return e_bind_from_nucleon_trace_mev(total_mode_shell(n, ell), c)


def total_mode_mass_mev(
    n: int,
    ell: int,
    *,
    proton_constituent_mev: float,
    derived_proton_mev: float,
    c: float = 1.0,
) -> float:
    """
    Lean `totalModeMass` up to constituent input.

    At (0,0) this matches `derivedProtonMass` when constituent/binding are consistent.
    """
    return proton_constituent_mev - total_mode_binding_mev(n, ell, c)


def delta_m_mode_mev(
    n: int,
    ell: int,
    *,
    proton_constituent_mev: float,
    derived_proton_mev: float,
    c: float = 1.0,
) -> float:
    """ΔM above derived proton ground: totalModeMass(n,ℓ) − derivedProtonMass."""
    ground = total_mode_mass_mev(0, 0, proton_constituent_mev=proton_constituent_mev, derived_proton_mev=derived_proton_mev, c=c)
    excited = total_mode_mass_mev(n, ell, proton_constituent_mev=proton_constituent_mev, derived_proton_mev=derived_proton_mev, c=c)
    _ = ground  # ground should equal derived_proton_mev when inputs are Lean-consistent
    return excited - derived_proton_mev


def proton_constituent_from_witness(derived_proton_mev: float, shared_binding_mev: float | None = None) -> float:
    """Invert derivedProtonMass = constituent − sharedBinding at referenceM."""
    bind = shared_binding_mev if shared_binding_mev is not None else e_bind_from_nucleon_trace_mev(REFERENCE_M)
    return derived_proton_mev + bind


def delta_m_radial_naive_mev(
    n: int,
    ell: int = 0,
    *,
    proton_constituent_mev: float,
    derived_proton_mev: float,
    c: float = 1.0,
) -> float:
    """Lean `metaHorizonExcitationDeltaNaive`: composite-trace `totalModeMass − m_p`."""
    return delta_m_mode_mev(
        n,
        ell,
        proton_constituent_mev=proton_constituent_mev,
        derived_proton_mev=derived_proton_mev,
        c=c,
    )


def delta_m_radial_operational_mev(
    n: int,
    *,
    derived_proton_mev: float,
) -> float:
    """
    Lean `radialExcitationDeltaOperational n`:
      m_p · (S(referenceM + n) / S(referenceM) − 1),  S(m) = (m+1)(m+2).
    """
    if n == 0:
        return 0.0
    s0 = cpr.shell_surface(float(REFERENCE_M))
    s1 = cpr.shell_surface(float(REFERENCE_M + n))
    return derived_proton_mev * (s1 / s0 - 1.0)


def delta_m_radial_mev(
    n: int = 1,
    *,
    derived_proton_mev: float,
    shared_binding_mev: float | None = None,
) -> float:
    """Catalog radial step: operational surface readout (alias for n=1 decuplet tag)."""
    _ = shared_binding_mev
    return delta_m_radial_operational_mev(n, derived_proton_mev=derived_proton_mev)


def delta_m_orbital_operational_mev(
    ell: int,
    *,
    derived_proton_mev: float,
) -> float:
    """
    Lean `orbitalExcitationDeltaOperational ℓ`:
      m_p · max(0, geometricResonanceStep(referenceM + ℓ, referenceM) − 1).
    """
    if ell == 0:
        return 0.0
    step = cpr.geometric_resonance_step(float(REFERENCE_M + ell), float(REFERENCE_M))
    return derived_proton_mev * max(step - 1.0, 0.0)


def delta_m_orbital_mev(
    ell: int = 1,
    *,
    derived_proton_mev: float,
    shared_binding_mev: float | None = None,
) -> float:
    """Catalog orbital step (vector tag); meson scaling applied in `excitation_for_tag`."""
    _ = shared_binding_mev
    return delta_m_orbital_operational_mev(ell, derived_proton_mev=derived_proton_mev)


def meta_horizon_excited_mass_mev(
    n: int,
    ell: int,
    *,
    derived_proton_mev: float,
    proton_constituent_mev: float | None = None,
    readout: Literal["operational", "naive", "trapped_planck"] = "operational",
    c: float = 1.0,
) -> float:
    """Lean readout: operational catalog, naive composite trace, or trapped Planck."""
    if readout == "trapped_planck":
        return meta_horizon_trapped_planck_mass_mev(n, ell, derived_proton_mev=derived_proton_mev)
    if readout == "operational":
        return (
            derived_proton_mev
            + delta_m_radial_operational_mev(n, derived_proton_mev=derived_proton_mev)
            + delta_m_orbital_operational_mev(ell, derived_proton_mev=derived_proton_mev)
        )
    pc = proton_constituent_mev or proton_constituent_from_witness(derived_proton_mev)
    return total_mode_mass_mev(
        n,
        ell,
        proton_constituent_mev=pc,
        derived_proton_mev=derived_proton_mev,
        c=c,
    )


def shell_shape(m: int) -> float:
    """Lean `shell_shape m = curvatureDensity (m+1)`."""
    x = float(m + 1)
    return (1.0 / x) * (1.0 + ALPHA * math.log(x))


def curvature_volume_through(m: int) -> float:
    """Lean `metaHorizonCurvatureVolumeThrough m = curvature_integral (m+1)`."""
    return sum(shell_shape(k) for k in range(m + 1))


def trapped_planck_shell_slice(m: int) -> float:
    """Single-shell Planck zero-point slice: `N_m · ω_m / 2`."""
    nm = 8 if m == 0 else 8 * (m + 1)
    return nm / (2.0 * (m + 1))


def trapped_planck_cumulative_budget(m: int) -> float:
    """Lean `trappedPlanckCumulativeBudget m = vacuumZeroPointEnergy 0 m`."""
    return sum(trapped_planck_shell_slice(k) for k in range(m + 1))


def meta_horizon_trapped_inside_ratio(m_exc: int, m_ref: int = REFERENCE_M) -> float:
    """Lean `metaHorizonTrappedInsideRatio m_exc m_ref`."""
    return (
        curvature_volume_through(m_exc) / curvature_volume_through(m_ref)
    ) * (trapped_planck_cumulative_budget(m_exc) / trapped_planck_cumulative_budget(m_ref))


def meta_horizon_trapped_planck_mass_mev(
    n: int,
    ell: int,
    *,
    derived_proton_mev: float,
) -> float:
    """Lean `metaHorizonTrappedPlanckMassReadout n ℓ`."""
    m_exc = total_mode_shell(n, ell)
    return derived_proton_mev * meta_horizon_trapped_inside_ratio(m_exc, REFERENCE_M)


def excitation_table_rows(
    *,
    derived_proton_mev: float,
    n_max: int = 3,
    ell_max: int = 2,
) -> list[dict[str, float | int | str]]:
    """Grid of naive vs operational readouts for low-lying (n, ℓ)."""
    pc = proton_constituent_from_witness(derived_proton_mev)
    rows: list[dict[str, float | int | str]] = []
    for n in range(n_max + 1):
        for ell in range(ell_max + 1):
            rows.append(
                {
                    "n": n,
                    "ell": ell,
                    "shell": total_mode_shell(n, ell),
                    "naive_delta_mev": delta_m_radial_naive_mev(
                        n, ell, proton_constituent_mev=pc, derived_proton_mev=derived_proton_mev
                    ),
                    "radial_op_mev": delta_m_radial_operational_mev(
                        n, derived_proton_mev=derived_proton_mev
                    ),
                    "orbital_op_mev": delta_m_orbital_operational_mev(
                        ell, derived_proton_mev=derived_proton_mev
                    ),
                    "operational_mass_mev": meta_horizon_excited_mass_mev(
                        n, ell, derived_proton_mev=derived_proton_mev, readout="operational"
                    ),
                    "trapped_planck_mass_mev": meta_horizon_trapped_planck_mass_mev(
                        n, ell, derived_proton_mev=derived_proton_mev
                    ),
                }
            )
    return rows


@dataclass(frozen=True)
class ExcitationReadout:
    tag: ExcitationTag
    delta_mev: float
    mode: str
    pipeline_suffix: str


def excitation_for_tag(
    note: str,
    *,
    derived_proton_mev: float,
    meson_anchor_mev: float | None = None,
) -> ExcitationReadout:
    """
    Map catalog note tags to MetaHorizon mode increments.

    Decuplet: radial n=1 on baryon ground (same valence, spin excitation).
    Vector: orbital ℓ=1 on meson ground rest slot (uses meson anchor when given).
    """
    if note == "decuplet":
        dm = delta_m_radial_mev(1, derived_proton_mev=derived_proton_mev)
        return ExcitationReadout("decuplet", dm, "radial_n1", "+meta_horizon_radial_n1")
    if note == "vector":
        anchor = meson_anchor_mev if meson_anchor_mev is not None else derived_proton_mev * 0.5
        # Orbital step relative to meson ground: scale proton-derived ΔM by meson/proton anchor ratio.
        dm_proton = delta_m_orbital_mev(1, derived_proton_mev=derived_proton_mev)
        scale = anchor / derived_proton_mev if derived_proton_mev > 0 else 0.5
        dm = dm_proton * scale
        return ExcitationReadout("vector", dm, "orbital_l1", "+meta_horizon_orbital_l1")
    return ExcitationReadout("", 0.0, "ground", "")


def apply_excitation_to_ground_mev(ground_mev: float, exc: ExcitationReadout) -> float:
    return ground_mev + exc.delta_mev


def print_excitation_table(
    *,
    derived_proton_mev: float,
    n_max: int = 3,
    ell_max: int = 2,
) -> None:
    rows = excitation_table_rows(
        derived_proton_mev=derived_proton_mev, n_max=n_max, ell_max=ell_max
    )
    print()
    print(
        f"Meta-horizon excitations (m_p = {derived_proton_mev:.4f} MeV, "
        f"referenceM = {REFERENCE_M}; operational = Lean catalog readout):"
    )
    print(
        f"  {'n':>2} {'ℓ':>2} {'shell':>5} {'naive ΔM':>10} {'rad op':>10} "
        f"{'orb op':>10} {'M_op':>10} {'M_trap':>10}"
    )
    for r in rows:
        print(
            f"  {r['n']:2d} {r['ell']:2d} {r['shell']:5d} "
            f"{r['naive_delta_mev']:10.2f} {r['radial_op_mev']:10.2f} "
            f"{r['orbital_op_mev']:10.2f} {r['operational_mass_mev']:10.2f} "
            f"{r['trapped_planck_mass_mev']:10.2f}"
        )
    print("  (n=1,ℓ=0: naive ΔM < 0 certified in Lean; radial_op > 0.)")


def main() -> None:
    import argparse

    import hqiv_scale_witness as sw

    p = argparse.ArgumentParser(description="HQIV meta-horizon excited-state readouts")
    p.add_argument("--table", action="store_true", help="print (n,ℓ) naive vs operational grid")
    p.add_argument("--n-max", type=int, default=3)
    p.add_argument("--ell-max", type=int, default=2)
    p.add_argument("--witness-json", type=Path, default=sw.DEFAULT_WITNESS_JSON)
    args = p.parse_args()
    b = sw.load_witness_bundle(args.witness_json)
    mp = b.derived_proton_mass_gev * 1000.0
    if args.table:
        print_excitation_table(derived_proton_mev=mp, n_max=args.n_max, ell_max=args.ell_max)
    else:
        print_excitation_table(derived_proton_mev=mp, n_max=2, ell_max=1)


if __name__ == "__main__":
    main()

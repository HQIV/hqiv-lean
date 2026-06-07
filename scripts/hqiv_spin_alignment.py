#!/usr/bin/env python3
"""Long-term disk–filament spin alignment from coupled WHIM torque exchange.

This module evolves disk orientation over Gyr timescales using the same
``coherence``, ``seed_ratio``, and ``misalignment_sin`` inputs as the WHIM
filament layer. It is a **σ₈ / large-scale structure** predictor (observed
filament–disk alignments, inclination drift, spine pinch) — **not** part of the
instantaneous rotation-curve acceleration readout.

Coupled boundary exchange (diagnostic):

    τ_galaxy + τ_filament = 0

Over cosmic time, misaligned WHIM inflow drives the disk spin toward the spine
when phase is coherent; active disks decohere and freeze their orientation.
The filament spine co-rotates (pinch/shear) by equal and opposite torque.
"""

from __future__ import annotations

import math
from dataclasses import asdict, dataclass
from typing import Protocol

import hqiv_whim_filament as _whim

GYR_S = 3.15576e16
C_LIGHT = _whim.C_LIGHT
# σ₈ diagnostic coupling [rad/Gyr] — not fitted to rotation-curve χ²
ALIGNMENT_COUPLING_RAD_GYR = 0.08


class GalaxyMasterLike(Protocol):
    name: str
    hubble_type: int
    inclination_deg: float
    rdisk_kpc: float
    sb_disk_lsun_pc2: float
    L36_e9_lsun: float
    mhi_e9_msun: float
    rhi_kpc: float
    vflat_kms: float
    distance_mpc: float


@dataclass(frozen=True)
class SpinAlignmentState:
    time_gyr: float
    position_angle_deg: float
    inclination_deg: float
    misalignment_sin: float
    phase_coherence: float
    whim_seed_ratio: float
    torque_on_galaxy_ppm: float
    torque_on_filament_ppm: float

    def as_dict(self) -> dict[str, object]:
        return asdict(self)


@dataclass(frozen=True)
class SpinAlignmentSummary:
    initial_misalignment_sin: float
    final_misalignment_sin: float
    alignment_fraction: float
    equilibrium_time_gyr: float | None
    n_steps: int
    trajectory: tuple[SpinAlignmentState, ...]

    def as_dict(self) -> dict[str, object]:
        return {
            "initial_misalignment_sin": self.initial_misalignment_sin,
            "final_misalignment_sin": self.final_misalignment_sin,
            "alignment_fraction": self.alignment_fraction,
            "equilibrium_time_gyr": self.equilibrium_time_gyr,
            "n_steps": self.n_steps,
            "trajectory": [s.as_dict() for s in self.trajectory],
        }


def _misalignment_from_orientation(
    master: GalaxyMasterLike,
    position_angle_deg: float,
    inclination_deg: float,
    *,
    options: _whim.WhimFilamentOptions,
) -> tuple[float, float]:
    """Return (misalignment_sin, coherence) at fixed disk orientation."""
    import hqiv_filament_environment as _fil

    env = _fil.resolve_filament_environment(master, options.filament_catalog)
    spin = _fil.disk_spin_unit(inclination_deg)
    mis = _fil.misalignment_sin(spin, env.unit())
    tort, _ = _whim.tortuosity_index(
        master,
        max(master.rdisk_kpc, 0.5),
        options=options,
    )
    coherence = math.exp(-tort * options.tortuosity_gain)
    return mis, coherence


def torque_exchange_rate_rad_gyr(
    master: GalaxyMasterLike,
    *,
    options: _whim.WhimFilamentOptions = _whim.WhimFilamentOptions(),
    radius_kpc: float | None = None,
) -> float:
    """Effective spin-precession rate [rad/Gyr] from coupled torque diagnostic."""
    tau = _whim.hqiv_torque_exchange_diagnostics(master, options=options, radius_kpc=radius_kpc)
    return (
        ALIGNMENT_COUPLING_RAD_GYR
        * tau.misalignment_sin
        * tau.phase_coherence
        * tau.whim_seed_ratio
    )


def evolve_spin_alignment(
    master: GalaxyMasterLike,
    *,
    duration_gyr: float = 10.0,
    n_steps: int = 80,
    position_angle_deg: float | None = None,
    options: _whim.WhimFilamentOptions = _whim.WhimFilamentOptions(),
) -> SpinAlignmentSummary:
    """Integrate disk spin toward filament spine over cosmic time.

    Uses a damped misalignment equation:

        d(sin θ)/dt = −Γ · sin θ · coherence · seed_ratio

    with Γ from ``torque_exchange_rate_rad_gyr``. Active disks (low coherence)
    freeze orientation; seed-class galaxies align on ~1–5 Gyr when coherent.
    """
    pa = position_angle_deg if position_angle_deg is not None else 0.0
    inc = master.inclination_deg
    dt = duration_gyr / max(n_steps, 1)
    trajectory: list[SpinAlignmentState] = []
    eq_time: float | None = None
    mis0, coh0 = _misalignment_from_orientation(master, pa, inc, options=options)
    mis = mis0
    activity = _whim.galaxy_activity_index(master)
    seed_ratio = _whim.smooth_seed_ratio(activity, seed_class=_whim.is_seed_galaxy(master))
    gamma = torque_exchange_rate_rad_gyr(master, options=options)

    for step in range(n_steps + 1):
        t = step * dt
        tau = _whim.hqiv_torque_exchange_diagnostics(master, options=options)
        tort, _ = _whim.tortuosity_index(master, max(master.rdisk_kpc, 0.5), options=options)
        coherence = math.exp(-tort * options.tortuosity_gain)
        trajectory.append(
            SpinAlignmentState(
                time_gyr=t,
                position_angle_deg=pa,
                inclination_deg=inc,
                misalignment_sin=mis,
                phase_coherence=coherence,
                whim_seed_ratio=seed_ratio,
                torque_on_galaxy_ppm=tau.torque_on_galaxy_ppm,
                torque_on_filament_ppm=tau.torque_on_filament_ppm,
            )
        )
        if step == n_steps:
            break
        damp = gamma
        mis_prev = mis
        mis = max(0.0, mis - damp * dt * mis)
        if mis_prev > 1.0e-6 and mis / mis_prev < 0.5 and eq_time is None:
            eq_time = t + dt * math.log(2.0)
        if damp > 0.0 and mis > 1.0e-4:
            pa += math.degrees(damp * dt * 0.35 * mis)
            pa %= 180.0

    mis_f = trajectory[-1].misalignment_sin
    align_frac = 1.0 - (mis_f / max(mis0, 1.0e-6))
    return SpinAlignmentSummary(
        initial_misalignment_sin=mis0,
        final_misalignment_sin=mis_f,
        alignment_fraction=max(0.0, min(1.0, align_frac)),
        equilibrium_time_gyr=eq_time,
        n_steps=n_steps,
        trajectory=tuple(trajectory),
    )


def galaxy_spin_alignment_metadata(
    master: GalaxyMasterLike,
    *,
    options: _whim.WhimFilamentOptions = _whim.WhimFilamentOptions(),
    duration_gyr: float = 10.0,
) -> dict[str, object]:
    """Compact σ₈ diagnostic payload for SPARC / API export."""
    summary = evolve_spin_alignment(master, duration_gyr=duration_gyr, options=options)
    rate = torque_exchange_rate_rad_gyr(master, options=options)
    return {
        "duration_gyr": duration_gyr,
        "torque_exchange_rate_rad_gyr": rate,
        "initial_misalignment_sin": summary.initial_misalignment_sin,
        "final_misalignment_sin": summary.final_misalignment_sin,
        "alignment_fraction_10gyr": summary.alignment_fraction,
        "equilibrium_time_gyr": summary.equilibrium_time_gyr,
        "note": (
            "Long-term σ₈ diagnostic: disk spin and filament spine co-evolve via "
            "coupled WHIM-boundary torque. Does not enter rotation-curve φ or χ²."
        ),
    }

#!/usr/bin/env python3
"""WHIM filament lapse for galaxy seeding and active-disk decoherence.

Diffuse, gas-rich systems are modelled as **WHIM-seeded**: the longitudinal
O-Maxwell boundary lapse (filament contact → disk ISM) supplies φ before a
mature stellar disk exists. Once a galaxy is **active**, accretion streams
traverse a tortuous path through the disk (boosted when the filament spine is
misaligned with the spin axis), destroying coherent phase.

Activity and seeding use **smooth ratios** (no step functions):

    whim_seed_ratio(A)   = (1−A)² / ((1−A)² + A²)  (boosted for seed class)
    whim_active_ratio(A) = A² / (A² + (1−A)²)

Torque exchange on the shared WHIM boundary follows the fluid companion
``g_vac ∝ φ∇δθ′ + δθ′∇φ`` (wire + coronal papers): the disk and filament receive
**equal and opposite** exchange torques when the inflow axis is misaligned with
spin. This is a **long-term / σ₈ diagnostic only** — disk inclination drift,
spin alignment, and filament pinch — not part of the instantaneous rotation-curve
acceleration readout.
"""

from __future__ import annotations

import math
from dataclasses import asdict, dataclass
from typing import Protocol

import hqiv_filament_environment as _fil
import hqiv_galaxy_rotation as _gal

ALPHA_HQIV = 3.0 / 5.0
M_ISM_DEFAULT = 0
M_WHIM_DEFAULT = 1
SB_DISK_ACTIVE_REF = 80.0
DEFAULT_TORTUOSITY_GAIN = 1.75
DIFFUSE_HUBBLE_TYPES = frozenset({7, 8, 9, 10, 11})
GAMMA_HQIV = _gal.GAMMA_HQIV
C_LIGHT = _gal.C_LIGHT


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
class WhimFilamentOptions:
    enabled: bool = True
    m_ism: int = M_ISM_DEFAULT
    m_whim: int = M_WHIM_DEFAULT
    coupling_log: float = 1.0
    tortuosity_gain: float = DEFAULT_TORTUOSITY_GAIN
    filament_catalog: dict[str, _fil.FilamentEnvironment] | None = None


@dataclass(frozen=True)
class WhimFilamentState:
    radius_kpc: float
    activity_index: float
    seed_class: bool
    whim_seed_ratio: float
    whim_active_ratio: float
    tortuosity: float
    phase_coherence: float
    misalignment_sin: float
    phi_cosmic_m_s2: float
    phi_whim_m_s2: float
    phi_boundary_m_s2: float
    phi_combined_m_s2: float
    filament_radius_kpc: float
    filament_source: str


@dataclass(frozen=True)
class TorqueExchangeDiagnostics:
    """Coupled torque exchange on the shared WHIM boundary (diagnostic)."""

    torque_on_galaxy_ppm: float
    torque_on_filament_ppm: float
    misalignment_sin: float
    phase_coherence: float
    whim_seed_ratio: float
    inflow_speed_kms: float
    note: str

    def as_dict(self) -> dict[str, object]:
        return asdict(self)


def smooth_seed_ratio(activity: float, *, seed_class: bool) -> float:
    """Smooth WHIM-seed weight; 1 at A=0, 0 at A=1."""
    a = max(0.0, min(1.0, activity))
    num = (1.0 - a) ** 2
    den = num + a * a
    base = num / max(den, 1.0e-12)
    if seed_class:
        return min(1.0, 0.08 + 0.92 * base)
    return 0.30 * base


def smooth_active_ratio(activity: float) -> float:
    """Smooth mature-disk weight; complementary to seed ratio."""
    a = max(0.0, min(1.0, activity))
    num = a * a
    den = num + (1.0 - a) ** 2
    return num / max(den, 1.0e-12)


def smoothstep(edge0: float, edge1: float, x: float) -> float:
    if edge1 <= edge0:
        return 1.0 if x >= edge1 else 0.0
    t = max(0.0, min(1.0, (x - edge0) / (edge1 - edge0)))
    return t * t * (3.0 - 2.0 * t)


def is_seed_galaxy(master: GalaxyMasterLike) -> bool:
    if master.hubble_type in DIFFUSE_HUBBLE_TYPES:
        return True
    return master.name.upper().startswith("DDO") or master.name.upper().startswith("UGCA")


def galaxy_activity_index(master: GalaxyMasterLike) -> float:
    morph = master.hubble_type / 11.0
    sb = max(master.sb_disk_lsun_pc2, 0.5)
    sb_factor = math.sqrt(sb / SB_DISK_ACTIVE_REF)
    gas_richness = master.mhi_e9_msun / max(master.L36_e9_lsun, 0.02)
    raw = morph * sb_factor / max(gas_richness, 0.08) ** 0.35
    if is_seed_galaxy(master):
        raw *= 0.55
    return max(0.0, min(1.0, raw))


def filament_radius_kpc(master: GalaxyMasterLike) -> float:
    rd = max(master.rdisk_kpc, 0.08)
    if master.rhi_kpc > 0.05:
        return max(master.rhi_kpc, 2.0 * rd)
    return max(3.0 * rd, 1.5)


def _filament_env(master: GalaxyMasterLike, options: WhimFilamentOptions) -> _fil.FilamentEnvironment:
    return _fil.resolve_filament_environment(master, options.filament_catalog)


def tortuosity_index(
    master: GalaxyMasterLike,
    radius_kpc: float,
    *,
    options: WhimFilamentOptions,
) -> tuple[float, float]:
    """Return (tortuosity, misalignment_sin)."""
    rd = max(master.rdisk_kpc, 0.08)
    r = max(radius_kpc, 0.05)
    inc = max(master.inclination_deg, 5.0)
    cos_i = max(math.cos(math.radians(inc)), 0.25)
    activity = galaxy_activity_index(master)
    sb_weight = math.sqrt(max(master.sb_disk_lsun_pc2, 0.5) / SB_DISK_ACTIVE_REF)
    env = _filament_env(master, options)
    spin = _fil.disk_spin_unit(master.inclination_deg)
    mis = _fil.misalignment_sin(spin, env.unit())
    # Misaligned filaments force more disk crossings → higher tortuosity.
    mis_boost = 1.0 + mis * mis
    base = activity * (rd / r) * sb_weight / cos_i * mis_boost
    return base, mis


def phase_coherence(
    master: GalaxyMasterLike,
    radius_kpc: float,
    *,
    options: WhimFilamentOptions,
) -> float:
    tort, _ = tortuosity_index(master, radius_kpc, options=options)
    return math.exp(-tort * options.tortuosity_gain)


def whim_shell_delta_phi(m_ism: int, m_whim: int) -> float:
    return 2.0 * float(m_whim - m_ism)


def _whim_boundary_phi_amplitude(m_ism: int, m_whim: int) -> float:
    phi_hom = _gal.phi_acceleration_homogeneous_si()
    delta_phi = whim_shell_delta_phi(m_ism, m_whim)
    phi_ref = _gal.phi_of_shell(m_ism)
    return phi_hom * (delta_phi / max(phi_ref, 1.0e-30))


def phi_cosmic_radial(radius_kpc: float, rdisk_kpc: float) -> float:
    phi_hom = _gal.phi_acceleration_homogeneous_si()
    rd = max(rdisk_kpc, 0.05)
    r = max(radius_kpc, 0.05)
    return phi_hom / (1.0 + r / rd)


def whim_phi_part(
    master: GalaxyMasterLike,
    radius_kpc: float,
    *,
    options: WhimFilamentOptions = WhimFilamentOptions(),
) -> WhimFilamentState:
    """Combined φ with smooth seed/active blend and optional boundary hump."""
    r = max(radius_kpc, 0.05)
    rd = max(master.rdisk_kpc, 0.08)
    r_fil = filament_radius_kpc(master)
    activity = galaxy_activity_index(master)
    seed = is_seed_galaxy(master)
    seed_ratio = smooth_seed_ratio(activity, seed_class=seed)
    active_ratio = smooth_active_ratio(activity)
    tort, mis = tortuosity_index(master, r, options=options)
    coherence = math.exp(-tort * options.tortuosity_gain)
    env = _filament_env(master, options)

    phi_cosmic = phi_cosmic_radial(r, rd)
    phi_whim_amp = _whim_boundary_phi_amplitude(options.m_ism, options.m_whim)

    if not options.enabled:
        return WhimFilamentState(
            radius_kpc=r,
            activity_index=activity,
            seed_class=seed,
            whim_seed_ratio=seed_ratio,
            whim_active_ratio=active_ratio,
            tortuosity=tort,
            phase_coherence=coherence,
            misalignment_sin=mis,
            phi_cosmic_m_s2=phi_cosmic,
            phi_whim_m_s2=0.0,
            phi_boundary_m_s2=0.0,
            phi_combined_m_s2=phi_cosmic,
            filament_radius_kpc=r_fil,
            filament_source=env.source,
        )

    whim_envelope = 1.0 / (1.0 + r / r_fil)
    seed_ramp = min(r / r_fil, 1.0)
    seed_suppression = 0.08 + 0.92 * (1.0 - activity)
    if seed:
        # Gas-rich seeds at intermediate activity still need a sub-cosmic floor at small R.
        seed_suppression *= 0.55 + 0.45 * seed_ratio

    phi_seed = phi_cosmic * seed_ramp * seed_suppression
    phi_mature = phi_cosmic

    # Outer boundary hump only for non-seed transitional systems (both ratios partial).
    inner_gate = smoothstep(rd, r_fil, r)
    transitional = active_ratio * seed_ratio * (1.0 - seed_ratio) * 4.0
    if seed and seed_ratio > 0.55:
        phi_boundary = 0.0
    else:
        phi_boundary = (
            phi_whim_amp * coherence * inner_gate * whim_envelope * transitional
        )

    phi_combined = seed_ratio * phi_seed + (1.0 - seed_ratio) * phi_mature + phi_boundary
    phi_whim = seed_ratio * phi_seed + phi_boundary

    return WhimFilamentState(
        radius_kpc=r,
        activity_index=activity,
        seed_class=seed,
        whim_seed_ratio=seed_ratio,
        whim_active_ratio=active_ratio,
        tortuosity=tort,
        phase_coherence=coherence,
        misalignment_sin=mis,
        phi_cosmic_m_s2=phi_cosmic,
        phi_whim_m_s2=phi_whim,
        phi_boundary_m_s2=phi_boundary,
        phi_combined_m_s2=phi_combined,
        filament_radius_kpc=r_fil,
        filament_source=env.source,
    )


def hqiv_torque_exchange_diagnostics(
    master: GalaxyMasterLike,
    *,
    options: WhimFilamentOptions = WhimFilamentOptions(),
    radius_kpc: float | None = None,
) -> TorqueExchangeDiagnostics:
    """Diagnostic coupled torque from misaligned WHIM inflow on the shared boundary.

    HQIV assigns **equal and opposite** exchange torques to the galaxy and the
    filament spine (isolated pair on the WHIM contact). Long-term signatures:
    disk inclination drift and spin reorientation on the galaxy side; spine shear
    and pinch on the filament side. **Not** used in the rotation-curve φ readout.
    """
    r = radius_kpc if radius_kpc is not None else max(master.rdisk_kpc, 0.5)
    activity = galaxy_activity_index(master)
    seed_ratio = smooth_seed_ratio(activity, seed_class=is_seed_galaxy(master))
    tort, mis = tortuosity_index(master, r, options=options)
    coherence = math.exp(-tort * options.tortuosity_gain)
    env = _filament_env(master, options)
    v_in = env.inflow_speed_kms if env.inflow_speed_kms > 0.0 else max(0.3 * master.vflat_kms, 20.0)
    v_ref = max(master.vflat_kms, v_in, 30.0)

    # Dimensionless exchange strength: sinθ_mis × coherence × seed coupling × (v_in/c).
    # Reported in ppm of specific torque scale (a/c · v/c).
    phi_hom = _gal.phi_acceleration_homogeneous_si()
    a_over_c = phi_hom / (6.0 * C_LIGHT)
    exchange = mis * coherence * seed_ratio * (v_in / C_LIGHT) * a_over_c
    tau_ppm = exchange * 1.0e6

    return TorqueExchangeDiagnostics(
        torque_on_galaxy_ppm=tau_ppm,
        torque_on_filament_ppm=-tau_ppm,
        misalignment_sin=mis,
        phase_coherence=coherence,
        whim_seed_ratio=seed_ratio,
        inflow_speed_kms=v_in,
        note=(
            "Coupled WHIM-boundary exchange (σ₈ / long-term diagnostic): "
            "τ_galaxy + τ_filament = 0. Drives inclination drift, disk spin "
            "alignment, and filament pinch over cosmic time — not instantaneous a(r)."
        ),
    )


def galaxy_whim_metadata(
    master: GalaxyMasterLike,
    *,
    options: WhimFilamentOptions = WhimFilamentOptions(),
) -> dict[str, object]:
    r_mid = max(master.rdisk_kpc, 0.5)
    state = whim_phi_part(master, r_mid, options=options)
    env_meta = _fil.filament_environment_metadata(master, options.filament_catalog)
    torque = hqiv_torque_exchange_diagnostics(master, options=options, radius_kpc=r_mid)
    return {
        "seed_class": state.seed_class,
        "activity_index": state.activity_index,
        "whim_seed_ratio": state.whim_seed_ratio,
        "whim_active_ratio": state.whim_active_ratio,
        "filament_radius_kpc": state.filament_radius_kpc,
        "phase_coherence_at_rdisk": state.phase_coherence,
        "misalignment_sin": state.misalignment_sin,
        "phi_whim_at_rdisk_m_s2": state.phi_whim_m_s2,
        "phi_combined_at_rdisk_m_s2": state.phi_combined_m_s2,
        "filament_source": state.filament_source,
        "filament_environment": env_meta,
        "torque_exchange": torque.as_dict(),
        "m_ism": options.m_ism,
        "m_whim": options.m_whim,
    }


def state_as_dict(state: WhimFilamentState) -> dict[str, object]:
    return asdict(state)

#!/usr/bin/env python3
"""HQIV galaxy rotation calculator using the flyby mass-horizon equations."""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from typing import Iterable


G_NEWTON = 6.67430e-11
C_LIGHT = 299_792_458.0
H0_SI = 2.27e-18
GAMMA_HQIV = 2.0 / 5.0
KPC = 3.0856775814913673e19
M_SUN_KG = 1.98847e30


def phi_of_shell(m: int) -> float:
    return 2.0 * (float(m) + 1.0)


def hqiv_inertia_factor(a_loc: float, phi: float) -> float:
    """Lean `hqivFluidInertiaFactor`: f(a,φ)=a/(a+φ/6)."""
    return a_loc / (a_loc + phi / 6.0) if a_loc > 0.0 else 1.0


def phi_acceleration_homogeneous_si() -> float:
    """Homogeneous HQIV acceleration readout φ≈2cH0."""
    return 2.0 * C_LIGHT * H0_SI


def exponential_disk_mass_inside(radius_m: float, disk_mass_kg: float, scale_length_m: float) -> float:
    """Mass enclosed by a razor-thin exponential disk approximation."""
    x = max(radius_m, 0.0) / max(scale_length_m, 1.0)
    return disk_mass_kg * (1.0 - math.exp(-x) * (1.0 + x))


def rindler_denominator(tangent_speed_m_s: float) -> float:
    """Shared angular Rindler denominator D_R=1+(γ/2)(c/v)^2."""
    v = max(abs(tangent_speed_m_s), 1.0)
    return 1.0 + (GAMMA_HQIV / 2.0) * (C_LIGHT / v) ** 2


def mass_horizon_doppler_lapse(
    tangent_speed_m_s: float,
    *,
    projection: float = 1.0,
    support_fraction: float = 1.0,
    use_rindler_denominator: bool = True,
) -> float:
    """
    Co-rotating mass-horizon Doppler lapse.

    This is the galaxy analogue of the flyby term
    `2(v_tan/c)|vhat·phihat|`, optionally suppressed by the same angular Rindler
    denominator used for the local Milky-Way disk term in the flyby calculator.
    """
    eps = 2.0 * abs(tangent_speed_m_s) / C_LIGHT
    eps *= max(0.0, min(1.0, abs(projection)))
    eps *= max(0.0, min(1.0, support_fraction))
    if use_rindler_denominator:
        eps /= rindler_denominator(tangent_speed_m_s)
    return eps


@dataclass(frozen=True)
class GalaxyDisk:
    name: str = "exponential_disk"
    disk_mass_kg: float = 6.0e10 * M_SUN_KG
    scale_length_m: float = 2.6 * KPC
    phi_shell: int = 0
    lapse_radius_m: float | None = None
    support_fraction: float = 1.0

    def lapse_radius(self) -> float:
        return self.lapse_radius_m if self.lapse_radius_m is not None else self.scale_length_m

    def phi_reference(self) -> float:
        return phi_of_shell(self.phi_shell)


@dataclass(frozen=True)
class GalaxyPreset:
    """Approximate named-galaxy baryonic input for first-pass HQIV checks."""

    disk: GalaxyDisk
    observed_flat_km_s: float
    reference_radius_kpc: float
    note: str


GALAXY_PRESETS: dict[str, GalaxyPreset] = {
    # First-pass literature-scale inputs; not a SPARC mass-model import.
    "m33": GalaxyPreset(
        disk=GalaxyDisk(name="M33", disk_mass_kg=5.0e9 * M_SUN_KG, scale_length_m=1.8 * KPC),
        observed_flat_km_s=110.0,
        reference_radius_kpc=10.0,
        note="Triangulum; nearby low-mass spiral, slowly rising outer curve.",
    ),
    "ngc2403": GalaxyPreset(
        disk=GalaxyDisk(name="NGC 2403", disk_mass_kg=1.0e10 * M_SUN_KG, scale_length_m=1.8 * KPC),
        observed_flat_km_s=135.0,
        reference_radius_kpc=12.0,
        note="THINGS/SPARC benchmark late-type spiral.",
    ),
    "ngc3198": GalaxyPreset(
        disk=GalaxyDisk(name="NGC 3198", disk_mass_kg=5.0e10 * M_SUN_KG, scale_length_m=3.5 * KPC),
        observed_flat_km_s=150.0,
        reference_radius_kpc=20.0,
        note="Classic extended flat rotation-curve galaxy.",
    ),
    "ngc6503": GalaxyPreset(
        disk=GalaxyDisk(name="NGC 6503", disk_mass_kg=6.0e9 * M_SUN_KG, scale_length_m=1.7 * KPC),
        observed_flat_km_s=115.0,
        reference_radius_kpc=8.0,
        note="Well-studied nearby disk with compact baryonic component.",
    ),
    "ddo154": GalaxyPreset(
        disk=GalaxyDisk(name="DDO 154", disk_mass_kg=5.0e8 * M_SUN_KG, scale_length_m=1.6 * KPC),
        observed_flat_km_s=50.0,
        reference_radius_kpc=8.0,
        note="Gas-dominated dwarf; exponential disk is only a crude stand-in.",
    ),
    "ugc2885": GalaxyPreset(
        disk=GalaxyDisk(name="UGC 2885", disk_mass_kg=2.0e11 * M_SUN_KG, scale_length_m=8.0 * KPC),
        observed_flat_km_s=300.0,
        reference_radius_kpc=40.0,
        note="Giant high-speed spiral; useful upper-mass sanity check.",
    ),
}


@dataclass(frozen=True)
class RotationPoint:
    radius_kpc: float
    baryonic_speed_km_s: float
    hqiv_speed_km_s: float
    baryonic_accel_m_s2: float
    hqiv_accel_m_s2: float
    inertia_factor_full: float
    one_minus_f_full: float
    epsilon_doppler: float
    phi_accel_si: float


def baryonic_acceleration(radius_m: float, disk: GalaxyDisk) -> float:
    mass = exponential_disk_mass_inside(radius_m, disk.disk_mass_kg, disk.scale_length_m)
    return G_NEWTON * mass / max(radius_m * radius_m, 1.0)


def phi_acceleration_si(radius_m: float, disk: GalaxyDisk) -> float:
    """
    Local φ acceleration scale (m/s²).

    Default ``phi_shell=0`` gives the Kirchhoff/propagation-band readout
    φ_hom / (1 + r/R) with no hadron lock-in index.  Non-zero ``phi_shell`` is
    a sensitivity hook only.
    """
    if disk.phi_shell == 0:
        return phi_acceleration_homogeneous_si() / (
            1.0 + radius_m / max(disk.lapse_radius(), 1.0)
        )
    shell_mod = phi_of_shell(disk.phi_shell) / (1.0 + radius_m / disk.lapse_radius())
    shell_mod /= max(disk.phi_reference(), 1.0e-30)
    return phi_acceleration_homogeneous_si() * shell_mod


def hqiv_rotation_point(
    radius_m: float,
    disk: GalaxyDisk,
    *,
    projection: float = 1.0,
    use_rindler_denominator: bool = True,
) -> RotationPoint:
    """Circular-speed point from the shared HQIV modified-inertia/horizon repartition."""
    a_b = baryonic_acceleration(radius_m, disk)
    v_b = math.sqrt(max(a_b * radius_m, 0.0))
    eps = mass_horizon_doppler_lapse(
        v_b,
        projection=projection,
        support_fraction=disk.support_fraction,
        use_rindler_denominator=use_rindler_denominator,
    )
    phi_part = phi_acceleration_si(radius_m, disk)
    phi_full = phi_part + 6.0 * a_b * eps
    f_full = hqiv_inertia_factor(a_b, phi_full)
    a_hqiv = a_b / max(f_full, 1.0e-15)
    v_hqiv = math.sqrt(max(a_hqiv * radius_m, 0.0))
    return RotationPoint(
        radius_kpc=radius_m / KPC,
        baryonic_speed_km_s=v_b / 1.0e3,
        hqiv_speed_km_s=v_hqiv / 1.0e3,
        baryonic_accel_m_s2=a_b,
        hqiv_accel_m_s2=a_hqiv,
        inertia_factor_full=f_full,
        one_minus_f_full=max(0.0, 1.0 - f_full),
        epsilon_doppler=eps,
        phi_accel_si=phi_part,
    )


def rotation_curve(
    disk: GalaxyDisk,
    radii_kpc: Iterable[float],
    *,
    projection: float = 1.0,
    use_rindler_denominator: bool = True,
) -> list[RotationPoint]:
    return [
        hqiv_rotation_point(
            r_kpc * KPC,
            disk,
            projection=projection,
            use_rindler_denominator=use_rindler_denominator,
        )
        for r_kpc in radii_kpc
    ]


def default_radii_kpc(r_min: float = 0.5, r_max: float = 30.0, n: int = 40) -> list[float]:
    if n <= 1:
        return [r_min]
    step = (r_max - r_min) / float(n - 1)
    return [r_min + i * step for i in range(n)]


def preset_payload(
    preset_name: str,
    *,
    n: int = 40,
    projection: float = 1.0,
    use_rindler_denominator: bool = True,
) -> dict[str, object]:
    preset = GALAXY_PRESETS[preset_name]
    r_max = max(2.0 * preset.reference_radius_kpc, 8.0 * preset.disk.scale_length_m / KPC)
    rows = rotation_curve(
        preset.disk,
        default_radii_kpc(0.2, r_max, n),
        projection=projection,
        use_rindler_denominator=use_rindler_denominator,
    )
    ref = hqiv_rotation_point(
        preset.reference_radius_kpc * KPC,
        preset.disk,
        projection=projection,
        use_rindler_denominator=use_rindler_denominator,
    )
    return {
        "preset": preset_name,
        "note": preset.note,
        "observed_flat_km_s": preset.observed_flat_km_s,
        "reference_radius_kpc": preset.reference_radius_kpc,
        "reference_model": asdict(ref),
        "disk": asdict(preset.disk),
        "rows": [asdict(row) for row in rows],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="HQIV galaxy rotation calculator")
    parser.add_argument("--preset", choices=tuple(sorted(GALAXY_PRESETS)), default=None)
    parser.add_argument("--list-presets", action="store_true")
    parser.add_argument("--disk-mass-msun", type=float, default=6.0e10)
    parser.add_argument("--scale-kpc", type=float, default=2.6)
    parser.add_argument("--support-fraction", type=float, default=1.0)
    parser.add_argument("--phi-shell", type=int, default=0)
    parser.add_argument("--r-min-kpc", type=float, default=0.5)
    parser.add_argument("--r-max-kpc", type=float, default=30.0)
    parser.add_argument("--n", type=int, default=40)
    parser.add_argument("--projection", type=float, default=1.0)
    parser.add_argument("--no-rindler-denominator", action="store_true")
    args = parser.parse_args(argv)

    if args.list_presets:
        print(json.dumps({name: {"observed_flat_km_s": p.observed_flat_km_s, "note": p.note} for name, p in GALAXY_PRESETS.items()}, indent=2))
        return 0

    if args.preset:
        print(
            json.dumps(
                preset_payload(
                    args.preset,
                    n=args.n,
                    projection=args.projection,
                    use_rindler_denominator=not args.no_rindler_denominator,
                ),
                indent=2,
            )
        )
        return 0

    disk = GalaxyDisk(
        disk_mass_kg=args.disk_mass_msun * M_SUN_KG,
        scale_length_m=args.scale_kpc * KPC,
        phi_shell=args.phi_shell,
        support_fraction=args.support_fraction,
    )
    rows = rotation_curve(
        disk,
        default_radii_kpc(args.r_min_kpc, args.r_max_kpc, args.n),
        projection=args.projection,
        use_rindler_denominator=not args.no_rindler_denominator,
    )
    print(json.dumps({"disk": asdict(disk), "rows": [asdict(row) for row in rows]}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""
Universal dynamics scaffold (standalone; no Lean spine edits).

Goal:
  Build coupled shell-step dynamics where:
  - one oscillation per temperature step is explicit in the phase equation,
  - curvature / Omega_k self-support is explicit in the Omega equation,
  - lapse drives width,
  - spin-statistics and uncertainty contribute to broadening.

This is a modeling scaffold for calibration against accelerator/nature data.
It reuses HQIV ladder primitives from `cubic_phase_relax_probe.py`.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from dataclasses import asdict, dataclass

import cubic_phase_relax_probe as cp


EPS = 1e-12


@dataclass
class ModelParams:
    # Phase dynamics coefficients.
    c_omega: float = 0.8
    c_curv: float = 0.6

    # Omega self-support dynamics: Omega_{m+1} = Omega_m + a*drive - b*(Omega_m-1).
    omega_drive_gain: float = 0.25
    omega_relax_gain: float = 0.35

    # Lapse model N = 1 + l1*|Omega-1| + l2*|curvature|/rindler.
    lapse_omega: float = 0.7
    lapse_curv: float = 0.5

    # Width model: Gamma = gamma0 * N * (phase_mismatch + uncertainty + spin/stat factor).
    gamma0: float = 1.0
    uncertainty_gain: float = 0.25
    spin_gain: float = 0.2
    stat_gain: float = 0.1

    # Energy transport over shell steps.
    energy_damp_gain: float = 0.06


@dataclass
class ParticleConfig:
    name: str
    spin: float
    # +1 boson, -1 fermion
    statistics_sign: int
    shell_anchor: int


@dataclass
class ShellStep:
    m: int
    temperature: float
    curvature: float
    omega_target: float
    omega_state: float
    rindler_support: float
    phase_step: float
    phase_mismatch: float
    lapse: float
    uncertainty_term: float
    spin_stat_term: float
    width_gamma: float
    energy_state: float


def temperature(m: int) -> float:
    return 1.0 / float(m + 1)


def omega_target(m: int, horizon: int) -> float:
    return cp.omega_k_at_horizon(m, horizon)


def phase_step_from_fields(m: int, omega_s: float, curvature: float, p: ModelParams) -> float:
    # One-step oscillation target is 2π; field corrections perturb around it.
    corr = p.c_omega * (omega_s - 1.0) + p.c_curv * curvature / (cp.rindler_detuning_shared(float(m)) + EPS)
    return 2.0 * math.pi * (1.0 + corr)


def update_omega(omega_s: float, omega_t: float, curvature: float, p: ModelParams) -> float:
    drive = curvature * (omega_t - 1.0)
    return omega_s + p.omega_drive_gain * drive - p.omega_relax_gain * (omega_s - 1.0)


def lapse_from_state(m: int, omega_s: float, curvature: float, p: ModelParams) -> float:
    return 1.0 + p.lapse_omega * abs(omega_s - 1.0) + p.lapse_curv * abs(curvature) / (
        cp.rindler_detuning_shared(float(m)) + EPS
    )


def uncertainty_term(m: int, p: ModelParams) -> float:
    # Shell-step uncertainty proxy (smaller support -> larger uncertainty load).
    return p.uncertainty_gain / math.sqrt(cp.rindler_detuning_shared(float(m)) + EPS)


def spin_stat_term(spin: float, stat_sign: int, temp: float, p: ModelParams) -> float:
    # spin magnitude proxy
    spin_mag = math.sqrt(spin * (spin + 1.0))
    # simple finite-T occupancy correction surrogate; bounded and stable.
    occ = 1.0 / (math.exp(1.0 / max(temp, EPS)) - stat_sign + EPS)
    return p.spin_gain * spin_mag + p.stat_gain * abs(occ)


def step_width_gamma(lapse: float, phase_mismatch: float, uterm: float, sterm: float, p: ModelParams) -> float:
    return p.gamma0 * lapse * (phase_mismatch + uterm + sterm)


def evolve_particle(
    particle: ParticleConfig,
    m_min: int,
    m_max: int,
    horizon: int,
    p: ModelParams,
) -> list[ShellStep]:
    omega_s = 1.0
    energy_s = 1.0
    out: list[ShellStep] = []
    for m in range(m_min, m_max + 1):
        temp = temperature(m)
        curv = cp.shell_shape(m)
        o_t = omega_target(m, horizon)
        omega_s = update_omega(omega_s, o_t, curv, p)
        phase_step = phase_step_from_fields(m, omega_s, curv, p)
        phase_mismatch = abs(phase_step - 2.0 * math.pi) / (2.0 * math.pi)
        lapse = lapse_from_state(m, omega_s, curv, p)
        uterm = uncertainty_term(m, p)
        sterm = spin_stat_term(particle.spin, particle.statistics_sign, temp, p)
        gamma = step_width_gamma(lapse, phase_mismatch, uterm, sterm, p)
        energy_s = energy_s * math.exp(-p.energy_damp_gain * gamma)

        out.append(
            ShellStep(
                m=m,
                temperature=temp,
                curvature=curv,
                omega_target=o_t,
                omega_state=omega_s,
                rindler_support=cp.rindler_detuning_shared(float(m)),
                phase_step=phase_step,
                phase_mismatch=phase_mismatch,
                lapse=lapse,
                uncertainty_term=uterm,
                spin_stat_term=sterm,
                width_gamma=gamma,
                energy_state=energy_s,
            )
        )
    return out


def summarize_track(track: list[ShellStep], particle: ParticleConfig) -> dict[str, object]:
    best = min(track, key=lambda r: r.phase_mismatch + abs(r.omega_state - 1.0))
    return {
        "particle": particle.name,
        "shell_anchor": particle.shell_anchor,
        "best_shell": best.m,
        "best_phase_mismatch": best.phase_mismatch,
        "best_omega_error": abs(best.omega_state - 1.0),
        "best_lapse": best.lapse,
        "best_width_gamma": best.width_gamma,
    }


def read_observed_widths(path: str) -> dict[int, float]:
    # CSV format: m,width
    out: dict[int, float] = {}
    with open(path, "r", encoding="utf-8") as f:
        rdr = csv.DictReader(f)
        for row in rdr:
            m = int(row["m"])
            w = float(row["width"])
            out[m] = w
    return out


def rmse_against_observed(track: list[ShellStep], observed: dict[int, float]) -> float | None:
    pairs = [(r.width_gamma, observed[r.m]) for r in track if r.m in observed]
    if not pairs:
        return None
    mse = sum((a - b) ** 2 for a, b in pairs) / len(pairs)
    return math.sqrt(mse)


def default_particles() -> list[ParticleConfig]:
    # Minimal starter set; user should extend with hadron-specific assignments.
    return [
        ParticleConfig(name="fermion_ref", spin=0.5, statistics_sign=-1, shell_anchor=cp.M_LOCKIN),
        ParticleConfig(name="boson_ref", spin=1.0, statistics_sign=+1, shell_anchor=cp.M_LOCKIN),
    ]


def build_parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(description="Universal dynamics shell-step scaffold")
    ap.add_argument("--m-min", type=int, default=1)
    ap.add_argument("--m-max", type=int, default=24)
    ap.add_argument("--horizon", type=int, default=cp.M_LOCKIN)
    ap.add_argument("--observed-widths-csv", type=str, default=None, help="optional CSV with columns: m,width")
    ap.add_argument("--json-out", type=str, default=None)
    return ap


def main() -> None:
    args = build_parser().parse_args()
    params = ModelParams()
    particles = default_particles()
    observed = read_observed_widths(args.observed_widths_csv) if args.observed_widths_csv else None

    particle_reports = []
    for part in particles:
        track = evolve_particle(part, args.m_min, args.m_max, args.horizon, params)
        summary = summarize_track(track, part)
        summary["rmse_width"] = rmse_against_observed(track, observed) if observed is not None else None
        particle_reports.append(
            {
                "summary": summary,
                "track": [asdict(x) for x in track],
            }
        )

    payload = {
        "config": {
            "m_min": args.m_min,
            "m_max": args.m_max,
            "horizon": args.horizon,
            "params": asdict(params),
            "referenceM": cp.REFERENCE_M,
            "M_LOCKIN": cp.M_LOCKIN,
        },
        "particles": particle_reports,
    }

    if args.json_out:
        with open(args.json_out, "w", encoding="utf-8") as f:
            json.dump(payload, f, indent=2, sort_keys=True)
    else:
        print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

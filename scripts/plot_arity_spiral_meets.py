#!/usr/bin/env python3
"""
Visualize how the **arity** search parameter tilts the 3-ray rapidity scaffold.

Uses the same geometry as `factor_from_curvature.py`:
  pole on S^1 = wrap(-axis + pi/2) with axis = pi/(2k); E' = 1 for delta_theta_prime (fixed tipping)
  three_spiral_rays_about_axis = pole + polar_angle + {0, 2pi/3, 4pi/3}

For each arity, as shell index `m` sweeps, **radius** can vary with `m`; ray **angles** use fixed E′.
Different arities **meet** at different angles — this plot makes that visible.

Dependencies: `matplotlib` optional (`pip install matplotlib`). Without it, use `--csv` only.

**`t` as step count:** prefer integer `--t` (1, 2, …) to match discrete shell-clock semantics; default is `1`.

Examples:
  python scripts/plot_arity_spiral_meets.py --m-max 120 --arities 2,3,4,6
  python scripts/plot_arity_spiral_meets.py --m-max 200 --csv /tmp/arity_spiral.csv
  python scripts/plot_arity_spiral_meets.py --n 221 --phi 1 --t 1 --meet-scan
"""

from __future__ import annotations

import argparse
import csv
import math
import sys
from pathlib import Path

# Reuse Lean-aligned geometry (single source of truth).
_SCRIPTS = Path(__file__).resolve().parent
if str(_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS))

from fractions import Fraction

from factor_from_curvature import (  # noqa: E402
    axis_angle_for_arity,
    omega_k_imprint,
    polar_angle_from_rapidity_omega,
    spiral_turn_e_prime,
    three_spiral_rays_about_axis,
)


def spiral_xy(m: int, theta: float, radius_mode: str) -> tuple[float, float]:
    if radius_mode == "unit":
        r = 1.0
    elif radius_mode == "shell_succ":
        r = float(m + 1)
    elif radius_mode == "sqrt_m":
        r = math.sqrt(float(max(m, 1)))
    else:
        raise ValueError(radius_mode)
    return r * math.cos(theta), r * math.sin(theta)


def collect_series(
    m_min: int,
    m_max: int,
    arities: list[int],
    phi: float,
    t: float,
    curvature: Fraction,
    omega_override: float | None,
    omega_mode: str,
    radius_mode: str,
) -> list[dict]:
    rows: list[dict] = []
    for m in range(m_min, m_max + 1):
        for k in arities:
            omega_k = omega_k_imprint(
                curvature, omega_override, arity=k, omega_mode=omega_mode
            )
            e_prime = spiral_turn_e_prime(m)
            rays = three_spiral_rays_about_axis(phi, t, omega_k, e_prime, k)
            for ri, theta in enumerate(rays):
                x, y = spiral_xy(m, theta, radius_mode)
                rows.append(
                    {
                        "m": m,
                        "arity": k,
                        "ray": ri,
                        "omega_k": omega_k,
                        "axis_deg": math.degrees(axis_angle_for_arity(k)),
                        "theta_deg": math.degrees(theta),
                        "theta": theta,
                        "x": x,
                        "y": y,
                        "polar_angle_base_deg": math.degrees(
                            polar_angle_from_rapidity_omega(phi, t, omega_k, e_prime)
                        ),
                    }
                )
    return rows


def write_csv(path: Path, rows: list[dict]) -> None:
    if not rows:
        return
    keys = list(rows[0].keys())
    with path.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=keys)
        w.writeheader()
        w.writerows(rows)


def scan_near_meets(
    m_min: int,
    m_max: int,
    arities: list[int],
    phi: float,
    t: float,
    curvature: Fraction,
    omega_override: float | None,
    omega_mode: str,
    tol_deg: float,
) -> list[tuple[int, int, int, float]]:
    """
    For each m, compare base ray (index 0) between pairs of arities; report |Δθ| in degrees
    wrapped to [0, 180] when below tol_deg.
    """
    out: list[tuple[int, int, int, float]] = []
    tol = math.radians(tol_deg)
    for m in range(m_min, m_max + 1):
        bases = {}
        for k in arities:
            ok = omega_k_imprint(curvature, omega_override, arity=k, omega_mode=omega_mode)
            r0 = three_spiral_rays_about_axis(phi, t, ok, spiral_turn_e_prime(m), k)[0]
            bases[k] = r0
        for i, k1 in enumerate(arities):
            for k2 in arities[i + 1 :]:
                d = abs((bases[k2] - bases[k1] + math.pi) % (2 * math.pi) - math.pi)
                if d <= tol:
                    out.append((m, k1, k2, math.degrees(d)))
    return out


def plot_matplotlib(
    rows: list[dict],
    arities: list[int],
    title: str,
    show: bool,
    outfile: Path | None,
    mark_m: int | None,
) -> None:
    import matplotlib.pyplot as plt

    fig, axes = plt.subplots(1, 2, figsize=(12, 5))

    # Left: (x,y) spiral trails, one color per arity, thin lines per ray index
    ax = axes[0]
    cmap = plt.cm.tab10
    for j, k in enumerate(arities):
        c = cmap(j % 10)
        for ri in (0, 1, 2):
            pts = [(r["x"], r["y"]) for r in rows if r["arity"] == k and r["ray"] == ri]
            if len(pts) < 2:
                continue
            xs, ys = zip(*pts)
            ls = ["-", "--", ":"][ri]
            ax.plot(xs, ys, color=c, linestyle=ls, linewidth=1.2, label=f"k={k} ray{ri}" if ri == 0 else None)
    ax.set_aspect("equal")
    ax.axhline(0, color="k", linewidth=0.3)
    ax.axvline(0, color="k", linewidth=0.3)
    ax.set_title("Spiral trails (x,y) — color=arity, linestyle=ray")
    ax.set_xlabel("x")
    ax.set_ylabel("y")
    ax.legend(loc="upper right", fontsize=7, ncol=2)

    # Right: theta vs m for base ray only (shows arity-dependent phase shear)
    ax2 = axes[1]
    for j, k in enumerate(arities):
        c = cmap(j % 10)
        series = [(r["m"], r["theta_deg"]) for r in rows if r["arity"] == k and r["ray"] == 0]
        series.sort()
        if len(series) < 2:
            continue
        ms, thetas = zip(*series)
        ax2.plot(ms, thetas, color=c, linewidth=1.4, label=f"arity k={k} (base ray)")
    ax2.set_title("Base-ray polar angle (deg) vs shell m")
    ax2.set_xlabel("m")
    ax2.set_ylabel("theta (deg)")
    if mark_m is not None:
        ax2.axvline(mark_m, color="k", linestyle="--", linewidth=0.8, alpha=0.5, label=f"m={mark_m}")
    ax2.legend(loc="best", fontsize=8)
    ax2.grid(True, alpha=0.3)

    fig.suptitle(title)
    fig.tight_layout()
    if outfile:
        fig.savefig(outfile, dpi=150)
        print(f"wrote {outfile}", file=sys.stderr)
    if show:
        plt.show()
    else:
        plt.close()


def main() -> None:
    p = argparse.ArgumentParser(description="Plot arity-tilted 3-ray spirals (factor_from_curvature geometry).")
    p.add_argument("--m-min", type=int, default=1)
    p.add_argument("--m-max", type=int, default=150)
    p.add_argument("--arities", type=str, default="2,3,4,6", help="comma-separated integers >= 2")
    p.add_argument("--phi", type=float, default=1.0)
    p.add_argument(
        "--t",
        type=float,
        default=1.0,
        help="rapidity t (prefer integer step count; default 1)",
    )
    p.add_argument("--curvature", type=float, default=0.0, help="rational imprint as float; 0 => Omega=1")
    p.add_argument("--omega-override", type=float, default=None, help="if set, ignores --curvature")
    p.add_argument(
        "--omega-mode",
        choices=("rational", "ramanujan_arity"),
        default="rational",
        help="Ω_k model: rational (1+curvature) or ramanujan_arity (1+τ(k)/k^{11/2} per arity k)",
    )
    p.add_argument(
        "--radius",
        choices=("shell_succ", "sqrt_m", "unit"),
        default="shell_succ",
        help="radial scale for plane plot (shell_succ = m+1, Lean polarRadiusShellSucc)",
    )
    p.add_argument("--csv", type=Path, default=None, help="write numeric series to CSV")
    p.add_argument("--png", type=Path, default=None, help="save figure (needs matplotlib)")
    p.add_argument("--show", action="store_true", help="show interactive window (needs matplotlib)")
    p.add_argument("--meet-scan", action="store_true", help="print m where base rays of two arities align within tol")
    p.add_argument("--meet-tol-deg", type=float, default=2.0)
    p.add_argument("--n", type=int, default=None, help="mark vertical line at m=n in angle plot (optional)")
    args = p.parse_args()

    arities = [int(x.strip()) for x in args.arities.split(",") if x.strip()]
    arities = [max(2, k) for k in arities]
    if args.m_max < args.m_min:
        raise SystemExit("m-max must be >= m-min")

    fr = Fraction(str(args.curvature)).limit_denominator(10_000)

    title = (
        f"phi={args.phi} t={args.t} omega_mode={args.omega_mode} "
        f"radius={args.radius} arities={arities}"
    )

    rows = collect_series(
        args.m_min,
        args.m_max,
        arities,
        args.phi,
        args.t,
        fr,
        args.omega_override,
        args.omega_mode,
        args.radius,
    )

    if args.csv:
        write_csv(args.csv, rows)
        print(f"wrote {len(rows)} rows to {args.csv}", file=sys.stderr)

    if args.meet_scan:
        hits = scan_near_meets(
            args.m_min,
            args.m_max,
            arities,
            args.phi,
            args.t,
            fr,
            args.omega_override,
            args.omega_mode,
            args.meet_tol_deg,
        )
        print(f"near-alignments base-ray |dtheta| <= {args.meet_tol_deg}° (count={len(hits)}):")
        for m, k1, k2, deg in hits[:200]:
            print(f"  m={m}  k={k1} vs k={k2}  dtheta={deg:.3f}°")
        if len(hits) > 200:
            print(f"  ... ({len(hits) - 200} more)")

    if args.show or args.png:
        try:
            plot_matplotlib(rows, arities, title, args.show, args.png, args.n)
        except ImportError:
            print(
                "matplotlib not installed; use `pip install matplotlib` or only --csv / --meet-scan",
                file=sys.stderr,
            )
            raise SystemExit(1) from None

if __name__ == "__main__":
    main()

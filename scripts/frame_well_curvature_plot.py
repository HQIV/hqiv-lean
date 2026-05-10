#!/usr/bin/env python3
"""
Plot helper for `scripts/frame_well_curvature_probe.py` output.

Usage:
  python3 scripts/frame_well_curvature_plot.py \
    --input-json scripts/frame_well_probe_output.json \
    --output-png scripts/frame_well_probe_plot.png
"""

from __future__ import annotations

import argparse
import json


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Plot frame well curvature probe output")
    p.add_argument("--input-json", type=str, required=True, help="probe JSON file")
    p.add_argument("--output-png", type=str, required=True, help="output PNG path")
    p.add_argument(
        "--show-no-rindler",
        action=argparse.BooleanOptionalAction,
        default=False,
        help="also plot no-rindler curves as dashed lines",
    )
    p.add_argument(
        "--mark-minima",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="mark detected local minima for each horizon",
    )
    return p


def main() -> None:
    args = build_parser().parse_args()

    try:
        import matplotlib.pyplot as plt
    except Exception as exc:  # pragma: no cover
        raise SystemExit(
            "matplotlib is required for plotting. "
            "Install with `python3 -m pip install matplotlib`."
        ) from exc

    with open(args.input_json, "r", encoding="utf-8") as f:
        report = json.load(f)

    ms = report["series"]["m"]
    by_horizon = report["series"]["by_horizon"]
    horizon_stats = {int(row["horizon"]): row for row in report["horizon_stats"]}
    excitation_shells = report["config"].get("excitation_shells", [])
    lockin = int(report["config"].get("M_LOCKIN", 4))

    fig, ax = plt.subplots(figsize=(12, 7))

    horizons = sorted(int(h) for h in by_horizon.keys())
    for h in horizons:
        hstr = str(h)
        vals = by_horizon[hstr]["rindler"]
        label = f"h={h} (rindler)"
        ax.plot(ms, vals, label=label, linewidth=2)

        if args.show_no_rindler:
            vals_nr = by_horizon[hstr]["no_rindler"]
            ax.plot(ms, vals_nr, linestyle="--", alpha=0.5, label=f"h={h} (no-rindler)")

        if args.mark_minima:
            mins = horizon_stats[h]["minima_shells"]
            if mins:
                yvals = []
                for m in mins:
                    idx = ms.index(m)
                    yvals.append(vals[idx])
                ax.scatter(mins, yvals, s=30)

    for shell in excitation_shells:
        ax.axvline(shell, color="gray", linestyle=":", alpha=0.25)
    ax.axvline(lockin, color="black", linestyle="-.", alpha=0.4, label=f"lockin={lockin}")

    p_val = report["excitation_null_test"].get("empirical_p_value", None)
    title = "Frame Well Depth vs Shell (Curvature + Omega_k on Rindler support)"
    if p_val is not None:
        title += f"\nExcitation null-test p-value: {p_val:.4f}"
    ax.set_title(title)
    ax.set_xlabel("shell m")
    ax.set_ylabel("well_depth(m, h)")
    ax.grid(True, alpha=0.25)
    ax.legend(loc="best", fontsize=8, ncol=2)
    fig.tight_layout()
    fig.savefig(args.output_png, dpi=150)


if __name__ == "__main__":
    main()

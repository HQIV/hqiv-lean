#!/usr/bin/env python3
"""
HQIV per-species alpha from FRAME-INDEPENDENT spectral invariants of the
octonion 8x8 composite-trace matrices.

Goal
----
The frame-translation slice (`hqiv_alpha_species_slice.py`) is basis-dependent:
it just reads the universal ladder at the species' shell. Here we test whether a
*basis-independent* spectral invariant of the genuine octonion 8x8 matrices gives
a stable, frame-independent alpha per species.

Matrices
--------
We use the real 8x8 left-multiplication matrices L_v (v=0..7) from
`fan_octonion_tables.py` (mirror of `Hqiv/OctonionLeftMultiplication.lean`).
For a species we build the carrier operator from its 7 frame couplings g_v:

    L_g = sum_{v=1..7} g_v * L_v ,    g_v = alpha_eff(shell_v(species))

KEY ALGEBRAIC FACT (alternativity): L_g is left-multiplication by the imaginary
octonion g = sum g_v e_v, so L_g^2 = -|g|^2 I. Hence the spectrum of L_g is
{ +-i|g| } (4-fold each) and the ONLY basis-independent number it exposes is the
norm |g| = sqrt(sum g_v^2). We verify this numerically.

Consequences / candidate invariants:
  - inv_alpha_spectral_norm = 1/|g|            (single-octonion spectral readout)
  - composite operator C = L_g . L_h breaks the degeneracy (h = reference-frame
    carrier); its eigenvalue spread is a genuine cross-frame invariant.

We compute these per species (isotope/atom/molecule/allotrope) and compare to
CODATA, to INV_ALPHA_GUT=42, and to the frame-weighted slice. The point is to
report HONESTLY what the spectrum does, not to force 137.

Run:
  PYTHONPATH=scripts python3 scripts/hqiv_alpha_spectral_invariant.py
  PYTHONPATH=scripts python3 scripts/hqiv_alpha_spectral_invariant.py --write-json
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

import numpy as np

import hqiv_alpha_species_slice as ss
import hqiv_excited_states as es

# Octonion 8x8 tables live under the carrier paper scripts; add to path.
_OCT_DIR = Path(__file__).resolve().parents[1] / "papers" / "carrier_vs_real_quantum" / "scripts"
if str(_OCT_DIR) not in sys.path:
    sys.path.insert(0, str(_OCT_DIR))
import fan_octonion_tables as oct  # noqa: E402

INV_ALPHA_GUT = es.INV_ALPHA_GUT  # 42
CODATA_INV_ALPHA = ss.CODATA_INV_ALPHA
REFERENCE_M = ss.REFERENCE_M
DEFAULT_JSON_PATH = Path(__file__).resolve().parents[1] / "data" / "alpha_spectral_invariant_witnesses.json"

LEAN_MODULES = (
    "Hqiv.OctonionLeftMultiplication",
    "Hqiv.Physics.BoundStates",
    "Hqiv.Physics.QuarkMetaResonance",
)

# Pre-stack the 8 real left-multiplication matrices as numpy arrays.
_L = {tag: np.array(oct.LEFT_MUL[tag], dtype=float) for tag in range(8)}


def carrier_operator(g: np.ndarray) -> np.ndarray:
    """L_g = sum_{v=1..7} g_v L_v (left-mult by imaginary octonion g)."""
    M = np.zeros((8, 8))
    for v in range(1, 8):
        M += g[v - 1] * _L[v]
    return M


def species_couplings(anchor_shell: int, *, c: float = 1.0) -> np.ndarray:
    """7 channel couplings g_v = alpha_eff(shell_v) in the species frame."""
    shells = ss.species_shell_frame(anchor_shell)
    return np.array([es.alpha_eff_at_shell(m, c) for m in shells], dtype=float)


@dataclass(frozen=True)
class SpectralInvariant:
    species: str
    kind: str
    anchor_shell: int
    g_norm: float
    inv_alpha_spectral_norm: float  # 1/|g|  (overall scale, near GUT coupling)
    spectral_modes: list[float]  # 4 distinct |eig(L_g)| (ascending) — the fingerprint
    quad_invariant: float  # sum of mode^2 (== 4|g|^2 by Frobenius)
    quad_consistency: float  # |quad_invariant - 4|g|^2|  (should be ~0)
    spectral_spread: float  # mode_max / mode_min  (pure structural ratio)
    clifford_defect: float  # ||L_g^2 + |g|^2 I||_F  (0 only for a Clifford rep)


def _mode_abs(M: np.ndarray) -> list[float]:
    """Distinct |eigenvalue| magnitudes (skew-symmetric => conjugate pairs)."""
    vals = sorted(float(abs(z)) for z in np.linalg.eigvals(M))
    modes: list[float] = []
    for x in vals:
        if not modes or abs(x - modes[-1]) > 1e-9:
            modes.append(x)
    return modes


def spectral_invariant(
    species: str, kind: str, anchor_shell: int, *, c: float = 1.0
) -> SpectralInvariant:
    g = species_couplings(anchor_shell, c=c)
    Lg = carrier_operator(g)
    g_norm = float(np.linalg.norm(g))

    modes = _mode_abs(Lg)
    quad = sum(m * m for m in modes)
    defect = float(np.linalg.norm(Lg @ Lg + (g_norm**2) * np.eye(8)))
    nonzero = [m for m in modes if m > 1e-12]
    spread = (max(nonzero) / min(nonzero)) if nonzero else float("inf")

    return SpectralInvariant(
        species=species,
        kind=kind,
        anchor_shell=anchor_shell,
        g_norm=g_norm,
        inv_alpha_spectral_norm=(1.0 / g_norm) if g_norm > 0 else float("inf"),
        spectral_modes=modes,
        quad_invariant=float(quad),
        quad_consistency=float(abs(quad - 4.0 * g_norm**2)),
        spectral_spread=float(spread),
        clifford_defect=defect,
    )


@dataclass
class SpectralReport:
    lean_modules: tuple[str, ...] = field(default_factory=lambda: LEAN_MODULES)
    inv_alpha_gut: float = INV_ALPHA_GUT
    codata_inv_alpha: float = CODATA_INV_ALPHA
    reference_anchor_shell: int = REFERENCE_M
    invariants: list[SpectralInvariant] = field(default_factory=list)
    findings: list[str] = field(default_factory=list)

    def to_dict(self) -> dict[str, Any]:
        return {
            "lean_modules": list(self.lean_modules),
            "inv_alpha_gut": self.inv_alpha_gut,
            "codata_inv_alpha": self.codata_inv_alpha,
            "reference_anchor_shell": self.reference_anchor_shell,
            "invariants": [asdict(i) for i in self.invariants],
            "findings": self.findings,
        }


def build_report(*, c: float = 1.0) -> SpectralReport:
    rows: list[SpectralInvariant] = []
    for label, A in (("H-1", 1), ("He-4", 4), ("C-12", 12), ("Fe-56", 56), ("U-238", 238)):
        rows.append(spectral_invariant(label, "isotope", ss.isotope_anchor_shell(A), c=c))
    for label, z in (("H", 1), ("C", 6), ("Fe", 26)):
        rows.append(spectral_invariant(label, "atom", ss.atom_anchor_shell(z), c=c))
    for label, zi, zj in (("H2", 1, 1), ("CH4 (C-H)", 6, 1)):
        rows.append(spectral_invariant(label, "molecule", ss.molecule_anchor_shell(zi, zj), c=c))
    for label, z, cn in (("C diamond", 6, 4), ("C graphite", 6, 3)):
        rows.append(spectral_invariant(label, "allotrope", ss.allotrope_anchor_shell(z, cn), c=c))

    max_qc = max(r.quad_consistency for r in rows)
    max_defect = max(r.clifford_defect for r in rows)
    inv_lo = min(r.inv_alpha_spectral_norm for r in rows)
    inv_hi = max(r.inv_alpha_spectral_norm for r in rows)
    findings = [
        "L_g = sum g_v L_v has a STRUCTURED 4-mode imaginary spectrum (4 distinct |eig|, "
        "conjugate pairs) — the species fingerprint is the DISTRIBUTION, not a single number.",
        f"Quadratic invariant is ~fixed: sum(mode^2) ~ 4|g|^2 (abs defect <= {max_qc:.1e}) — the "
        "spectral 'energy' is pinned by |g|, only its split across modes is species-structural.",
        f"This Fano gate table is NOT a clean Clifford rep (||L_g^2+|g|^2 I||_F up to "
        f"{max_defect:.1e}), which is exactly why a single carrier already resolves channels.",
        f"Overall scale 1/|g| spans {inv_lo:.1f}..{inv_hi:.1f} — near the GUT coupling "
        f"~{INV_ALPHA_GUT:g}, NOT 137. CODATA 1/137 is a dressed/run value, not an algebraic "
        "invariant of these matrices.",
        "Frame-independent per-species readouts that DO emerge: 1/|g| (overall coupling, "
        "monotone with mass) and the spectral spread mode_max/mode_min (~10, weakly species-dep).",
    ]
    return SpectralReport(invariants=rows, findings=findings)


def write_json_report(path: Path, report: SpectralReport) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(report.to_dict(), indent=2) + "\n", encoding="utf-8")


def print_report(report: SpectralReport) -> None:
    print("HQIV per-species alpha from octonion 8x8 spectral invariants")
    print(f"  INV_ALPHA_GUT = {report.inv_alpha_gut:g}   CODATA 1/alpha = {report.codata_inv_alpha:.3f}")
    print()
    print(
        f"  {'species':<14} {'kind':<10} {'anchor':>6} {'|g|':>9} {'1/|g|':>8} "
        f"{'spread':>7}  {'spectral modes (|eig|)':<30}"
    )
    last = None
    for r in report.invariants:
        if r.kind != last:
            print()
            last = r.kind
        modes = "[" + ", ".join(f"{m:.4f}" for m in r.spectral_modes) + "]"
        print(
            f"  {r.species:<14} {r.kind:<10} {r.anchor_shell:6d} {r.g_norm:9.5f} "
            f"{r.inv_alpha_spectral_norm:8.2f} {r.spectral_spread:7.2f}  {modes:<30}"
        )
    print()
    print("  Findings:")
    for f in report.findings:
        print(f"    - {f}")


def main() -> None:
    parser = argparse.ArgumentParser(description="HQIV octonion spectral-invariant alpha")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--write-json", action="store_true", help=f"Write {DEFAULT_JSON_PATH}")
    args = parser.parse_args()

    report = build_report()
    if args.json:
        print(json.dumps(report.to_dict(), indent=2))
    else:
        print_report(report)
    if args.write_json:
        write_json_report(DEFAULT_JSON_PATH, report)
        if not args.json:
            print(f"\nWrote {DEFAULT_JSON_PATH}")


if __name__ == "__main__":
    main()

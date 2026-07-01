#!/usr/bin/env python3
"""
HQIV per-species alpha by slicing the 7x7 Fano coupling matrix.

Idea
----
HQIV already has ONE matrix whose solve yields an inverse fine-structure-like
coupling: the 7x7 Fano holonomy / line-incidence system in
`scripts/hqiv_coupling_linear_system.py`. It places the 7 imaginary-octonion
(Fano) vertices on shells `m_v` via a *chart*, builds a 7x7 incidence matrix
`A`, solves `A c = b` for the per-vertex normalization `c_v`, and reads

    1/alpha_v = 42 * (1 + c_v * (3/5) * ln(phi(m_v) + 1)).

Nothing about that matrix is global-only. Every species type already PINS a
characteristic shell:

  - isotope  : nuclear curvature drum   `nucleus_curvature_shell(A)`
  - atom     : outermost electronic Compton shell `electronic_compton_shells(Z)`
  - molecule : bond-contact shell       `bond_contact_compton_shell(z, z')`
  - allotrope: coordination-shifted electronic shell

So "alpha per species" = **re-frame the same 7x7 Fano solve on the species'
pinned shell** and read `1/alpha`. We rigidly translate the canonical sector
chart by `offset = anchor_shell - referenceM`, re-solve the matrix, and report:

  - `inv_alpha_vertex`     : per-Fano-vertex 1/alpha in the species frame
  - `inv_alpha_weighted`   : Fano-weight mean (the species' scalar 1/alpha)
  - `inv_alpha_em_braced`  : Gauss->EW double-axis brace in the species frame

HONESTY: this is a *frame/readout* of the existing matrix, physically motivated
and parameter-free, NOT a uniqueness proof. The canonical normalization is
universal (octonion algebra); the species only chooses where the frame sits.
See `data/alpha_model_comparison_witnesses.json` UniquenessAudit for the open
policy question (which slice is canonical).

Run:
  PYTHONPATH=scripts python3 scripts/hqiv_alpha_species_slice.py
  PYTHONPATH=scripts python3 scripts/hqiv_alpha_species_slice.py --json
  PYTHONPATH=scripts python3 scripts/hqiv_alpha_species_slice.py --write-json
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

import numpy as np

import hqiv_chemistry_tuft_dynamics as ctd
import hqiv_coupling_linear_system as cls
import hqiv_nuclear_curvature_binding as ncb

REFERENCE_M = cls.REFERENCE_M
CODATA_INV_ALPHA = cls.CODATA_INV_ALPHA
DEFAULT_JSON_PATH = Path(__file__).resolve().parents[1] / "data" / "alpha_species_slice_witnesses.json"

LEAN_MODULES = (
    "Hqiv.Physics.DoublePreferredAxisAlpha",
    "Hqiv.Physics.FanoSectorSpectralMassEmergence",
    "Hqiv.QuantumChemistry.AtomNucleusCurvatureShell",
)

# Canonical Fano sector shells (vertex -> shell role); read from the shared module
# so we never duplicate the chart definition.
_SECTOR_SHELLS: tuple[int, ...] = tuple(
    cls.shell_for_vertex(v, "sector", REFERENCE_M) for v in range(7)
)


# ---------------------------------------------------------------------------
# Frame transform + species solve (reuses shared primitives verbatim)
# ---------------------------------------------------------------------------


def species_shell_frame(anchor_shell: int) -> list[int]:
    """Rigidly translate the canonical Fano sector chart onto the species shell."""
    offset = anchor_shell - REFERENCE_M
    return [max(0, m + offset) for m in _SECTOR_SHELLS]


def _build_species_line_incidence(shells: list[int]) -> tuple[np.ndarray, np.ndarray]:
    """Faithful copy of `build_line_incidence(..., 'spectral_detuning', line_weighted=True)`
    but on explicit species shells instead of a global chart."""
    A = np.zeros((7, 7))
    b = np.zeros(7)
    for i, pts in enumerate(cls.FANO_LINES):
        weights = [(v, cls.fano_line_weight(v)) for v in pts]
        wsum = sum(w for _, w in weights)
        for v, w in weights:
            k = cls.log_phi_slot(shells[v])
            A[i, v] = cls.INV_ALPHA_GUT * k * (w / wsum)
        const = cls.INV_ALPHA_GUT * len(pts) / wsum
        m_line = int(round(sum(shells[v] for v in pts) / len(pts)))
        b[i] = cls.INV_ALPHA_GUT * cls.rindler_1jet(m_line) - const
    return A, b


@dataclass(frozen=True)
class SpeciesAlphaSlice:
    species: str
    kind: str  # isotope | atom | molecule | allotrope
    anchor_shell: int
    anchor_source: str
    shells: list[int]
    c: list[float]
    residual: float
    inv_alpha_vertex: list[float]
    inv_alpha_weighted: float
    inv_alpha_em_braced: float
    alpha_weighted: float
    pct_vs_codata: float


def solve_species_alpha(
    species: str, kind: str, anchor_shell: int, anchor_source: str
) -> SpeciesAlphaSlice:
    shells = species_shell_frame(anchor_shell)
    A, b = _build_species_line_incidence(shells)
    c, resid = cls.solve_linear(A, b)
    inv_v = [cls.one_over_alpha_eff(shells[v], float(c[v])) for v in range(7)]

    weights = np.array([cls.fano_line_weight(v) for v in range(7)], dtype=float)
    inv_weighted = float(np.dot(weights, inv_v) / weights.sum())

    # Gauss->EW double-axis brace re-framed onto the species offset.
    offset = anchor_shell - REFERENCE_M
    m_gauss = max(0, cls.EM_GAUSS_SHELL + offset)
    m_ew = max(0, cls.EW_PHI_SHELL + offset)
    inv_braced = cls.shell_brace_inv_alpha(float(c[0]), m_gauss, m_ew)

    return SpeciesAlphaSlice(
        species=species,
        kind=kind,
        anchor_shell=anchor_shell,
        anchor_source=anchor_source,
        shells=shells,
        c=[float(x) for x in c],
        residual=float(resid),
        inv_alpha_vertex=[float(x) for x in inv_v],
        inv_alpha_weighted=inv_weighted,
        inv_alpha_em_braced=float(inv_braced),
        alpha_weighted=1.0 / inv_weighted,
        pct_vs_codata=100.0 * (inv_weighted / CODATA_INV_ALPHA - 1.0),
    )


# ---------------------------------------------------------------------------
# Per-species anchor selectors (reuse existing pinned shells)
# ---------------------------------------------------------------------------


def isotope_anchor_shell(A: int) -> int:
    """Nuclear curvature drum m_nuc(A)."""
    return ncb.nucleus_curvature_shell(A)


def atom_anchor_shell(z: int) -> int:
    """Outermost electronic Compton shell (centre slot)."""
    centre, _p, _h = ctd.electronic_compton_shells(z)
    return centre


def molecule_anchor_shell(z: int, z_partner: int) -> int:
    """Bond-contact Compton shell for the z--z_partner bond."""
    return ctd.bond_contact_compton_shell(z, z_partner)


def allotrope_anchor_shell(z: int, coordination: int, *, reference_coordination: int = 4) -> int:
    """Atom electronic shell shifted by (coordination - reference) — denser packing
    pulls the contact frame inward. Demonstration adapter for allotropes."""
    base = atom_anchor_shell(z)
    return max(0, base + (coordination - reference_coordination))


# ---------------------------------------------------------------------------
# Benchmark panel
# ---------------------------------------------------------------------------


@dataclass
class SpeciesAlphaReport:
    lean_modules: tuple[str, ...] = field(default_factory=lambda: LEAN_MODULES)
    codata_inv_alpha: float = CODATA_INV_ALPHA
    method: str = (
        "re-frame the 7x7 Fano line-incidence coupling solve onto the species' "
        "pinned shell (rigid sector-chart translation); read weighted 1/alpha"
    )
    sector_shells: list[int] = field(default_factory=lambda: list(_SECTOR_SHELLS))
    slices: list[SpeciesAlphaSlice] = field(default_factory=list)
    note: str = ""

    def to_dict(self) -> dict[str, Any]:
        return {
            "lean_modules": list(self.lean_modules),
            "codata_inv_alpha": self.codata_inv_alpha,
            "method": self.method,
            "sector_shells": self.sector_shells,
            "slices": [asdict(s) for s in self.slices],
            "note": self.note,
        }


def build_report() -> SpeciesAlphaReport:
    slices: list[SpeciesAlphaSlice] = []

    # Isotopes (nuclear drum frame)
    for label, A in (("H-1", 1), ("He-4", 4), ("C-12", 12), ("Fe-56", 56), ("U-238", 238)):
        m = isotope_anchor_shell(A)
        slices.append(solve_species_alpha(label, "isotope", m, f"nucleus_curvature_shell(A={A})"))

    # Atoms (outermost electronic frame)
    for label, z in (("H", 1), ("He", 2), ("C", 6), ("Fe", 26)):
        m = atom_anchor_shell(z)
        slices.append(solve_species_alpha(label, "atom", m, f"electronic_compton_shells(Z={z})"))

    # Molecules (bond-contact frame)
    for label, zi, zj in (("H2", 1, 1), ("CH4 (C-H)", 6, 1), ("HF (H-F)", 1, 9)):
        m = molecule_anchor_shell(zi, zj)
        slices.append(solve_species_alpha(label, "molecule", m, f"bond_contact_compton_shell({zi},{zj})"))

    # Allotropes (coordination-shifted frame)
    for label, z, cn in (("C diamond (sp3)", 6, 4), ("C graphite (sp2)", 6, 3)):
        m = allotrope_anchor_shell(z, cn)
        slices.append(solve_species_alpha(label, "allotrope", m, f"coordination={cn}"))

    return SpeciesAlphaReport(
        slices=slices,
        note=(
            "Per-species 1/alpha is the same Fano coupling matrix read in the species' "
            "shell frame. It is a parameter-free readout, not a uniqueness proof: the "
            "octonion normalization is universal; the species only selects the frame "
            "offset. Nuclear (isotope) and electronic (atom) frames are deliberately "
            "different slices of the same object."
        ),
    )


def write_json_report(path: Path, report: SpeciesAlphaReport) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(report.to_dict(), indent=2) + "\n", encoding="utf-8")


def print_report(report: SpeciesAlphaReport) -> None:
    print("HQIV per-species alpha (7x7 Fano matrix re-framed on pinned shells)")
    print(f"  canonical sector shells = {report.sector_shells}")
    print(f"  CODATA 1/alpha          = {report.codata_inv_alpha:.4f}")
    print()
    print(
        f"  {'species':<18} {'kind':<10} {'anchor m':>8} {'frame shells':<22} "
        f"{'1/a(wt)':>9} {'1/a(brace)':>10} {'%vsCODATA':>10}"
    )
    last_kind = None
    for s in report.slices:
        if s.kind != last_kind:
            print()
            last_kind = s.kind
        print(
            f"  {s.species:<18} {s.kind:<10} {s.anchor_shell:8d} "
            f"{str(s.shells):<22} {s.inv_alpha_weighted:9.3f} "
            f"{s.inv_alpha_em_braced:10.3f} {s.pct_vs_codata:+9.2f}%"
        )
    print()
    print(f"  Note: {report.note}")


def main() -> None:
    parser = argparse.ArgumentParser(description="HQIV per-species alpha slice")
    parser.add_argument("--json", action="store_true", help="Print JSON to stdout")
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

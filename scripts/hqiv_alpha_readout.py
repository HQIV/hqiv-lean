#!/usr/bin/env python3
"""
Canonical HQIV electromagnetic α readouts (scale-witness discipline).

Mirrors `Hqiv/Physics/EffectiveAlphaReadout.lean`.

Under default `proton_lockin`, α comes from the O–Maxwell double-axis brace — not CODATA.
CODATA 137.036 is the low-energy comparison; the primary brace prediction is ≈ 129 (1/α).

Run:
  python3 scripts/hqiv_alpha_readout.py
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

import hqiv_coupling_linear_system as hcls
import hqiv_scale_witness as sw

AlphaReadoutTier = Literal[
    "primary_brace_mz",
    "lockin_continuous",
    "codata_comparison",
    "paper_mz_witness",
]
ScaleWitness = sw.ScaleWitness

# Comparison layers (never physical inputs under proton_lockin)
CODATA_INV_ALPHA = sw.CODATA_INV_ALPHA
PAPER_INV_ALPHA_MZ = 127.9
XI_LOCKIN = sw.XI_LOCKIN
XI_EW = hcls.XI_EW


@dataclass(frozen=True)
class AlphaReadout:
    tier: AlphaReadoutTier
    scale_witness: ScaleWitness
    inv_alpha: float
    c_fano: float
    note: str

    @property
    def alpha(self) -> float:
        return 1.0 / self.inv_alpha


def holonomy_c0_proton_lockin() -> float:
    """EM vertex Fano coefficient from line+holonomy solve (c₀ ≈ 1 anchor)."""
    c, _, _, _, _ = hcls.solve_line_holonomy_anchor(
        "sector",
        hcls.REFERENCE_M,
        scale_setter=None,
        anchor_weight=1.0,
        scale_witness="proton_lockin",
    )
    return float(c[0])


def inv_alpha_primary_brace_mz(c_fano: float = 1.0) -> float:
    """Lean `one_over_alpha_EM_double_axis`: discrete Gauss→EW brace."""
    return hcls.double_axis_inv_alpha(c_fano)


def inv_alpha_lockin_continuous(c_fano: float = 1.0, xi_g: float = XI_LOCKIN) -> float:
    """Lean `one_over_alpha_EM_braced_at_xi` at lock-in."""
    return hcls.shell_brace_inv_alpha_continuous(c_fano, xi_g, XI_EW)


def resolve_inv_alpha_em(
    *,
    scale_witness: ScaleWitness = sw.DEFAULT_SCALE_WITNESS,
    tier: AlphaReadoutTier | None = None,
    c_fano: float | None = None,
    use_holonomy_c0: bool = False,
) -> AlphaReadout:
    """
    Canonical inverse α for the active scale witness.

    Default (`proton_lockin`, primary brace): double-axis discrete brace with
    `c₀ = 1` (unit anchor row in the holonomy solve — not the CODATA comparison).
    """
    if scale_witness == "codata_alpha":
        return AlphaReadout(
            tier="codata_comparison",
            scale_witness=scale_witness,
            inv_alpha=CODATA_INV_ALPHA,
            c_fano=1.0,
            note="codata_alpha witness pins brace to CODATA in coupling solve",
        )

    c = c_fano
    if c is None and use_holonomy_c0 and scale_witness == "proton_lockin":
        c = holonomy_c0_proton_lockin()
    if c is None:
        c = 1.0

    if tier is None:
        tier = "lockin_continuous" if scale_witness == "cmb_now" else "primary_brace_mz"

    if tier == "primary_brace_mz":
        inv = inv_alpha_primary_brace_mz(c)
        note = "O–Maxwell double-axis discrete brace (EW-scale prediction)"
    elif tier == "lockin_continuous":
        inv = inv_alpha_lockin_continuous(c)
        note = f"continuous brace at ξ_G={XI_LOCKIN}"
    elif tier == "codata_comparison":
        inv = CODATA_INV_ALPHA
        note = "CODATA low-energy comparison only"
    elif tier == "paper_mz_witness":
        inv = PAPER_INV_ALPHA_MZ
        note = "legacy paper α(M_Z) witness"
    else:
        raise ValueError(tier)

    return AlphaReadout(
        tier=tier,
        scale_witness=scale_witness,
        inv_alpha=inv,
        c_fano=c,
        note=note,
    )


def resolve_alpha_em(**kwargs) -> AlphaReadout:
    """Return full readout bundle; `.alpha` is the fine-structure constant."""
    return resolve_inv_alpha_em(**kwargs)


def tuft_fine_structure_alpha_derived(
    c_fano: float | None = None,
    *,
    scale_witness: ScaleWitness = sw.DEFAULT_SCALE_WITNESS,
) -> float:
    """Lean `tuftFineStructureAlphaDerived` for sector determinants / g−2."""
    return resolve_alpha_em(
        scale_witness=scale_witness,
        tier="primary_brace_mz",
        c_fano=c_fano,
    ).alpha


def main() -> None:
    print("HQIV α readouts (scale-witness discipline)")
    print(f"  CODATA 1/α (comparison)     = {CODATA_INV_ALPHA:.6f}")
    print(f"  paper witness 1/α(M_Z)      = {PAPER_INV_ALPHA_MZ:.6f}")
    print()
    for witness in ("proton_lockin", "cmb_now", "codata_alpha"):
        for tier in ("primary_brace_mz", "lockin_continuous"):
            if witness == "codata_alpha" and tier != "primary_brace_mz":
                continue
            try:
                r = resolve_inv_alpha_em(scale_witness=witness, tier=tier)  # type: ignore[arg-type]
            except Exception:
                continue
            print(
                f"  [{witness:14s} {r.tier:20s}]  "
                f"1/α={r.inv_alpha:10.4f}  α={r.alpha:.12e}  c₀={r.c_fano:.4f}  ({r.note})"
            )
        if witness == "codata_alpha":
            r = resolve_inv_alpha_em(scale_witness="codata_alpha")
            print(
                f"  [{witness:14s} {r.tier:20s}]  "
                f"1/α={r.inv_alpha:10.4f}  α={r.alpha:.12e}  ({r.note})"
            )
    print()
    comp = resolve_inv_alpha_em(tier="codata_comparison")
    pred = resolve_inv_alpha_em(scale_witness="proton_lockin", tier="primary_brace_mz")
    print(
        f"  proton_lockin prediction vs CODATA: Δ(1/α)={pred.inv_alpha - comp.inv_alpha:+.4f} "
        f"({100*(pred.inv_alpha/comp.inv_alpha - 1):+.2f}%)"
    )


if __name__ == "__main__":
    main()

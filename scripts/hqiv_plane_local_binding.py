#!/usr/bin/env python3
"""
Plane-local / generator-dependent binding on the so(8) network (n-body ready).

Lean: ``HqivSpine.Physics.GeneratorDependentCoupling``

  planeLocalCoupling(m,k) = bindingCouplingAtShell(m) · planeSectorFilter(k)
  E_bind_planeLocal = Σ_k w_k · planeLocalCoupling
  promoteWeight moves fraction t of weight from src → tgt

Strong–strong planes (both endpoints in {4,5,6,7}) get C_A/C_F = 9/4.
Promotion onto those planes changes E_bind by the colour excess 5/4 — the
structural statement that SO(8) weight redistribution is no longer a no-op.

The chemistry chart still uses the scalar preferred-axis dress as the promoted
n-body second-order factor; this module is the matrix-level Tier-2 path.
"""

from __future__ import annotations

from typing import Sequence

import hqiv_lean_physics_primitives as lean

# Lean ``colourChartFilter = C_A/C_F = 9/4``.
COLOUR_FILTER = 9.0 / 4.0
COLOUR_EXCESS = COLOUR_FILTER - 1.0  # 5/4
STRONG_COMPONENTS = frozenset({4, 5, 6, 7})
N_SO8 = 28  # dim so(8) = C(8,2)


def ordered_pairs_8() -> list[tuple[int, int]]:
    """Canonical enumeration of ordered pairs i < j in Fin 8 (Lean ``OrderedPair 8``)."""
    return [(i, j) for i in range(8) for j in range(i + 1, 8)]


def plane_of_index(k: int) -> tuple[int, int]:
    """Lean ``planeOfIndex`` via the Fin 28 ≃ OrderedPair 8 enumeration."""
    pairs = ordered_pairs_8()
    return pairs[int(k) % len(pairs)]


def plane_is_strong(k: int) -> bool:
    """Lean ``planeIsStrong``: both endpoints in strongComponents {4,5,6,7}."""
    lo, hi = plane_of_index(k)
    return lo in STRONG_COMPONENTS and hi in STRONG_COMPONENTS


def plane_sector_filter(k: int) -> float:
    """Lean ``planeSectorFilter``."""
    return COLOUR_FILTER if plane_is_strong(k) else 1.0


def binding_coupling_at_shell(m: int, c: float = 1.0) -> float:
    """
    Lean ``bindingCouplingAtShell`` (generator-independent cell).

    Mirror of the spine coupling used by ``E_bind_from_network``:
    ``c · latticeSimplexCount(m) / 14`` channel scale is absorbed into the
    weight normalisation; here we expose the relative cell as ``c`` so that
    plane-local ratios are exact.
    """
    _ = m
    return float(c)


def plane_local_coupling(m: int, k: int, c: float = 1.0) -> float:
    """Lean ``planeLocalCoupling``."""
    return binding_coupling_at_shell(m, c) * plane_sector_filter(k)


def e_bind_from_network(m: int, weight: Sequence[float], c: float = 1.0) -> float:
    """Lean ``E_bind_from_network`` (abelian / generator-independent)."""
    coup = binding_coupling_at_shell(m, c)
    return sum(float(w) * coup for w in weight)


def e_bind_plane_local(m: int, weight: Sequence[float], c: float = 1.0) -> float:
    """Lean ``E_bind_planeLocal``."""
    return sum(
        float(w) * plane_local_coupling(m, k, c) for k, w in enumerate(weight)
    )


def promote_weight(
    weight: Sequence[float],
    src: int,
    tgt: int,
    t: float,
) -> list[float]:
    """Lean ``promoteWeight``: move fraction ``t`` of ``w[src]`` onto ``tgt``."""
    w = [float(x) for x in weight]
    t = max(0.0, min(1.0, float(t)))
    if src == tgt:
        return w
    delta = t * w[src]
    w[src] = (1.0 - t) * w[src]
    w[tgt] = w[tgt] + delta
    return w


def promotion_fraction(eta: float) -> float:
    """Lean ``promotionFraction``."""
    return max(0.0, min(1.0, float(eta))) * lean.STRONG_CHANNEL_FRACTION


def uniform_network_weight(scale: float = 1.0) -> list[float]:
    """Equal weight on all 28 so(8) generators."""
    return [float(scale) / N_SO8] * N_SO8


def nucleon_like_weight(scale: float = 1.0) -> list[float]:
    """
    Approximate nucleon-trace support: first three colour-singlet-ish channels.

    Diagnostic only — full composite-trace diagonal lives in Lean ``nucleonWeight``.
    """
    w = [0.0] * N_SO8
    for k in range(3):
        w[k] = float(scale) / 3.0
    return w


def plane_local_promotion_ratio(
    m: int,
    weight: Sequence[float],
    src: int,
    tgt: int,
    t: float,
    c: float = 1.0,
) -> dict[str, float]:
    """
    Abelian vs plane-local readout before/after a promotion move.

    Demonstrates ``planeLocal_promotion_delta``: promoting onto a strong plane
    changes the plane-local binding by the colour excess.
    """
    abelian0 = e_bind_from_network(m, weight, c)
    local0 = e_bind_plane_local(m, weight, c)
    w1 = promote_weight(weight, src, tgt, t)
    abelian1 = e_bind_from_network(m, w1, c)
    local1 = e_bind_plane_local(m, w1, c)
    return {
        "abelian_before": abelian0,
        "abelian_after": abelian1,
        "plane_local_before": local0,
        "plane_local_after": local1,
        "abelian_delta": abelian1 - abelian0,
        "plane_local_delta": local1 - local0,
        "src_strong": float(plane_is_strong(src)),
        "tgt_strong": float(plane_is_strong(tgt)),
        "promotion_t": float(t),
        "colour_excess": COLOUR_EXCESS,
    }


def first_strong_index() -> int:
    """Smallest So8Index whose plane is strong."""
    for k in range(N_SO8):
        if plane_is_strong(k):
            return k
    raise RuntimeError("no strong plane in so(8) enumeration")


def first_non_strong_index() -> int:
    """Smallest So8Index whose plane is not strong."""
    for k in range(N_SO8):
        if not plane_is_strong(k):
            return k
    raise RuntimeError("no non-strong plane in so(8) enumeration")

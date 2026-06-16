"""Sparse OSH carrier peaking — geometry encoding without full Hilbert support."""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Any, Literal

from hqiv_lab._scripts import ensure_scripts_on_path

ensure_scripts_on_path()
import hqiv_quantum_gate_alias_probe as _osh  # noqa: E402

SparseKet = _osh.SparseKet
REFERENCE_M_DEFAULT = _osh.REFERENCE_M_DEFAULT

sparse_basis_card = _osh.sparse_basis_card
wrap_idx = _osh.wrap_idx
harmonic_flat_index = _osh.harmonic_flat_index
decode_idx = _osh.decode_idx
hqiv_pivot_from_shells = _osh.hqiv_pivot_from_shells
causal_expand_support = _osh.causal_expand_support
apply_gate_sparse_hqiv_native = _osh.apply_gate_sparse_hqiv_native
detect_flipped_kets = _osh.detect_flipped_kets
prune_to_flipped = _osh.prune_to_flipped
sector_histogram_from_indices = _osh.sector_histogram_from_indices
local_maxima_bins = _osh.local_maxima_bins

BOHR_RADIUS_ANGSTROM = 0.529177210903
EncodingKind = Literal["mixed_radix", "contact_ell", "card"]


@dataclass(frozen=True)
class GeometryLevelSpec:
    """Discrete geometry sample (bond / angle bins)."""

    angle_level: int = 0
    bond0_level: int = 0
    bond1_level: int = 0


def mixed_radix_flat(spec: GeometryLevelSpec) -> int:
    """Injective map for three 4-level DOFs: ``la·36 + lb0·9 + lb1`` (AGENTS note)."""
    for v in (spec.angle_level, spec.bond0_level, spec.bond1_level):
        if not 0 <= v <= 3:
            raise ValueError(f"mixed-radix levels must be in 0..3, got {spec!r}")
    return spec.angle_level * 36 + spec.bond0_level * 9 + spec.bond1_level


def contact_ell_flat(distance_angstrom: float, L: int) -> int:
    """Map bond length to angular ladder slot via horizon contact weight ``1/(1+d/a₀)``."""
    if L < 1:
        raise ValueError("L must be >= 1")
    w = 1.0 / (1.0 + distance_angstrom / BOHR_RADIUS_ANGSTROM)
    ell = int(round(w * float(L)))
    return wrap_idx(L, ell * ell)


def geometry_flat_index(
    *,
    encoding: EncodingKind,
    L: int,
    spec: GeometryLevelSpec,
    bond_distance_angstrom: float | None = None,
) -> int:
    if encoding == "mixed_radix":
        return wrap_idx(L, mixed_radix_flat(spec))
    if encoding == "contact_ell":
        if bond_distance_angstrom is None:
            raise ValueError("contact_ell encoding requires bond_distance_angstrom")
        return contact_ell_flat(bond_distance_angstrom, L)
    if encoding == "card":
        return wrap_idx(L, mixed_radix_flat(spec))
    raise ValueError(f"unknown encoding {encoding!r}")


def build_sparse_carrier(
    L: int,
    flat_indices: list[int],
    *,
    amplitude: float = 1.0,
) -> list[SparseKet]:
    """One sparse ket per geometry sample — never materialize ``(L+1)²`` amplitudes."""
    seen: set[int] = set()
    out: list[SparseKet] = []
    for flat in flat_indices:
        idx = wrap_idx(L, flat)
        if idx in seen:
            continue
        seen.add(idx)
        out.append(SparseKet(idx=idx, amp=amplitude))
    return out


def shells_from_compton_list(compton_shells: list[int], L: int) -> list[int]:
    if not compton_shells:
        raise ValueError("compton_shells must be non-empty")
    if L < 1:
        raise ValueError("L must be >= 1")
    return [compton_shells[i % len(compton_shells)] for i in range(L)]


def run_carrier_peaking(
    L: int,
    shells: list[int],
    flat_indices: list[int],
    *,
    reference_m: int = REFERENCE_M_DEFAULT,
    peak_min_frac: float = 0.35,
) -> dict[str, Any]:
    """One HQIV-native OSH step + sector peaking readout on a geometry carrier."""
    card = sparse_basis_card(L)
    seed = build_sparse_carrier(L, flat_indices)
    evolved, pivot_flat = apply_gate_sparse_hqiv_native(L, seed, shells=shells, reference_m=reference_m)
    flipped = detect_flipped_kets(seed, evolved)
    pruned = prune_to_flipped(flipped, evolved)

    h16 = sector_histogram_from_indices(L, pruned, sectors=16)
    h32 = sector_histogram_from_indices(L, pruned, sectors=32)
    peaks16 = local_maxima_bins(h16, min_frac=peak_min_frac)
    peaks32 = local_maxima_bins(h32, min_frac=peak_min_frac)
    predicted32 = sorted({(2 * p) % 32 for p in peaks16} | {(2 * p + 1) % 32 for p in peaks16})
    secondary32 = [p for p in peaks32 if p not in predicted32]

    n_samples = len(flat_indices)
    n_unique = len({wrap_idx(L, f) for f in flat_indices})
    return {
        "L": L,
        "sparse_basis_card": card,
        "encoding_samples": n_samples,
        "encoding_unique": n_unique,
        "encoding_injective": n_unique == n_samples,
        "sparse_seed_len": len(seed),
        "sparse_evolved_len": len(evolved),
        "flip_count": len(flipped),
        "pruned_len": len(pruned),
        "hqiv_pivot_flat": pivot_flat,
        "hqiv_pivot_harmonic": decode_idx(L, pivot_flat).__dict__,
        "compression_vs_dense_card": card / max(len(seed), 1),
        "support_growth_factor": len(evolved) / max(len(seed), 1),
        "peaks16": peaks16,
        "peaks32": peaks32,
        "secondary32": secondary32,
        "hist16": h16,
        "hist32": h32,
    }


def enumerate_geometry_levels(n_bonds: int, *, n_levels: int = 4, include_angle: bool) -> list[GeometryLevelSpec]:
    """Cartesian product of ``n_levels`` bins per active DOF."""
    if n_levels < 2:
        raise ValueError("n_levels must be >= 2")
    specs: list[GeometryLevelSpec] = []
    if include_angle and n_bonds >= 2:
        for a in range(n_levels):
            for b0 in range(n_levels):
                for b1 in range(n_levels):
                    specs.append(GeometryLevelSpec(angle_level=a, bond0_level=b0, bond1_level=b1))
    elif n_bonds == 1:
        for b0 in range(n_levels):
            specs.append(GeometryLevelSpec(bond0_level=b0))
    else:
        for b0 in range(n_levels):
            for b1 in range(n_levels):
                specs.append(GeometryLevelSpec(bond0_level=b0, bond1_level=b1))
    return specs


def flat_indices_for_molecule_geometry(
    *,
    encoding: EncodingKind,
    L: int,
    specs: list[GeometryLevelSpec],
    bond_distances_angstrom: list[float] | None = None,
) -> list[int]:
    out: list[int] = []
    for i, spec in enumerate(specs):
        d = None if bond_distances_angstrom is None else bond_distances_angstrom[min(i, len(bond_distances_angstrom) - 1)]
        out.append(
            geometry_flat_index(
                encoding=encoding,
                L=L,
                spec=spec,
                bond_distance_angstrom=d,
            )
        )
    return out

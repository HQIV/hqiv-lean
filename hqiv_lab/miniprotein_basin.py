"""
Computed Ramachandran basin assignment — no named register profiles.

Each residue selects (φ, ψ) from proved α/γ basin pairs by:
  1. Local 8×8 carrier matrix phase alignment (octonion-slot waveform readout).
  2. Curvature-channel Ω readout vs reference shell m⋆ = 4.
  3. SS topology (coil blends use α-weighted bridges between neighbor basins).

Lean target: ``Hqiv.ProteinResearch.MiniproteinBasinReadout``.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from enum import Enum
from typing import Callable

from hqiv_lab.miniprotein_backbone import SecondaryStructure

BasinFn = Callable[[], tuple[float, float]]

REFERENCE_M = 4
CARRIER_DIM = 8


class BasinKind(str, Enum):
    ALPHA = "alpha"
    BETA = "beta"
    STRAP = "strap"
    DISTORTED_HELIX = "distorted_helix"
    EXTENDED = "extended"
    HELIX_EXIT = "helix_exit"


@dataclass(frozen=True)
class ResidueContext:
    index: int
    ss: SecondaryStructure
    upstream: SecondaryStructure | None
    downstream: SecondaryStructure | None
    helix_count: int


@dataclass(frozen=True)
class SpineContactCoupling:
    hairpin_helix_sheet_singleton: bool
    compact_helix_contacts: bool
    strap_sheet_i2_contacts: bool


def _alpha_gamma() -> tuple[float, float]:
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_lean_physics_primitives as lean

    return float(lean.ALPHA), float(lean.GAMMA)


def rho_curvature(x: float) -> float:
    alpha, _ = _alpha_gamma()
    return (1.0 / x) * (1.0 + alpha * math.log(x))


def curvature_channel_K(n: int) -> float:
    n = max(int(n), 1)
    return sum(rho_curvature(float(m + 1)) for m in range(n))


def lattice_full_mode_energy(m: int) -> float:
    return 4.0 * (m + 2) * (m + 1) * (2.0 * (m + 1) / 2.0)


def residue_compton_shell(aa: str) -> int:
    from hqiv_lab.miniprotein_osh import residue_compton_shell as _rcs

    return _rcs(aa)


def shells_for_sequence(sequence: str) -> list[int]:
    from hqiv_lab.miniprotein_osh import shells_for_sequence as _sfs

    return _sfs(sequence)


def local_omega_readout(site_shell: int, neighbor_shells: list[int]) -> float:
    """Normalized curvature readout Ω_local (reference m⋆ = 4)."""
    alpha, _ = _alpha_gamma()
    k_site = curvature_channel_K(site_shell)
    if neighbor_shells:
        k_nei = sum(curvature_channel_K(s) for s in neighbor_shells) / len(neighbor_shells)
    else:
        k_nei = 0.0
    k_ref = curvature_channel_K(REFERENCE_M)
    return (k_site + alpha * k_nei) / k_ref


def carrier_slot_weight(slot: int, phi: float, psi: float) -> float:
    """Phase weight on octonion carrier slot (α channel on φ, γ channel on ψ)."""
    alpha, gamma = _alpha_gamma()
    if slot < 5:
        return (alpha / 5.0) * math.cos((slot + 1) * phi / math.pi) ** 2
    s = slot - 5
    return (gamma / 3.0) * math.cos((s + 1) * psi / math.pi) ** 2


def matrix_waveform_score(shell: int, phi: float, psi: float) -> float:
    """Tr-like readout: mode energy × Σ_slot carrier coherence."""
    mode = lattice_full_mode_energy(shell)
    coherence = sum(carrier_slot_weight(k, phi, psi) for k in range(CARRIER_DIM))
    return mode * coherence


def _lazy_basin_table() -> dict[BasinKind, BasinFn]:
    from hqiv_lab.miniprotein_backbone import (
        ramachandran_alpha_rad,
        ramachandran_beta_rad,
        ramachandran_distorted_helix_rad,
        ramachandran_extended_rad,
        ramachandran_helix_exit_rad,
        ramachandran_strap_rad,
    )

    return {
        BasinKind.ALPHA: ramachandran_alpha_rad,
        BasinKind.BETA: ramachandran_beta_rad,
        BasinKind.STRAP: ramachandran_strap_rad,
        BasinKind.DISTORTED_HELIX: ramachandran_distorted_helix_rad,
        BasinKind.EXTENDED: ramachandran_extended_rad,
        BasinKind.HELIX_EXIT: ramachandran_helix_exit_rad,
    }


BASIN_TABLE: dict[BasinKind, BasinFn] = _lazy_basin_table()


def basin_to_dihedral(kind: BasinKind) -> tuple[float, float]:
    return BASIN_TABLE[kind]()


def basin_matrix_score(kind: BasinKind, shell: int) -> float:
    phi, psi = basin_to_dihedral(kind)
    return matrix_waveform_score(shell, phi, psi)


def prefer_compact_basins(omega: float) -> bool:
    """Compact positive-φ family when local Ω exceeds lock-in dress slot."""
    _, gamma = _alpha_gamma()
    return omega >= 1.0 + gamma / 6.0


def pick_basin_by_matrix(
    shell: int,
    omega: float,
    open_kind: BasinKind,
    compact_kind: BasinKind,
) -> BasinKind:
    """Choose open vs compact basin pair by waveform score + Ω gate."""
    if prefer_compact_basins(omega):
        return compact_kind
    s_open = basin_matrix_score(open_kind, shell)
    s_compact = basin_matrix_score(compact_kind, shell)
    return compact_kind if s_compact >= s_open else open_kind


def max_helix_run_length(ss: list[SecondaryStructure]) -> int:
    from hqiv_lab.miniprotein_contacts import max_helix_run_length as _m

    return _m(ss)


def _helix_runs(ss: list[SecondaryStructure]) -> tuple[tuple[int, int], ...]:
    runs: list[tuple[int, int]] = []
    i = 0
    while i < len(ss):
        if ss[i] != "H":
            i += 1
            continue
        j = i
        while j < len(ss) and ss[j] == "H":
            j += 1
        runs.append((i, j))
        i = j
    return tuple(runs)


def helix_segment_roles(ss: list[SecondaryStructure]) -> dict[int, str]:
    roles: dict[int, str] = {}
    for start, end in _helix_runs(ss):
        run_len = end - start
        for k in range(start, end):
            if run_len == 1:
                roles[k] = "body"
            elif k == start:
                roles[k] = "ncap"
            elif k == end - 1:
                roles[k] = "ccap"
            elif k - start == 1:
                roles[k] = "ncap"
            elif end - k == 2:
                roles[k] = "ccap"
            else:
                roles[k] = "body"
    return roles


def _neighbor_shells(sequence: str, index: int, radius: int = 2) -> list[int]:
    shells = shells_for_sequence(sequence)
    n = len(shells)
    out: list[int] = []
    for j in range(max(0, index - radius), min(n, index + radius + 1)):
        if j != index:
            out.append(shells[j])
    return out


def resolve_strand_basin(ctx: ResidueContext, sequence: str) -> BasinKind:
    shell = residue_compton_shell(sequence[ctx.index])
    omega = local_omega_readout(shell, _neighbor_shells(sequence, ctx.index))
    return pick_basin_by_matrix(shell, omega, BasinKind.BETA, BasinKind.STRAP)


def _is_helix_exit_coil(ss: list[SecondaryStructure], i: int) -> bool:
    """First coil residue immediately after a helix run (C-cap exit slot)."""
    if ss[i] != "C" or i == 0 or ss[i - 1] != "H":
        return False
    for j in range(i + 1, len(ss)):
        if ss[j] == "H":
            return False
    return True


def _has_helix_downstream(ss: list[SecondaryStructure], i: int) -> bool:
    return any(ss[j] == "H" for j in range(i + 1, len(ss)))


def _compact_helix_register_active(ss: list[SecondaryStructure]) -> bool:
    """Cage-class distorted/exit helix slots: long run with sheet context or run ≥ 6."""
    run = max_helix_run_length(ss)
    if run < 4:
        return False
    has_e = any(s == "E" for s in ss)
    has_h = any(s == "H" for s in ss)
    return run >= 6 or (has_e and has_h)


def _helix_after_strand(ss: list[SecondaryStructure], i: int) -> bool:
    for j in range(i - 1, -1, -1):
        if ss[j] == "E":
            return True
        if ss[j] == "H":
            return False
    return False


def resolve_helix_basin(
    ctx: ResidueContext,
    sequence: str,
    ss: list[SecondaryStructure],
    helix_roles: dict[int, str],
) -> BasinKind:
    shell = residue_compton_shell(sequence[ctx.index])
    omega = local_omega_readout(shell, _neighbor_shells(sequence, ctx.index))
    run_len = max_helix_run_length(ss)
    role = helix_roles.get(ctx.index, "body")
    compact_reg = _compact_helix_register_active(ss)

    if role == "ncap":
        if _helix_after_strand(ss, ctx.index):
            return BasinKind.ALPHA
        return pick_basin_by_matrix(shell, omega, BasinKind.ALPHA, BasinKind.STRAP)
    if role == "ccap":
        j = ctx.index + 1
        if j < len(ss) and ss[j] == "C":
            return BasinKind.HELIX_EXIT
        if compact_reg and run_len >= 6 and ctx.index == len(ss) - 1:
            return BasinKind.HELIX_EXIT
        if compact_reg:
            return pick_basin_by_matrix(shell, omega, BasinKind.ALPHA, BasinKind.DISTORTED_HELIX)
        return BasinKind.ALPHA

    if compact_reg and (run_len >= 4 or prefer_compact_basins(omega)):
        return pick_basin_by_matrix(shell, omega, BasinKind.ALPHA, BasinKind.DISTORTED_HELIX)
    return BasinKind.ALPHA


def blend_basin_dihedrals(
    upstream: BasinKind,
    downstream: BasinKind,
) -> tuple[float, float]:
    """α-weighted bridge between resolved neighbor basins (Lean ``ramachandranSheetHelixBridge``)."""
    alpha, _ = _alpha_gamma()
    pu = basin_to_dihedral(upstream)
    pd = basin_to_dihedral(downstream)
    return (alpha * pd[0] + (1.0 - alpha) * pu[0], alpha * pd[1] + (1.0 - alpha) * pu[1])


def _upstream_structured(ss: list[SecondaryStructure], i: int) -> SecondaryStructure | None:
    for j in range(i - 1, -1, -1):
        if ss[j] != "C":
            return ss[j]
    return None


def _downstream_structured(ss: list[SecondaryStructure], i: int) -> SecondaryStructure | None:
    for j in range(i + 1, len(ss)):
        if ss[j] != "C":
            return ss[j]
    return None


def build_residue_contexts(ss: list[SecondaryStructure]) -> tuple[ResidueContext, ...]:
    helix_count = sum(1 for s in ss if s == "H")
    return tuple(
        ResidueContext(
            index=i,
            ss=ss[i],
            upstream=_upstream_structured(ss, i),
            downstream=_downstream_structured(ss, i),
            helix_count=helix_count,
        )
        for i in range(len(ss))
    )


def _nearest_resolved_basin(
    basins: list[BasinKind | None],
    index: int,
    direction: int,
    ss: list[SecondaryStructure],
    sequence: str,
    helix_roles: dict[int, str],
) -> BasinKind:
    j = index + direction
    while 0 <= j < len(basins):
        if basins[j] is not None:
            return basins[j]  # type: ignore[return-value]
        j += direction
    # Fallback from SS letter at boundary
    ctx = build_residue_contexts(ss)[index]
    target = ctx.upstream if direction < 0 else ctx.downstream
    if target == "E":
        return resolve_strand_basin(ctx, sequence)
    if target == "H":
        return resolve_helix_basin(ctx, sequence, ss, helix_roles)
    return BasinKind.EXTENDED


def resolve_basins_for_sequence(
    sequence: str,
    ss: list[SecondaryStructure],
) -> list[BasinKind]:
    helix_roles = helix_segment_roles(ss)
    contexts = build_residue_contexts(ss)
    basins: list[BasinKind | None] = [None] * len(ss)
    for ctx in contexts:
        if ctx.ss == "E":
            basins[ctx.index] = resolve_strand_basin(ctx, sequence)
        elif ctx.ss == "H":
            basins[ctx.index] = resolve_helix_basin(ctx, sequence, ss, helix_roles)
        elif _is_helix_exit_coil(ss, ctx.index):
            basins[ctx.index] = BasinKind.HELIX_EXIT
        else:
            basins[ctx.index] = BasinKind.EXTENDED
    return [b if b is not None else BasinKind.EXTENDED for b in basins]


def dihedral_for_residue(
    ctx: ResidueContext,
    basins: list[BasinKind],
    ss: list[SecondaryStructure],
    sequence: str,
    helix_roles: dict[int, str],
) -> tuple[float, float]:
    from hqiv_lab.miniprotein_backbone import (
        coil_dihedral_from_topology,
        extended_placement_dihedral_rad,
    )

    if ctx.ss != "C":
        return basin_to_dihedral(basins[ctx.index])
    return coil_dihedral_from_topology(
        ctx.index,
        len(sequence),
        ss,
        basins,
        sequence,
        helix_roles,
        extended_placement_dihedral_rad,
    )


def dihedrals_from_spine(
    sequence: str,
    ss_map: dict[SecondaryStructure, tuple[int, ...]],
) -> tuple[tuple[float, float], ...]:
    """Assign (φ, ψ) from 8×8 readout + SS topology — no named profiles."""
    from hqiv_lab.miniprotein_contacts import ss_per_residue

    ss = ss_per_residue(sequence, ss_map)
    helix_roles = helix_segment_roles(ss)
    contexts = build_residue_contexts(ss)
    basins = resolve_basins_for_sequence(sequence, ss)
    return tuple(
        dihedral_for_residue(ctx, basins, ss, sequence, helix_roles) for ctx in contexts
    )


def _segmented_compact_register(basins: list[BasinKind], ss: list[SecondaryStructure]) -> bool:
    """Trp-cage class: long helix body + strap strands + cap/exit (not short hairpins)."""
    if max_helix_run_length(ss) < 4:
        return False
    roles = helix_segment_roles(ss)
    has_strand_strap = any(ss[i] == "E" and basins[i] == BasinKind.STRAP for i in range(len(ss)))
    has_distorted_body = any(
        ss[i] == "H" and roles.get(i) == "body" and basins[i] == BasinKind.DISTORTED_HELIX
        for i in range(len(ss))
    )
    has_cap_slot = any(
        basins[i] in (BasinKind.STRAP, BasinKind.HELIX_EXIT) for i in range(len(ss))
    )
    return has_strand_strap and has_distorted_body and has_cap_slot


def contact_coupling_from_basins(
    basins: list[BasinKind],
    ss: list[SecondaryStructure],
) -> SpineContactCoupling:
    has_e = any(s == "E" for s in ss)
    has_h = any(s == "H" for s in ss)
    segmented = _segmented_compact_register(basins, ss)
    strap_on_all_strands = all(
        basins[i] == BasinKind.STRAP for i in range(len(ss)) if ss[i] == "E"
    )
    distorted_on_helix = any(basins[i] == BasinKind.DISTORTED_HELIX for i in range(len(ss)) if ss[i] == "H")
    return SpineContactCoupling(
        hairpin_helix_sheet_singleton=max_helix_run_length(ss) <= 2 and has_e and has_h,
        compact_helix_contacts=distorted_on_helix and not segmented,
        strap_sheet_i2_contacts=strap_on_all_strands and not segmented,
    )


def contact_flags_from_spine(
    basins: list[BasinKind],
    ss: list[SecondaryStructure],
) -> dict[str, bool]:
    c = contact_coupling_from_basins(basins, ss)
    return {
        "strap_sheet_i2": c.strap_sheet_i2_contacts,
        "compact_helix": c.compact_helix_contacts,
        "hairpin_strap": c.hairpin_helix_sheet_singleton,
    }

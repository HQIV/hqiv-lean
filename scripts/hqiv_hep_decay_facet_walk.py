#!/usr/bin/env python3
"""
HEP decay walks over discharge facets (OSH-oracle sparse register).

Geometry-first channel enumeration:
  1. Parent ``HadronPatch`` ledger + sector → admissible daughter *patches* (not PDG tables).
  2. Terminal facet paths = partitions of the parent ledger into 1–3 discharge slots.
  3. Path amplitudes = √(open-flavour contact product) on the spine ledger.
  4. Sparse OSH step (``hqiv_quantum_gate_alias_probe``) dresses paths on a mixed-radix flat
     index; flip/prune keeps support practical on ~24-qubit hardware.

Lean mirrors:
  - ``Hqiv.QuantumComputing.OSHoracle`` (causal expand → gate → prune)
  - ``Hqiv.QuantumComputing.CarrierPeaking``
  - ``Hqiv.Physics.HepDecayChannelRouting`` (ledger + topology predicates)

This module does **not** simulate a full dense 2²⁴ Hilbert space; it uses explicit sparse
superposition bookkeeping—the proved OSHoracle pattern.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Any, Callable, Literal, Sequence

_SCRIPT_DIR = Path(__file__).resolve().parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))

import hqiv_hep_decay_readout as hdr
import hqiv_hep_multichannel_expansion as mc
import hqiv_hep_patch_species as hps
import hqiv_lean_physics_primitives as lean
import hqiv_quantum_gate_alias_probe as osh

ChannelTag = Literal["strong", "weak", "electromagnetic", "weak_hadron"]

# Practical hardware / simulation budget (sparse support, not dense 2^n).
DEFAULT_MAX_QUBITS = 24
DEFAULT_CARRIER_L = 11  # (L+1)² = 144 flat slots; injective mixed-radix below that.
REFERENCE_M_DEFAULT = lean.REFERENCE_M

# Signed ledger ranges for injective mixed-radix (HEP discharge cone).
_Q3_OFFSET = 9  # q3 ∈ [-9, 9]
_S_OFFSET = 3  # S ∈ [-3, 3]
_S_RANGE = 2 * _S_OFFSET + 1
_C_RANGE = 3  # charm 0..2
_B_RANGE = 3  # bottom 0..2
_A3_RANGE = 2  # 0 meson / 3 baryon → tag 0/1


@dataclass(frozen=True)
class LedgerFacetStep:
    """One discharge slot on a facet path (patch-key tagged, no nominal_id)."""

    patch_key: tuple[Any, ...]
    nominal_id: str | None  # mass lookup alias only
    ledger: mc.HadronLedger


@dataclass(frozen=True)
class FacetPath:
    """Terminal facet path: daughters sum to the parent ledger."""

    parent_id: str
    channel: ChannelTag
    steps: tuple[LedgerFacetStep, ...]
    contact_weight: float
    source: str = "facet_walk"

    @property
    def daughter_ids(self) -> tuple[str, ...]:
        out: list[str] = []
        for st in self.steps:
            if st.nominal_id is None:
                raise ValueError(f"facet path missing nominal alias: {st.patch_key}")
            out.append(st.nominal_id)
        return tuple(out)

    @property
    def path_key(self) -> tuple[Any, ...]:
        return (self.parent_id, self.channel, tuple(s.patch_key for s in self.steps))


@dataclass(frozen=True)
class FacetWalkPeak:
    flat: int
    amplitude: float
    path: FacetPath
    sector: int


@dataclass(frozen=True)
class FacetWalkResult:
    parent_id: str
    channel: ChannelTag
    L: int
    pivot_flat: int
    paths: tuple[FacetPath, ...]
    peaks: tuple[FacetWalkPeak, ...]
    support_len: int
    pruned_support_len: int
    shells: tuple[int, ...]

    def modes_payload(self) -> list[dict[str, Any]]:
        total = sum(abs(p.amplitude) for p in self.peaks) or 1.0
        out: list[dict[str, Any]] = []
        for i, peak in enumerate(self.peaks):
            out.append(
                {
                    "rank": i,
                    "daughter_ids": list(peak.path.daughter_ids),
                    "relative_branch": abs(peak.amplitude) / total,
                    "contact_weight": peak.path.contact_weight,
                    "flat": peak.flat,
                    "sector": peak.sector,
                    "source": peak.path.source,
                }
            )
        return out


def _a3_tag(a3: int) -> int:
    return 1 if a3 == 3 else 0


def _ledger_mixed_radix(ledger: mc.HadronLedger) -> int:
    """Injective flat tag for a single ledger within the HEP discharge range."""
    q = ledger.q3 + _Q3_OFFSET
    s = ledger.strangeness + _S_OFFSET
    c = max(0, min(_C_RANGE - 1, ledger.charm))
    b = max(0, min(_B_RANGE - 1, ledger.bottom))
    a = _a3_tag(ledger.a3)
    return (((q * _S_RANGE + s) * _C_RANGE + c) * _B_RANGE + b) * _A3_RANGE + a


def _mixed_radix_card() -> int:
    return (2 * _Q3_OFFSET + 1) * _S_RANGE * _C_RANGE * _B_RANGE * _A3_RANGE


def encode_path_flat(path_index: int, *, L: int, channel: ChannelTag) -> int:
    """
    Mixed-radix path index → harmonic flat slot (carrier-peaking style).

    Reserves low sectors for path ids; channel bit avoids weak/strong collision on same flat.
    """
    card = osh.sparse_basis_card(L)
    ch = 0 if channel == "strong" else 1
    base = _mixed_radix_card()
    raw = (path_index % max(base, 1)) * 2 + ch
    return osh.wrap_idx(L, raw)


def ledger_equal(a: mc.HadronLedger, b: mc.HadronLedger) -> bool:
    return (
        a.q3 == b.q3
        and a.strangeness == b.strangeness
        and a.charm == b.charm
        and a.bottom == b.bottom
        and a.a3 == b.a3
    )


def _pool_patch_entries(parent: hps.HadronPatch, channel: ChannelTag) -> list[hps.HadronPatch]:
    pool_ids = (
        hps.strong_daughter_pool_for(parent)
        if channel == "strong"
        else hps.weak_daughter_pool_for(parent)
    )
    seen: set[tuple[Any, ...]] = set()
    out: list[hps.HadronPatch] = []
    for sid in pool_ids:
        p = hps.patch_from_species_id(sid)
        if p is None:
            continue
        key = p.patch_key()
        if key in seen:
            continue
        seen.add(key)
        out.append(p)
    return out


def _topology_ok(parent_id: str, channel: ChannelTag, daughter_ids: Sequence[str]) -> bool:
    if channel == "strong":
        return mc._light_strong_channel_allowed(parent_id, daughter_ids) or (
            mc._strong_curvature_allowed(parent_id, daughter_ids)
            and mc._ds_strong_sparse(parent_id, daughter_ids)
        )
    return mc._weak_channel_allowed(parent_id, daughter_ids)


def _contact_weight(parent_id: str, channel: ChannelTag, daughter_ids: Sequence[str]) -> float:
    return mc.open_flavour_topology_weight(parent_id, channel, daughter_ids)


def _steps_from_ids(
    parent_id: str,
    channel: ChannelTag,
    daughter_ids: Sequence[str],
) -> tuple[LedgerFacetStep, ...] | None:
    steps: list[LedgerFacetStep] = []
    for did in daughter_ids:
        p = hps.patch_from_species_id(did)
        if p is None:
            return None
        steps.append(
            LedgerFacetStep(
                patch_key=p.patch_key(),
                nominal_id=p.nominal_id or did,
                ledger=p.ledger,
            )
        )
    parent = hps.patch_from_species_id(parent_id)
    if parent is None:
        return None
    if channel == "strong":
        total = mc._ledger_sum([s.ledger for s in steps])
        if total.q3 != parent.ledger.q3 or total.a3 != parent.ledger.a3:
            return None
    if not _topology_ok(parent_id, channel, daughter_ids):
        return None
    return tuple(steps)


def _combos_of_patches(
    patches: Sequence[hps.HadronPatch],
    n: int,
) -> list[tuple[hps.HadronPatch, ...]]:
    """Sorted combinations with replacement (small pools only)."""
    if n <= 0:
        return []
    out: list[tuple[hps.HadronPatch, ...]] = []

    def rec(start: int, acc: list[hps.HadronPatch]) -> None:
        if len(acc) == n:
            out.append(tuple(acc))
            return
        for j in range(start, len(patches)):
            acc.append(patches[j])
            rec(j, acc)
            acc.pop()

    rec(0, [])
    return out


def enumerate_facet_paths(
    parent_id: str,
    channel: ChannelTag,
    *,
    n_body_min: int = 1,
    n_body_max: int = 3,
    max_paths: int = 256,
) -> list[FacetPath]:
    """
    Ledger-first terminal facet paths: daughter patches sum to parent ledger.

    No itertools over string tables — iterates unique ``HadronPatch`` entries from the
    property daughter pool, then filters by topology + contact ledger.
    """
    parent = hps.patch_from_species_id(parent_id)
    if parent is None:
        return []
    pool = _pool_patch_entries(parent, channel)
    if not pool:
        return []

    paths: list[FacetPath] = []
    seen: set[tuple[Any, ...]] = set()
    for n in range(n_body_min, n_body_max + 1):
        for combo in _combos_of_patches(pool, n):
            daughter_ids = tuple(p.nominal_id or "?" for p in combo)
            if "?" in daughter_ids:
                continue
            steps = _steps_from_ids(parent_id, channel, daughter_ids)
            if steps is None:
                continue
            key = (parent_id, channel, tuple(s.patch_key for s in steps))
            if key in seen:
                continue
            seen.add(key)
            w = _contact_weight(parent_id, channel, daughter_ids)
            paths.append(
                FacetPath(
                    parent_id=parent_id,
                    channel=channel,
                    steps=steps,
                    contact_weight=w,
                )
            )
            if len(paths) >= max_paths:
                return paths
    return paths


def _shells_for_parent(parent: hps.HadronPatch) -> tuple[int, ...]:
    """TUFT shell tags for HQIV pivot (excitation ladder)."""
    e = max(0, parent.excitation)
    if parent.is_decuplet_baryon:
        return (4, 3, 1) if e <= 1 else (4, 3, e)
    if parent.is_hidden_quarkonium:
        return (4, 3, 2)
    if parent.is_open_charm or parent.is_open_bottom:
        return (4, 3, max(1, e))
    return (4, 3, max(0, e))


def _seed_sparse_register(
    paths: Sequence[FacetPath],
    *,
    L: int,
    channel: ChannelTag,
) -> list[osh.SparseKet]:
    reg: list[osh.SparseKet] = []
    for i, path in enumerate(paths):
        flat = encode_path_flat(i, L=L, channel=channel)
        amp = math.sqrt(max(path.contact_weight, 0.0))
        reg.append(osh.SparseKet(idx=flat, amp=amp))
    return reg


def _merge_kets(reg: list[osh.SparseKet]) -> list[osh.SparseKet]:
    amps: dict[int, float] = {}
    for ket in reg:
        amps[ket.idx] = amps.get(ket.idx, 0.0) + ket.amp
    return [osh.SparseKet(idx=i, amp=a) for i, a in sorted(amps.items())]


def run_facet_walk(
    parent_id: str,
    channel: ChannelTag,
    *,
    L: int = DEFAULT_CARRIER_L,
    max_qubits: int = DEFAULT_MAX_QUBITS,
    osh_steps: int = 1,
    prune: bool = False,
    min_amp_frac: float = 1e-6,
) -> FacetWalkResult | None:
    """
  Sparse OSH facet walk on terminal discharge paths.

  ``max_qubits`` guards path count (2^24 dense is never built; support stays ``O(paths)``).
    """
    parent = hps.patch_from_species_id(parent_id)
    if parent is None:
        return None

    paths = tuple(enumerate_facet_paths(parent_id, channel))
    if not paths:
        return None
    if len(paths) > (1 << min(max_qubits, 20)):
        raise ValueError(
            f"facet path count {len(paths)} exceeds practical budget for {parent_id} {channel}"
        )

    shells = _shells_for_parent(parent)
    reg = _seed_sparse_register(paths, L=L, channel=channel)
    pivot = 0
    for _ in range(max(0, osh_steps)):
        before = reg
        reg, pivot = osh.apply_gate_sparse_hqiv_native(
            L, reg, shells=list(shells), reference_m=REFERENCE_M_DEFAULT
        )
        if prune:
            flipped = osh.detect_flipped_kets(before, reg)
            pruned = osh.prune_to_flipped(flipped, reg)
            if pruned:
                reg = pruned

    reg = _merge_kets(reg)

    # Read dressed amplitudes on seed flats (path index → flat is stable).
    peaks: list[FacetWalkPeak] = []
    for i, path in enumerate(paths):
        flat = encode_path_flat(i, L=L, channel=channel)
        amp = sum(k.amp for k in reg if k.idx == flat)
        if abs(amp) < min_amp_frac:
            continue
        card = osh.sparse_basis_card(L)
        sector = int(math.floor((flat / card) * 32)) % 32
        peaks.append(
            FacetWalkPeak(flat=flat, amplitude=amp, path=path, sector=sector)
        )
    peaks.sort(key=lambda p: abs(p.amplitude), reverse=True)

    return FacetWalkResult(
        parent_id=parent_id,
        channel=channel,
        L=L,
        pivot_flat=pivot,
        paths=paths,
        peaks=tuple(peaks),
        support_len=len(reg),
        pruned_support_len=len(reg),
        shells=shells,
    )


def facet_walk_modes(
    parent_id: str,
    channel: ChannelTag,
    **kwargs: Any,
) -> list[dict[str, Any]]:
    """Convenience: peaks as normalized branch rows."""
    res = run_facet_walk(parent_id, channel, **kwargs)
    if res is None:
        return []
    return res.modes_payload()


def compare_with_multichannel(
    parent_id: str,
    channel: ChannelTag,
) -> dict[str, Any]:
    """Diagnostic: facet-walk peaks vs programmatic multichannel keys."""
    walk = run_facet_walk(parent_id, channel)
    mc_keys: set[tuple[str, ...]] = set()
    parent = hps.patch_from_species_id(parent_id)
    if parent is not None:

        def mass_of(did: str) -> float:
            return 1.0  # kinematic filter skipped for topology compare

        for gm in mc.generate_multichannel_modes(
            parent_id, parent_mass_mev=1e6, mass_of=mass_of
        ):
            if gm.channel == channel:
                mc_keys.add(tuple(sorted(gm.daughter_ids)))

    walk_keys = set()
    if walk is not None:
        walk_keys = {tuple(sorted(p.daughter_ids)) for p in walk.paths}

    return {
        "parent_id": parent_id,
        "channel": channel,
        "facet_path_count": len(walk.paths) if walk else 0,
        "multichannel_count": len(mc_keys),
        "only_facet": sorted(walk_keys - mc_keys),
        "only_multichannel": sorted(mc_keys - walk_keys),
        "intersection": sorted(walk_keys & mc_keys),
        "peaks": walk.modes_payload() if walk else [],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="HEP decay facet walk (OSH sparse register)")
    parser.add_argument("parent_id", help="comparison alias e.g. lambda, K_plus, rho_zero")
    parser.add_argument(
        "--channel",
        choices=("strong", "weak"),
        default="weak",
    )
    parser.add_argument("--L", type=int, default=DEFAULT_CARRIER_L)
    parser.add_argument("--osh-steps", type=int, default=1)
    parser.add_argument("--compare", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    if args.compare:
        payload = compare_with_multichannel(args.parent_id, args.channel)
    else:
        res = run_facet_walk(
            args.parent_id,
            args.channel,
            L=args.L,
            osh_steps=args.osh_steps,
        )
        payload = {
            "parent_id": args.parent_id,
            "channel": args.channel,
            "result": None if res is None else {
                "L": res.L,
                "pivot_flat": res.pivot_flat,
                "shells": list(res.shells),
                "support_len": res.support_len,
                "path_count": len(res.paths),
                "modes": res.modes_payload(),
            },
        }

    if args.json:
        print(json.dumps(payload, indent=2))
    else:
        print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()

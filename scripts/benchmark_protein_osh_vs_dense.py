#!/usr/bin/env python3
"""
Side-by-side benchmark inspired by:
  - Hqiv/ProteinResearch/AdditiveFieldAndTorque.lean
  - Hqiv/QuantumComputing/OSHoracle.lean

Goal
----
Compare a "traditional dense" update against an OSH-style sparse update to show
whether sparse bookkeeping is faster (or not) for a given workload.

This is a computational benchmark harness, not a physics claim.
"""

from __future__ import annotations

from dataclasses import dataclass
import math
import random
import statistics
import time
from typing import Dict, List, Sequence, Tuple


Coord3 = Tuple[float, float, float]


def available_modes(m: int) -> float:
    # From OctonionicLightCone.lean: available_modes = 4*(m+2)*(m+1)
    return 4.0 * (m + 2) * (m + 1)


def phi_of_shell(m: int) -> float:
    # From AuxiliaryField.lean closed form: phi(m) = 2*(m+1)
    return 2.0 * (m + 1)


def lattice_full_mode_energy(m: int) -> float:
    # From AtomEnergyOSHoracleBridge.lean:
    # latticeFullModeEnergy = available_modes * (phi_of_shell / 2)
    return available_modes(m) * (phi_of_shell(m) / 2.0)


def additive_field_kernel(i: int, j: int, shells: Sequence[int], pos: Sequence[Coord3]) -> float:
    # Mirrors AdditiveFieldAndTorque.lean placeholder kernel.
    dx = pos[i][0] - pos[j][0]
    dy = pos[i][1] - pos[j][1]
    dz = pos[i][2] - pos[j][2]
    r_proxy = abs(dx) + abs(dy) + abs(dz) + 1.0
    return lattice_full_mode_energy(shells[j]) / r_proxy


def should_update_torque(step: int, update_every: int = 10) -> bool:
    return True if update_every == 0 else (step % update_every == 0)


def init_problem(n_sites: int, active_fraction: float, seed: int) -> Tuple[List[int], List[Coord3], List[float], List[float]]:
    rng = random.Random(seed)
    shells = [rng.randint(0, 12) for _ in range(n_sites)]
    pos = [(rng.uniform(-5, 5), rng.uniform(-5, 5), rng.uniform(-5, 5)) for _ in range(n_sites)]

    # "Dense" amplitude/state channel: mostly zeros if low active fraction.
    amp = [0.0] * n_sites
    n_active = max(1, int(n_sites * active_fraction))
    for idx in rng.sample(range(n_sites), n_active):
        amp[idx] = rng.uniform(0.1, 1.0)

    orientation = [rng.uniform(-1.0, 1.0) for _ in range(n_sites)]
    return shells, pos, amp, orientation


def dense_step(
    step: int,
    shells: Sequence[int],
    pos: Sequence[Coord3],
    orientation: Sequence[float],
    amp: List[float],
    torque_cache: List[float],
    update_every: int,
) -> None:
    n = len(amp)

    # Traditional full additive field: O(n^2)
    field = [0.0] * n
    for i in range(n):
        s = 0.0
        for j in range(n):
            s += additive_field_kernel(i, j, shells, pos)
        field[i] = s

    if should_update_torque(step, update_every):
        for i in range(n):
            torque_cache[i] = orientation[i] * field[i]

    # Dense causal-like update (self + predecessor), then energy-side scaling.
    # This is a deterministic stand-in for dense reconstruction + gate action.
    new_amp = [0.0] * n
    for i in range(n):
        expanded = amp[i] + amp[(i - 1) % n]
        new_amp[i] = expanded * (1.0 + 1e-6 * torque_cache[i])

    amp[:] = new_amp


def sparse_from_dense(amp: Sequence[float], eps: float = 1e-12) -> Dict[int, float]:
    return {i: a for i, a in enumerate(amp) if abs(a) > eps}


def sparse_step(
    step: int,
    shells: Sequence[int],
    pos: Sequence[Coord3],
    orientation: Sequence[float],
    sparse: Dict[int, float],
    torque_cache: Dict[int, float],
    n_basis: int,
    update_every: int,
) -> Dict[int, float]:
    active = list(sparse.keys())
    if not active:
        return {}

    # OSH-style local additive field over active support: O(k^2)
    field: Dict[int, float] = {}
    for i in active:
        s = 0.0
        for j in active:
            s += additive_field_kernel(i, j, shells, pos)
        field[i] = s

    if should_update_torque(step, update_every):
        for i in active:
            torque_cache[i] = orientation[i] * field[i]

    # causalExpandSupport + denseOfSparse-style accumulation
    expanded: List[Tuple[int, float]] = []
    for i, a in sparse.items():
        expanded.append((i % n_basis, a))
        expanded.append(((i + 1) % n_basis, a))

    accum: Dict[int, float] = {}
    for i, a in expanded:
        accum[i] = accum.get(i, 0.0) + a

    # Gate-like update with torque side-channel.
    after: Dict[int, float] = {}
    for i, a in accum.items():
        t = torque_cache.get(i, 0.0)
        after[i] = a * (1.0 + 1e-6 * t)

    # detectFlippedKets + pruneToFlipped analogue.
    before_idx = set(sparse.keys())
    after_idx = set(after.keys())
    flipped = (before_idx - after_idx) | (after_idx - before_idx)
    if not flipped:
        # Keep everything if no support flip happened.
        return after
    return {i: a for i, a in after.items() if i in flipped}


@dataclass
class BenchCase:
    n_sites: int
    steps: int
    active_fraction: float
    update_every: int
    runs: int


def run_case(case: BenchCase, seed: int) -> Dict[str, float]:
    dense_times_ms: List[float] = []
    sparse_times_ms: List[float] = []
    final_active_counts: List[int] = []

    for r in range(case.runs):
        shells, pos, amp0, orientation = init_problem(
            n_sites=case.n_sites,
            active_fraction=case.active_fraction,
            seed=seed + r,
        )

        # Dense path
        amp_dense = amp0[:]
        dense_torque = [0.0] * case.n_sites
        t0 = time.perf_counter()
        for step in range(case.steps):
            dense_step(
                step=step,
                shells=shells,
                pos=pos,
                orientation=orientation,
                amp=amp_dense,
                torque_cache=dense_torque,
                update_every=case.update_every,
            )
        t1 = time.perf_counter()
        dense_times_ms.append((t1 - t0) * 1000.0)

        # OSH-style sparse path
        sparse = sparse_from_dense(amp0)
        sparse_torque: Dict[int, float] = {}
        s0 = time.perf_counter()
        for step in range(case.steps):
            sparse = sparse_step(
                step=step,
                shells=shells,
                pos=pos,
                orientation=orientation,
                sparse=sparse,
                torque_cache=sparse_torque,
                n_basis=case.n_sites,
                update_every=case.update_every,
            )
        s1 = time.perf_counter()
        sparse_times_ms.append((s1 - s0) * 1000.0)
        final_active_counts.append(len(sparse))

    dense_med = statistics.median(dense_times_ms)
    sparse_med = statistics.median(sparse_times_ms)
    speedup = dense_med / sparse_med if sparse_med > 0 else math.inf

    return {
        "n_sites": float(case.n_sites),
        "steps": float(case.steps),
        "active_fraction": case.active_fraction,
        "update_every": float(case.update_every),
        "runs": float(case.runs),
        "dense_median_ms": dense_med,
        "sparse_median_ms": sparse_med,
        "dense_vs_sparse_speedup": speedup,
        "final_active_median": statistics.median(final_active_counts),
    }


def main() -> None:
    # You can tune these to probe where sparse helps or hurts.
    cases = [
        BenchCase(n_sites=192, steps=24, active_fraction=0.05, update_every=10, runs=4),
        BenchCase(n_sites=192, steps=24, active_fraction=0.20, update_every=10, runs=4),
        BenchCase(n_sites=384, steps=20, active_fraction=0.05, update_every=10, runs=4),
        BenchCase(n_sites=384, steps=20, active_fraction=0.30, update_every=10, runs=4),
    ]

    print("Protein-style benchmark: traditional dense vs OSH-style sparse")
    print("=" * 78)
    print(
        "n_sites  steps  active  dense_ms  sparse_ms  speedup(dense/sparse)  final_active_med"
    )
    print("-" * 78)

    for i, case in enumerate(cases):
        out = run_case(case, seed=42 + i * 1000)
        print(
            f"{int(out['n_sites']):7d}  "
            f"{int(out['steps']):5d}  "
            f"{out['active_fraction']:.2f}   "
            f"{out['dense_median_ms']:8.2f}  "
            f"{out['sparse_median_ms']:9.2f}  "
            f"{out['dense_vs_sparse_speedup']:22.2f}  "
            f"{int(out['final_active_median']):16d}"
        )

    print("\nInterpretation:")
    print("- speedup > 1.0  => OSH-style sparse path is faster")
    print("- speedup < 1.0  => dense path is faster")
    print("- Expect sparse advantage mainly when active support remains small.")


if __name__ == "__main__":
    main()


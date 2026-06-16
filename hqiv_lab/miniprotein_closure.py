"""Apply tertiary Cα contact closure (fast Jacobi path)."""

from __future__ import annotations

import math

from hqiv_lab.miniprotein_backbone import Vec3
from hqiv_lab.miniprotein_contacts import TertiaryContact

_CompiledContact = tuple[int, int, float, float]


def _compile_contacts(
    contacts: tuple[TertiaryContact, ...],
    step_fraction: float,
) -> tuple[_CompiledContact, ...]:
    return tuple(
        (c.i, c.j, c.target_angstrom, step_fraction * 0.5) for c in contacts
    )


def apply_tertiary_contact_closure(
    ca: list[Vec3],
    contacts: tuple[TertiaryContact, ...],
    *,
    steps: int = 40,
    step_fraction: float = 0.25,
    tolerance_angstrom: float = 1e-4,
) -> list[Vec3]:
    """
    Jacobi-style relaxation toward sequence-derived tertiary contact targets.

    Pre-compiles contacts and exits early when max pair error < tolerance.
    """
    if len(ca) < 2 or not contacts:
        return ca
    compiled = _compile_contacts(contacts, step_fraction)
    out: list[list[float]] = [list(p) for p in ca]
    n = len(out)
    disp = [0.0] * (3 * n)
    weight = [0.0] * n

    for _ in range(steps):
        max_delta = 0.0
        for k in range(3 * n):
            disp[k] = 0.0
        for k in range(n):
            weight[k] = 0.0

        for i, j, target, half_step in compiled:
            vx = out[j][0] - out[i][0]
            vy = out[j][1] - out[i][1]
            vz = out[j][2] - out[i][2]
            dist_sq = vx * vx + vy * vy + vz * vz
            if dist_sq < 1e-16:
                continue
            dist = math.sqrt(dist_sq)
            delta = dist - target
            ad = abs(delta)
            if ad < tolerance_angstrom:
                continue
            if ad > max_delta:
                max_delta = ad
            scale = (delta / dist) * half_step
            mx, my, mz = vx * scale, vy * scale, vz * scale
            disp[3 * i] += mx
            disp[3 * i + 1] += my
            disp[3 * i + 2] += mz
            disp[3 * j] -= mx
            disp[3 * j + 1] -= my
            disp[3 * j + 2] -= mz
            w = half_step * 2.0
            weight[i] += w
            weight[j] += w

        if max_delta < tolerance_angstrom:
            break

        for idx in range(n):
            w = weight[idx]
            if w <= 0.0:
                continue
            base = 3 * idx
            inv = 1.0 / w
            out[idx][0] += disp[base] * inv
            out[idx][1] += disp[base + 1] * inv
            out[idx][2] += disp[base + 2] * inv

    return [tuple(p) for p in out]


def default_structure_step_fraction() -> float:
    """Jacobi step fraction (Lean ``defaultClosureStepFraction`` = 1/4)."""
    return 1.0 / 4.0


def hydrophobic_step_fraction(structure_fraction: float | None = None) -> float:
    """Gentler hydrophobic pass: ``step · (1 − α/3)`` (α = 3/5 → 4/5 · step)."""
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_lean_physics_primitives as lean

    base = default_structure_step_fraction() if structure_fraction is None else structure_fraction
    return base * (1.0 - lean.ALPHA / 3.0)


def apply_staged_tertiary_contact_closure(
    ca: list[Vec3],
    contacts: tuple[TertiaryContact, ...],
    *,
    structure_steps: int = 40,
    structure_step_fraction: float | None = None,
    hydrophobic_steps: int = 60,
    terminus_steps: int = 40,
    tolerance_angstrom: float = 1e-4,
) -> list[Vec3]:
    """
    Three-pass Jacobi closure — locality order:

    1. SS register (helix, sheet, helix–sheet packing)
    2. Sequence hydrophobic pairs (gentler ``(1 − α/3)`` step)
    3. Compact terminus cap alone (global end-to-end)
    """
    from hqiv_lab.miniprotein_contacts import partition_tertiary_contacts_staged

    structure, hydrophobic, terminus = partition_tertiary_contacts_staged(contacts)
    sf = default_structure_step_fraction() if structure_step_fraction is None else structure_step_fraction
    hf = hydrophobic_step_fraction(sf)
    out = apply_tertiary_contact_closure(
        ca,
        structure,
        steps=structure_steps,
        step_fraction=sf,
        tolerance_angstrom=tolerance_angstrom,
    )
    if hydrophobic:
        out = apply_tertiary_contact_closure(
            out,
            hydrophobic,
            steps=hydrophobic_steps,
            step_fraction=hf,
            tolerance_angstrom=tolerance_angstrom,
        )
    if terminus:
        out = apply_tertiary_contact_closure(
            out,
            terminus,
            steps=terminus_steps,
            step_fraction=sf,
            tolerance_angstrom=tolerance_angstrom,
        )
    return out


def apply_two_pass_tertiary_contact_closure(
    ca: list[Vec3],
    contacts: tuple[TertiaryContact, ...],
    *,
    structure_steps: int = 40,
    structure_step_fraction: float = 0.25,
    burial_steps: int = 60,
    burial_step_fraction: float = 0.2,
    tolerance_angstrom: float = 1e-4,
) -> list[Vec3]:
    """
    Legacy alias: structure pass then combined burial (hydrophobic + terminus).

    Prefer ``apply_staged_tertiary_contact_closure`` for terminus isolation.
    """
    return apply_staged_tertiary_contact_closure(
        ca,
        contacts,
        structure_steps=structure_steps,
        structure_step_fraction=structure_step_fraction,
        hydrophobic_steps=burial_steps,
        terminus_steps=burial_steps,
        tolerance_angstrom=tolerance_angstrom,
    )

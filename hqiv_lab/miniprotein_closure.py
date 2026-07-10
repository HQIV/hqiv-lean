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


def apply_nerf_contact_refinement(
    sequence: str,
    dihedrals: tuple[tuple[float, float], ...],
    contacts: tuple[TertiaryContact, ...],
    *,
    rounds: int | None = None,
    initial_delta_rad: float | None = None,
    min_delta_rad: float = 0.012,
    ss: list[str] | None = None,
    curvature_weights: bool = False,
    macro_ricci_soft: bool = False,
    temperature_k: float | None = None,
    atom_sites: bool = False,
) -> tuple[list[Vec3], tuple[tuple[float, float], ...]]:
    """
    Contact closure via NeRF-consistent φ/ψ refinement (no unconstrained Cα Jacobi).

    Minimizes squared tertiary contact violations by coordinate search on dihedrals.
    """
    from hqiv_lab.miniprotein_backbone import place_backbone_atom_state, place_ca_trace

    if not contacts:
        ca = place_ca_trace(sequence, dihedrals)
        return ca, dihedrals

    def _score_sse(trial_dihedrals: tuple[tuple[float, float], ...]) -> float:
        if atom_sites:
            from hqiv_lab.miniprotein_osh import (
                atom_contact_sse,
                prepare_atom_contacts,
            )

            state = place_backbone_atom_state(sequence, trial_dihedrals)
            atom_c = prepare_atom_contacts(
                contacts, state, temperature_k=temperature_k
            )
            return atom_contact_sse(state, atom_c)
        ca = place_ca_trace(sequence, trial_dihedrals)
        weights = _curvature_weights_for_sse(
            sequence,
            ca,
            contacts,
            ss,
            curvature_weights,
            temperature_k,
            macro_ricci_soft=macro_ricci_soft,
        )
        return _contact_sse(
            sequence,
            ca,
            contacts,
            weights,
            ss=ss,
            macro_ricci_soft=macro_ricci_soft,
        )

    n = len(sequence)
    if rounds is None:
        rounds = 12 if n <= 8 else 6
    if initial_delta_rad is None:
        initial_delta_rad = 0.4 if n <= 8 else 0.25
    # Register piezo: open/low-occupancy contacts get larger thermal step size.
    from hqiv_lab.peptide_shell_dress import staged_pass_piezo_step_dress

    initial_delta_rad = float(initial_delta_rad) * staged_pass_piezo_step_dress(
        contacts, temperature_k=temperature_k
    )

    best = list(dihedrals)
    best_ca = place_ca_trace(sequence, tuple(best))
    best_sse = _score_sse(tuple(best))
    delta = initial_delta_rad
    indices = tuple(range(n))

    for _ in range(rounds):
        improved = False
        for i in indices:
            for dphi in (-delta, 0.0, delta):
                for dpsi in (-delta, 0.0, delta):
                    if dphi == 0.0 and dpsi == 0.0:
                        continue
                    trial = best[:]
                    phi_i, psi_i = trial[i]
                    trial[i] = (phi_i + dphi, psi_i + dpsi)
                    sse = _score_sse(tuple(trial))
                    if sse < best_sse:
                        best_sse = sse
                        best = trial
                        best_ca = place_ca_trace(sequence, tuple(best))
                        improved = True
        if not improved:
            delta *= 0.5
        if delta < min_delta_rad:
            break

    return best_ca, tuple(best)


def apply_staged_nerf_contact_refinement(
    sequence: str,
    dihedrals: tuple[tuple[float, float], ...],
    contacts: tuple[TertiaryContact, ...],
    *,
    structure_rounds: int = 8,
    hydrophobic_rounds: int = 8,
    terminus_rounds: int = 10,
    final_rounds: int = 10,
    initial_delta_rad: float | None = None,
    min_delta_rad: float = 0.012,
    ss: list[str] | None = None,
    curvature_weights: bool = False,
    macro_ricci_soft: bool = False,
    temperature_k: float | None = None,
    atom_sites: bool = False,
) -> tuple[list[Vec3], tuple[tuple[float, float], ...]]:
    """
    NeRF φ/ψ refinement in staged contact passes (Lean ``tertiaryContactPass`` order).

    Structure register (helix/sheet packing) → hydrophobic burial → terminus cap →
    full graph polish.  Intended for compact miniproteins (Trp-cage class) where
    single-pass coordinate search stalls in local contact minima.
    """
    from hqiv_lab.miniprotein_contacts import partition_tertiary_contacts_staged
    from hqiv_lab.miniprotein_backbone import place_ca_trace

    if not contacts:
        ca = place_ca_trace(sequence, dihedrals)
        return ca, dihedrals

    structure, hydrophobic, terminus = partition_tertiary_contacts_staged(contacts)
    best = list(dihedrals)
    best_ca = place_ca_trace(sequence, tuple(best))
    kwargs: dict[str, float | bool | list[str] | None] = {
        "min_delta_rad": min_delta_rad,
        "ss": ss,
        "curvature_weights": curvature_weights,
        "macro_ricci_soft": macro_ricci_soft,
        "temperature_k": temperature_k,
        "atom_sites": atom_sites,
    }
    if initial_delta_rad is not None:
        kwargs["initial_delta_rad"] = initial_delta_rad
    kwargs.pop("temperature_k", None)
    if temperature_k is not None:
        kwargs["temperature_k"] = temperature_k
    if atom_sites and len(sequence) >= 8:
        kwargs["atom_sites"] = True

    for stage, rounds in (
        (structure, structure_rounds),
        (hydrophobic, hydrophobic_rounds),
        (terminus, terminus_rounds),
        (contacts, final_rounds),
    ):
        if not stage or rounds <= 0:
            continue
        stage_kw = dict(kwargs)
        # System Ricci dresses the whole graph on the final polish pass only.
        if stage is not contacts:
            stage_kw["macro_ricci_soft"] = False
        best_ca, best = apply_nerf_contact_refinement(
            sequence,
            tuple(best),
            stage,
            rounds=rounds,
            **stage_kw,
        )

    return best_ca, tuple(best)


def _curvature_weights_for_sse(
    sequence: str,
    ca: list[Vec3],
    contacts: tuple[TertiaryContact, ...],
    ss: list[str] | None,
    enabled: bool,
    temperature_k: float | None = None,
    *,
    macro_ricci_soft: bool = False,
) -> tuple[float, ...] | None:
    from hqiv_lab.macro_ricci_flow import (
        macro_ricci_contact_sse_multiplier,
    )
    from hqiv_lab.residue_site_physics import macro_ricci_system_dress_amplitude as _sys_amp

    base: list[float] | None = None
    if enabled and contacts:
        from hqiv_lab.protein_solvent_phase import contact_curvature_weights

        base = list(contact_curvature_weights(ca, contacts, ss, temperature_k=temperature_k))
    elif macro_ricci_soft and contacts:
        base = [1.0] * len(contacts)

    if not macro_ricci_soft or not contacts or base is None:
        return tuple(base) if base is not None else None

    # Curvature weights already carry B_eff; macro Ricci acts via soft targets only.
    if enabled:
        return tuple(base)

    system_amp = _sys_amp(sequence, contacts, ca, ss)
    out = base[:]
    for k, c in enumerate(contacts):
        out[k] *= macro_ricci_contact_sse_multiplier(
            sequence, ca, c, ss, contacts, system_amp=system_amp
        )
    return tuple(out)


def _contact_sse(
    sequence: str,
    ca: list[Vec3],
    contacts: tuple[TertiaryContact, ...],
    weights: tuple[float, ...] | None = None,
    *,
    ss: list[str] | None = None,
    macro_ricci_soft: bool = False,
) -> float:
    from hqiv_lab.macro_ricci_flow import macro_ricci_soft_contact_target
    from hqiv_lab.residue_site_physics import macro_ricci_system_dress_amplitude

    system_amp = (
        macro_ricci_system_dress_amplitude(sequence, contacts, ca, ss)
        if macro_ricci_soft
        else 0.0
    )
    sse = 0.0
    for k, c in enumerate(contacts):
        vx = ca[c.j][0] - ca[c.i][0]
        vy = ca[c.j][1] - ca[c.i][1]
        vz = ca[c.j][2] - ca[c.i][2]
        dist = math.sqrt(vx * vx + vy * vy + vz * vz)
        target = (
            macro_ricci_soft_contact_target(
                c, sequence, ca, ss, contacts, system_amp=system_amp
            )
            if macro_ricci_soft
            else c.target_angstrom
        )
        delta = dist - target
        w = 1.0 if weights is None else weights[k]
        sse += w * delta * delta
    return sse


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
    Four-pass Jacobi closure — locality order:

    1. SS register (helix, sheet, helix–sheet packing)
    2. Sequence hydrophobic pairs (gentler ``(1 − α/3)`` step; no E↔H cross pairs)
    3. SS register refresh (undo hydrophobic collapse of sheet–helix register)
    4. Compact terminus cap alone (global end-to-end)
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
        out = apply_tertiary_contact_closure(
            out,
            structure,
            steps=max(structure_steps // 2, 20),
            step_fraction=sf,
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

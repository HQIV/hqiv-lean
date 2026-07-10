"""
Macro Ricci flow on protein tertiary contacts (soft NeRF closure).

Lean mirror: ``Hqiv.QuantumChemistry.MacroRicciFlowDynamics``.

All dress policy uses spine-derived α, γ, strong-channel fraction, directional ρ,
closure pass order, and homogeneous feedback — no fitted kind-weight tables.
"""

from __future__ import annotations

from hqiv_lab.miniprotein_backbone import Vec3
from hqiv_lab.miniprotein_contacts import TertiaryContact


def open_beta_register_discriminant_angstrom() -> float:
    """
    Register discriminant between open vs strap β i+2 targets.

    ``α · |d_open − d_strap| / 2`` from peptide geometry witnesses.
    """
    from hqiv_lab._scripts import ensure_scripts_on_path
    from hqiv_lab.peptide_geometry import (
        sheet_ca_i_i2_distance_angstrom,
        sheet_ca_i_i2_strap_distance_angstrom,
    )

    ensure_scripts_on_path()
    import hqiv_lean_physics_primitives as lean

    open_d = sheet_ca_i_i2_distance_angstrom()
    strap_d = sheet_ca_i_i2_strap_distance_angstrom()
    return lean.ALPHA * abs(open_d - strap_d) / 2.0


def is_open_beta_sheet_i2_contact(contact: TertiaryContact) -> bool:
    """True when the contact target is the open β i+2 chord (not strap register)."""
    if contact.kind != "sheet_i2":
        return False
    from hqiv_lab.peptide_geometry import sheet_ca_i_i2_distance_angstrom

    open_d = sheet_ca_i_i2_distance_angstrom()
    return abs(contact.target_angstrom - open_d) < open_beta_register_discriminant_angstrom()


def macro_ricci_stacked_line_breathing_scale() -> float:
    """Lean ``macroRicciStackedLineBreathingScale``."""
    from hqiv_lab.peptide_geometry import (
        beta_strand_stacking_angle_rad,
        stacked_line_outside_curvature_scale,
    )
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_lean_physics_primitives as lean

    theta = beta_strand_stacking_angle_rad()
    geff = stacked_line_outside_curvature_scale(theta)
    return 1.0 + (lean.GAMMA / 2.0) * (geff - 1.0)


def macro_ricci_inward_strength_for_kind(kind: str) -> float:
    """
    Lean ``macroRicciInwardStrengthForContactKind`` — α/γ/sc channels only.

    Helix axial slots use 0 (already at witness scale; dressing hurts).
    """
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_lean_physics_primitives as lean

    if kind in ("helix_i3", "helix_i4"):
        return 0.0
    if kind == "terminus":
        return lean.STRONG_CHANNEL_FRACTION
    if kind == "hydrophobic":
        return lean.GAMMA / 2.0
    if kind == "helix_sheet":
        return lean.ALPHA
    if kind == "sheet_i2":
        return lean.GAMMA / 4.0
    return lean.GAMMA / 8.0


def macro_ricci_inward_breathing_scale(breathing: float, strength: float) -> float:
    """Lean ``macroRicciInwardBreathingScale``."""
    return 1.0 - strength * max(1.0 - breathing, 0.0)


def macro_ricci_contact_breathing_scale(contact: TertiaryContact) -> float:
    """Kind-specific inward breathing from spine channel strengths."""
    base = macro_ricci_stacked_line_breathing_scale()
    if contact.kind == "sheet_i2" and is_open_beta_sheet_i2_contact(contact):
        return base
    strength = macro_ricci_inward_strength_for_kind(contact.kind)
    if strength <= 0.0:
        return 1.0
    return macro_ricci_inward_breathing_scale(base, strength)


def macro_ricci_contact_dress_blend(
    sequence: str,
    contact: TertiaryContact,
    ca: list[Vec3],
    ss: list[str] | None,
    contacts: tuple[TertiaryContact, ...],
    *,
    system_amp: float | None = None,
    xi: float | None = None,
) -> float:
    """Lean ``macroRicciContactParticipation`` × system amplitude."""
    from hqiv_lab.residue_site_physics import (
        macro_ricci_contact_participation,
        macro_ricci_system_dress_amplitude,
    )

    if not contacts:
        return 0.0
    amp = (
        system_amp
        if system_amp is not None
        else macro_ricci_system_dress_amplitude(sequence, contacts, ca, ss, xi=xi)
    )
    part = macro_ricci_contact_participation(contact, ca, ss, contacts)
    return min(1.0, max(0.0, amp * part))


def macro_ricci_soft_contact_target(
    contact: TertiaryContact,
    sequence: str,
    ca: list[Vec3],
    ss: list[str] | None,
    contacts: tuple[TertiaryContact, ...],
    *,
    system_amp: float | None = None,
    xi: float | None = None,
) -> float:
    """Lean ``macroRicciSoftContactTarget``."""
    base = contact.target_angstrom
    blend = macro_ricci_contact_dress_blend(
        sequence, contact, ca, ss, contacts, system_amp=system_amp, xi=xi
    )
    if blend <= 0.0:
        return base
    breathing = macro_ricci_contact_breathing_scale(contact)
    if breathing >= 1.0:
        return base
    dressed = base * breathing
    return base + blend * (dressed - base)


def macro_ricci_contact_sse_multiplier(
    sequence: str,
    ca: list[Vec3],
    contact: TertiaryContact,
    ss: list[str] | None,
    contacts: tuple[TertiaryContact, ...],
    *,
    system_amp: float | None = None,
    xi: float | None = None,
) -> float:
    """
    SSE weight boost from effective contact curvature budget (dynamic, not fitted).

    ``1 + blend · max(B_eff − 1, 0)`` at the contact horizon.
    """
    from hqiv_lab.protein_solvent_phase import contact_curvature_weight

    blend = macro_ricci_contact_dress_blend(
        sequence, contact, ca, ss, contacts, system_amp=system_amp, xi=xi
    )
    if blend <= 0.0:
        return 1.0
    b_eff = contact_curvature_weight(ca, contact, ss, xi=xi)
    return 1.0 + blend * max(b_eff - 1.0, 0.0)


def macro_ricci_sheet_i2_sse_multiplier(
    sequence: str,
    ca: list[Vec3],
    contact: TertiaryContact,
    ss: list[str] | None,
    *,
    xi: float | None = None,
) -> float:
    """Legacy alias."""
    return macro_ricci_contact_sse_multiplier(
        sequence, ca, contact, ss, (contact,), xi=xi
    )

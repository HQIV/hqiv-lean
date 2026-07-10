"""
Per-residue site physics for macro Ricci contact dynamics.

Lean mirrors:
  ``Hqiv.ProteinResearch.AtomEnergyOSHoracleBridge.latticeFullModeEnergy``
  ``Hqiv.Physics.HomogeneousCurvatureSecondOrder``
  ``Hqiv.QuantumChemistry.MacroRicciFlowDynamics``
  ``Hqiv.ProteinResearch.MiniproteinChemistryDynamics.contactDirectionalLocalRho``
"""

from __future__ import annotations

import math

# Backbone heavy-atom Z proxy for Compton shell ladder (same witness as OSH path).
_AA_Z: dict[str, int] = {
    "G": 6,
    "A": 6,
    "S": 6,
    "C": 6,
    "V": 6,
    "L": 6,
    "I": 6,
    "P": 6,
    "F": 6,
    "Y": 6,
    "W": 6,
    "H": 7,
    "N": 7,
    "Q": 7,
    "D": 6,
    "E": 6,
    "K": 7,
    "R": 7,
    "M": 6,
}

# Monoisotopic composition witnesses (stoichiometry, not fold-fit parameters).
_RESIDUE_MASS_DA: dict[str, float] = {
    "G": 57.021464,
    "A": 71.037114,
    "R": 156.101111,
    "N": 114.042927,
    "D": 115.026943,
    "C": 103.009185,
    "E": 129.042593,
    "Q": 128.058578,
    "H": 137.058912,
    "I": 113.084064,
    "L": 113.084064,
    "K": 128.094963,
    "M": 131.040485,
    "F": 147.068414,
    "P": 97.052764,
    "S": 87.032028,
    "T": 101.047679,
    "W": 186.079313,
    "Y": 163.063329,
    "V": 99.068414,
}

_GLY_MASS_DA = _RESIDUE_MASS_DA["G"]


def residue_compton_shell(aa: str) -> int:
    """Electronic Compton shell from valence Z (Lean electronic valence chart)."""
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_electronic_valence_shells as evs

    z = _AA_Z.get(aa.upper(), 6)
    m_s, _ = evs.electronic_compton_shells(z)
    return m_s


def lattice_full_mode_energy(shell: int) -> float:
    """Lean ``latticeFullModeEnergy`` closed form: ``4(m+2)(m+1)²``."""
    m = float(max(shell, 0))
    return 4.0 * (m + 2.0) * (m + 1.0) ** 2


def residue_mass_ratio_gly(aa: str) -> float:
    """Residue mass relative to glycine (unity at G) — composition witness only."""
    mass = _RESIDUE_MASS_DA.get(aa.upper(), _GLY_MASS_DA)
    return mass / _GLY_MASS_DA


def contact_mass_ratio_geometric_mean(sequence: str, i: int, j: int) -> float:
    """Geometric mean of endpoint residue masses (Gly = 1)."""
    if not sequence:
        return 1.0
    mi = residue_mass_ratio_gly(sequence[min(max(i, 0), len(sequence) - 1)])
    mj = residue_mass_ratio_gly(sequence[min(max(j, 0), len(sequence) - 1)])
    return math.sqrt(mi * mj)


def contact_site_energy_ratio_geometric_mean(sequence: str, i: int, j: int) -> float:
    """Geometric mean of per-site ``latticeFullModeEnergy`` at Compton shells."""
    si = residue_compton_shell(sequence[min(max(i, 0), len(sequence) - 1)])
    sj = residue_compton_shell(sequence[min(max(j, 0), len(sequence) - 1)])
    ei = lattice_full_mode_energy(si)
    ej = lattice_full_mode_energy(sj)
    eg = lattice_full_mode_energy(residue_compton_shell("G"))
    if eg < 1e-30:
        return 1.0
    return math.sqrt(max(ei, 0.0) / eg * max(ej, 0.0) / eg)


def contact_curvature_be_excess(
    ca: list,
    contact,
    ss: list[str] | None,
    *,
    xi: float | None = None,
) -> float:
    """Local binding-curvature excess ``B_eff − 1`` at the contact horizon."""
    from hqiv_lab._scripts import ensure_scripts_on_path
    from hqiv_lab.miniprotein_contacts import TertiaryContact
    from hqiv_lab.protein_solvent_phase import (
        directional_local_network_rho,
        protein_effective_curvature_budget,
        solvent_curvature_density_at_site,
    )

    ensure_scripts_on_path()
    import hqiv_lean_physics_primitives as lean

    assert isinstance(contact, TertiaryContact)
    if xi is None:
        xi = lean.XI_LOCKIN
    vx = ca[contact.j][0] - ca[contact.i][0]
    vy = ca[contact.j][1] - ca[contact.i][1]
    vz = ca[contact.j][2] - ca[contact.i][2]
    r_contact = math.sqrt(vx * vx + vy * vy + vz * vz)
    rho_local = directional_local_network_rho(ca, contact, ss)
    rho_site = solvent_curvature_density_at_site(rho_local, r_contact)
    b_eff = protein_effective_curvature_budget(xi, rho_site, rho_local)
    return max(b_eff - 1.0, 0.0)


def macro_ricci_local_dress_amplitude(
    sequence: str,
    contact,
    ca: list,
    ss: list[str] | None,
    *,
    xi: float | None = None,
) -> float:
    """Lean ``macroRicciLocalDressAmplitude`` on a single contact pair."""
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_lean_physics_primitives as lean

    be_excess = contact_curvature_be_excess(ca, contact, ss, xi=xi)
    m_pair = contact_mass_ratio_geometric_mean(sequence, contact.i, contact.j)
    mass_term = max(m_pair - 1.0, 0.0) / max(m_pair, 1.0)
    site_ratio = contact_site_energy_ratio_geometric_mean(sequence, contact.i, contact.j)
    sc = lean.STRONG_CHANNEL_FRACTION
    raw = sc * be_excess * mass_term * site_ratio
    return min(1.0, max(0.0, raw))


def sequence_mass_participation(sequence: str) -> float:
    """Lean ``contactMassParticipation`` aggregated over the chain."""
    if not sequence:
        return 0.0
    ratios = [residue_mass_ratio_gly(aa) for aa in sequence]
    mean_ratio = sum(ratios) / len(ratios)
    return max(mean_ratio - 1.0, 0.0) / max(mean_ratio, 1.0)


def sequence_site_energy_participation(sequence: str) -> float:
    """Mean Compton-shell site-energy ratio vs glycine."""
    if not sequence:
        return 1.0
    eg = lattice_full_mode_energy(residue_compton_shell("G"))
    if eg < 1e-30:
        return 1.0
    energies = [lattice_full_mode_energy(residue_compton_shell(aa)) for aa in sequence]
    mean_e = sum(energies) / len(energies)
    return math.sqrt(max(mean_e, 0.0) / eg)


def macro_ricci_system_network_stats(
    ca: list,
    contacts: tuple,
    ss: list[str] | None,
) -> tuple[float, float]:
    """Network-mean directional ρ and max coordination excess."""
    from hqiv_lab.miniprotein_contacts import TertiaryContact
    from hqiv_lab.protein_solvent_phase import (
        directional_local_network_rho,
        directional_register_baseline_rho,
        solvent_curvature_density_at_site,
    )

    if not contacts:
        base = directional_register_baseline_rho("terminus")
        return base, 0.0
    rhos: list[float] = []
    excesses: list[float] = []
    for contact in contacts:
        assert isinstance(contact, TertiaryContact)
        rho_local = directional_local_network_rho(ca, contact, ss)
        rhos.append(rho_local)
        vx = ca[contact.j][0] - ca[contact.i][0]
        vy = ca[contact.j][1] - ca[contact.i][1]
        vz = ca[contact.j][2] - ca[contact.i][2]
        r_contact = math.sqrt(vx * vx + vy * vy + vz * vz)
        rho_site = solvent_curvature_density_at_site(rho_local, r_contact)
        excesses.append(max(rho_local - min(1.0, max(0.0, rho_site)), 0.0))
    rho_network = sum(rhos) / len(rhos)
    coord_excess = max(excesses) if excesses else 0.0
    return rho_network, coord_excess


def macro_ricci_system_feedback_excess(
    ca: list,
    contacts: tuple,
    ss: list[str] | None,
    *,
    xi: float | None = None,
) -> float:
    """``macroRicciHomogeneousFeedbackRound − 1`` on the whole network."""
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_homogeneous_curvature_feedback as hcf
    import hqiv_lean_physics_primitives as lean

    if xi is None:
        xi = lean.XI_LOCKIN
    rho_network, coord_excess = macro_ricci_system_network_stats(ca, contacts, ss)
    fb = hcf.binding_curvature_feedback_second_order_homogeneous(
        xi, rho_network, coord_excess
    )
    return max(fb - 1.0, 0.0)


def electronic_compound_error_guard(xi: float | None = None) -> float:
    """Lean ``electronicCompoundErrorGuard`` — electronic over-count guard at ξ."""
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_lean_physics_primitives as lean

    if xi is None:
        xi = lean.XI_LOCKIN
    c2 = lean.tuft_lapse_concentration_at_xi(xi)
    c2_lock = lean.tuft_lapse_concentration_at_xi(lean.XI_LOCKIN)
    sc = lean.STRONG_CHANNEL_FRACTION
    return 1.0 - sc * (1.0 - c2 / max(c2_lock, 1e-30))


def structure_register_contact_count(contacts: tuple) -> int:
    """Register contacts for ``macroRicciCompoundBreathingScale`` (stacked-line depth)."""
    from hqiv_lab.miniprotein_contacts import STRUCTURE_CONTACT_KINDS

    return sum(1 for c in contacts if c.kind in STRUCTURE_CONTACT_KINDS)


def macro_ricci_network_compound_excess(n_register: int, breathing: float) -> float:
    """
    Lean ``macroRicciCompoundBreathingScale n θ − 1``.

    Multiplicative register compounding on structure slots (not total graph size).
    """
    n = max(int(n_register), 0)
    if n == 0:
        return 0.0
    return breathing ** n - 1.0


def macro_ricci_contact_participation(
    contact,
    ca: list,
    ss: list[str] | None,
    contacts: tuple,
) -> float:
    """
    Dynamic network participation: live directional ρ × closure pass weight.

    Lean ``macroRicciDynamicContactParticipation`` — no fitted kind table.
    """
    from hqiv_lab.miniprotein_contacts import closure_pass_weight
    from hqiv_lab.protein_solvent_phase import directional_local_network_rho

    rho_local = directional_local_network_rho(ca, contact, ss)
    rho_network, _ = macro_ricci_system_network_stats(ca, contacts, ss)
    pass_w = closure_pass_weight(contact.kind)
    if rho_network < 1e-12:
        return min(1.0, pass_w)
    return min(1.0, (rho_local / rho_network) * pass_w)


def macro_ricci_system_dress_amplitude(
    sequence: str,
    contacts: tuple,
    ca: list,
    ss: list[str] | None,
    *,
    xi: float | None = None,
) -> float:
    """
    Lean ``macroRicciSystemDressAmplitude`` with proved compound + electronic guard.

    ``clamp( sc · fbExcess · mass · site · (1 + compound) · guard )``
    """
    from hqiv_lab._scripts import ensure_scripts_on_path
    from hqiv_lab.peptide_geometry import (
        beta_strand_stacking_angle_rad,
        stacked_line_outside_curvature_scale,
    )

    ensure_scripts_on_path()
    import hqiv_lean_physics_primitives as lean

    if not contacts:
        return 0.0
    fb_excess = macro_ricci_system_feedback_excess(ca, contacts, ss, xi=xi)
    mass_term = sequence_mass_participation(sequence)
    site_term = sequence_site_energy_participation(sequence)
    theta = beta_strand_stacking_angle_rad()
    geff = stacked_line_outside_curvature_scale(theta)
    breathing = 1.0 + (lean.GAMMA / 2.0) * (geff - 1.0)
    n_reg = structure_register_contact_count(contacts)
    compound = macro_ricci_network_compound_excess(n_reg, breathing)
    guard = electronic_compound_error_guard(xi)
    sc = lean.STRONG_CHANNEL_FRACTION
    raw = sc * fb_excess * mass_term * site_term * (1.0 + compound) * guard
    return min(1.0, max(0.0, raw))

"""
Peptide / protein shell-equation dress — same language as spectral / carbon packing.

Lean target: ``Hqiv.ProteinResearch.MiniproteinChemistryDynamics`` +
``Hqiv.QuantumChemistry.PeptideBackboneGeometry``.

Composes the chemistry shell projection into protein geometry without molecule-type
cases:

* backbone bonds: ``r → r · em^(α · length_share)`` (identity at length_share → 0);
* tertiary Cα network: ``d → d · (1 + base · open²)`` from register occupancy;
* H-bond pivots: hydrogen-acceptor length / energy scales;
* solvent SSE weights: energy_share × polarity amplitude on polar registers.

Laboratory PDB/RMSD remain comparison quarantine only.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from functools import lru_cache
from typing import Any  # noqa: F401 — used by staged_pass_piezo_step_dress

from hqiv_lab._scripts import ensure_scripts_on_path

ensure_scripts_on_path()

import hqiv_lean_physics_primitives as lean  # noqa: E402
import hqiv_molecular_spectroscopy as ms  # noqa: E402
import hqiv_two_way_feedback_dynamics as twf  # noqa: E402

# Peptide backbone atom Z / coordination / bond-order slots (Lean PeptideBackboneGeometry).
PEPTIDE_BOND_SLOTS: dict[str, dict[str, float | int]] = {
    "N_CA": {"z_i": 7, "z_j": 6, "capacity": 4, "bond_order": 1},
    "CA_C": {"z_i": 6, "z_j": 6, "capacity": 4, "bond_order": 1},
    "C_N": {"z_i": 6, "z_j": 7, "capacity": 3, "bond_order": 1},  # amide partial-double via capacity
    "C_O": {"z_i": 6, "z_j": 8, "capacity": 2, "bond_order": 2},
}

# Tertiary register → shell occupancy (filled shared channels).  Higher occupancy
# → smaller open-channel packing.  No molecule names — register topology only.
REGISTER_OCCUPANCY: dict[str, float] = {
    "helix_i3": 0.75,
    "helix_i4": 0.80,
    "sheet_i2": 0.55,
    "helix_sheet": 0.45,
    "hydrophobic": 0.30,
    "terminus": 0.35,
}

# Period-channel Z for covalent open^(w²) fade (Lean ``covalentNetworkPeriodChannelWeight``).
# Peptide Cα / amide registers are period-2 (C/N/O → w=1, full open).  Sulfur-rich
# hydrophobic packing can pass Z=16 to fade open continuously — no hard gate.
REGISTER_PERIOD_Z: dict[str, int] = {
    "helix_i3": 6,
    "helix_i4": 6,
    "sheet_i2": 6,
    "helix_sheet": 7,  # amide N–O H-bond register
    "hydrophobic": 6,
    "terminus": 7,
}


@dataclass(frozen=True)
class PeptideShellDress:
    """Shell projection + EM length scale for one peptide / register contact."""

    projection: twf.ShellAnchorProjection
    em: float
    length_scale: float
    packing_scale: float
    energy_scale: float
    h_acceptor_length_scale: float
    h_acceptor_energy_scale: float

    @property
    def total_length_scale(self) -> float:
        return self.length_scale * self.packing_scale * self.h_acceptor_length_scale

    def to_dict(self) -> dict[str, Any]:
        return {
            "em": self.em,
            "length_scale": self.length_scale,
            "packing_scale": self.packing_scale,
            "energy_scale": self.energy_scale,
            "h_acceptor_length_scale": self.h_acceptor_length_scale,
            "h_acceptor_energy_scale": self.h_acceptor_energy_scale,
            "total_length_scale": self.total_length_scale,
            "shell": self.projection.to_dict(),
        }


def _peptide_ionic_character(z_i: int, z_j: int) -> float:
    return float(ms.bond_ionic_character(int(z_i), int(z_j)))


def _peptide_em(z_i: int, z_j: int) -> float:
    n = ms.curvature_dielectric_ratio(int(z_i), int(z_j))
    return float(twf.em_feedback_from_dielectric(n).em)


def peptide_bond_shell_projection(
    slot: str,
    *,
    phase_contact_weight: float = 0.0,
) -> twf.ShellAnchorProjection:
    """Shell projection for a named peptide backbone bond slot."""
    if slot not in PEPTIDE_BOND_SLOTS:
        raise KeyError(f"unknown peptide bond slot {slot!r}")
    spec = PEPTIDE_BOND_SLOTS[slot]
    z_i, z_j = int(spec["z_i"]), int(spec["z_j"])
    ionic = _peptide_ionic_character(z_i, z_j)
    # Amide / carbonyl: hydrogen-acceptor weight from O or N acceptor character.
    h_acc = 0.0
    if slot == "C_O":
        h_acc = 1.0
    elif slot == "C_N":
        h_acc = lean.GAMMA  # partial acceptor on amide N
    return twf.shell_anchor_projection(
        capacity=float(spec["capacity"]),
        bond_order=float(spec["bond_order"]),
        ionic_character=ionic,
        phase_contact_weight=phase_contact_weight,
        hydrogen_acceptor_weight=h_acc,
    )


def peptide_bond_dress(
    slot: str,
    *,
    apply_packing: bool = False,
    environment: str = "aqueous",
    temperature_k: float | None = None,
) -> PeptideShellDress:
    """
    Dress scales for one backbone bond.

    ``environment``:
      * ``aqueous`` (default, protein fold): covalent σ bonds stay on the diamond-node
        bare length (Engh–Huber-class).  Gas-phase EM is *not* applied — NIST diatomic
        EM is a vacuum assay.  Optional thermal γ/16 breathing only.
      * ``gas``: dilute-gas spectral path ``em^(α·length_share)`` with
        ``phase_contact_weight=0`` (comparison / spectroscopy parity).
    """
    if environment not in ("aqueous", "gas"):
        raise ValueError(f"unknown peptide bond environment {environment!r}")

    if environment == "gas":
        proj = peptide_bond_shell_projection(slot, phase_contact_weight=0.0)
        spec = PEPTIDE_BOND_SLOTS[slot]
        em = _peptide_em(int(spec["z_i"]), int(spec["z_j"]))
        length_scale = max(em, 1.0e-30) ** (lean.ALPHA * float(proj.length_share))
        packing = float(proj.network_open_channel_packing_scale) if apply_packing else 1.0
        energy = float(proj.energy_scale_from_em(em))
        return PeptideShellDress(
            projection=proj,
            em=em,
            length_scale=length_scale,
            packing_scale=packing,
            energy_scale=energy,
            h_acceptor_length_scale=1.0,
            h_acceptor_energy_scale=float(proj.hydrogen_acceptor_energy_scale),
        )

    # Aqueous protein: outside density/curvature dresses tertiary contacts, not σ bonds.
    from hqiv_lab.protein_solvent_phase import (
        PROTEIN_FOLDING_TEMPERATURE_K,
        aqueous_phase_contact_weight,
        thermal_peptide_contact_scale,
    )

    t_k = PROTEIN_FOLDING_TEMPERATURE_K if temperature_k is None else temperature_k
    phase_w = aqueous_phase_contact_weight(t_k, "neutral")
    proj = peptide_bond_shell_projection(slot, phase_contact_weight=phase_w)
    thermal = thermal_peptide_contact_scale(t_k)
    packing = float(proj.network_open_channel_packing_scale) if apply_packing else 1.0
    return PeptideShellDress(
        projection=proj,
        em=1.0,
        length_scale=thermal,
        packing_scale=packing,
        energy_scale=1.0,
        h_acceptor_length_scale=1.0,
        h_acceptor_energy_scale=float(proj.hydrogen_acceptor_energy_scale),
    )


@lru_cache(maxsize=32)
def peptide_bond_dress_cached(
    slot: str,
    environment: str = "aqueous",
    temperature_k: float | None = None,
) -> PeptideShellDress:
    """Cached shell dress for a backbone bond slot."""
    return peptide_bond_dress(
        slot, environment=environment, temperature_k=temperature_k
    )


def dress_peptide_bond_length(
    r_bare: float,
    slot: str,
    *,
    environment: str = "aqueous",
    temperature_k: float | None = None,
) -> float:
    """Apply environment-appropriate dress to a bare diamond-node peptide bond."""
    return float(r_bare) * peptide_bond_dress_cached(
        slot, environment=environment, temperature_k=temperature_k
    ).length_scale


@lru_cache(maxsize=16)
def peptide_bond_length_scales(
    environment: str = "aqueous",
    temperature_k: float | None = None,
) -> dict[str, float]:
    """Cached length scales for N_CA / CA_C / C_N / C_O."""
    return {
        slot: peptide_bond_dress_cached(
            slot, environment=environment, temperature_k=temperature_k
        ).length_scale
        for slot in PEPTIDE_BOND_SLOTS
    }


def register_shell_projection(
    contact_kind: str,
    *,
    ionic_character: float = 0.0,
    hydrogen_acceptor_weight: float = 0.0,
    phase_contact_weight: float = 0.0,
) -> twf.ShellAnchorProjection:
    """
    Shell projection for a tertiary contact register.

    Occupancy is register-topology derived; capacity is the peptide steric domain
    count 4 (sp³ Cα horizon).  Bond order = occupancy · capacity.
    """
    occ = twf.clamp01(REGISTER_OCCUPANCY.get(contact_kind, 0.45))
    capacity = 4.0
    return twf.shell_anchor_projection(
        capacity=capacity,
        bond_order=occ * capacity,
        ionic_character=twf.clamp01(ionic_character),
        phase_contact_weight=phase_contact_weight,
        hydrogen_acceptor_weight=hydrogen_acceptor_weight,
    )


def register_period_channel_weight(
    contact_kind: str,
    *,
    period_z: int | None = None,
) -> float:
    """
    Lean ``covalentNetworkPeriodChannelWeight`` for a tertiary register.

    ``w = (2/P)^{constructiveValleyCap}``.  Period-2 peptide C/N/O → ``w=1``.
    """
    from hqiv_lab.crystal_geometry import covalent_network_period_channel_weight

    z = int(period_z) if period_z is not None else int(
        REGISTER_PERIOD_Z.get(contact_kind, 6)
    )
    return float(covalent_network_period_channel_weight(z))


def open_channel_period_fade(open_scale: float, period_weight: float) -> float:
    """
    Chemistry open^(w²) continuous fade on a packing / open scale.

    Period-2 (``w=1``) keeps full open; deeper periods fade open faster than the
    EM/nuclear blend — same equation as ``covalentNetworkEmPackingLength``.
    """
    w = max(float(period_weight), 0.0)
    return float(open_scale) ** (w * w)


@lru_cache(maxsize=64)
def tertiary_contact_packing_scale(
    contact_kind: str,
    aqueous: bool = True,
    temperature_k: float | None = None,
    period_z: int | None = None,
) -> float:
    """
    Open-channel packing ``(1 + base · open²)^(w²)`` for a tertiary Cα contact.

    Bare shell open², then covalent period-channel fade (Lean open^(w²)).
    """
    phase_w = 0.0
    if aqueous:
        from hqiv_lab.protein_solvent_phase import (
            PROTEIN_FOLDING_TEMPERATURE_K,
            aqueous_phase_contact_weight,
            interface_exposure_from_contact_kind,
        )

        t_k = PROTEIN_FOLDING_TEMPERATURE_K if temperature_k is None else temperature_k
        phase_w = aqueous_phase_contact_weight(
            t_k, interface_exposure_from_contact_kind(contact_kind)
        )
    open_scale = float(
        register_shell_projection(
            contact_kind, phase_contact_weight=phase_w
        ).network_open_channel_packing_scale
    )
    w = register_period_channel_weight(contact_kind, period_z=period_z)
    return open_channel_period_fade(open_scale, w)


def register_piezo_cage(occupancy: float) -> float:
    """Lean ``registerPiezoCage``: ``open + strong·open²``."""
    open_f = max(0.0, min(1.0, 1.0 - float(occupancy)))
    return open_f + lean.STRONG_CHANNEL_FRACTION * open_f * open_f


def register_lindemann_strain(
    temperature_k: float,
    melt_k: float,
    occupancy: float,
) -> float:
    """Lean ``registerLindemannStrain`` — Brownian / piezo loader on a register."""
    if melt_k <= 0.0 or temperature_k <= 0.0:
        return 0.0
    amp = lean.GAMMA / 2.0
    cage = register_piezo_cage(occupancy)
    return twf.clamp01(
        amp * math.sqrt(temperature_k / melt_k) * (1.0 + cage)
    )


def register_piezo_energy_dress(
    temperature_k: float,
    melt_k: float,
    occupancy: float,
) -> float:
    """Lean ``registerPiezoEnergyDress``: ``1 + (4/8)·ε_reg``."""
    return 1.0 + lean.STRONG_CHANNEL_FRACTION * register_lindemann_strain(
        temperature_k, melt_k, occupancy
    )


def tertiary_contact_piezo_energy_dress(
    contact_kind: str,
    *,
    temperature_k: float | None = None,
    melt_k: float | None = None,
) -> float:
    """Lean ``tertiaryContactPiezoEnergyDress`` for a named register."""
    from hqiv_lab.protein_solvent_phase import (
        H2O_BULK_MELT_TEMPERATURE_K,
        PROTEIN_FOLDING_TEMPERATURE_K,
    )

    t_k = PROTEIN_FOLDING_TEMPERATURE_K if temperature_k is None else float(temperature_k)
    t_m = H2O_BULK_MELT_TEMPERATURE_K if melt_k is None else float(melt_k)
    occ = float(REGISTER_OCCUPANCY.get(contact_kind, 0.45))
    return register_piezo_energy_dress(t_k, t_m, occ)


def staged_pass_piezo_step_dress(
    contacts: tuple[Any, ...] | list[Any],
    *,
    temperature_k: float | None = None,
    melt_k: float | None = None,
) -> float:
    """
    Mild mean register piezo dress over a staged contact pass → NeRF/OSH ``Δ`` scale.

    Full ``1+(4/8)·ε`` is reserved for energy / SSE weights; coordinate search uses
    the monogamy half ``1+(4/8)·ε·(γ/2)`` so burial passes explore without overshoot.
    Identity at ``T→0``.
    """
    if not contacts:
        return 1.0
    from hqiv_lab.protein_solvent_phase import (
        H2O_BULK_MELT_TEMPERATURE_K,
        PROTEIN_FOLDING_TEMPERATURE_K,
    )

    t_k = PROTEIN_FOLDING_TEMPERATURE_K if temperature_k is None else float(temperature_k)
    t_m = H2O_BULK_MELT_TEMPERATURE_K if melt_k is None else float(melt_k)
    strains = []
    for c in contacts:
        kind = getattr(c, "kind", "hydrophobic")
        occ = float(REGISTER_OCCUPANCY.get(kind, 0.45))
        strains.append(register_lindemann_strain(t_k, t_m, occ))
    eps_bar = sum(strains) / float(len(strains))
    return 1.0 + lean.STRONG_CHANNEL_FRACTION * eps_bar * (lean.GAMMA / 2.0)


@lru_cache(maxsize=64)
def tertiary_contact_energy_weight(
    contact_kind: str,
    aqueous: bool = True,
    temperature_k: float | None = None,
) -> float:
    """
    SSE multiplier from shell energy share × acceptor softener × carrier thermo
    × register piezo.

    Polar / burial registers get energy-channel activation; filled helix contacts
    stay near identity.  Acceptor softener (Lean ``acceptorPolarizabilitySoftener``)
    and carrier thermo/Joule dress (``carrierThermoConductivityDress``) modulate
    energy, not Cα length.  Register piezo ``1+(4/8)·ε_reg`` adds thermal compliance
    on open/low-occupancy contacts (identity at ``T→0``).
    """
    phase_w = 0.0
    soft = 1.0
    thermo = 1.0
    piezo = 1.0
    if aqueous:
        from hqiv_lab.protein_solvent_phase import (
            PROTEIN_FOLDING_TEMPERATURE_K,
            aqueous_phase_contact_weight,
            interface_exposure_from_contact_kind,
            peptide_register_carrier_thermo_dress,
            peptide_register_steric_counts,
        )
        from hqiv_lab._scripts import ensure_scripts_on_path

        ensure_scripts_on_path()
        import hqiv_phase_material_response as pmr

        t_k = PROTEIN_FOLDING_TEMPERATURE_K if temperature_k is None else temperature_k
        phase_w = aqueous_phase_contact_weight(
            t_k, interface_exposure_from_contact_kind(contact_kind)
        )
        n_b, n_lp = peptide_register_steric_counts(contact_kind)
        soft = float(pmr.acceptor_polarizability_softener(n_b, n_lp))
        thermo = float(
            peptide_register_carrier_thermo_dress(
                contact_kind, temperature_k=t_k
            )
        )
        piezo = tertiary_contact_piezo_energy_dress(
            contact_kind, temperature_k=t_k
        )
    proj = register_shell_projection(
        contact_kind,
        ionic_character=lean.GAMMA if contact_kind in ("helix_sheet", "terminus") else 0.0,
        hydrogen_acceptor_weight=1.0 if contact_kind in ("helix_sheet", "terminus") else 0.0,
        phase_contact_weight=phase_w,
    )
    # Map energy_share ∈ [0,1] → weight around 1: ``1 + γ · (2·energy_share − 1)``.
    base = 1.0 + lean.GAMMA * (2.0 * float(proj.energy_share) - 1.0)
    return base * soft * thermo * piezo


def aqueous_hbond_shell_dress(
    *,
    donor_z: int = 7,
    acceptor_z: int = 8,
) -> PeptideShellDress:
    """N–H···O (or similar) hydrogen-bond pivot dress from shell projection."""
    ionic = _peptide_ionic_character(donor_z, acceptor_z)
    proj = twf.shell_anchor_projection(
        capacity=3.0,
        bond_order=1.0,
        ionic_character=ionic,
        hydrogen_acceptor_weight=1.0,
    )
    em = _peptide_em(donor_z, acceptor_z)
    length_scale = max(em, 1.0e-30) ** (lean.ALPHA * float(proj.length_share))
    return PeptideShellDress(
        projection=proj,
        em=em,
        length_scale=length_scale,
        packing_scale=float(proj.network_open_channel_packing_scale),
        energy_scale=float(proj.energy_scale_from_em(em)),
        h_acceptor_length_scale=1.0,
        h_acceptor_energy_scale=float(proj.hydrogen_acceptor_energy_scale),
    )


@lru_cache(maxsize=4)
def aqueous_hbond_pivot_shell_factor() -> float:
    """
    Multiplicative factor on the aqueous H-bond pivot from shell H-acceptor energy.

    Uses ``sqrt(h_acceptor_energy_scale)`` so the length-side pivot tracks the
    two-sided donor/acceptor share without double-counting EM length dress.
    Acceptor polarizability softener is an *energy/optical* channel — not applied
    to the Å pivot (see ``tertiary_contact_energy_weight``).
    """
    dress = aqueous_hbond_shell_dress()
    return math.sqrt(max(dress.h_acceptor_energy_scale, 1.0e-30))


def peptide_shell_dress_manifest(
    *,
    environment: str = "aqueous",
    temperature_k: float | None = None,
) -> dict[str, Any]:
    """Audit / paper readout of peptide shell dresses (no PDB inputs)."""
    bonds = {
        slot: peptide_bond_dress(
            slot, environment=environment, temperature_k=temperature_k
        ).to_dict()
        for slot in PEPTIDE_BOND_SLOTS
    }
    aqueous = environment == "aqueous"
    registers = {
        kind: {
            "occupancy": REGISTER_OCCUPANCY[kind],
            "packing_scale": tertiary_contact_packing_scale(
                kind, aqueous=aqueous, temperature_k=temperature_k
            ),
            "energy_weight": tertiary_contact_energy_weight(
                kind, aqueous=aqueous, temperature_k=temperature_k
            ),
            "shell": register_shell_projection(kind).to_dict(),
        }
        for kind in REGISTER_OCCUPANCY
    }
    hbond = aqueous_hbond_shell_dress().to_dict()
    hbond["pivot_shell_factor"] = aqueous_hbond_pivot_shell_factor()
    outside = None
    if aqueous:
        from hqiv_lab.protein_solvent_phase import aqueous_outside_geometry_scale

        outside = {
            kind: aqueous_outside_geometry_scale(
                temperature_k=temperature_k, contact_kind=kind
            )
            for kind in REGISTER_OCCUPANCY
        }
    return {
        "source": "hqiv_lab/peptide_shell_dress.py",
        "environment": environment,
        "policy": (
            "aqueous: covalent σ = diamond-node + thermal γ/16 (no gas EM); "
            "tertiary length = open^(w²) × outsideBulk(foldXi)×local×piezo↔stiffness; "
            "optical softener + carrier thermo + register piezo → energy weights; "
            "staged Δφ/Δψ × mean register piezo; "
            "gas: em^(α·length_share) for spectroscopy parity only"
        ),
        "backbone_bonds": bonds,
        "tertiary_registers": registers,
        "aqueous_outside_geometry": outside,
        "aqueous_hbond": hbond,
    }

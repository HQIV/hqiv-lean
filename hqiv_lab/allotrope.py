"""Derive and rank allotrope candidates from molecular inputs."""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import TYPE_CHECKING

from hqiv_lab.coordination import MonomerGeometry, infer_monomer_geometry
from hqiv_lab.packing import PackingTemplate, templates_for_motif
from hqiv_lab.spec import MoleculeSpec
from hqiv_lab.unit_cell import PhaseUnitCell, density_g_cm3, unit_cell_for_allotrope

from hqiv_lab._scripts import ensure_scripts_on_path

if TYPE_CHECKING:
    pass

ensure_scripts_on_path()
import hqiv_electronic_valence_shells as evs  # noqa: E402
import hqiv_lean_physics_primitives as lean  # noqa: E402
import hqiv_thermodynamic_phase_from_tp as tptp  # noqa: E402


@dataclass(frozen=True)
class AllotropeCandidate:
    """One derived condensed-phase orientation."""

    label: str
    template: PackingTemplate
    unit_cell: PhaseUnitCell
    density_g_cm3: float
    curvature_density_fraction: float
    score: float
    motif: str
    intermolecular_contacts: int
    description: str

    def to_dict(self) -> dict:
        return {
            "label": self.label,
            "allotrope": self.unit_cell.allotrope,
            "density_g_cm3": self.density_g_cm3,
            "curvature_density_fraction": self.curvature_density_fraction,
            "score": self.score,
            "motif": self.motif,
            "intermolecular_contacts": self.intermolecular_contacts,
            "description": self.description,
            "unit_cell": {
                "a_angstrom": self.unit_cell.a_angstrom,
                "b_angstrom": self.unit_cell.b_angstrom,
                "c_angstrom": self.unit_cell.c_angstrom,
                "crystal": self.unit_cell.crystal.value,
                "Z": self.unit_cell.molecules_per_cell,
            },
        }


def liquid_reference_density_g_cm3(spec: MoleculeSpec) -> float:
    """Liquid comparison scale at melt (species-specific where tabulated)."""
    refs = {"H2O": 1.0, "CH4": 0.423, "NH3": 0.682, "HF": 1.0}
    return refs.get(spec.formula_key, 1.0)


def _score_candidate(
    spec: MoleculeSpec,
    mono: MonomerGeometry,
    template: PackingTemplate,
    cell: PhaseUnitCell,
    rho_g: float,
    *,
    temperature_k: float,
    pressure_pa: float,
) -> float:
    """
    Rank allotropes: network cohesion + density match to liquid reference.

    Higher is better. No fitted coefficients beyond lattice α, γ.
    """
    rho_liq = liquid_reference_density_g_cm3(spec)
    rho_frac = min(1.0, max(0.0, rho_g / rho_liq)) if rho_liq > 0 else 0.0

    mat = tptp.MaterialThermodynamicScales(
        name=f"{spec.name}_bulk",
        characteristic_binding_ev=spec.reference_binding_ev or 5.0,
        contact_points=mono.intermolecular_contacts,
        molecular_weight_amu=spec.molecular_weight_amu,
        intermolecular_contacts=mono.intermolecular_contacts,
        contact_xi=lean.xi_from_compton_triplet(evs.chemistry_compton_triplet(spec.fragments)),
        bulk_condensed=True,
        medium_density_fraction=rho_frac,
        intermolecular_motif=mono.motif.value,
        z_heavy=mono.z_heavy,
    )
    t_melt, _ = tptp.characteristic_temperatures_K(mat)
    env = tptp.ThermodynamicEnvironment(temperature_k, pressure_pa)
    phase = tptp.derive_phase(env, mat)

    # Prefer solid at low T; penalize density far from liquid scale for H-bonded nets
    solid_bonus = 2.0 if phase.phase == tptp.DerivedPhase.SOLID else 0.0
    density_penalty = abs(rho_g - rho_liq) / max(rho_liq, 1e-6)
    opening_bonus = lean.PHASE_LIFT_3 if template.label == "Ih" else 1.0
    melt_proximity = 1.0 / (1.0 + abs(temperature_k - t_melt) / max(t_melt, 1.0))

    return (
        solid_bonus
        + opening_bonus * melt_proximity
        - density_penalty
        + lean.ALPHA * rho_frac
    )


def derive_allotropes(
    spec: MoleculeSpec,
    *,
    temperature_k: float = 273.15,
    pressure_pa: float = tptp.STP_PRESSURE_PA,
) -> tuple[AllotropeCandidate, ...]:
    """All allotrope candidates for this monomer, sorted by score (best first)."""
    mono = infer_monomer_geometry(spec)
    templates = templates_for_motif(mono.motif)
    candidates: list[AllotropeCandidate] = []

    for tmpl in templates:
        cell = unit_cell_for_allotrope(spec, tmpl, mono, temperature_k=temperature_k)
        rho = density_g_cm3(cell)
        rho_liq = liquid_reference_density_g_cm3(spec)
        rho_frac = min(1.0, max(0.0, rho / rho_liq)) if rho_liq > 0 else 0.0
        score = _score_candidate(
            spec, mono, tmpl, cell, rho,
            temperature_k=temperature_k,
            pressure_pa=pressure_pa,
        )
        candidates.append(
            AllotropeCandidate(
                label=tmpl.label,
                template=tmpl,
                unit_cell=cell,
                density_g_cm3=rho,
                curvature_density_fraction=rho_frac,
                score=score,
                motif=mono.motif.value,
                intermolecular_contacts=mono.intermolecular_contacts,
                description=tmpl.description,
            )
        )

    return tuple(sorted(candidates, key=lambda c: c.score, reverse=True))


def preferred_allotrope(
    spec: MoleculeSpec,
    *,
    temperature_k: float = 273.15,
    pressure_pa: float = tptp.STP_PRESSURE_PA,
) -> AllotropeCandidate:
    """Highest-scoring allotrope at (T, P)."""
    cands = derive_allotropes(spec, temperature_k=temperature_k, pressure_pa=pressure_pa)
    if not cands:
        raise ValueError(f"no allotrope candidates for {spec.name}")
    return cands[0]

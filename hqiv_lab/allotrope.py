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


def _characteristic_binding_ev(spec: MoleculeSpec) -> float:
    """Internal cohesive scale from derived bonds; no benchmark reference energy."""
    if not spec.bonds:
        return lean.ALPHA * lean.STRONG_CHANNEL_FRACTION
    bohr_angstrom = 0.529177210903
    rydberg_ev = 13.605693122994
    gaps = [
        rydberg_ev
        * lean.ALPHA
        * (1.0 + lean.STRONG_CHANNEL_FRACTION)
        / (1.0 + max(b.distance_angstrom, 1.0e-9) / bohr_angstrom)
        for b in spec.bonds
    ]
    return sum(gaps) / float(len(gaps))


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


def liquid_reference_density_g_cm3(
    spec: MoleculeSpec,
    *,
    temperature_k: float = 273.15,
) -> float:
    """Liquid comparison scale from solid template + motif melt opening."""
    import hqiv_derived_chemistry as hdc

    return hdc.derived_liquid_reference_density_g_cm3(
        spec.name,
        temperature_k=temperature_k,
    )


def packing_disorder_score(
    *,
    periodic_weight: float,
    mean_coordination: float,
    coordination_variance: float,
    open_fraction: float,
) -> float:
    """
    Glass / amorphous disorder score (Lean ``packingDisorderScore``):

      S = γ · [(1 − w_periodic) + Var(CN)/⟨CN⟩ + open²]

    Prefer amorphous packing when ``S > α``.
    """
    w = max(0.0, min(1.0, float(periodic_weight)))
    cn = max(float(mean_coordination), 1e-9)
    var_term = max(0.0, float(coordination_variance)) / cn
    open_sq = max(0.0, float(open_fraction)) ** 2
    return lean.GAMMA * ((1.0 - w) + var_term + open_sq)


def _template_open_fraction(template: PackingTemplate) -> float:
    """Openness from packing template scale (amorphous / Ic excess over identity)."""
    if template.label == "amorphous":
        return max(0.0, template.a_factor - 1.0)
    if template.label == "Ic":
        return max(0.0, template.a_factor - 1.0) * lean.GAMMA
    return 0.0


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
    Amorphous templates are gated by packing disorder score ``S > α``.
    """
    rho_liq = liquid_reference_density_g_cm3(spec)
    rho_frac = min(1.0, max(0.0, rho_g / rho_liq)) if rho_liq > 0 else 0.0

    mat = tptp.MaterialThermodynamicScales(
        name=f"{spec.name}_bulk",
        characteristic_binding_ev=_characteristic_binding_ev(spec),
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

    # Ordered ice / molecular solids: full periodic weight, zero CN variance.
    # Amorphous: lose periodic weight and inflate CN variance (disordered shell).
    cn = float(max(mono.intermolecular_contacts, 1))
    if template.label == "amorphous":
        w_per = phase.periodic_weight * lean.GAMMA
        cn_var = cn * lean.STRONG_CHANNEL_FRACTION
    else:
        w_per = phase.periodic_weight
        cn_var = 0.0
    disorder = packing_disorder_score(
        periodic_weight=w_per,
        mean_coordination=cn,
        coordination_variance=cn_var,
        open_fraction=_template_open_fraction(template),
    )
    # Amorphous only scores when disorder exceeds α; otherwise penalize.
    if template.label == "amorphous":
        amorphous_bonus = lean.ALPHA if disorder > lean.ALPHA else -1.0
    else:
        amorphous_bonus = 0.0

    return (
        solid_bonus
        + opening_bonus * melt_proximity
        - density_penalty
        + lean.ALPHA * rho_frac
        + amorphous_bonus
        - lean.GAMMA * disorder  # ordered templates prefer low disorder
    )


def derive_allotropes(
    spec: MoleculeSpec,
    *,
    temperature_k: float = 273.15,
    pressure_pa: float = tptp.STP_PRESSURE_PA,
    melt_k: float | None = None,
) -> tuple[AllotropeCandidate, ...]:
    """All allotrope candidates for this monomer, sorted by score (best first)."""
    mono = infer_monomer_geometry(spec)
    templates = templates_for_motif(mono.motif, spec=spec)
    candidates: list[AllotropeCandidate] = []
    t_melt = melt_k
    if t_melt is None:
        try:
            from hqiv_lab.species_panel import panel_entry

            t_melt = float(panel_entry(spec.name).nist_melt_k)
        except Exception:
            t_melt = temperature_k

    for tmpl in templates:
        cell = unit_cell_for_allotrope(
            spec,
            tmpl,
            mono,
            temperature_k=temperature_k,
            melt_k=t_melt,
        )
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
    melt_k: float | None = None,
) -> AllotropeCandidate:
    """Highest-scoring allotrope at (T, P)."""
    cands = derive_allotropes(
        spec,
        temperature_k=temperature_k,
        pressure_pa=pressure_pa,
        melt_k=melt_k,
    )
    if not cands:
        raise ValueError(f"no allotrope candidates for {spec.name}")
    return cands[0]

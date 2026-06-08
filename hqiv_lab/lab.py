"""MaterialsLab — unified entry point for the HQIV chem / materials package."""

from __future__ import annotations

from dataclasses import asdict
from typing import Any

from hqiv_lab.allotrope import AllotropeCandidate, derive_allotropes, preferred_allotrope
from hqiv_lab.coordination import MonomerGeometry, infer_monomer_geometry
from hqiv_lab.packing import PackingTemplate
from hqiv_lab.spec import MoleculeSpec
from hqiv_lab.unit_cell import PhaseUnitCell, density_g_cm3, unit_cell_for_allotrope

from hqiv_lab._scripts import ensure_scripts_on_path

ensure_scripts_on_path()


class MaterialsLab:
    """
    HQIV chemistry and materials lab.

    Input: molecular spec (fragments + bonds, or GMTKN55 name).
    Output: derived allotropes, unit cells, and downstream material readouts.
    """

    def spec_from_name(self, name: str) -> MoleculeSpec:
        return MoleculeSpec.from_chart_name(name)

    def spec_from_formula(self, formula: str) -> MoleculeSpec:
        return MoleculeSpec.from_formula(formula)

    def monomer_geometry(self, spec: MoleculeSpec) -> MonomerGeometry:
        return infer_monomer_geometry(spec)

    def derive_allotropes(
        self,
        spec: MoleculeSpec,
        *,
        temperature_k: float = 273.15,
        pressure_pa: float | None = None,
    ) -> tuple[AllotropeCandidate, ...]:
        import hqiv_thermodynamic_phase_from_tp as tptp

        p = pressure_pa if pressure_pa is not None else tptp.STP_PRESSURE_PA
        return derive_allotropes(spec, temperature_k=temperature_k, pressure_pa=p)

    def preferred_allotrope(
        self,
        spec: MoleculeSpec,
        *,
        temperature_k: float = 273.15,
        pressure_pa: float | None = None,
    ) -> AllotropeCandidate:
        import hqiv_thermodynamic_phase_from_tp as tptp

        p = pressure_pa if pressure_pa is not None else tptp.STP_PRESSURE_PA
        return preferred_allotrope(spec, temperature_k=temperature_k, pressure_pa=p)

    def unit_cell(
        self,
        spec: MoleculeSpec,
        allotrope_label: str | None = None,
        *,
        temperature_k: float = 273.15,
    ) -> PhaseUnitCell:
        if allotrope_label is None:
            return self.preferred_allotrope(spec, temperature_k=temperature_k).unit_cell
        for cand in self.derive_allotropes(spec, temperature_k=temperature_k):
            if cand.label.upper() == allotrope_label.upper():
                return cand.unit_cell
        mono = infer_monomer_geometry(spec)
        from hqiv_lab.packing import templates_for_motif

        for tmpl in templates_for_motif(mono.motif):
            if tmpl.label.upper() == allotrope_label.upper():
                return unit_cell_for_allotrope(spec, tmpl, mono, temperature_k=temperature_k)
        raise KeyError(f"allotrope {allotrope_label!r} not in derived set for {spec.name}")

    def material_response(
        self,
        spec: MoleculeSpec,
        *,
        allotrope_label: str | None = None,
        phase: str = "solid",
        temperature_k: float = 273.15,
    ) -> dict[str, Any]:
        """Phase geometry + n, k_th, C_p, … via existing script mirrors."""
        import hqiv_phase_material_response as pmr

        return pmr.material_response_readout(
            spec.name,
            allotrope=allotrope_label or self.preferred_allotrope(spec).label,
            phase="solid" if phase == "solid" else "liquid",
            temperature_k=temperature_k,
        )

    def readout(self, spec: MoleculeSpec, **kwargs: Any) -> dict[str, Any]:
        """Full lab witness: monomer → allotropes → preferred → optional response."""
        mono = self.monomer_geometry(spec)
        cands = self.derive_allotropes(spec, temperature_k=kwargs.get("temperature_k", 273.15))
        best = cands[0] if cands else None
        out: dict[str, Any] = {
            "molecule": spec.name,
            "molecular_weight_amu": spec.molecular_weight_amu,
            "monomer": {
                "motif": mono.motif.value,
                "intermolecular_contacts": mono.intermolecular_contacts,
                "mean_bond_length_angstrom": mono.mean_bond_length_angstrom,
                "bond_angle_deg": mono.bond_angle_rad * 180.0 / 3.14159265,
                "lone_pairs": mono.lone_pair_count,
            },
            "allotropes": [c.to_dict() for c in cands],
            "preferred_allotrope": best.to_dict() if best else None,
        }
        if kwargs.get("include_response", True) and best is not None:
            out["material_response"] = self.material_response(
                spec,
                allotrope_label=best.label,
                phase=kwargs.get("phase", "solid"),
                temperature_k=kwargs.get("temperature_k", 273.15),
            )
        return out

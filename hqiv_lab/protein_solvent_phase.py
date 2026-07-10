"""
Aqueous protein folding: bulk water ρ + directional local shape curvature.

Lean mirror: ``Hqiv.ProteinResearch.ProteinSolventPhaseGeometry``.

Bulk liquid H₂O supplies homogeneous curvature via ``meltComparisonCurvatureDensityFraction``.
Heavy-atom / backbone shape augments the local readout through inverse-square slots and
**directional** alignment of the contact chord with local backbone flow (helix axis vs
sheet–helix cross register).

Interface dress: hydrophobic/hydrophilic exposure biases local ``f_LDL`` (two-liquid
mixture spine) before ρ_curv enters the contact horizon budget.
"""

from __future__ import annotations

import math
from functools import lru_cache
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from hqiv_lab.miniprotein_backbone import Vec3
    from hqiv_lab.miniprotein_contacts import TertiaryContact

# Å-scale first-shell aqueous pivot (H-bond contact reference, not fitted).
AQUEOUS_BULK_PIVOT_ANGSTROM = 2.8

# Lean ``ProteinFoldThermodynamics`` reference temperatures (Kelvin).
H2O_BULK_MELT_TEMPERATURE_K = 273.15
CRYO_CRYSTALLOGRAPHY_TEMPERATURE_K = 100.0
PROTEIN_FOLDING_TEMPERATURE_K = 310.15

InterfaceExposure = str  # "hydrophobic" | "hydrophilic" | "neutral"


def _clamp_medium_density(rho: float) -> float:
    return min(1.0, max(0.0, rho))


def directional_register_baseline_rho(contact_kind: str) -> float:
    """
    Lean ``directionalLocalNetworkRho register 0`` at zero flow alignment.

    Baseline slots from ``ProteinSolventPhaseGeometry`` (not fitted).
    """
    if contact_kind in ("helix_i3", "helix_i4"):
        return 0.30
    if contact_kind == "helix_sheet":
        return 0.20 + 0.55  # flow = 0 → (1 - |flow|) = 1
    if contact_kind == "sheet_i2":
        return 0.40
    if contact_kind == "hydrophobic":
        return 0.35
    if contact_kind == "terminus":
        return 0.25
    return _clamp_medium_density(0.45)


def directional_register_baseline_rho_max() -> float:
    """Max baseline slot across registers (normalization for static kind weights)."""
    kinds = ("helix_i3", "helix_i4", "helix_sheet", "sheet_i2", "hydrophobic", "terminus")
    return max(directional_register_baseline_rho(k) for k in kinds)


def aqueous_bulk_curvature_fraction() -> float:
    """Lean ``aqueousBulkCurvatureFraction`` (= melt comparison, physiological default)."""
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_phase_geometry_density as pgd

    return pgd.melt_comparison_curvature_density_fraction()


@lru_cache(maxsize=32)
def aqueous_bulk_curvature_at_t(temperature_k: float, melt_k: float = 273.15) -> float:
    """
    Lean ``aqueousBulkCurvatureAtT`` — ice crystalline bulk below melt, liquid above.

    Cryo crystallography (~100 K) sits on the frozen network; cytosolic folding (~310 K)
    on the melt-released liquid comparison (ρ = 1).
    """
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_phase_geometry_density as pgd

    if temperature_k < melt_k:
        cell = pgd.phase_unit_cell(
            "H2O",
            "Ih",
            temperature_k=temperature_k,
        )
        rho_g = pgd.density_g_cm3(cell)
        return pgd.curvature_density_fraction(rho_g, "H2O")
    return pgd.melt_comparison_curvature_density_fraction()


def interface_exposure_from_contact_kind(contact_kind: str) -> InterfaceExposure:
    """Map tertiary contact register to solvent interface exposure class."""
    if contact_kind == "hydrophobic":
        return "hydrophobic"
    if contact_kind in ("helix_sheet", "terminus", "helix_i3", "helix_i4", "sheet_i2"):
        return "hydrophilic"
    return "neutral"


def local_low_density_fraction_at_interface(
    f_bulk: float,
    exposure: InterfaceExposure,
) -> float:
    """
    Lean ``localLowDensityFractionAtInterface`` — hydrophobic → LDL, hydrophilic → HDL.
    """
    from hqiv_lab.phase_diagram import ALPHA, GAMMA

    f = _clamp_medium_density(f_bulk)
    boost = GAMMA * ALPHA
    if exposure == "hydrophobic":
        return _clamp_medium_density(f + (1.0 - f) * boost)
    if exposure == "hydrophilic":
        return _clamp_medium_density(f * (1.0 - ALPHA))
    return f


def bulk_low_density_fraction(
    temperature_k: float,
    pressure_pa: float | None = None,
    *,
    melt_k: float = H2O_BULK_MELT_TEMPERATURE_K,
) -> float:
    """Bulk ``f_LDL`` from the (T,P) phase engine (0 on HDL liquid branch)."""
    from hqiv_lab.phase_diagram import low_density_liquid_fraction, material_scales_for_spec
    from hqiv_lab.spec import resolve_spec

    import hqiv_thermodynamic_phase_from_tp as tptp

    if pressure_pa is None:
        pressure_pa = tptp.STP_PRESSURE_PA
    mat = material_scales_for_spec(
        resolve_spec("H2O"), bulk=True, temperature_k=temperature_k
    )
    env = tptp.ThermodynamicEnvironment(temperature_k, pressure_pa)
    state = tptp.derive_phase(env, mat)
    if state.phase == tptp.DerivedPhase.LIQUID:
        return 0.0
    if state.phase != tptp.DerivedPhase.METASTABLE_LIQUID:
        return 0.0
    return low_density_liquid_fraction(temperature_k, pressure_pa, mat)


def _interface_mixture_dress_active(
    temperature_k: float,
    *,
    melt_k: float = H2O_BULK_MELT_TEMPERATURE_K,
    pressure_pa: float | None = None,
) -> bool:
    """True when (T,P) sits on a liquid branch that supports LDL/HDL mixture dress."""
    import hqiv_thermodynamic_phase_from_tp as tptp
    from hqiv_lab.phase_diagram import material_scales_for_spec
    from hqiv_lab.spec import resolve_spec

    if pressure_pa is None:
        pressure_pa = tptp.STP_PRESSURE_PA
    if temperature_k >= melt_k:
        return True
    mat = material_scales_for_spec(
        resolve_spec("H2O"), bulk=True, temperature_k=temperature_k
    )
    env = tptp.ThermodynamicEnvironment(temperature_k, pressure_pa)
    state = tptp.derive_phase(env, mat)
    return state.phase == tptp.DerivedPhase.METASTABLE_LIQUID


def aqueous_mixture_curvature_at_interface(
    temperature_k: float,
    exposure: InterfaceExposure,
    *,
    pressure_pa: float | None = None,
    melt_k: float = H2O_BULK_MELT_TEMPERATURE_K,
) -> float:
    """
    Mixture ρ_curv at a protein–solvent interface from local ``f_LDL``.

    Below melt: crystalline bulk network.  At/above melt: LDL/HDL mixture dress.
    """
    from hqiv_lab.phase_diagram import (
        end_members_for_molecule,
        liquid_mixture_curvature_fraction,
    )

    if not _interface_mixture_dress_active(
        temperature_k, melt_k=melt_k, pressure_pa=pressure_pa
    ):
        return aqueous_bulk_curvature_at_t(temperature_k, melt_k)
    f_bulk = bulk_low_density_fraction(temperature_k, pressure_pa, melt_k=melt_k)
    f_local = local_low_density_fraction_at_interface(f_bulk, exposure)
    low, high = end_members_for_molecule("H2O")
    return liquid_mixture_curvature_fraction(f_local, low.rho_curv, high.rho_curv)


def local_hoh_angle_mixture_rad(f_local: float) -> float:
    """
    Lean ``localHohAngleMixtureAtInterface`` — LDL/HDL angle mixture in radians.

    End members: tetrahedral ``centreAngleRadFromDomains 4`` and gas
    ``dynamicCentreAngleRad 8 2`` (torque-tree witness).
    """
    from hqiv_lab.phase_diagram import hoh_angle_mixture_deg

    return math.radians(hoh_angle_mixture_deg(f_local))


def aqueous_hbond_pivot_dress_from_angle(theta_mix_rad: float, theta_gas_rad: float) -> float:
    """Lean ``aqueousHbPivotDressFromAngle`` — scale pivot by local tetrahedral opening."""
    if abs(theta_gas_rad) < 1e-30:
        return 1.0
    return theta_mix_rad / theta_gas_rad


def aqueous_hbond_pivot_at_interface(f_local: float) -> float:
    """Lean ``aqueousHbPivotAtInterface`` — dressed Å pivot from local ``f_LDL``."""
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_chemistry_tuft_dynamics as ctd

    theta_gas = ctd.dynamic_centre_angle_rad(8, 2)
    theta_mix = local_hoh_angle_mixture_rad(f_local)
    return AQUEOUS_BULK_PIVOT_ANGSTROM * aqueous_hbond_pivot_dress_from_angle(
        theta_mix, theta_gas
    )


def aqueous_angle_pivot_dress_factor(
    temperature_k: float,
    exposure: InterfaceExposure,
    *,
    pressure_pa: float | None = None,
    melt_k: float = H2O_BULK_MELT_TEMPERATURE_K,
) -> float:
    """θ_mix / θ_gas × shell H-acceptor pivot factor at a protein–solvent interface."""
    if not _interface_mixture_dress_active(
        temperature_k, melt_k=melt_k, pressure_pa=pressure_pa
    ):
        from hqiv_lab.peptide_shell_dress import aqueous_hbond_pivot_shell_factor

        return aqueous_hbond_pivot_shell_factor()
    f_bulk = bulk_low_density_fraction(temperature_k, pressure_pa, melt_k=melt_k)
    f_local = local_low_density_fraction_at_interface(f_bulk, exposure)
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_chemistry_tuft_dynamics as ctd
    from hqiv_lab.peptide_shell_dress import aqueous_hbond_pivot_shell_factor

    theta_gas = ctd.dynamic_centre_angle_rad(8, 2)
    angle_dress = aqueous_hbond_pivot_dress_from_angle(
        local_hoh_angle_mixture_rad(f_local), theta_gas
    )
    return angle_dress * aqueous_hbond_pivot_shell_factor()


def aqueous_bulk_pivot_at_contact(
    contact_kind: str,
    *,
    temperature_k: float | None = None,
    pressure_pa: float | None = None,
    melt_k: float = H2O_BULK_MELT_TEMPERATURE_K,
) -> float:
    """Interface-dressed bulk pivot for a tertiary contact register at fold T."""
    if temperature_k is None:
        return AQUEOUS_BULK_PIVOT_ANGSTROM
    exposure = interface_exposure_from_contact_kind(contact_kind)
    if not _interface_mixture_dress_active(
        temperature_k, melt_k=melt_k, pressure_pa=pressure_pa
    ):
        return AQUEOUS_BULK_PIVOT_ANGSTROM
    f_bulk = bulk_low_density_fraction(temperature_k, pressure_pa, melt_k=melt_k)
    f_local = local_low_density_fraction_at_interface(f_bulk, exposure)
    return aqueous_hbond_pivot_at_interface(f_local)


def fold_xi_from_temperature_k(temperature_k: float) -> float:
    """Lean ``foldXiFromTemperatureK`` via Hopf ξ = T_Pl / T."""
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_lean_physics_primitives as lean

    k_b_mev_per_k = 8.617333262e-11
    t_mev = k_b_mev_per_k * max(temperature_k, 1e-30)
    return lean.xi_from_T_MeV(t_mev)


def thermal_basin_amplitude(temperature_k: float, *, ref_k: float = 273.15) -> float:
    """Lean ``thermalBasinAmplitude`` — γ/6 weak-channel dress at fold T."""
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_lean_physics_primitives as lean

    ratio = max(temperature_k, ref_k) / max(ref_k, 1e-30)
    return ratio ** (lean.GAMMA / 6.0)


def thermal_peptide_contact_scale(temperature_k: float, *, ref_k: float = 273.15) -> float:
    """
    Legacy allotrope-class γ/16 breathing (Lean ``thermalPeptideContactScale``).

    Prefer ``lindemann_peptide_contact_scale`` for aqueous tertiary / outside dress —
    same Brownian piezo slot that pushed organic condensed residuals to ~1%.
    Kept for covalent backbone mild thermal and Lean identity theorems.
    """
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_lean_physics_primitives as lean

    ratio = max(temperature_k, ref_k) / max(ref_k, 1e-30)
    return ratio ** (lean.GAMMA / 16.0)


def lindemann_motif_for_contact_kind(contact_kind: str | None):
    """Map tertiary register → condensed packing motif (no molecule-name cases)."""
    from hqiv_lab.coordination import IntermolecularMotif

    if contact_kind == "hydrophobic":
        return IntermolecularMotif.APOLAR_CLOSE_PACK
    if contact_kind in (
        "helix_sheet",
        "terminus",
        "helix_i3",
        "helix_i4",
        "sheet_i2",
    ):
        return IntermolecularMotif.PEPTIDE_LAYER
    return IntermolecularMotif.PEPTIDE_LAYER


def lindemann_peptide_contact_scale(
    temperature_k: float,
    *,
    melt_k: float = H2O_BULK_MELT_TEMPERATURE_K,
    contact_kind: str | None = None,
    exposure: InterfaceExposure | None = None,
    phonon_cage: float = 0.0,
    stress_pa: float = 0.0,
    r0_angstrom: float | None = None,
    binding_ev: float | None = None,
    n_coord: float = 4.0,
) -> float:
    """
    Condensed piezo↔stiffness length dress for aqueous protein contacts.

    Lean: ``lindemannThermalStrain`` seed → ``strainFromStressStiffness`` fixed
    point → packing ``lindemann_contact_scale`` (``f^{1/3}`` with apolar open).

    Zero external stress recovers pure Lindemann (organic ~1% panel).  Optional
    ``stress_pa`` closes the mechanical loop when a wall/spectrum stress lands.
    Hydrophobic registers use apolar close-pack open; H-bond / helix registers use
    peptide-layer motif.
    """
    from hqiv_lab.coordination import IntermolecularMotif
    from hqiv_lab.packing import lindemann_contact_scale

    if exposure == "hydrophobic" and contact_kind is None:
        motif = IntermolecularMotif.APOLAR_CLOSE_PACK
    elif contact_kind is not None:
        motif = lindemann_motif_for_contact_kind(contact_kind)
    else:
        motif = IntermolecularMotif.PEPTIDE_LAYER
    return float(
        lindemann_contact_scale(
            temperature_k,
            melt_k,
            motif=motif,
            phonon_cage=phonon_cage,
            stress_pa=stress_pa,
            r0_angstrom=r0_angstrom,
            binding_ev=binding_ev,
            n_coord=n_coord,
        )
    )


def aqueous_phase_contact_weight(
    temperature_k: float | None = None,
    exposure: InterfaceExposure = "neutral",
    *,
    melt_k: float = H2O_BULK_MELT_TEMPERATURE_K,
    pressure_pa: float | None = None,
) -> float:
    """
    Spectral-analogue phase/contact weight for aqueous vs dilute gas.

    Gas assay: ρ → 0 ⇒ weight 0 (vacuum outside).
    Cytosol / ice network: ρ → 1 ⇒ weight 1 (full medium outside).
    """
    if temperature_k is None:
        temperature_k = PROTEIN_FOLDING_TEMPERATURE_K
    if (
        exposure is not None
        and _interface_mixture_dress_active(
            temperature_k, melt_k=melt_k, pressure_pa=pressure_pa
        )
    ):
        rho = aqueous_mixture_curvature_at_interface(
            temperature_k,
            exposure,
            pressure_pa=pressure_pa,
            melt_k=melt_k,
        )
    else:
        rho = aqueous_bulk_curvature_at_t(temperature_k, melt_k)
    return _clamp_medium_density(rho)


def peptide_register_steric_counts(contact_kind: str | None) -> tuple[int, int]:
    """
    Structural (n_σ, n_lp) for a tertiary register — Lean donor/acceptor excess inputs.

    No molecule-name cases: hydrophobic = apolar (no lp); H-bond / helix / sheet =
    peptide-layer amide–carbonyl contact (1σ donor vs 2 lp acceptor → acceptor excess).
    """
    if contact_kind == "hydrophobic":
        return (4, 0)  # Cα packing, no lone-pair channel
    if contact_kind in (
        "helix_sheet",
        "terminus",
        "helix_i3",
        "helix_i4",
        "sheet_i2",
    ):
        return (1, 2)  # carbonyl-class acceptor excess on H-bond registers
    return (1, 2)


def peptide_register_carrier_fraction(contact_kind: str | None) -> float:
    """
    Dimensionless carrier fraction for the thermo/Joule conductivity dress.

    Acceptor-excess weight on polar registers (Lean ``hbondAcceptorExcessWeight``);
    hydrophobic / apolar → 0 (identity).  No electrolyte SI mash.
    """
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_phase_material_response as pmr

    n_b, n_lp = peptide_register_steric_counts(contact_kind)
    return float(pmr.hbond_acceptor_excess_weight(n_b, n_lp))


def peptide_register_phonon_cage(
    temperature_k: float | None = None,
    *,
    rho_curv: float = 1.0,
) -> float:
    """Phonon cage ``1 − B_hom(foldXi(T), ρ)`` — heat-trapping complement."""
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_homogeneous_curvature_feedback as hcf

    if temperature_k is None:
        temperature_k = PROTEIN_FOLDING_TEMPERATURE_K
    xi = fold_xi_from_temperature_k(temperature_k)
    b_hom = hcf.homogeneous_curvature_budget_at_xi(xi, float(rho_curv))
    return _clamp_medium_density(1.0 - float(b_hom))


def peptide_register_carrier_thermo_dress(
    contact_kind: str | None,
    *,
    temperature_k: float | None = None,
    rho_curv: float = 1.0,
) -> float:
    """
    Lean ``carrierThermoConductivityDress`` on a tertiary energy channel.

    Identity when acceptor-carrier fraction is 0 (hydrophobic).  Does **not**
    rescale Cα nn length — conductivity/thermo loop only.
    """
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_voltage_generation_ledger as vgl

    return float(
        vgl.carrier_thermo_conductivity_dress(
            peptide_register_carrier_fraction(contact_kind),
            phonon_cage_fraction=peptide_register_phonon_cage(
                temperature_k, rho_curv=rho_curv
            ),
        )
    )


def aqueous_optical_length_dress(
    *,
    rho_curv: float,
    contact_kind: str | None = None,
    exposure: InterfaceExposure | None = None,
    n_dielectric: float = 1.33,
) -> dict[str, float]:
    """
    Donor/acceptor optical voltage dress for aqueous tertiary length scales.

    Lean ``VoltageGenerationLedger.opticalVoltageDress`` ×
    ``acceptorPolarizabilitySoftener``.  Geometric mean of donor optical and
    acceptor softener → isotropic length factor (same spirit as packing f^{1/3}).
    """
    import math

    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_phase_material_response as pmr

    kind = contact_kind
    if kind is None and exposure == "hydrophobic":
        kind = "hydrophobic"
    n_bonds, n_lp = peptide_register_steric_counts(kind)
    optical = float(
        pmr.optical_voltage_dress(
            float(rho_curv),
            float(n_dielectric),
            n_bonds=n_bonds,
            n_lone_pairs=n_lp,
        )
    )
    soft = float(pmr.acceptor_polarizability_softener(n_bonds, n_lp))
    # Length from volume-like optical × softener: geometric mean keeps O(γ) mild.
    length = math.sqrt(max(optical, 1e-30) * max(soft, 1e-30))
    return {
        "n_bonds": float(n_bonds),
        "n_lone_pairs": float(n_lp),
        "donor_excess": float(pmr.hbond_donor_excess_weight(n_bonds, n_lp)),
        "acceptor_excess": float(pmr.hbond_acceptor_excess_weight(n_bonds, n_lp)),
        "optical_voltage": optical,
        "acceptor_softener": soft,
        "length_scale": length,
    }


def aqueous_outside_geometry_scale(
    *,
    temperature_k: float | None = None,
    exposure: InterfaceExposure = "neutral",
    rho_local: float | None = None,
    contact_kind: str | None = None,
    melt_k: float = H2O_BULK_MELT_TEMPERATURE_K,
    pressure_pa: float | None = None,
    apply_thermal: bool = True,
    apply_optical: bool = True,
    stress_pa: float = 0.0,
) -> dict[str, float]:
    """
    Outside-ledger length scale for aqueous protein geometry (not gas-phase EM).

    Lean: ``OutsideContactLedger.outsideBulkChannel`` × ``outsideLocalDefectChannel``
    with bulk target ``homogeneousCurvatureBudgetAtXi(foldXi(T), 1)`` and site ρ from
    the aqueous mixture / bulk spine, times piezo↔stiffness (Lindemann-seeded).
    Donor/acceptor optical + carrier thermo are reported for energy-channel consumers
    but do **not** rescale Cα length.  Dilute gas (ρ=0) recovers identity.

    Covalent backbone bonds should *not* use this as a substitute for Engh–Huber;
    it dresses solvent-mediated tertiary Cα / contact scales.
    """
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_homogeneous_curvature_feedback as hcf
    import hqiv_outside_contact_ledger as ocl

    if temperature_k is None:
        temperature_k = PROTEIN_FOLDING_TEMPERATURE_K
    if contact_kind is not None:
        exposure = interface_exposure_from_contact_kind(contact_kind)
    if rho_local is None:
        if contact_kind is not None:
            rho_local = directional_register_baseline_rho(contact_kind)
        else:
            rho_local = 0.0

    xi = fold_xi_from_temperature_k(temperature_k)
    bulk_target = hcf.homogeneous_curvature_budget_at_xi(xi, 1.0)
    if (
        _interface_mixture_dress_active(
            temperature_k, melt_k=melt_k, pressure_pa=pressure_pa
        )
    ):
        rho_site = aqueous_mixture_curvature_at_interface(
            temperature_k,
            exposure,
            pressure_pa=pressure_pa,
            melt_k=melt_k,
        )
    else:
        rho_site = aqueous_bulk_curvature_at_t(temperature_k, melt_k)

    bulk = ocl.outside_bulk_channel(bulk_target, rho_site)
    excess = solvent_coordination_excess(rho_site, float(rho_local))
    local = ocl.outside_local_channel(excess)
    cage = peptide_register_phonon_cage(temperature_k, rho_curv=rho_site)
    thermal = (
        lindemann_peptide_contact_scale(
            temperature_k,
            melt_k=melt_k,
            contact_kind=contact_kind,
            exposure=exposure,
            phonon_cage=cage,
            stress_pa=stress_pa,
        )
        if apply_thermal
        else 1.0
    )
    optical = (
        aqueous_optical_length_dress(
            rho_curv=rho_site,
            contact_kind=contact_kind,
            exposure=exposure,
        )
        if apply_optical
        else {
            "length_scale": 1.0,
            "optical_voltage": 1.0,
            "acceptor_softener": 1.0,
            "donor_excess": 0.0,
            "acceptor_excess": 0.0,
            "n_bonds": 0.0,
            "n_lone_pairs": 0.0,
        }
    )
    thermo = (
        peptide_register_carrier_thermo_dress(
            contact_kind, temperature_k=temperature_k, rho_curv=rho_site
        )
        if apply_optical
        else 1.0
    )
    phase_w = aqueous_phase_contact_weight(
        temperature_k, exposure, melt_k=melt_k, pressure_pa=pressure_pa
    )
    # Length = bulk × local × piezo↔stiffness only. Optical/thermo → energy channel.
    scale = bulk * local * thermal
    return {
        "xi": xi,
        "bulk_target": bulk_target,
        "rho_site": rho_site,
        "rho_local": float(rho_local),
        "coordination_excess": excess,
        "bulk": bulk,
        "local_defect": local,
        "thermal": thermal,
        "thermal_channel": "piezo_stiffness" if apply_thermal else "off",
        "phonon_cage": cage,
        "stress_pa": float(stress_pa),
        "optical_length": 1.0,  # not applied to Cα nn
        "optical_voltage": float(optical["optical_voltage"]),
        "acceptor_softener": float(optical["acceptor_softener"]),
        "donor_excess": float(optical["donor_excess"]),
        "acceptor_excess": float(optical["acceptor_excess"]),
        "carrier_thermo": float(thermo),
        "phase_contact_weight": phase_w,
        "scale": scale,
    }


def solvent_curvature_density_at_site(
    rho_local_network: float,
    r_contact_angstrom: float,
    r_bulk_pivot_angstrom: float = AQUEOUS_BULK_PIVOT_ANGSTROM,
    *,
    temperature_k: float | None = None,
    melt_k: float = 273.15,
    interface_exposure: InterfaceExposure | None = None,
    pressure_pa: float | None = None,
) -> float:
    """Lean ``solventCurvatureDensityAtSite`` / interface-dressed bulk at fold T."""
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_phase_geometry_density as pgd

    w_bulk = pgd.orbital_bulk_dominance_weight(
        r_bulk_pivot_angstrom, r_contact_angstrom
    )
    if (
        temperature_k is not None
        and interface_exposure is not None
        and _interface_mixture_dress_active(
            temperature_k, melt_k=melt_k, pressure_pa=pressure_pa
        )
    ):
        rho_bulk = aqueous_mixture_curvature_at_interface(
            temperature_k,
            interface_exposure,
            pressure_pa=pressure_pa,
            melt_k=melt_k,
        )
    elif temperature_k is not None:
        rho_bulk = aqueous_bulk_curvature_at_t(temperature_k, melt_k)
    else:
        rho_bulk = aqueous_bulk_curvature_fraction()
    return _clamp_medium_density(
        w_bulk * rho_bulk + (1.0 - w_bulk) * _clamp_medium_density(rho_local_network)
    )


def solvent_coordination_excess(rho_hom: float, rho_local_raw: float) -> float:
    """Lean ``solventCoordinationExcess`` / ``nucleationCoordinationExcess``."""
    return max(rho_local_raw - _clamp_medium_density(rho_hom), 0.0)


def protein_horizon_curvature_budget(xi: float, rho_site: float) -> float:
    """Lean ``proteinHorizonCurvatureBudget``."""
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_homogeneous_curvature_feedback as hcf

    return hcf.homogeneous_curvature_budget_at_xi(xi, rho_site)


def protein_effective_curvature_budget(
    xi: float,
    rho_site: float,
    rho_local_raw: float,
) -> float:
    """Lean ``proteinEffectiveCurvatureBudget``."""
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_homogeneous_curvature_feedback as hcf

    excess = solvent_coordination_excess(rho_site, rho_local_raw)
    return hcf.effective_curvature_budget(xi, rho_site, excess)


def _unit_tangent(ca: list[Vec3], i: int) -> tuple[float, float, float]:
    n = len(ca)
    if n < 2:
        return (0.0, 0.0, 1.0)
    if i <= 0:
        vx, vy, vz = ca[1][0] - ca[0][0], ca[1][1] - ca[0][1], ca[1][2] - ca[0][2]
    elif i >= n - 1:
        vx, vy, vz = ca[i][0] - ca[i - 1][0], ca[i][1] - ca[i - 1][1], ca[i][2] - ca[i - 1][2]
    else:
        vx = ca[i + 1][0] - ca[i - 1][0]
        vy = ca[i + 1][1] - ca[i - 1][1]
        vz = ca[i + 1][2] - ca[i - 1][2]
    mag = math.sqrt(vx * vx + vy * vy + vz * vz)
    if mag < 1e-12:
        return (0.0, 0.0, 1.0)
    return (vx / mag, vy / mag, vz / mag)


def _dot(a: tuple[float, float, float], b: tuple[float, float, float]) -> float:
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]


def directional_local_network_rho(
    ca: list[Vec3],
    contact: TertiaryContact,
    ss: list[str] | None,
) -> float:
    """
    Local network ρ from **directional** backbone shape at a tertiary contact.

    • Intra-helix axial register (i, i+3/4): high ρ when chord aligns with helix flow.
    • Sheet–helix cross register: elevated ρ when chord is *transverse* to strand flow.
    • Hydrophobic / terminus: moderate bulk-dominated background.
    """
    i, j = contact.i, contact.j
    si = ss[i] if ss and i < len(ss) else "C"
    sj = ss[j] if ss and j < len(ss) else "C"
    ci = _unit_tangent(ca, i)
    cj = _unit_tangent(ca, j)
    vx = ca[j][0] - ca[i][0]
    vy = ca[j][1] - ca[i][1]
    vz = ca[j][2] - ca[i][2]
    cmag = math.sqrt(vx * vx + vy * vy + vz * vz)
    if cmag < 1e-12:
        chord = (0.0, 0.0, 1.0)
    else:
        chord = (vx / cmag, vy / cmag, vz / cmag)
    flow = 0.5 * (abs(_dot(ci, chord)) + abs(_dot(cj, chord)))

    if contact.kind in ("helix_i3", "helix_i4"):
        return _clamp_medium_density(0.30 + 0.70 * flow)
    if contact.kind == "helix_sheet":
        return _clamp_medium_density(0.20 + 0.55 * (1.0 - flow))
    if contact.kind == "sheet_i2":
        return _clamp_medium_density(0.40 + 0.35 * flow)
    if contact.kind == "hydrophobic":
        return 0.35
    if contact.kind == "terminus":
        return 0.25
    return 0.45


def contact_curvature_weight(
    ca: list[Vec3],
    contact: TertiaryContact,
    ss: list[str] | None,
    *,
    xi: float | None = None,
    temperature_k: float | None = None,
    bulk_pivot_angstrom: float = AQUEOUS_BULK_PIVOT_ANGSTROM,
    melt_k: float = 273.15,
) -> float:
    """SSE weight from effective curvature budget at the contact horizon."""
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_lean_physics_primitives as lean

    if xi is None:
        # Contact horizon stays at lock-in shell (ξ = 5); laboratory T dresses bulk ρ only.
        # Lean ``contactCurvatureWeightAtEnv`` uses ``foldXiFromTemperatureK`` for the
        # thermodynamic witness; fold closure anchors here at ``xiLockin`` like the
        # pre-T ``ProteinSolventPhaseGeometry`` spine.
        xi = lean.XI_LOCKIN
    vx = ca[contact.j][0] - ca[contact.i][0]
    vy = ca[contact.j][1] - ca[contact.i][1]
    vz = ca[contact.j][2] - ca[contact.i][2]
    r_contact = math.sqrt(vx * vx + vy * vy + vz * vz)
    rho_local = directional_local_network_rho(ca, contact, ss)
    exposure = interface_exposure_from_contact_kind(contact.kind)
    if temperature_k is None:
        pivot = bulk_pivot_angstrom
    else:
        pivot = aqueous_bulk_pivot_at_contact(
            contact.kind,
            temperature_k=temperature_k,
            melt_k=melt_k,
        )
    rho_site = solvent_curvature_density_at_site(
        rho_local,
        r_contact,
        pivot,
        temperature_k=temperature_k,
        melt_k=melt_k,
        interface_exposure=exposure,
    )
    budget = protein_effective_curvature_budget(xi, rho_site, rho_local)
    # Shell energy-share weight (same language as spectral energy projection).
    from hqiv_lab.peptide_shell_dress import tertiary_contact_energy_weight

    return budget * tertiary_contact_energy_weight(contact.kind)


def contact_curvature_weights(
    ca: list[Vec3],
    contacts: tuple[TertiaryContact, ...],
    ss: list[str] | None = None,
    *,
    xi: float | None = None,
    temperature_k: float | None = None,
    bulk_pivot_angstrom: float = AQUEOUS_BULK_PIVOT_ANGSTROM,
    melt_k: float = H2O_BULK_MELT_TEMPERATURE_K,
) -> tuple[float, ...]:
    """Per-contact weights for curvature-dressed tertiary closure."""
    return tuple(
        contact_curvature_weight(
            ca,
            c,
            ss,
            xi=xi,
            temperature_k=temperature_k,
            bulk_pivot_angstrom=bulk_pivot_angstrom,
            melt_k=melt_k,
        )
        for c in contacts
    )

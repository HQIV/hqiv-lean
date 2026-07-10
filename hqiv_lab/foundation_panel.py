"""Foundation validation reference panel — benchmark witnesses only.

All ``reference_*`` fields are external literature / NIST / crystallographic values
used **only** to grade HQIV readouts. They must never be imported by geometry,
binding, packing, or folding builders as fit inputs or hardcoded targets.

Witness temperatures label the thermodynamic state at which comparisons are made
(solid @ melt, liquid @ 298.15 K, etc.); they are not tuning knobs.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

FoundationTier = Literal[
    "tier0_binding",
    "tier0_condensed",
    "tier1_polyol",
    "tier1_sugar",
    "tier2_peptide_crystal",
    "tier2_peptide_geometry",
    "tier3_peptide_fold",
]

ComparisonPolicy = (
    "Literature/NIST/COD values for benchmark comparison only — never HQIV fit inputs"
)


@dataclass(frozen=True)
class FoundationCondensedReference:
    """Condensed-phase witness for a molecular solid or liquid reference state."""

    name: str
    formula: str
    tier: FoundationTier
    allotrope: str
    motif_label: str
    witness_temperature_k: float
    reference_density_g_cm3: float | None
    reference_refractive_index: float | None
    reference_melt_k: float | None
    reference_source: str
    reference_citation: str
    hqiv_spec_available: bool
    notes: str = ""


@dataclass(frozen=True)
class PeptideGeometryReference:
    """Backbone internal coordinate witnesses (comparison to high-resolution peptide crystals)."""

    name: str
    tier: FoundationTier
    quantity: str
    reference_value: float
    unit: str
    reference_source: str
    reference_citation: str
    notes: str = ""


@dataclass(frozen=True)
class PeptideFoldReference:
    """Peptide fold grading witness — structure source and pass threshold."""

    name: str
    sequence: str
    tier: FoundationTier
    structure_source: str
    structure_id: str | None
    ca_rmsd_pass_angstrom: float
    reference_source: str
    reference_citation: str
    notes: str = ""


# --- Tier 0: inherited from existing GMTKN55 + condensed panel (re-exported in JSON) ---

# --- Tier 1: polyols (H-bond ladder between H2O and carbohydrates) ---

POLYOL_FOUNDATION_REFERENCES: tuple[FoundationCondensedReference, ...] = (
    FoundationCondensedReference(
        name="CH3OH",
        formula="CH3OH",
        tier="tier1_polyol",
        allotrope="liquid",
        motif_label="primary_alcohol / liquid @ 298 K",
        witness_temperature_k=298.15,
        reference_density_g_cm3=0.7918,
        reference_refractive_index=1.3284,
        reference_melt_k=175.59,
        reference_source="NIST Chemistry WebBook",
        reference_citation=(
            "NIST WebBook ID C67561: Tfus avg 175.59 K; "
            "liquid rho 0.7918 g/cm3 and nD 1.3284 at 20 C (CRC/NIST compilation)"
        ),
        hqiv_spec_available=True,
        notes="Liquid witness at 298 K; solid rho/n morphology-dependent (ice studies 0.64–0.84 g/cm3).",
    ),
    FoundationCondensedReference(
        name="C3H8O3",
        formula="C3H8O3",
        tier="tier1_polyol",
        allotrope="liquid",
        motif_label="triol / liquid @ 298 K",
        witness_temperature_k=298.15,
        reference_density_g_cm3=1.259,
        reference_refractive_index=1.473,
        reference_melt_k=291.05,
        reference_source="NIST Chemistry WebBook / KDB",
        reference_citation=(
            "Glycerol (CID 753): Tfus 291.05 K (NIST); "
            "liquid rho 1259 kg/m3 at 298.15 K; n ≈ 1.473 at 20 C (CRC/PubChem)"
        ),
        hqiv_spec_available=True,
        notes="Glass/crystal polymorphism; liquid witness chosen for polyol ladder step.",
    ),
)

# --- Tier 1: sugars ---

SUGAR_FOUNDATION_REFERENCES: tuple[FoundationCondensedReference, ...] = (
    FoundationCondensedReference(
        name="C6H12O6_alpha",
        formula="C6H12O6",
        tier="tier1_sugar",
        allotrope="chair",
        motif_label="pyranose chair / polyol H-bond network",
        witness_temperature_k=414.0,
        reference_density_g_cm3=1.562,
        reference_refractive_index=None,
        reference_melt_k=414.0,
        reference_source="NIST Chemistry WebBook / PubChem",
        reference_citation=(
            "alpha-D-glucose anhydrous: rho 1.5620 g/cm3 at 18 C/4 C (PubChem); "
            "Delta_fusH at 414 K (Parks & Thomas 1934, NIST WebBook ID C492626)"
        ),
        hqiv_spec_available=True,
        notes="Solid n not tabulated in NIST WebBook; decomposes on heating past fusion witness.",
    ),
    FoundationCondensedReference(
        name="C6H12O6_monohydrate",
        formula="C6H12O6.H2O",
        tier="tier1_sugar",
        allotrope="alpha_monohydrate",
        motif_label="pyranose hydrate / monoclinic",
        witness_temperature_k=373.15,
        reference_density_g_cm3=1.54,
        reference_refractive_index=None,
        reference_melt_k=373.15,
        reference_source="PubChem / CRC",
        reference_citation=(
            "alpha-D-glucose monohydrate: rho 1.54 g/cm3 at 25 C/4 C (PubChem); "
            "MP ~83 C (dec.) commercial hydrate form"
        ),
        hqiv_spec_available=False,
        notes="Hydrate allotrope; distinct from anhydrous fusion witness at 414 K.",
    ),
    FoundationCondensedReference(
        name="C12H22O11",
        formula="C12H22O11",
        tier="tier1_sugar",
        allotrope="chair",
        motif_label="disaccharide chair / glycosidic link",
        witness_temperature_k=462.0,
        reference_density_g_cm3=1.587,
        reference_refractive_index=None,
        reference_melt_k=462.0,
        reference_source="NIST Chemistry WebBook / ICUMSA",
        reference_citation=(
            "Sucrose: rho 1.587 g/cm3 (25 C, d425); Tfus 461–462 K with decomposition "
            "(Kofler & Sitte 1950, NIST WebBook ID C57501); "
            "solid n not standard — 10 wt% solution nD20 = 1.34783 (CRC)"
        ),
        hqiv_spec_available=True,
        notes="Melting witness is decomposition onset; solid refractive index not used.",
    ),
)

# --- Tier 2: peptide crystal (condensed) ---

PEPTIDE_CRYSTAL_REFERENCES: tuple[FoundationCondensedReference, ...] = (
    FoundationCondensedReference(
        name="GlyGly",
        formula="C4H8N2O3",
        tier="tier2_peptide_crystal",
        allotrope="sheet",
        motif_label="dipeptide beta-sheet layer (backbone graph)",
        witness_temperature_k=298.15,
        reference_density_g_cm3=1.516,
        reference_refractive_index=None,
        reference_melt_k=535.15,
        reference_source="IUCr Acta Cryst B 2006 / COD",
        reference_citation=(
            "alpha-glycylglycine ambient: Dx 1.516 Mg/m3, space group P21/c "
            "(Moggach et al., Acta Cryst. B62, 310, 2006); "
            "MP 262–264 C dec. (Fisher Scientific product spec, CAS 556-50-3)"
        ),
        hqiv_spec_available=True,
        notes="Structure ID COD 2100438 series; zwitterionic crystal, sequence GG.",
    ),
)

# --- Tier 2: peptide backbone geometry (internal coordinates) ---

PEPTIDE_GEOMETRY_REFERENCES: tuple[PeptideGeometryReference, ...] = (
    PeptideGeometryReference(
        name="N_CA",
        tier="tier2_peptide_geometry",
        quantity="backbone_bond_length",
        reference_value=1.459,
        unit="angstrom",
        reference_source="Engh & Huber 1999",
        reference_citation="Engh RA, Huber R. Acta Cryst. 1999; D55:383-393 (peptide restraints)",
        notes="High-resolution protein crystallography average; not an HQIV input.",
    ),
    PeptideGeometryReference(
        name="CA_C",
        tier="tier2_peptide_geometry",
        quantity="backbone_bond_length",
        reference_value=1.525,
        unit="angstrom",
        reference_source="Engh & Huber 1999",
        reference_citation="Engh RA, Huber R. Acta Cryst. 1999; D55:383-393",
    ),
    PeptideGeometryReference(
        name="C_N_peptide",
        tier="tier2_peptide_geometry",
        quantity="backbone_bond_length",
        reference_value=1.336,
        unit="angstrom",
        reference_source="Engh & Huber 1999",
        reference_citation="Engh RA, Huber R. Acta Cryst. 1999; D55:383-393",
    ),
    PeptideGeometryReference(
        name="C_O",
        tier="tier2_peptide_geometry",
        quantity="backbone_bond_length",
        reference_value=1.231,
        unit="angstrom",
        reference_source="Engh & Huber 1999",
        reference_citation="Engh RA, Huber R. Acta Cryst. 1999; D55:383-393",
    ),
    PeptideGeometryReference(
        name="phi_alpha",
        tier="tier2_peptide_geometry",
        quantity="backbone_dihedral_deg",
        reference_value=-60.0,
        unit="degree",
        reference_source="Ramachandran plot literature centroid",
        reference_citation=(
            "Typical alpha-helix basin centroid near phi=-60, psi=-45 deg "
            "(Pauling/Corey/standard biochemistry texts)"
        ),
        notes="Basin centroid for comparison; HQIV rational alpha uses derived phi/psi.",
    ),
    PeptideGeometryReference(
        name="psi_alpha",
        tier="tier2_peptide_geometry",
        quantity="backbone_dihedral_deg",
        reference_value=-45.0,
        unit="degree",
        reference_source="Ramachandran plot literature centroid",
        reference_citation="Alpha-helix basin centroid (literature)",
    ),
)

# --- Tier 3: peptide fold grading ladder ---

PEPTIDE_FOLD_REFERENCES: tuple[PeptideFoldReference, ...] = (
    PeptideFoldReference(
        name="GG",
        sequence="GG",
        tier="tier3_peptide_fold",
        structure_source="COD/IUCr alpha-glycylglycine",
        structure_id="COD:2100438",
        ca_rmsd_pass_angstrom=2.0,
        reference_source="Crystallography Open Database",
        reference_citation="Moggach et al., Acta Cryst. B62, 310 (2006); ambient P21/c structure",
        notes="Extract Cα trace from zwitterionic crystal; 2-residue foundation gate.",
    ),
    PeptideFoldReference(
        name="ACE_ALA_NME",
        sequence="A",
        tier="tier3_peptide_fold",
        structure_source="OpenMM/ParmEd test conformation",
        structure_id="openmm:alanine-dipeptide-implicit.pdb",
        ca_rmsd_pass_angstrom=2.0,
        reference_source="OpenMM test systems",
        reference_citation=(
            "Ace-Ala-Nme capped dipeptide model geometry "
            "(OpenMM wrappers/python/tests/systems/alanine-dipeptide-implicit.pdb); "
            "not an experimental crystal — conformational reference only"
        ),
        notes="Capped dipeptide; grade backbone internal geometry before tertiary contacts.",
    ),
    PeptideFoldReference(
        name="GGG",
        sequence="GGG",
        tier="tier3_peptide_fold",
        structure_source="pending",
        structure_id=None,
        ca_rmsd_pass_angstrom=2.0,
        reference_source="TBD",
        reference_citation="Tripeptide crystal or high-quality model structure not yet pinned",
        notes="Placeholder witness; assign PDB/COD when structure source selected.",
    ),
    PeptideFoldReference(
        name="AAAA",
        sequence="AAAA",
        tier="tier3_peptide_fold",
        structure_source="extended_chain_control",
        structure_id=None,
        ca_rmsd_pass_angstrom=2.0,
        reference_source="HQIV extended-chain geometry witness",
        reference_citation=(
            "Four-residue extended control: no tertiary contacts; "
            "validates backbone placement before hairpin closure"
        ),
        notes="No experimental gold PDB in suite yet; extended phi/psi control.",
    ),
    PeptideFoldReference(
        name="trp_cage",
        sequence="NLYIQWLKDGGPSSGRPPPS",
        tier="tier3_peptide_fold",
        structure_source="wwPDB",
        structure_id="1L2Y",
        ca_rmsd_pass_angstrom=2.0,
        reference_source="Protein Data Bank",
        reference_citation="Neidigh JW et al., PNAS 2008; PDB 1L2Y (Trp-cage miniprotein)",
        notes="Competitive Cα RMSD < 2 Å gate (AlphaFold-class); same bar as every ladder length.",
    ),
)


def all_condensed_foundation_references() -> tuple[FoundationCondensedReference, ...]:
    return POLYOL_FOUNDATION_REFERENCES + SUGAR_FOUNDATION_REFERENCES + PEPTIDE_CRYSTAL_REFERENCES


def foundation_entry(name: str) -> FoundationCondensedReference:
    key = name.upper()
    for row in all_condensed_foundation_references():
        if row.name.upper() == key or row.formula.upper() == key:
            return row
    raise KeyError(f"no foundation condensed reference for {name!r}")


def peptide_fold_entry(name: str) -> PeptideFoldReference:
    key = name.upper()
    for row in PEPTIDE_FOLD_REFERENCES:
        if row.name.upper() == key or row.sequence.upper() == key:
            return row
    raise KeyError(f"no peptide fold reference for {name!r}")

import Hqiv.ProteinResearch.MiniproteinRamachandranRegister
import Hqiv.ProteinResearch.MiniproteinTertiaryContacts
import Hqiv.ProteinResearch.MiniproteinStagedNerfClosure
import Hqiv.ProteinResearch.ProteinSolventPhaseGeometry
import Hqiv.ProteinResearch.ProteinFoldThermodynamics
import Hqiv.QuantumChemistry.PeptideBackboneGeometry
import Hqiv.QuantumChemistry.CurvatureBondContact
import Hqiv.QuantumChemistry.MacroRicciFlowDynamics

/-!
# Miniprotein chemistry dynamics from first principles

No PDB inputs, no fitted Å.  All backbone slots chain:

1. **Forced lattice constants** ``α = 3/5``, ``γ = 2/5`` (informational monogamy on the null
   lattice; see ``AlphaGammaForcedByLattice``).
2. **Ramachandran basins** — φ/ψ register slots as rational multiples of π built only from α, γ
   (``MiniproteinRamachandran``).
3. **Derived bond geometry** — diamond-node bond lengths + dynamic centre angles
   (``PeptideBackboneGeometry``).
4. **Tertiary Cα targets** — helix i±3/4 and sheet i+2 scales from α, γ; hydrophobic graph from
   sequence alphabet only (``MiniproteinTertiaryContacts``).
5. **Aqueous curvature dress** — bulk melt-comparison ρ + inverse-square local augmentation at
   contact horizons (``ProteinSolventPhaseGeometry``); **temperature bridge**
   ``ProteinFoldThermodynamics`` (cryo ice bulk vs physiological liquid, T → ξ).
6. **Closure dynamics** — staged pass order: SS register before burial before terminus
   (``MiniproteinStagedNerfClosure`` / informational locality).

Python mirrors: ``hqiv_lab/miniprotein_backbone.py``, ``peptide_geometry.py``,
``protein_solvent_phase.py``, ``miniprotein_closure.py``.
-/

namespace Hqiv.ProteinResearch

open Hqiv
open Hqiv.QuantumChemistry
open Hqiv.Physics
open Real

/-!
## Ramachandran dynamics — all basins forced by α, γ
-/

/-- Every register basin φ slot is a rational multiple of π (α, γ only). -/
theorem strap_phi_forced_by_gamma :
    ramachandranStrapPhi = gamma_HQIV * Real.pi := rfl

theorem strap_psi_forced_by_alpha :
    ramachandranStrapPsi = (alpha / 2) * Real.pi := rfl

theorem distorted_helix_phi_forced :
    ramachandranDistortedHelixPhi = (gamma_HQIV + alpha / 2) * Real.pi / 2 := rfl

theorem alpha_helix_psi_dressed_forced :
    ramachandranAlphaPsiDressed = -Real.pi / 4 * (1 + gamma_HQIV / 6) := rfl

theorem sheet_helix_turn_phi_monogamy_blend :
    (basinRamachandranPair .sheetHelixTurn).phi =
      alpha * (-Real.pi / 3) + (1 - alpha) * (-2 * Real.pi / 3) := by
  rw [basin_sheet_helix_turn_is_alpha_bridge]
  simp only [ramachandranAlphaPhi, ramachandranBetaPhi]

theorem strap_distorted_turn_uses_alpha_blend :
    (basinRamachandranPair .strapHelixTurn).psi =
      (1 - alpha) * ramachandranStrapPsi + alpha * ramachandranDistortedHelixPsi := by
  simp only [basinRamachandranPair, ramachandranStrapHelixTurn, ramachandranStrapPair,
    ramachandranDistortedHelixPair, ramachandranStrapPsi, ramachandranDistortedHelixPsi]

theorem distorted_helix_phi_ne_alpha_helix_phi :
    ramachandranDistortedHelixPhi ≠ ramachandranAlphaPhi := by
  rw [ramachandran_distorted_helix_phi_rational]
  unfold ramachandranAlphaPhi
  nlinarith [Real.pi_pos]

theorem strap_phi_ne_beta_phi :
    ramachandranStrapPhi ≠ ramachandranBetaPhi := by
  rw [ramachandran_strap_phi_eq_gamma_pi]
  unfold ramachandranBetaPhi
  nlinarith [Real.pi_pos]

/-!
## Peptide geometry — contact scales from α, γ (not witnesses)
-/

theorem helix_i3_scale_from_alpha_gamma :
    helixCaIi3DistanceScale = 1 + alpha + gamma_HQIV / 4 := rfl

theorem sheet_i2_scale_from_gamma :
    sheetCaIi2DistanceScale = 1 + gamma_HQIV / 4 := rfl

theorem peptide_diameter_factor_from_alpha_gamma :
    peptideBackboneDiameterFactor = 2 * (1 + alpha + gamma_HQIV / 8) := rfl

theorem derived_tertiary_scale_is_backbone_contact :
    derivedTertiaryContactScale meanBond nInter =
      peptideBackboneContactDistance meanBond nInter := rfl

/-!
## Macro Ricci stacked-line dress (``MacroRicciFlowDynamics``)
-/

open Hqiv.QuantumChemistry (stackedLineOutsideCurvatureScale stackedLineContactBreathingScale
  macroRicciStackedLineBreathingScale macroRicciStackedLineDressedDistance)

theorem protein_open_beta_sheet_i2_dressed_distance (dOpen θ : ℝ) :
    macroRicciStackedLineDressedDistance dOpen θ = dOpen * stackedLineContactBreathingScale θ := rfl

/-!
## Solvent phase at fold horizon — bulk ρ + local defect channel
-/

theorem aqueous_fold_uses_melt_comparison_bulk :
    aqueousBulkCurvatureFraction = 1 := aqueousBulkCurvatureFraction_eq_one

theorem solvent_site_blends_bulk_with_local (ρLocal rContact : ℝ) :
    solventCurvatureDensityAtSite ρLocal rContact aqueousBulkPivotAngstrom =
      let wBulk := orbitalBulkDominanceWeight aqueousBulkPivotAngstrom rContact
      clampMediumDensity (wBulk * 1 + (1 - wBulk) * ρLocal) := by
  simp only [solventCurvatureDensityAtSite, aqueousBulkCurvatureFraction_eq_one]

theorem protein_effective_budget_uses_nucleation_excess (ξ ρSite ρLocal : ℝ) :
    proteinEffectiveCurvatureBudget ξ ρSite ρLocal =
      effectiveCurvatureBudgetAtXi ξ ρSite (solventCoordinationExcess ρSite ρLocal) := rfl

/-!
## Closure dynamics — locality order (register before burial)
-/

theorem structure_pass_precedes_hydrophobic_in_staged_order :
    stagedNerfPassOrder.head? = some .structureRegister ∧
      stagedNerfPassOrder.getLast? = some .fullPolish := by
  constructor <;> decide

theorem hydrophobic_pass_after_structure_register :
    ∃ p₁ p₂, p₁ ∈ stagedNerfPassOrder ∧ p₂ ∈ stagedNerfPassOrder ∧
      p₁ = .structureRegister ∧ p₂ = .hydrophobicBurial ∧
      (stagedNerfPassOrder.idxOf .structureRegister <
        stagedNerfPassOrder.idxOf .hydrophobicBurial) := by
  refine ⟨_, _, ?_, ?_, rfl, rfl, ?_⟩
  all_goals decide

theorem tertiary_contact_pass_register_before_burial :
    tertiaryContactPass .helix_i3 < tertiaryContactPass .hydrophobic := by
  simp [tertiaryContactPass]

theorem tertiary_contact_pass_burial_before_terminus :
    tertiaryContactPass .hydrophobic < tertiaryContactPass .terminus := by
  simp [tertiaryContactPass]

/-- Map tertiary contact kind → directional solvent register (Python ``contact_curvature_weight``). -/
def directionalRegisterOfContactKind (k : TertiaryContactKind) : DirectionalContactRegister :=
  match k with
  | .helix_i3 | .helix_i4 => .helixAxial
  | .helix_sheet => .helixSheetCross
  | .sheet_i2 => .sheetStrand
  | .hydrophobic => .hydrophobicBurial
  | .terminus => .terminusCap

theorem helix_i3_directional_register :
    directionalRegisterOfContactKind .helix_i3 = .helixAxial := rfl

theorem helix_sheet_directional_register :
    directionalRegisterOfContactKind .helix_sheet = .helixSheetCross := rfl

/-- Closure pass weight ``(pass + 1) / (maxPass + 1)`` for dynamic Ricci participation. -/
noncomputable def closurePassWeight (k : TertiaryContactKind) : ℝ :=
  (tertiaryContactPass k + 1 : ℝ) / (tertiaryContactPass .terminus + 1 : ℝ)

theorem closure_pass_weight_terminus :
    closurePassWeight .terminus = 1 := by
  unfold closurePassWeight tertiaryContactPass
  norm_num

theorem closure_pass_weight_register :
    closurePassWeight .helix_i3 = 1 / 3 := by
  unfold closurePassWeight tertiaryContactPass
  norm_num

noncomputable def contactDirectionalLocalRho (k : TertiaryContactKind) (flowAlignment : ℝ) : ℝ :=
  directionalLocalNetworkRho (directionalRegisterOfContactKind k) flowAlignment

/-!
## Temperature-linked fold environment (cryo crystal vs physiological)

See ``ProteinFoldThermodynamics``: bulk aqueous ρ and ξ_contact follow ``(T, P)``;
Ramachandran basins remain α/γ-rational at all T — thermal dress is a γ-channel amplitude
on closure weights and contact breathing, not a fitted force field.
-/

theorem cytosol_bulk_aqueous_curvature_is_melt_comparison :
    aqueousBulkCurvatureAtT proteinFoldingTemperatureKelvin h2oBulkMeltTemperatureKelvin = 1 := by
  exact aqueousBulkAtT_physiological_eq_one

theorem cryo_bulk_aqueous_curvature_is_ice_network :
    aqueousBulkCurvatureAtT cryoCrystallographyTemperatureKelvin h2oBulkMeltTemperatureKelvin =
      crystallineIceCurvatureFraction := aqueousBulkAtT_cryo_uses_ice

/-!
## Shell-equation dress on peptide / tertiary contacts

Python mirror: ``hqiv_lab/peptide_shell_dress.py``.  Same language as the spectral /
carbon packing stack (``shell_anchor_projection``): occupancy → open-channel fraction →
``1 + base · open²`` packing and ``em^(α · length_share)`` bond dress.  No molecule-type
cases — register topology and bond-slot capacity only.
-/

/-- Shared spectral contact share ``γ · strong`` (Python ``spectral_contact_share``). -/
noncomputable def peptideShellBaseShare : ℝ :=
  gamma_HQIV * strongChannelFraction

/-- Open-channel fraction from filled occupancy ``bo / capacity`` (clamped to ``[0,1]``). -/
noncomputable def peptideOpenChannelFraction (occupancy : ℝ) : ℝ :=
  max (0 : ℝ) (min (1 : ℝ) (1 - occupancy))

/-- Network packing scale ``1 + base · open²`` (Python ``network_open_channel_packing_scale``). -/
noncomputable def peptideNetworkOpenChannelPackingScale (occupancy : ℝ) : ℝ :=
  1 + peptideShellBaseShare * (peptideOpenChannelFraction occupancy) ^ 2

/-- Length share soft projection (filled channels + open lift; polarity omitted at 0). -/
noncomputable def peptideLengthShare (occupancy : ℝ) : ℝ :=
  let openLift := 1 + strongChannelFraction * peptideOpenChannelFraction occupancy
  max (0 : ℝ) (min (1 : ℝ) (peptideShellBaseShare * openLift))

/-- Register occupancy slots (Python ``REGISTER_OCCUPANCY``). -/
noncomputable def tertiaryRegisterOccupancy (k : TertiaryContactKind) : ℝ :=
  match k with
  | .helix_i3 => (3 : ℝ) / 4
  | .helix_i4 => (4 : ℝ) / 5
  | .sheet_i2 => (11 : ℝ) / 20
  | .helix_sheet => (9 : ℝ) / 20
  | .hydrophobic => (3 : ℝ) / 10
  | .terminus => (7 : ℝ) / 20

noncomputable def tertiaryContactPackingScale (k : TertiaryContactKind) : ℝ :=
  peptideNetworkOpenChannelPackingScale (tertiaryRegisterOccupancy k)

theorem peptide_shell_base_share_eq :
    peptideShellBaseShare = gamma_HQIV * strongChannelFraction := rfl

theorem peptide_network_packing_at_full_occupancy :
    peptideNetworkOpenChannelPackingScale 1 = 1 := by
  unfold peptideNetworkOpenChannelPackingScale peptideOpenChannelFraction
  norm_num

theorem tertiary_register_occupancy_helix_i4 :
    tertiaryRegisterOccupancy .helix_i4 = (4 : ℝ) / 5 := rfl

theorem tertiary_register_occupancy_hydrophobic :
    tertiaryRegisterOccupancy .hydrophobic = (3 : ℝ) / 10 := rfl

theorem hydrophobic_more_open_than_helix_i4 :
    tertiaryRegisterOccupancy .hydrophobic < tertiaryRegisterOccupancy .helix_i4 := by
  unfold tertiaryRegisterOccupancy
  norm_num

theorem helix_i4_open_channel_fraction :
    peptideOpenChannelFraction (tertiaryRegisterOccupancy .helix_i4) = (1 : ℝ) / 5 := by
  unfold peptideOpenChannelFraction tertiaryRegisterOccupancy
  norm_num

theorem helix_i4_packing_scale_explicit :
    tertiaryContactPackingScale .helix_i4 =
      1 + peptideShellBaseShare * ((1 : ℝ) / 5) ^ 2 := by
  unfold tertiaryContactPackingScale peptideNetworkOpenChannelPackingScale
  rw [helix_i4_open_channel_fraction]

theorem helix_i4_packing_gt_one :
    1 < tertiaryContactPackingScale .helix_i4 := by
  rw [helix_i4_packing_scale_explicit, peptide_shell_base_share_eq,
    gamma_eq_2_5, strongChannelFraction_eq_four_eighths]
  norm_num

/-!
## Register piezo / Brownian dress (constraint-system promotion)

Same Lindemann loader as condensed packing, keyed by register occupancy rather than
motif name:

`cage = (1 − occ) + strong · open²`,
`ε = clamp01((γ/2)·√(T/T_fold)·(1+cage))`,
`w_E *= 1 + strong·ε`,
`λ_pass *= 1 + strong·ε̄_pass`.

Identity at `T → 0` or full occupancy (`cage → 0`).  Energy / staged step only —
Cα length already carries outside piezo↔stiffness.
-/

/-- Coordination deficit + open-channel stress for a register occupancy. -/
noncomputable def registerPiezoCage (occupancy : ℝ) : ℝ :=
  let openFrac := peptideOpenChannelFraction occupancy
  openFrac + strongChannelFraction * openFrac ^ 2

/-- Lindemann thermal strain on a tertiary register (Brownian / piezo loader). -/
noncomputable def registerLindemannStrain
    (temperatureK meltK occupancy : ℝ) : ℝ :=
  if meltK ≤ 0 ∨ temperatureK ≤ 0 then 0
  else
    let amp := gamma_HQIV / 2
    let raw := amp * Real.sqrt (temperatureK / meltK) *
      (1 + registerPiezoCage occupancy)
    min 1 (max 0 raw)

/-- Energy / torque weight dress ``1 + (4/8)·ε_reg``. -/
noncomputable def registerPiezoEnergyDress
    (temperatureK meltK occupancy : ℝ) : ℝ :=
  1 + strongChannelFraction *
    registerLindemannStrain temperatureK meltK occupancy

/-- Staged closure step-size dress: mild ``1 + (4/8)·ε·(γ/2)`` (energy keeps full). -/
noncomputable def registerPiezoClosureStepDress
    (temperatureK meltK occupancy : ℝ) : ℝ :=
  1 + strongChannelFraction *
    registerLindemannStrain temperatureK meltK occupancy * (gamma_HQIV / 2)

noncomputable def tertiaryContactPiezoEnergyDress
    (k : TertiaryContactKind) (temperatureK meltK : ℝ) : ℝ :=
  registerPiezoEnergyDress temperatureK meltK (tertiaryRegisterOccupancy k)

theorem register_piezo_cage_full_occupancy :
    registerPiezoCage 1 = 0 := by
  unfold registerPiezoCage peptideOpenChannelFraction
  norm_num

theorem register_lindemann_strain_zero_temp (meltK occupancy : ℝ) :
    registerLindemannStrain 0 meltK occupancy = 0 := by
  unfold registerLindemannStrain
  split_ifs <;> first | rfl | simp_all

theorem register_piezo_energy_dress_zero_temp (meltK occupancy : ℝ) :
    registerPiezoEnergyDress 0 meltK occupancy = 1 := by
  unfold registerPiezoEnergyDress
  rw [register_lindemann_strain_zero_temp]
  ring

theorem register_piezo_closure_step_dress_zero_temp (meltK occupancy : ℝ) :
    registerPiezoClosureStepDress 0 meltK occupancy = 1 := by
  unfold registerPiezoClosureStepDress
  rw [register_lindemann_strain_zero_temp]
  ring

theorem hydrophobic_cage_gt_helix_i4 :
    registerPiezoCage (tertiaryRegisterOccupancy .helix_i4) <
      registerPiezoCage (tertiaryRegisterOccupancy .hydrophobic) := by
  unfold registerPiezoCage peptideOpenChannelFraction tertiaryRegisterOccupancy
  rw [strongChannelFraction_eq_four_eighths]
  norm_num

end Hqiv.ProteinResearch

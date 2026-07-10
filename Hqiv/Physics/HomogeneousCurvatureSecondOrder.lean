import Hqiv.Physics.DynamicBBNBaryogenesis
import Hqiv.Physics.HopfShellBeltramiMassBridge
import Hqiv.QuantumChemistry.DynamicBindingChart

/-!
# Homogeneous-curvature second order with local defect feedback

**Program (not yet the default chart):**

1. Compute the **homogeneous** curvature budget `B_hom(ξ, ρ)` at bulk medium density ρ
   (unity at dilute limit, full `B_curv(ξ)` at ice-like ρ = 1).
2. Add a **local** perturbation `δB` from nucleation / defect sites (coordination spike above
   the homogeneous background) — same geometric role as BBN `bbn_binding_curvature_perturbation`.
3. Feed `B_eff = B_hom + δB` back into the binding / melt readout (κ₆ and outside `G_eff`).

Nucleation sites matter because they break homogeneity: a dust grain, surface defect, or
local H-bond template raises `δB` before the bulk phase is stable.

Python mirror: `scripts/hqiv_homogeneous_curvature_feedback.py`.

Phase geometry supplies ρ without atom counting: `Hqiv.QuantumChemistry.PhaseGeometryDensity`.
-/

namespace Hqiv.Physics

open Hqiv
open Hqiv.QuantumChemistry

/-- Medium density ρ ∈ [0,1]: intermolecular coordination vs ice tetrahedral reference. -/
def clampMediumDensity (ρ : ℝ) : ℝ := max 0 (min 1 ρ)

/-- κ(ξ) coupling slot used as homogeneous curvature budget proxy (chart spine). -/
noncomputable def bindingCurvatureBudgetAtXi (ξ : ℝ) : ℝ :=
  dynamicBindingCurvatureCouplingAtXi ξ

/-- Homogeneous bulk curvature budget: dilute → 1, fully condensed → `bindingCurvatureBudgetAtXi`. -/
noncomputable def homogeneousCurvatureBudgetAtXi (ξ ρ : ℝ) : ℝ :=
  let ρc := clampMediumDensity ρ
  1 + ρc * (bindingCurvatureBudgetAtXi ξ - 1)

/-- Local defect excess above homogeneous background (nucleation / surface site). -/
noncomputable def localCurvatureDefectExcess (δ_coord : ℝ) : ℝ :=
  gamma_HQIV * strongChannelFraction * max δ_coord 0

/-- Effective curvature budget entering second-order feedback. -/
noncomputable def effectiveCurvatureBudgetAtXi (ξ ρ δ_coord : ℝ) : ℝ :=
  homogeneousCurvatureBudgetAtXi ξ ρ + localCurvatureDefectExcess δ_coord

/--
Second-order binding feedback using **effective** homogeneous+local budget.

Replaces bare `dynamicBindingCurvatureFeedbackSecondOrderAtXi` once the homogeneous
medium and nucleation defect are supplied — κ couples to `(B_eff − 1)` not raw chart ξ alone.
-/
noncomputable def bindingCurvatureFeedbackSecondOrderHomogeneous
    (ξ ρ δ_coord : ℝ) : ℝ :=
  let bEff := effectiveCurvatureBudgetAtXi ξ ρ δ_coord
  let κ := gamma_HQIV * strongChannelFraction * bEff
  let cRel := clusterBindingContrastRelative
  let c2Ratio := tuftLapseConcentrationAtXi ξ 0 0 / tuftLapseConcentrationAtXi xiLockin 0 0
  (1 + κ * cRel) * c2Ratio

/-- Nucleation raises local curvature: defect coordination above homogeneous ρ. -/
noncomputable def nucleationCoordinationExcess (ρ_hom ρ_local : ℝ) : ℝ :=
  max (ρ_local - clampMediumDensity ρ_hom) 0

theorem nucleationCoordinationExcess_nonneg (ρ_hom ρ_local : ℝ) :
    0 ≤ nucleationCoordinationExcess ρ_hom ρ_local := by
  unfold nucleationCoordinationExcess
  exact le_max_right (ρ_local - clampMediumDensity ρ_hom) 0

theorem homogeneousCurvatureBudgetAtXi_dilute (ξ : ℝ) :
    homogeneousCurvatureBudgetAtXi ξ 0 = 1 := by
  unfold homogeneousCurvatureBudgetAtXi clampMediumDensity
  simp

theorem homogeneousCurvatureBudgetAtXi_bulk (ξ : ℝ) :
    homogeneousCurvatureBudgetAtXi ξ 1 = bindingCurvatureBudgetAtXi ξ := by
  unfold homogeneousCurvatureBudgetAtXi clampMediumDensity bindingCurvatureBudgetAtXi
    dynamicBindingCurvatureCouplingAtXi
  simp [dynamicBindingCurvatureCouplingAtXi]

theorem localCurvatureDefectExcess_nonneg (δ : ℝ) :
    0 ≤ localCurvatureDefectExcess δ := by
  unfold localCurvatureDefectExcess
  apply mul_nonneg
  · apply mul_nonneg
    · rw [gamma_eq_2_5]; norm_num
    · rw [strongChannelFraction_eq_four_eighths]; norm_num
  · exact le_max_right δ 0

theorem effectiveCurvatureBudgetAtXi_ge_homogeneous (ξ ρ δ : ℝ) :
    homogeneousCurvatureBudgetAtXi ξ ρ ≤ effectiveCurvatureBudgetAtXi ξ ρ δ := by
  unfold effectiveCurvatureBudgetAtXi
  linarith [localCurvatureDefectExcess_nonneg δ]

/-! ## Defect formation energy (DFT-slot readout)

Outside `local` column surplus as an energy: the same
`localCurvatureDefectExcess` that dresses `M_out` multiplies the contact binding
depth.  Zero excess recovers zero formation cost (identity channel).

Python: ``scripts/hqiv_discrete_saddle_defect_readout.py``.
-/

/-- Defect formation energy [eV]:
`E_def = E_bind · localCurvatureDefectExcess(δ)`.
Equivalent to `E_bind · (outsideLocalDefectChannel(δ) − 1)`. -/
noncomputable def defectFormationEnergyEv (bindingEv δ_coord : ℝ) : ℝ :=
  bindingEv * localCurvatureDefectExcess δ_coord

theorem defectFormationEnergyEv_zero_excess (bindingEv : ℝ) :
    defectFormationEnergyEv bindingEv 0 = 0 := by
  unfold defectFormationEnergyEv localCurvatureDefectExcess
  simp

theorem defectFormationEnergyEv_nonneg
    (bindingEv δ_coord : ℝ) (hE : 0 ≤ bindingEv) :
    0 ≤ defectFormationEnergyEv bindingEv δ_coord := by
  unfold defectFormationEnergyEv
  exact mul_nonneg hE (localCurvatureDefectExcess_nonneg δ_coord)

/-- Cooperative vacancy formation: share the single-site defect across the
coordination shell ``E_vac = E_def / max(CN, 1)``.

For a monovacancy ``δ = 1/CN`` this is
``E_bind · γ · (4/8) / CN²``. -/
noncomputable def vacancyFormationEnergyEv
    (bindingEv δ_coord nCoord : ℝ) : ℝ :=
  defectFormationEnergyEv bindingEv δ_coord / max nCoord 1

theorem vacancyFormationEnergyEv_zero_excess (bindingEv nCoord : ℝ) :
    vacancyFormationEnergyEv bindingEv 0 nCoord = 0 := by
  unfold vacancyFormationEnergyEv
  rw [defectFormationEnergyEv_zero_excess]
  simp

/-- Grain-boundary formation scale: vacancy energy × ``γ``
(interface share of the cooperative vacancy across a misoriented contact).

``E_gb = γ · E_vac`` (= ``E_bind · γ² · (4/8) / CN²`` for δ=1/CN). -/
noncomputable def grainBoundaryFormationEnergyEv
    (bindingEv δ_coord nCoord : ℝ) : ℝ :=
  gamma_HQIV * vacancyFormationEnergyEv bindingEv δ_coord nCoord

theorem grainBoundaryFormationEnergyEv_zero_excess (bindingEv nCoord : ℝ) :
    grainBoundaryFormationEnergyEv bindingEv 0 nCoord = 0 := by
  unfold grainBoundaryFormationEnergyEv
  rw [vacancyFormationEnergyEv_zero_excess]
  simp

/-- Contact-edge gate on a rearrangement path = defect formation on that edge. -/
noncomputable def contactEdgeGateEv (bindingEv δ_coord : ℝ) : ℝ :=
  defectFormationEnergyEv bindingEv δ_coord

/-- Discrete saddle barrier [eV]: maximum edge gate along a contact-graph path.
Empty path → 0 (no barrier). -/
noncomputable def discreteSaddleBarrierEv (edgeGates : List ℝ) : ℝ :=
  edgeGates.foldl max 0

theorem discreteSaddleBarrierEv_nil :
    discreteSaddleBarrierEv [] = 0 := by
  unfold discreteSaddleBarrierEv; simp

theorem discreteSaddleBarrierEv_nonneg (edgeGates : List ℝ) :
    0 ≤ discreteSaddleBarrierEv edgeGates := by
  unfold discreteSaddleBarrierEv
  have h : ∀ (acc : ℝ) (xs : List ℝ), 0 ≤ acc → 0 ≤ xs.foldl max acc := by
    intro acc xs hacc
    induction xs generalizing acc with
    | nil => simpa
    | cons _ xs ih =>
      simp only [List.foldl]
      exact ih _ (le_trans hacc (le_max_left _ _))
  exact h 0 edgeGates (le_refl 0)

/-- Harmonic Morse saddle scale [eV] from `F²/(2k) = strong² · D`
(characteristic force / Hessian on the Morse backbone). -/
noncomputable def harmonicSaddleGateEv (bindingEv : ℝ) : ℝ :=
  strongChannelFraction ^ 2 * bindingEv

theorem harmonicSaddleGateEv_nonneg (bindingEv : ℝ) (h : 0 ≤ bindingEv) :
    0 ≤ harmonicSaddleGateEv bindingEv := by
  unfold harmonicSaddleGateEv
  have hs : 0 ≤ strongChannelFraction := by
    unfold strongChannelFraction; norm_num
  exact mul_nonneg (sq_nonneg _) h

end Hqiv.Physics

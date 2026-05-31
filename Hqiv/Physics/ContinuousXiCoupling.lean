import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Geometry.HQVMetric
import Hqiv.Geometry.OctonionicLightCone

namespace Hqiv
namespace Physics

/-!
# Continuous-ξ coupling witness

This module packages the Python `hqiv_coupling_linear_system.py` findings in Lean
terms, without importing numerical optimization into the proof layer.

The important formal move is that the electromagnetic sampling coordinate is the
continuous horizon coordinate

\[
  \xi = m+1 = \phi/2 = T_{\rm Pl}/T,
\]

while integer shells are chart samples of the same curve
`curvatureDensity`.  The numerical scan then lives as named witness data:

* normalization objective: the CODATA brace with `c₀ ≈ 1`, at `ξ_G ≈ 3.474`;
* structural objective: the density-weighted line/holonomy residual minimum,
  near `ξ_G ≈ 4.85`;
* mass/lock-in row: `Ω_k(ξ_lock)=1` at `ξ_lock = referenceM+1 = 5`.

No external lattice tables or fitted potentials are introduced here.
-/

/-- Continuous horizon coordinate attached to a shell chart point. -/
noncomputable def xiOfShell (m : Nat) : ℝ := (m + 1 : ℝ)

/-- Continuous auxiliary field slot: `φ = 2ξ`. -/
noncomputable def phiOfXi (ξ : ℝ) : ℝ := phiTemperatureCoeff * ξ

/-- O-Maxwell logarithmic slot on the continuous coordinate. -/
noncomputable def logPhiXi (ξ : ℝ) : ℝ :=
  alpha * Real.log (phiOfXi ξ + 1)

/-- Continuous shell shape, literally the Lean `curvatureDensity`. -/
noncomputable def sigmaXi (ξ : ℝ) : ℝ := curvatureDensity ξ

theorem sigmaXi_xiOfShell (m : Nat) :
    sigmaXi (xiOfShell m) = shell_shape m := by
  rw [shell_shape_eq_density_succ]
  rfl

theorem phiOfXi_xiOfShell (m : Nat) :
    phiOfXi (xiOfShell m) = phi_of_shell m := by
  unfold phiOfXi xiOfShell
  rw [phi_of_shell_closed_form]

/-- The GUT inverse coupling \(1/\alpha_{\rm GUT}=42\). -/
noncomputable def invAlphaGUT : ℝ := 42

theorem invAlphaGUT_eq_forty_two : invAlphaGUT = 42 := rfl

/-- Continuous O-Maxwell inverse coupling at horizon coordinate `ξ`. -/
noncomputable def oneOverAlphaEffXi (ξ c : ℝ) : ℝ :=
  invAlphaGUT * (1 + c * logPhiXi ξ)

/-- Shape ratio in the Gauss→EW brace. -/
noncomputable def sigmaRatio (ξG ξEW : ℝ) : ℝ :=
  sigmaXi ξG / sigmaXi ξEW

/-- Continuous brace readout:
`1/α(ξG) · σ(ξG)/σ(ξEW)`. -/
noncomputable def continuousBraceInvAlpha (c ξG ξEW : ℝ) : ℝ :=
  oneOverAlphaEffXi ξG c * sigmaRatio ξG ξEW

/-- Analytic primitive of `curvatureDensity` on the positive branch:
`∫ (1/ξ)(1+α log ξ)dξ = log ξ + (α/2)(log ξ)^2`.

The Python scan uses a numerical integral; this is the symbolic Lean-side object
for the same cumulative functional. -/
noncomputable def continuousCurvaturePrimitive (ξ : ℝ) : ℝ :=
  Real.log ξ + (alpha / 2) * (Real.log ξ) ^ 2

theorem continuousCurvaturePrimitive_one :
    continuousCurvaturePrimitive 1 = 0 := by
  simp [continuousCurvaturePrimitive]

/-- Continuous Ωₖ ratio against a lock-in horizon coordinate. -/
noncomputable def omegaKContinuous (ξ ξLock : ℝ) : ℝ :=
  if continuousCurvaturePrimitive ξLock = 0 then 1
  else continuousCurvaturePrimitive ξ / continuousCurvaturePrimitive ξLock

theorem omegaKContinuous_self (ξ : ℝ) :
    omegaKContinuous ξ ξ = 1 := by
  unfold omegaKContinuous
  by_cases h : continuousCurvaturePrimitive ξ = 0
  · simp [h]
  · simp [h]

/-- Reference lock-in coordinate: `referenceM = 4`, so `ξ_lock = 5`. -/
noncomputable def xiLockin : ℝ := xiOfShell referenceM

theorem xiLockin_eq_five : xiLockin = 5 := by
  unfold xiLockin xiOfShell referenceM qcdShell stepsFromQCDToLockin latticeStepCount
  norm_num

theorem omegaKContinuous_lockin :
    omegaKContinuous xiLockin xiLockin = 1 :=
  omegaKContinuous_self xiLockin

/-- The curvature primitive is positive for ξ > 1. -/
theorem continuousCurvaturePrimitive_pos_for_gt_one (ξ : ℝ) (h : 1 < ξ) :
    0 < continuousCurvaturePrimitive ξ := by
  unfold continuousCurvaturePrimitive
  have hlog : 0 < Real.log ξ := Real.log_pos h
  have hα : 0 < alpha := by unfold alpha; norm_num
  nlinarith [mul_pos hα (pow_pos hlog 2)]

/-- The curvature primitive is strictly increasing on (1, ∞) (its derivative is positive).

This is standard real analysis: the derivative (1/x)(1 + α log x) is positive for x > 1,
hence the function log x + (α/2)(log x)² is strictly increasing on (1, ∞).
The explicit factored difference `(Δlog) * (1 + (α/2) Σlog)` is positive by
strict monotonicity of `log` and positivity of the HQIV value `α = 3/5`.
-/
theorem continuousCurvaturePrimitive_strict_mono_gt_one (ξ1 ξ2 : ℝ)
    (h1 : 1 < ξ1) (h2 : ξ1 < ξ2) :
    continuousCurvaturePrimitive ξ1 < continuousCurvaturePrimitive ξ2 := by
  unfold continuousCurvaturePrimitive
  have hξ1_pos : 0 < ξ1 := by linarith
  set y1 : ℝ := Real.log ξ1
  set y2 : ℝ := Real.log ξ2
  set a : ℝ := alpha / 2
  have hy1_pos : 0 < y1 := by
    simpa [y1] using Real.log_pos h1
  have hy12 : y1 < y2 := by
    simpa [y1, y2] using Real.log_lt_log hξ1_pos h2
  have ha_pos : 0 < a := by
    subst a
    unfold alpha
    norm_num
  have hfactor_pos : 0 < (y2 - y1) * (1 + a * (y1 + y2)) := by
    have hdiff_pos : 0 < y2 - y1 := sub_pos.mpr hy12
    have hsum_pos : 0 < 1 + a * (y1 + y2) := by
      nlinarith
    exact mul_pos hdiff_pos hsum_pos
  have hfactor_eq :
      y2 + a * y2 ^ 2 - (y1 + a * y1 ^ 2) =
        (y2 - y1) * (1 + a * (y1 + y2)) := by
    ring
  have hdiff_pos : 0 < y2 + a * y2 ^ 2 - (y1 + a * y1 ^ 2) := by
    rwa [hfactor_eq]
  have hmain : y1 + a * y1 ^ 2 < y2 + a * y2 ^ 2 := sub_pos.mp hdiff_pos
  simpa [y1, y2, a] using hmain

/-- Preferred half-step sampled by the normalization objective. -/
noncomputable def xiHalfStep : ℝ := 7 / 2

theorem xiHalfStep_eq_three_point_five : xiHalfStep = 7 / 2 := rfl

/-- `Fin 7` vertex zero, the EM/Fano readout slot. -/
def fanoVertex0 : Fin 7 := ⟨0, by decide⟩

/-- Middle generation slot (`v = 1`, raw weight `2` in the `1,2,3` pattern). -/
def fanoVertexMiddle : Fin 7 := ⟨1, by decide⟩

/-- Heavy generation slot (`v = 2`, raw weight `3`). -/
def fanoVertexHeavyGen : Fin 7 := ⟨2, by decide⟩

/-- Raw Fano vertex weight pattern used by the Python solver: `1,2,3,1,2,3,1`. -/
noncomputable def fanoRawWeight (v : Fin 7) : ℝ :=
  (Nat.succ (v.val % 3) : ℝ)

/-- Same formula as `fanoRawWeight` on `v.val` (for normalization lemmas). -/
noncomputable def fanoRawWeightLookup (i : ℕ) : ℝ :=
  (Nat.succ (i % 3) : ℝ)

theorem fanoRawWeight_eq_lookup (v : Fin 7) : fanoRawWeight v = fanoRawWeightLookup v.val := rfl

/-- Sum of the raw pattern `1+2+3+1+2+3+1`. -/
noncomputable def fanoWeightSum : ℝ := 13

/-- Normalized Fano vertex weight. -/
noncomputable def fanoWeight (v : Fin 7) : ℝ :=
  fanoRawWeight v / fanoWeightSum

/-- Dimensionless row RHS after cancelling the `π/2` quarter-turn. -/
noncomputable def holonomyRowRhs (v : Fin 7) : ℝ :=
  (4 / 7 : ℝ) * (12 * fanoWeight v)

theorem holonomyRowRhs_zero :
    holonomyRowRhs fanoVertex0 = (48 : ℝ) / 91 := by
  unfold holonomyRowRhs fanoWeight fanoRawWeight fanoWeightSum fanoVertex0
  norm_num

/-- Middle generation slot (`v = 1`, raw weight `2`). -/
theorem holonomyRowRhs_middle :
    holonomyRowRhs fanoVertexMiddle = (96 : ℝ) / 91 := by
  unfold holonomyRowRhs fanoWeight fanoRawWeight fanoWeightSum fanoVertexMiddle
  norm_num

/-- Heavy generation slot (`v = 2`, raw weight `3`). -/
theorem holonomyRowRhs_heavyGen :
    holonomyRowRhs fanoVertexHeavyGen = (144 : ℝ) / 91 := by
  unfold holonomyRowRhs fanoWeight fanoRawWeight fanoWeightSum fanoVertexHeavyGen
  norm_num

/-! ## Admissible-cycle predicate for the three generation Fano vertices (T5/T10 advance)

Concrete combinatorial predicate replacing the former `True` scaffold.
The three generation-relevant vertices (light = fanoVertex0 with row 48/91,
middle with 96/91, heavyGen with 144/91) form an "admissible cycle" in the
sense required for discrete T10 overlap / mixing forms: they are distinct,
consecutive in the raw-weight pattern, and their holonomy rows are exactly
the proved arithmetic progression used by the T10 phase assembler and the
T1 chart-separation theorems.

This is the genuine overlap-form hook the roadmap requested. -/

def generationVerticesFormAdmissibleCycle : Prop :=
  fanoVertex0 ≠ fanoVertexMiddle ∧
  fanoVertexMiddle ≠ fanoVertexHeavyGen ∧
  fanoVertex0 ≠ fanoVertexHeavyGen ∧
  holonomyRowRhs fanoVertex0 = 48 / 91 ∧
  holonomyRowRhs fanoVertexMiddle = 96 / 91 ∧
  holonomyRowRhs fanoVertexHeavyGen = 144 / 91

theorem the_three_generation_fano_vertices_form_admissible_cycle :
    generationVerticesFormAdmissibleCycle := by
  unfold generationVerticesFormAdmissibleCycle
  constructor <;> try constructor <;> try constructor <;> try constructor <;> try constructor
  · decide
  · decide
  · decide
  · exact holonomyRowRhs_zero
  · exact holonomyRowRhs_middle
  · exact holonomyRowRhs_heavyGen

theorem holonomyRowRhs_heavyGen_div_middle :
    holonomyRowRhs fanoVertexHeavyGen / holonomyRowRhs fanoVertexMiddle = (3 : ℝ) / 2 := by
  rw [holonomyRowRhs_heavyGen, holonomyRowRhs_middle]
  norm_num

/-- Holonomy row RHS scales linearly with raw Fano weight: `(4/7)·12·(w/13)`. -/
theorem holonomyRowRhs_eq_fortyEight_over_ninetyOne_times_rawWeight (v : Fin 7) :
    holonomyRowRhs v = (48 : ℝ) / 91 * fanoRawWeight v := by
  unfold holonomyRowRhs fanoWeight fanoRawWeight fanoWeightSum
  ring_nf

/-- Weight ratio `3/2` from the `1,2,3` vertex pattern (middle / light slot). -/
theorem fanoHolonomyWeight_ratio_three_halves :
    ((3 : ℝ) / fanoWeightSum) / ((2 : ℝ) / fanoWeightSum) = (3 : ℝ) / 2 := by
  unfold fanoWeightSum
  norm_num

/-- Shifted weights `(w+1)` give `4/3` between slots `3` and `2`. -/
theorem fanoShiftedHolonomyWeight_ratio_four_thirds :
    ((3 : ℝ) + 1) / ((2 : ℝ) + 1) = (4 : ℝ) / 3 := by norm_num

theorem fanoWeightSum_ne_zero : fanoWeightSum ≠ 0 := by
  unfold fanoWeightSum
  norm_num

theorem fanoVertexMiddle_eq_finOne : fanoVertexMiddle = ⟨1, by decide⟩ := rfl

theorem fanoVertexHeavyGen_eq_finTwo : fanoVertexHeavyGen = ⟨2, by decide⟩ := rfl

theorem fanoRawWeightLookup_eq_succ_mod_lt {i : ℕ} (hi : i < 3) :
    fanoRawWeightLookup i = (i + 1 : ℝ) := by
  unfold fanoRawWeightLookup
  simp [Nat.mod_eq_of_lt hi]

theorem fanoRawWeightLookup_two_div_one :
    fanoRawWeightLookup 2 / fanoRawWeightLookup 1 = (3 : ℝ) / 2 := by
  rw [fanoRawWeightLookup_eq_succ_mod_lt (by decide : 2 < 3),
    fanoRawWeightLookup_eq_succ_mod_lt (by decide : 1 < 3)]
  norm_num

theorem fanoRawWeight_finTwo_div_finOne :
    fanoRawWeight fanoVertexHeavyGen / fanoRawWeight fanoVertexMiddle = (3 : ℝ) / 2 := by
  simpa [fanoRawWeight_eq_lookup, fanoVertexHeavyGen_eq_finTwo, fanoVertexMiddle_eq_finOne] using
    fanoRawWeightLookup_two_div_one

/-- Holonomy row ratio equals normalized Fano weight ratio. -/
theorem holonomyRowRhs_ratio_eq_fanoWeight_ratio {v₁ v₂ : Fin 7} (h₂ : fanoWeight v₂ ≠ 0) :
    holonomyRowRhs v₁ / holonomyRowRhs v₂ = fanoWeight v₁ / fanoWeight v₂ := by
  rw [holonomyRowRhs_eq_fortyEight_over_ninetyOne_times_rawWeight v₁,
    holonomyRowRhs_eq_fortyEight_over_ninetyOne_times_rawWeight v₂]
  have h48 : (48 : ℝ) / 91 ≠ 0 := by norm_num
  have hraw : fanoRawWeight v₂ ≠ 0 := by
    intro hz
    have : fanoWeight v₂ = 0 := by simp [fanoWeight, hz]
    exact h₂ this
  have hsum : (fanoWeightSum : ℝ) ≠ 0 := by norm_num [fanoWeightSum]
  calc ((48 : ℝ) / 91 * fanoRawWeight v₁) / ((48 : ℝ) / 91 * fanoRawWeight v₂)
      = fanoRawWeight v₁ / fanoRawWeight v₂ := by field_simp [h48, hraw]
    _ = fanoWeight v₁ / fanoWeight v₂ := by
      simp [fanoWeight, fanoWeightSum, div_eq_mul_inv]
      field_simp [hsum]

/-- Middle / heavy generation slots (`v = 1, 2`) carry weights `2/13` and `3/13`. -/
theorem fanoWeight_generation_middle_heavy_ratio :
    fanoWeight fanoVertexHeavyGen / fanoWeight fanoVertexMiddle = (3 : ℝ) / 2 := by
  calc
    fanoWeight fanoVertexHeavyGen / fanoWeight fanoVertexMiddle
        = fanoRawWeight fanoVertexHeavyGen / fanoRawWeight fanoVertexMiddle := by
      simp only [fanoWeight, fanoVertexHeavyGen, fanoVertexMiddle, fanoWeightSum]
      field_simp [fanoWeightSum_ne_zero]
    _ = (3 : ℝ) / 2 := fanoRawWeight_finTwo_div_finOne

theorem holonomyRowRhs_middle_heavy_ratio :
    holonomyRowRhs fanoVertexHeavyGen / holonomyRowRhs fanoVertexMiddle = (3 : ℝ) / 2 :=
  holonomyRowRhs_heavyGen_div_middle

/-- A one-row linear constraint on the seven `c_v` coefficients. -/
structure CouplingLinearRow where
  coeff : Fin 7 → ℝ
  target : ℝ

/-- Row evaluation against a coefficient vector. -/
noncomputable def CouplingLinearRow.eval (row : CouplingLinearRow) (c : Fin 7 → ℝ) : ℝ :=
  ∑ v : Fin 7, row.coeff v * c v

/-- Continuous brace row, linear in `c₀` once `ξG` and `ξEW` are chosen. -/
noncomputable def continuousBraceRow (ξG ξEW : ℝ) : CouplingLinearRow where
  coeff := fun v =>
    if v = fanoVertex0 then invAlphaGUT * logPhiXi ξG * sigmaRatio ξG ξEW else 0
  target := 137.035999177 - invAlphaGUT * sigmaRatio ξG ξEW

/-- Ωₖ mass/lock-in row: evaluate the EM coefficient at `ξ_lock = 5`
and scale the target by the same cumulative curvature functional. -/
noncomputable def omegaKMassRow (ξG : ℝ) : CouplingLinearRow where
  coeff := fun v => if v = fanoVertex0 then sigmaXi xiLockin else 0
  target := holonomyRowRhs fanoVertex0 * omegaKContinuous ξG xiLockin

theorem omegaKMassRow_target (ξG : ℝ) :
    (omegaKMassRow ξG).target =
      holonomyRowRhs fanoVertex0 * omegaKContinuous ξG xiLockin := rfl

theorem omegaKMassRow_lockin_target :
    (omegaKMassRow xiLockin).target = holonomyRowRhs fanoVertex0 := by
  rw [omegaKMassRow_target, omegaKContinuous_lockin]
  ring

/-- Localization energy `1/Θ_local(ξ)` on the continuous chart (`Θ = T_Pl/ξ`). -/
noncomputable def localizationEnergyXi (ξ : ℝ) : ℝ :=
  1 / (T_Pl / ξ)

theorem localizationEnergyXi_eq_xi_over_T_Pl (ξ : ℝ) (hξ : ξ ≠ 0) :
    localizationEnergyXi ξ = ξ / T_Pl := by
  unfold localizationEnergyXi
  rw [T_Pl_eq]
  field_simp [hξ]

/--
**Legacy informational-energy mass row** (per-vertex holonomy RHS share, `π/2` cancelled):

`c₀ + localization(ξ_G) = holonomyRowRhs(0) · Ω_k(ξ_G)`.
-/
noncomputable def informationalEnergyMassRowLegacy (ξG : ℝ) : CouplingLinearRow where
  coeff := fun v => if v = fanoVertex0 then 1 else 0
  target :=
    holonomyRowRhs fanoVertex0 * omegaKContinuous ξG xiLockin - localizationEnergyXi ξG

theorem informationalEnergyMassRowLegacy_target (ξG : ℝ) :
    (informationalEnergyMassRowLegacy ξG).target =
      holonomyRowRhs fanoVertex0 * omegaKContinuous ξG xiLockin - localizationEnergyXi ξG := rfl

theorem informationalEnergyMassRowLegacy_target_shift (ξG : ℝ) :
    (informationalEnergyMassRowLegacy ξG).target =
      (omegaKMassRow ξG).target - localizationEnergyXi ξG := by
  simp [informationalEnergyMassRowLegacy_target, omegaKMassRow_target]

/--
**Informational-energy mass row** (default; linear in `c₀`; localization in the target):

`c₀ + localization(ξ_G) = 2π · Ω_k(ξ_G)` — full horizon turn times the curvature fraction.

Implemented as `c₀ = 2π · Ω_k(ξ_G) − localization(ξ_G)` on the EM vertex.
Matches `InformationalEnergyMass.informationalEnergyAtXi` when `m_rest = c₀` (natural units).
-/
noncomputable def informationalEnergyMassRow (ξG : ℝ) : CouplingLinearRow where
  coeff := fun v => if v = fanoVertex0 then 1 else 0
  target :=
    twoPi * omegaKContinuous ξG xiLockin - localizationEnergyXi ξG

theorem informationalEnergyMassRow_target (ξG : ℝ) :
    (informationalEnergyMassRow ξG).target =
      twoPi * omegaKContinuous ξG xiLockin - localizationEnergyXi ξG := rfl

theorem informationalEnergyMassRow_budget (ξG : ℝ) :
    (informationalEnergyMassRow ξG).target + localizationEnergyXi ξG =
      twoPi * omegaKContinuous ξG xiLockin := by
  simp [informationalEnergyMassRow_target]

/-- A numerical scan point, recorded as witness data rather than a Lean proof of
transcendental inequalities. -/
structure XiScanPoint where
  xiG : ℝ
  c0 : ℝ
  residualNorm : ℝ
  omegaK : ℝ
  bracedInvAlpha : ℝ

/-- Brace-only normalization point: `c₀ ≈ 1`, `ξ_G ≈ 3.474`. -/
noncomputable def normalizationXiWitness : XiScanPoint where
  xiG := 3.4743752754774695
  c0 := 1.0000000031817042
  residualNorm := 3.2064366568692075
  omegaK := 0.7168
  bracedInvAlpha := 137.035999177

/-- Structural residual point from the aligned density-holonomy scan. -/
noncomputable def structureXiWitness : XiScanPoint where
  xiG := 4.85
  c0 := 1.2729
  residualNorm := 2.915845
  omegaK := 0.9750
  bracedInvAlpha := 137.035999177

/-- Half-step reference point: the clean midpoint near the normalization root. -/
noncomputable def halfStepXiWitness : XiScanPoint where
  xiG := xiHalfStep
  c0 := 1.0056
  residualNorm := 3.192326
  omegaK := 0.7222
  bracedInvAlpha := 137.035999177

/-- Side-by-side witness for the two objective axes seen in the Python scan. -/
structure TwoObjectiveXiWitness where
  normalizationPoint : XiScanPoint
  structuralPoint : XiScanPoint
  halfStep : XiScanPoint
  lockinXi : ℝ
  lockinOmega : ℝ

noncomputable def twoObjectiveXiWitness : TwoObjectiveXiWitness where
  normalizationPoint := normalizationXiWitness
  structuralPoint := structureXiWitness
  halfStep := halfStepXiWitness
  lockinXi := xiLockin
  lockinOmega := 1

theorem twoObjectiveXiWitness_lockin :
    twoObjectiveXiWitness.lockinOmega = 1 := rfl

theorem twoObjectiveXiWitness_halfStep :
    twoObjectiveXiWitness.halfStep.xiG = xiHalfStep := rfl

/-! ## Overdetermined residual ordering (Python scan witnesses) -/

/-- Structural scan residual is below the half-step normalization pocket. -/
theorem structure_residual_lt_halfStep :
    structureXiWitness.residualNorm < halfStepXiWitness.residualNorm := by
  unfold structureXiWitness halfStepXiWitness xiHalfStep
  norm_num

/-- Structural residual is below the brace-only normalization point. -/
theorem structure_residual_lt_normalization :
    structureXiWitness.residualNorm < normalizationXiWitness.residualNorm := by
  unfold structureXiWitness normalizationXiWitness
  norm_num

/-- Half-step residual is below normalization (normalization is not the structural minimum). -/
theorem halfStep_residual_lt_normalization :
    halfStepXiWitness.residualNorm < normalizationXiWitness.residualNorm := by
  unfold halfStepXiWitness normalizationXiWitness
  norm_num

/-- Brace CODATA pinning is shared across the three recorded scan anchors. -/
theorem scanWitnesses_brace_alpha_agree :
    normalizationXiWitness.bracedInvAlpha = structureXiWitness.bracedInvAlpha ∧
      structureXiWitness.bracedInvAlpha = halfStepXiWitness.bracedInvAlpha := by
  unfold normalizationXiWitness structureXiWitness halfStepXiWitness
  norm_num

/-!
Interpretation of the witness:

* `normalizationXiWitness` keeps the EM normalization natural (`c₀≈1`) and
  places the readout near the half-step `ξ≈3.5`;
* `structureXiWitness` minimizes the overdetermined density-weighted
  line/holonomy residual and moves toward the lock-in point `ξ_lock=5`;
* `omegaKMassRow` is the Lean-side row for testing EM and mass readouts on the
  same `curvatureDensity` / `Ω_k` curve without a second external input;
* `informationalEnergyMassRow` adds the `1/Θ_local(ξ_G)` localization slot to the
  full-turn budget `2π · Ω_k(ξ_G)` (see `InformationalEnergyMass`);
* `informationalEnergyMassRowLegacy` keeps the per-vertex `holonomyRowRhs · Ω_k` form.

**Scale note:** `omegaKContinuous ξ ξLock` is horizon-dependent. The coupling brace uses
`ξ_G ≈ 3.47` and `ξ_lock = 5`, giving `Ω_k ≈ 0.7` there. The axiom limit
`Ω_k^true ≈ 0.0098` and shallow-chart ratios `≈ 0.03` belong to other readouts
(CMB stop, early shells); they are not interchangeable with the brace mass row.
-/

end Physics
end Hqiv

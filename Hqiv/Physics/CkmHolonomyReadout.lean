import Hqiv.Physics.HepDecayReadout
import Hqiv.Physics.FanoHolonomyOverlap
import Hqiv.Physics.FanoMixingMatrix

/-!
# CKM holonomy readout

Full 3×3 CKM matrix from Fano second-order slot squares and holonomy CP orientation.
Magnitudes from the proved ledger in `HepDecayReadout`; phases from `fanoHolonomyCPPhase`.

No PDG comparison numerals in theorem hypotheses.
-/

namespace Hqiv.Physics

open Matrix Complex

/-! ## Magnitude-squared ledger (re-export) -/

/-- CKM |V_ij|² as a 3×3 matrix (rows u,c,t; cols d,s,b). -/
noncomputable def ckmMagnitudeSqMatrix : MixingMagnitudeSq :=
  Matrix.of fun i j =>
    match i, j with
    | ⟨0, _⟩, ⟨0, _⟩ => 1 - ckmSlotUS2 - ckmSlotCB2
    | ⟨0, _⟩, ⟨1, _⟩ => ckmSlotUS2
    | ⟨0, _⟩, ⟨2, _⟩ => ckmSlotCB2
    | ⟨1, _⟩, ⟨0, _⟩ => ckmSlotUS2
    | ⟨1, _⟩, ⟨1, _⟩ => 1 - ckmSlotUS2 - ckmSlotCB2
    | ⟨1, _⟩, ⟨2, _⟩ => ckmSlotCB2
    | ⟨2, _⟩, ⟨0, _⟩ => ckmSlotCB2
    | ⟨2, _⟩, ⟨1, _⟩ => ckmSlotCB2
    | ⟨2, _⟩, ⟨2, _⟩ => 1 - 2 * ckmSlotCB2
    | _, _ => 0

theorem ckmMagnitudeSqMatrix_row_unitary :
    MixingMagnitudeSqIsRowUnitary ckmMagnitudeSqMatrix := by
  intro i
  dsimp [MixingMagnitudeSqIsRowUnitary, mixingRowSumSq]
  fin_cases i
  · rw [Fin.sum_univ_three]
    simp [ckmMagnitudeSqMatrix, ckmSlotUS2, ckmSlotCB2, gamma_eq_2_5] <;> norm_num
  · rw [Fin.sum_univ_three]
    simp [ckmMagnitudeSqMatrix, ckmSlotUS2, ckmSlotCB2, gamma_eq_2_5] <;> norm_num
  · rw [Fin.sum_univ_three]
    simp [ckmMagnitudeSqMatrix, ckmSlotUS2, ckmSlotCB2, gamma_eq_2_5] <;> norm_num

theorem ckmMagnitudeSqMatrix_col_unitary :
    MixingMagnitudeSqIsColUnitary ckmMagnitudeSqMatrix := by
  intro j
  dsimp [MixingMagnitudeSqIsColUnitary, mixingColSumSq]
  fin_cases j
  · rw [Fin.sum_univ_three]
    simp [ckmMagnitudeSqMatrix, ckmSlotUS2, ckmSlotCD2, ckmSlotCB2, gamma_eq_2_5] <;> norm_num
  · rw [Fin.sum_univ_three]
    simp [ckmMagnitudeSqMatrix, ckmSlotUS2, ckmSlotCD2, ckmSlotCB2, gamma_eq_2_5] <;> norm_num
  · rw [Fin.sum_univ_three]
    simp [ckmMagnitudeSqMatrix, ckmSlotUS2, ckmSlotCD2, ckmSlotCB2, gamma_eq_2_5] <;> norm_num

noncomputable def ckmMagnitudeSqUnitary : MixingMagnitudeSqUnitary where
  entries := ckmMagnitudeSqMatrix
  row_unitary := ckmMagnitudeSqMatrix_row_unitary
  col_unitary := ckmMagnitudeSqMatrix_col_unitary

/-! ## Magnitudes and Wolfenstein-style angles -/

noncomputable def ckmMagnitude (i j : Fin 3) : ℝ :=
  mixingMagnitude ckmMagnitudeSqMatrix i j

theorem ckmMagnitude_us_sq : ckmMagnitudeSqMatrix 0 1 = ckmSlotUS2 := rfl

theorem ckmMagnitude_cd_sq : ckmMagnitudeSqMatrix 1 0 = ckmSlotUS2 := rfl

theorem ckmMagnitude_cb_sq : ckmMagnitudeSqMatrix 1 2 = ckmSlotCB2 := rfl

theorem ckmMagnitude_ub_sq : ckmMagnitudeSqMatrix 0 2 = ckmSlotCB2 := rfl

theorem ckmMagnitude_td_sq : ckmMagnitudeSqMatrix 2 0 = ckmSlotCB2 := rfl

/-- CKM CP phase from Fano holonomy orientation (equals `fanoHolonomyCPPhase`). -/
noncomputable def ckmDeltaCP : ℝ := fanoHolonomyCPPhase

theorem ckmDeltaCP_eq_fanoHolonomyCPPhase : ckmDeltaCP = fanoHolonomyCPPhase := rfl

theorem ckmDeltaCP_eq_three_pi_over_thirtytwo :
    ckmDeltaCP = (3 : ℝ) * Real.pi / 32 :=
  fanoHolonomyCPPhase_eq_three_pi_over_thirtytwo

theorem cpOddFanoHolonomySkew_eq_fanoSecondOrderPhaseSkew :
    cpOddFanoHolonomySkew = fanoSecondOrderPhaseSkew := by
  simp [cpOddFanoHolonomySkew, fanoSecondOrderPhaseSkew, ckmSlotUS2, ckmSlotCB2]

/-- Mixing angles from magnitude ledger (first octant). -/
noncomputable def ckmAngle12 : ℝ := mixingAngleFromSinSq (ckmMagnitudeSqMatrix 0 1)

noncomputable def ckmAngle23 : ℝ := mixingAngleFromSinSq (ckmMagnitudeSqMatrix 1 2)

noncomputable def ckmAngle13 : ℝ := mixingAngleFromSinSq (ckmMagnitudeSqMatrix 0 2)

theorem ckmAngle12_sin_sq : Real.sin ckmAngle12 ^ 2 = ckmSlotUS2 := by
  rw [ckmAngle12, ckmMagnitude_us_sq]
  exact mixingAngleFromSinSq_sin_sq ckmSlotUS2 (le_of_lt ckmSlotUS2_pos) (by
    rw [ckmSlotUS2, gamma_eq_2_5]; norm_num)

theorem ckmAngle23_sin_sq : Real.sin ckmAngle23 ^ 2 = ckmSlotCB2 := by
  rw [ckmAngle23, ckmMagnitude_cb_sq]
  exact mixingAngleFromSinSq_sin_sq ckmSlotCB2 (le_of_lt ckmSlotCB2_pos) (by
    rw [ckmSlotCB2, gamma_eq_2_5]; norm_num)

theorem ckmAngle13_sin_sq : Real.sin ckmAngle13 ^ 2 = ckmSlotCB2 := by
  rw [ckmAngle13, ckmMagnitude_ub_sq]
  exact mixingAngleFromSinSq_sin_sq ckmSlotCB2 (le_of_lt ckmSlotCB2_pos) (by
    rw [ckmSlotCB2, gamma_eq_2_5]; norm_num)

/-! ## Full unitary matrix and invariants -/

noncomputable def ckmUnitaryReal : Matrix (Fin 3) (Fin 3) ℝ :=
  mixingParameterizationReal ckmAngle12 ckmAngle23 ckmAngle13

noncomputable def ckmUnitary : MixingMatrix3 :=
  mixingApplyCPPhase (mixingRealToComplex ckmUnitaryReal) ckmDeltaCP

noncomputable def ckmJarlskog : ℝ := cpOddFanoHolonomySkew

theorem ckmJarlskog_eq_cp_odd_skew : ckmJarlskog = cpOddFanoHolonomySkew := rfl

theorem ckmJarlskog_pos : 0 < ckmJarlskog := cpOddFanoHolonomySkew_pos

/-- Standard PDG Jarlskog parameterization at lock-in CKM angles. -/
noncomputable def ckmJarlskogFromAngles : ℝ :=
  jarlskogFromAngles ckmAngle12 ckmAngle23 ckmAngle13 ckmDeltaCP

noncomputable def ckmJarlskogSinEnvelope : ℝ :=
  Real.sqrt ckmSlotUS2 * Real.sqrt ckmSlotCB2 * Real.sqrt ckmSlotCB2

noncomputable def ckmJarlskogCosineEnvelope : ℝ :=
  Real.cos ckmAngle12 * Real.cos ckmAngle23 * Real.cos ckmAngle13

theorem ckmJarlskogFromAngles_eq_sin_delta_sin_cos_envelope :
    ckmJarlskogFromAngles =
      Real.sin ckmDeltaCP * ckmJarlskogSinEnvelope * ckmJarlskogCosineEnvelope := by
  unfold ckmJarlskogFromAngles ckmJarlskogSinEnvelope ckmJarlskogCosineEnvelope
  rw [jarlskogFromAngles_eq_sin_delta_slot_factor_cos
    ckmAngle12 ckmAngle23 ckmAngle13 ckmDeltaCP
    ckmSlotUS2 ckmSlotCB2 ckmSlotCB2
    ckmAngle12_sin_sq ckmAngle23_sin_sq ckmAngle13_sin_sq
    (by rw [ckmAngle12, ckmMagnitude_us_sq])
    (by rw [ckmAngle23, ckmMagnitude_cb_sq])
    (by rw [ckmAngle13, ckmMagnitude_ub_sq])
    (le_of_lt ckmSlotUS2_pos) (le_of_lt ckmSlotCB2_pos) (le_of_lt ckmSlotCB2_pos)
    (by rw [ckmSlotUS2, gamma_eq_2_5]; norm_num)
    (by rw [ckmSlotCB2, gamma_eq_2_5]; norm_num)
    (by rw [ckmSlotCB2, gamma_eq_2_5]; norm_num)]
  ring

theorem ckmJarlskogFromAngles_pos : 0 < ckmJarlskogFromAngles := by
  rw [ckmJarlskogFromAngles_eq_sin_delta_sin_cos_envelope]
  have hsin : 0 < Real.sin ckmDeltaCP := by
    rw [ckmDeltaCP_eq_three_pi_over_thirtytwo]
    exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have hsinEnv : 0 < ckmJarlskogSinEnvelope := by
    unfold ckmJarlskogSinEnvelope
    apply mul_pos
    · exact mul_pos (Real.sqrt_pos.mpr ckmSlotUS2_pos) (Real.sqrt_pos.mpr ckmSlotCB2_pos)
    · exact Real.sqrt_pos.mpr ckmSlotCB2_pos
  have hcosSlot {slot : ℝ} (hpos : 0 < slot) (hlt : slot < 1) :
      0 < Real.cos (Real.arcsin (Real.sqrt slot)) := by
    have hll : (-1 : ℝ) ≤ Real.sqrt slot := by linarith [Real.sqrt_nonneg slot]
    have hsqrt_le : Real.sqrt slot ≤ 1 := by
      nlinarith [Real.sq_sqrt (le_of_lt hpos), sq_nonneg (Real.sqrt slot), le_of_lt hlt]
    have heq : Real.cos (Real.arcsin (Real.sqrt slot)) = Real.sqrt (1 - slot) := by
      rw [Real.cos_arcsin, Real.sq_sqrt (le_of_lt hpos)]
    rw [heq, Real.sqrt_pos]
    exact sub_pos.mpr hlt
  have hcosEnv : 0 < ckmJarlskogCosineEnvelope := by
    unfold ckmJarlskogCosineEnvelope ckmAngle12 ckmAngle23 ckmAngle13 mixingAngleFromSinSq
    rw [ckmMagnitude_us_sq, ckmMagnitude_cb_sq, ckmMagnitude_ub_sq]
    have hcos12 := hcosSlot ckmSlotUS2_pos (by rw [ckmSlotUS2, gamma_eq_2_5]; norm_num)
    have hcos23 := hcosSlot ckmSlotCB2_pos (by rw [ckmSlotCB2, gamma_eq_2_5]; norm_num)
    have hcos13 := hcosSlot ckmSlotCB2_pos (by rw [ckmSlotCB2, gamma_eq_2_5]; norm_num)
    exact mul_pos (mul_pos hcos12 hcos23) hcos13
  exact mul_pos (mul_pos hsin hsinEnv) hcosEnv

/-- Ledger holonomy skew is the CP-odd rung combination; parameterization J carries sin/cos envelopes. -/
theorem ckmJarlskog_eq_holonomy_skew : ckmJarlskog = cpOddFanoHolonomySkew := rfl

/-- Ratio of PDG-parameterization Jarlskog to ledger holonomy skew (sin/cos envelope correction). -/
noncomputable def ckmJarlskogParameterizationCorrection : ℝ :=
  ckmJarlskogFromAngles / ckmJarlskog

theorem ckmJarlskogParameterizationCorrection_eq :
    ckmJarlskogParameterizationCorrection =
      ckmJarlskogFromAngles / cpOddFanoHolonomySkew := by
  simp [ckmJarlskogParameterizationCorrection, ckmJarlskog_eq_cp_odd_skew]

theorem ckmJarlskogParameterizationCorrection_pos :
    0 < ckmJarlskogParameterizationCorrection := by
  rw [ckmJarlskogParameterizationCorrection_eq]
  exact div_pos ckmJarlskogFromAngles_pos cpOddFanoHolonomySkew_pos

/-! ## Unitarity triangle angles -/

noncomputable def ckmUnitarityTriangleBeta : ℝ :=
  unitarityTriangleBeta ckmJarlskog (ckmMagnitude 2 0) (ckmMagnitude 2 2)

noncomputable def ckmUnitarityTriangleGamma : ℝ :=
  unitarityTriangleGamma (ckmMagnitude 0 2) (ckmMagnitude 1 2)

noncomputable def ckmUnitarityTriangleAlpha : ℝ :=
  unitarityTriangleAlpha ckmUnitarityTriangleBeta ckmUnitarityTriangleGamma

structure CkmHolonomyReadout where
  magnitudeSq : MixingMagnitudeSq
  unitary : MixingMatrix3
  theta12 : ℝ
  theta23 : ℝ
  theta13 : ℝ
  deltaCP : ℝ
  jarlskog : ℝ
  alpha : ℝ
  beta : ℝ
  gamma : ℝ

noncomputable def assembleCkmHolonomyReadout : CkmHolonomyReadout where
  magnitudeSq := ckmMagnitudeSqMatrix
  unitary := ckmUnitary
  theta12 := ckmAngle12
  theta23 := ckmAngle23
  theta13 := ckmAngle13
  deltaCP := ckmDeltaCP
  jarlskog := ckmJarlskog
  alpha := ckmUnitarityTriangleAlpha
  beta := ckmUnitarityTriangleBeta
  gamma := ckmUnitarityTriangleGamma

theorem assembleCkmHolonomyReadout_deltaCP :
    assembleCkmHolonomyReadout.deltaCP = (3 : ℝ) * Real.pi / 32 :=
  ckmDeltaCP_eq_three_pi_over_thirtytwo

theorem assembleCkmHolonomyReadout_jarlskog_pos :
    0 < assembleCkmHolonomyReadout.jarlskog :=
  ckmJarlskog_pos

end Hqiv.Physics

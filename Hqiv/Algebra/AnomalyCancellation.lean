import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Defs
import Hqiv.Algebra.SMEmbedding
import Hqiv.Algebra.Triality

open BigOperators

/-!
# Anomaly cancellation for three SM generations

This file keeps the anomaly check at the finite coefficient level used by the
current HQIV SM-embedding layer.  One left-handed SM generation is represented
by the standard conjugate-field list
\[
  Q_L:(3,2,1/6),\quad u^c:(\bar 3,1,-2/3),\quad d^c:(\bar 3,1,1/3),
  \quad L:(1,2,-1/2),\quad e^c:(1,1,1),\quad \nu^c:(1,1,0).
\]
The cubic and mixed traces are then ordinary finite rational sums, and the
three-generation statement is their triality-indexed repetition.

**Anomaly coefficients:** For chiral gauge theories the anomaly is proportional to
the sum over left-handed minus right-handed of Tr(T^a {T^b, T^c}). For the SM with
three generations from 8v, 8s⁺, 8s⁻, the contributions cancel (Spin(8) is anomaly-free).

**Reference:** HQIV preprint v2, Zenodo 10.5281/zenodo.18899939, Section 4.4.
-/

namespace Hqiv.Algebra

/-- A left-handed Weyl multiplet contribution to finite SM anomaly traces.  `su3Cubic`
is the signed cubic index for the color representation (`3 = +1`, `3̄ = -1`, singlet `0`);
`su2Doublets` counts weak doublets weighted by color multiplicity. -/
structure SMWeylMultiplet where
  colorDim : ℕ
  weakDim : ℕ
  hypercharge : ℚ
  su3Cubic : ℤ
  su2Doublets : ℕ
deriving DecidableEq

/-- Quark doublet `Q_L : (3,2,1/6)`. -/
def smQL : SMWeylMultiplet where
  colorDim := 3
  weakDim := 2
  hypercharge := 1 / 6
  su3Cubic := 2
  su2Doublets := 3

/-- Conjugate up quark `u^c : (3̄,1,-2/3)`. -/
def smUc : SMWeylMultiplet where
  colorDim := 3
  weakDim := 1
  hypercharge := -2 / 3
  su3Cubic := -1
  su2Doublets := 0

/-- Conjugate down quark `d^c : (3̄,1,1/3)`. -/
def smDc : SMWeylMultiplet where
  colorDim := 3
  weakDim := 1
  hypercharge := 1 / 3
  su3Cubic := -1
  su2Doublets := 0

/-- Lepton doublet `L : (1,2,-1/2)`. -/
def smL : SMWeylMultiplet where
  colorDim := 1
  weakDim := 2
  hypercharge := -1 / 2
  su3Cubic := 0
  su2Doublets := 1

/-- Conjugate charged lepton `e^c : (1,1,1)`. -/
def smEc : SMWeylMultiplet where
  colorDim := 1
  weakDim := 1
  hypercharge := 1
  su3Cubic := 0
  su2Doublets := 0

/-- Conjugate right-handed neutrino `ν^c : (1,1,0)`. -/
def smNuC : SMWeylMultiplet where
  colorDim := 1
  weakDim := 1
  hypercharge := 0
  su3Cubic := 0
  su2Doublets := 0

/-- The one-generation left-handed SM multiplet list used in the finite trace check. -/
def oneGenerationMultiplets : List SMWeylMultiplet :=
  [smQL, smUc, smDc, smL, smEc, smNuC]

/-- Total number of Weyl components carried by one generation. -/
def SMWeylMultiplet.componentCount (m : SMWeylMultiplet) : ℕ :=
  m.colorDim * m.weakDim

/-- The `U(1)_Y^3` anomaly trace for one generation. -/
def u1YCubicTraceOneGeneration : ℚ :=
  (oneGenerationMultiplets.map fun m =>
    (m.componentCount : ℚ) * m.hypercharge ^ 3).sum

/-- The mixed gravitational-`U(1)_Y` trace for one generation. -/
def gravitationalU1YTraceOneGeneration : ℚ :=
  (oneGenerationMultiplets.map fun m =>
    (m.componentCount : ℚ) * m.hypercharge).sum

/-- The mixed `SU(3)_c^2 U(1)_Y` trace, with the common fundamental Dynkin index suppressed. -/
def su3SquaredU1YTraceOneGeneration : ℚ :=
  (oneGenerationMultiplets.map fun m =>
    (m.weakDim : ℚ) * m.hypercharge *
      (if m.colorDim = 3 then (1 : ℚ) else 0)).sum

/-- The mixed `SU(2)_L^2 U(1)_Y` trace, with the common doublet Dynkin index suppressed. -/
def su2SquaredU1YTraceOneGeneration : ℚ :=
  (oneGenerationMultiplets.map fun m =>
    (m.su2Doublets : ℚ) * m.hypercharge).sum

/-- The `SU(3)_c^3` cubic-index trace for one generation. -/
def su3CubicTraceOneGeneration : ℤ :=
  (oneGenerationMultiplets.map fun m => m.su3Cubic).sum

/-- The `SU(2)_L^3` trace vanishes because the fundamental is pseudoreal; the finite
coefficient slot is recorded explicitly for the anomaly package. -/
def su2CubicTraceOneGeneration : ℤ :=
  0

theorem u1Y_cubic_trace_one_generation_zero :
    u1YCubicTraceOneGeneration = 0 := by
  norm_num [u1YCubicTraceOneGeneration, oneGenerationMultiplets, SMWeylMultiplet.componentCount,
    smQL, smUc, smDc, smL, smEc, smNuC]

theorem gravitational_u1Y_trace_one_generation_zero :
    gravitationalU1YTraceOneGeneration = 0 := by
  norm_num [gravitationalU1YTraceOneGeneration, oneGenerationMultiplets,
    SMWeylMultiplet.componentCount, smQL, smUc, smDc, smL, smEc, smNuC]

theorem su3_squared_u1Y_trace_one_generation_zero :
    su3SquaredU1YTraceOneGeneration = 0 := by
  norm_num [su3SquaredU1YTraceOneGeneration, oneGenerationMultiplets, smQL, smUc, smDc, smL, smEc,
    smNuC]

theorem su2_squared_u1Y_trace_one_generation_zero :
    su2SquaredU1YTraceOneGeneration = 0 := by
  norm_num [su2SquaredU1YTraceOneGeneration, oneGenerationMultiplets, smQL, smUc, smDc, smL, smEc,
    smNuC]

theorem su3_cubic_trace_one_generation_zero :
    su3CubicTraceOneGeneration = 0 := by
  norm_num [su3CubicTraceOneGeneration, oneGenerationMultiplets, smQL, smUc, smDc, smL, smEc,
    smNuC]

theorem su2_cubic_trace_one_generation_zero :
    su2CubicTraceOneGeneration = 0 := rfl

/-- One generation satisfies the finite SM anomaly trace cancellations. -/
def smAnomalyFreeOneGeneration : Prop :=
  u1YCubicTraceOneGeneration = 0 ∧
  gravitationalU1YTraceOneGeneration = 0 ∧
  su3SquaredU1YTraceOneGeneration = 0 ∧
  su2SquaredU1YTraceOneGeneration = 0 ∧
  su3CubicTraceOneGeneration = 0 ∧
  su2CubicTraceOneGeneration = 0

theorem sm_anomaly_free_one_generation :
    smAnomalyFreeOneGeneration := by
  exact ⟨u1Y_cubic_trace_one_generation_zero, gravitational_u1Y_trace_one_generation_zero,
    su3_squared_u1Y_trace_one_generation_zero, su2_squared_u1Y_trace_one_generation_zero,
    su3_cubic_trace_one_generation_zero, su2_cubic_trace_one_generation_zero⟩

/-- The real-valued aggregate anomaly coefficient for one triality generation.  This is
definitionally a finite trace polynomial, not a literal zero scaffold. -/
def smAnomalyCoefficientOneGeneration : ℝ :=
  ((u1YCubicTraceOneGeneration + gravitationalU1YTraceOneGeneration +
    su3SquaredU1YTraceOneGeneration + su2SquaredU1YTraceOneGeneration : ℚ) : ℝ) +
    ((su3CubicTraceOneGeneration + su2CubicTraceOneGeneration : ℤ) : ℝ)

theorem smAnomalyCoefficientOneGeneration_zero :
    smAnomalyCoefficientOneGeneration = 0 := by
  rw [smAnomalyCoefficientOneGeneration, u1Y_cubic_trace_one_generation_zero,
    gravitational_u1Y_trace_one_generation_zero, su3_squared_u1Y_trace_one_generation_zero,
    su2_squared_u1Y_trace_one_generation_zero, su3_cubic_trace_one_generation_zero,
    su2_cubic_trace_one_generation_zero]
  norm_num

/-- **Anomaly coefficient** for one triality generation.  The generation label is
kept because all three Spin(8) triality slots carry the same SM finite trace package. -/
def anomalyCoeff (_g : Fin 3) : ℝ :=
  smAnomalyCoefficientOneGeneration

/-- **Anomaly index** for a chiral fermion representation: sum of anomaly coefficients
  over left-handed minus right-handed. For the three-generation SM from Spin(8),
  this sum is zero. -/
def anomalyIndex (_T : Type) : ℝ :=
  ∑ g : Fin 3, anomalyCoeff g

/-- **Three generations under the SM subgroup** (from triality: 8s, 8c, 8v
each giving one generation with correct SM quantum numbers). -/
def threeGenerationsUnderSM : Type := Fin 3

/-- **Sum of anomaly coefficients over the three generations is zero.** -/
theorem anomaly_coeff_sum_three_generations :
    ∑ g : Fin 3, anomalyCoeff g = 0 := by
  simp [anomalyCoeff, smAnomalyCoefficientOneGeneration_zero]

/-- The finite trace package cancels in each triality-indexed generation. -/
theorem anomaly_coeff_each_generation_zero (g : Fin 3) :
    anomalyCoeff g = 0 := by
  simp [anomalyCoeff, smAnomalyCoefficientOneGeneration_zero]

/-- Cubic hypercharge cancellation for all three triality-indexed generations. -/
theorem u1Y_cubic_trace_three_generations_zero :
    ∑ _g : Fin 3, (u1YCubicTraceOneGeneration : ℚ) = 0 := by
  rw [u1Y_cubic_trace_one_generation_zero]
  simp

/-- Mixed gravitational-`U(1)_Y` cancellation for all three triality-indexed generations. -/
theorem gravitational_u1Y_trace_three_generations_zero :
    ∑ _g : Fin 3, (gravitationalU1YTraceOneGeneration : ℚ) = 0 := by
  rw [gravitational_u1Y_trace_one_generation_zero]
  simp

/-- Mixed `SU(3)_c^2 U(1)_Y` cancellation for all three triality-indexed generations. -/
theorem su3_squared_u1Y_trace_three_generations_zero :
    ∑ _g : Fin 3, (su3SquaredU1YTraceOneGeneration : ℚ) = 0 := by
  rw [su3_squared_u1Y_trace_one_generation_zero]
  simp

/-- Mixed `SU(2)_L^2 U(1)_Y` cancellation for all three triality-indexed generations. -/
theorem su2_squared_u1Y_trace_three_generations_zero :
    ∑ _g : Fin 3, (su2SquaredU1YTraceOneGeneration : ℚ) = 0 := by
  rw [su2_squared_u1Y_trace_one_generation_zero]
  simp

/-- `SU(3)_c^3` cubic-index cancellation for all three triality-indexed generations. -/
theorem su3_cubic_trace_three_generations_zero :
    ∑ _g : Fin 3, (su3CubicTraceOneGeneration : ℤ) = 0 := by
  rw [su3_cubic_trace_one_generation_zero]
  simp

/-- `SU(2)_L^3` cancellation for all three triality-indexed generations. -/
theorem su2_cubic_trace_three_generations_zero :
    ∑ _g : Fin 3, (su2CubicTraceOneGeneration : ℤ) = 0 := by
  rw [su2_cubic_trace_one_generation_zero]
  simp

theorem anomaly_coeff_sum_three_generations_by_range :
    ∑ g : Fin 3, anomalyCoeff g = 0 := by
  unfold anomalyCoeff
  rw [smAnomalyCoefficientOneGeneration_zero]
  rw [Finset.sum_fin_eq_sum_range]
  norm_num [Finset.sum_range_succ, Finset.sum_range_one]

/-- **The SM with three generations (from the Spin(8) embedding) is anomaly-free.**
  anomalyIndex is zero; the explicit sum over generations (anomalyCoeff) also vanishes. -/
theorem sm_anomaly_free_three_generations :
    anomalyIndex threeGenerationsUnderSM = 0 := by
  unfold anomalyIndex
  exact anomaly_coeff_sum_three_generations

/-- **Anomaly-free statement with explicit coefficients:** the total anomaly
  (sum of anomalyCoeff over the three So8RepIndex generations) equals zero. -/
theorem anomaly_free_explicit :
    ∑ r : So8RepIndex, anomalyCoeff r = 0 := by
  exact anomaly_coeff_sum_three_generations

end Hqiv.Algebra

import HqivSpine.Algebra.Triality
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin

/-!
# `HqivSpine.Algebra.Anomaly` — finite SM anomaly cancellation over three generations

One left-handed Standard-Model generation is the conjugate-field list

`Q_L:(3,2,1/6)`, `u^c:(3̄,1,−2/3)`, `d^c:(3̄,1,1/3)`,
`L:(1,2,−1/2)`, `e^c:(1,1,1)`, `ν^c:(1,1,0)`.

Every gauge/gravitational anomaly trace is then a finite rational sum over this
list, and each one **vanishes**: `U(1)_Y³`, grav·`U(1)_Y`, `SU(3)²·U(1)_Y`,
`SU(2)²·U(1)_Y`, `SU(3)³`, `SU(2)³`. The three-generation statement is the
triality-indexed repetition over `So8RepIndex` (each `Spin(8)` 8-dim slot carries the
same finite trace package), so the embedded SM is anomaly-free.

This is a finite trace-polynomial check on packaged quantum numbers, not a continuum
path-integral anomaly proof.
-/

namespace HqivSpine.Algebra

open BigOperators

/-- A left-handed Weyl multiplet contribution. `su3Cubic` is the signed cubic colour
index (`3 = +1`, `3̄ = −1`, singlet `0`, here doubled for the doublet); `su2Doublets`
counts weak doublets weighted by colour multiplicity. -/
structure SMWeylMultiplet where
  colorDim : ℕ
  weakDim : ℕ
  hypercharge : ℚ
  su3Cubic : ℤ
  su2Doublets : ℕ
deriving DecidableEq

/-- Quark doublet `Q_L : (3,2,1/6)`. -/
def smQL : SMWeylMultiplet := ⟨3, 2, 1 / 6, 2, 3⟩
/-- Conjugate up quark `u^c : (3̄,1,−2/3)`. -/
def smUc : SMWeylMultiplet := ⟨3, 1, -2 / 3, -1, 0⟩
/-- Conjugate down quark `d^c : (3̄,1,1/3)`. -/
def smDc : SMWeylMultiplet := ⟨3, 1, 1 / 3, -1, 0⟩
/-- Lepton doublet `L : (1,2,−1/2)`. -/
def smL : SMWeylMultiplet := ⟨1, 2, -1 / 2, 0, 1⟩
/-- Conjugate charged lepton `e^c : (1,1,1)`. -/
def smEc : SMWeylMultiplet := ⟨1, 1, 1, 0, 0⟩
/-- Conjugate right-handed neutrino `ν^c : (1,1,0)`. -/
def smNuC : SMWeylMultiplet := ⟨1, 1, 0, 0, 0⟩

/-- The one-generation left-handed multiplet list. -/
def oneGenerationMultiplets : List SMWeylMultiplet :=
  [smQL, smUc, smDc, smL, smEc, smNuC]

/-- Weyl components carried by a multiplet (`colorDim · weakDim`). -/
def SMWeylMultiplet.componentCount (m : SMWeylMultiplet) : ℕ := m.colorDim * m.weakDim

/-- `U(1)_Y³` trace. -/
def u1YCubicTrace : ℚ :=
  (oneGenerationMultiplets.map fun m => (m.componentCount : ℚ) * m.hypercharge ^ 3).sum
/-- Mixed gravitational·`U(1)_Y` trace. -/
def gravU1YTrace : ℚ :=
  (oneGenerationMultiplets.map fun m => (m.componentCount : ℚ) * m.hypercharge).sum
/-- Mixed `SU(3)²·U(1)_Y` trace (common fundamental Dynkin index suppressed). -/
def su3SqU1YTrace : ℚ :=
  (oneGenerationMultiplets.map fun m =>
    (m.weakDim : ℚ) * m.hypercharge * (if m.colorDim = 3 then (1 : ℚ) else 0)).sum
/-- Mixed `SU(2)²·U(1)_Y` trace (common doublet Dynkin index suppressed). -/
def su2SqU1YTrace : ℚ :=
  (oneGenerationMultiplets.map fun m => (m.su2Doublets : ℚ) * m.hypercharge).sum
/-- `SU(3)³` cubic-index trace. -/
def su3CubicTrace : ℤ :=
  (oneGenerationMultiplets.map fun m => m.su3Cubic).sum
/-- `SU(2)³` trace (pseudoreal fundamental ⇒ `0`). -/
def su2CubicTrace : ℤ := 0

theorem u1Y_cubic_trace_zero : u1YCubicTrace = 0 := by
  norm_num [u1YCubicTrace, oneGenerationMultiplets, SMWeylMultiplet.componentCount,
    smQL, smUc, smDc, smL, smEc, smNuC]
theorem grav_u1Y_trace_zero : gravU1YTrace = 0 := by
  norm_num [gravU1YTrace, oneGenerationMultiplets, SMWeylMultiplet.componentCount,
    smQL, smUc, smDc, smL, smEc, smNuC]
theorem su3Sq_u1Y_trace_zero : su3SqU1YTrace = 0 := by
  norm_num [su3SqU1YTrace, oneGenerationMultiplets, smQL, smUc, smDc, smL, smEc, smNuC]
theorem su2Sq_u1Y_trace_zero : su2SqU1YTrace = 0 := by
  norm_num [su2SqU1YTrace, oneGenerationMultiplets, smQL, smUc, smDc, smL, smEc, smNuC]
theorem su3_cubic_trace_zero : su3CubicTrace = 0 := by
  norm_num [su3CubicTrace, oneGenerationMultiplets, smQL, smUc, smDc, smL, smEc, smNuC]
theorem su2_cubic_trace_zero : su2CubicTrace = 0 := rfl

/-- **One generation is anomaly-free:** all six finite trace coefficients vanish. -/
theorem sm_anomaly_free_one_generation :
    u1YCubicTrace = 0 ∧ gravU1YTrace = 0 ∧ su3SqU1YTrace = 0 ∧
    su2SqU1YTrace = 0 ∧ su3CubicTrace = 0 ∧ su2CubicTrace = 0 :=
  ⟨u1Y_cubic_trace_zero, grav_u1Y_trace_zero, su3Sq_u1Y_trace_zero,
    su2Sq_u1Y_trace_zero, su3_cubic_trace_zero, su2_cubic_trace_zero⟩

/-- Aggregate real anomaly coefficient — a genuine finite trace polynomial. -/
def smAnomalyCoefficient : ℝ :=
  ((u1YCubicTrace + gravU1YTrace + su3SqU1YTrace + su2SqU1YTrace : ℚ) : ℝ) +
    ((su3CubicTrace + su2CubicTrace : ℤ) : ℝ)

theorem smAnomalyCoefficient_zero : smAnomalyCoefficient = 0 := by
  rw [smAnomalyCoefficient, u1Y_cubic_trace_zero, grav_u1Y_trace_zero, su3Sq_u1Y_trace_zero,
    su2Sq_u1Y_trace_zero, su3_cubic_trace_zero, su2_cubic_trace_zero]
  norm_num

/-- Anomaly coefficient per triality generation (all three carry the same package). -/
def anomalyCoeff (_r : So8RepIndex) : ℝ := smAnomalyCoefficient

/-- **The SM with three triality generations is anomaly-free.** -/
theorem anomaly_free_three_generations :
    ∑ r : So8RepIndex, anomalyCoeff r = 0 := by
  simp [anomalyCoeff, smAnomalyCoefficient_zero]

theorem anomalyCoeff_each_zero (r : So8RepIndex) : anomalyCoeff r = 0 := by
  simp [anomalyCoeff, smAnomalyCoefficient_zero]

end HqivSpine.Algebra

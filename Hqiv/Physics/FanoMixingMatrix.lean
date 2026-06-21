import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Hqiv.Physics.FanoHolonomyOverlap

/-!
# Finite 3×3 mixing matrix infrastructure

Generic records and lemmas for unitary mixing matrices on `Fin 3`,
including magnitude-squared ledgers, Jarlskog invariant, and unitarity-triangle angles.

Shared by CKM and PMNS holonomy readouts.
-/

namespace Hqiv.Physics

open Matrix Complex

/-- Squared-magnitude ledger for a 3×3 mixing matrix. -/
abbrev MixingMagnitudeSq := Matrix (Fin 3) (Fin 3) ℝ

/-- Full complex mixing matrix. -/
abbrev MixingMatrix3 := Matrix (Fin 3) (Fin 3) ℂ

/-- Row sum of squared magnitudes. -/
noncomputable def mixingRowSumSq (Vsq : MixingMagnitudeSq) (i : Fin 3) : ℝ :=
  ∑ j : Fin 3, Vsq i j

/-- Column sum of squared magnitudes. -/
noncomputable def mixingColSumSq (Vsq : MixingMagnitudeSq) (j : Fin 3) : ℝ :=
  ∑ i : Fin 3, Vsq i j

def MixingMagnitudeSqIsRowUnitary (Vsq : MixingMagnitudeSq) : Prop :=
  ∀ i : Fin 3, mixingRowSumSq Vsq i = 1

def MixingMagnitudeSqIsColUnitary (Vsq : MixingMagnitudeSq) : Prop :=
  ∀ j : Fin 3, mixingColSumSq Vsq j = 1

structure MixingMagnitudeSqUnitary where
  entries : MixingMagnitudeSq
  row_unitary : MixingMagnitudeSqIsRowUnitary entries
  col_unitary : MixingMagnitudeSqIsColUnitary entries

/-- Magnitude (real, nonnegative) from squared ledger entry. -/
noncomputable def mixingMagnitude (Vsq : MixingMagnitudeSq) (i j : Fin 3) : ℝ :=
  Real.sqrt (Vsq i j)

theorem mixingMagnitude_nonneg (Vsq : MixingMagnitudeSq) (i j : Fin 3) :
    0 ≤ mixingMagnitude Vsq i j := Real.sqrt_nonneg _

theorem mixingMagnitude_sq (Vsq : MixingMagnitudeSq) (i j : Fin 3) (h : 0 ≤ Vsq i j) :
    mixingMagnitude Vsq i j ^ 2 = Vsq i j := Real.sq_sqrt h

/-- Standard PDG rotation in the (i,j) plane embedded in 3×3 real space. -/
noncomputable def mixingRotation (i j k : Fin 3) (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun r c =>
    if r = i ∧ c = i then Real.cos θ
    else if r = i ∧ c = j then Real.sin θ
    else if r = j ∧ c = i then -Real.sin θ
    else if r = j ∧ c = j then Real.cos θ
    else if r = k ∧ c = k then 1
    else 0

/-- PMNS/CKM-style parameterization: R₂₃ R₁₃ R₁₂ on `Fin 3`. -/
noncomputable def mixingParameterizationReal (θ12 θ23 θ13 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  mixingRotation 1 2 0 θ23 * mixingRotation 0 2 1 θ13 * mixingRotation 0 1 2 θ12

/-- Embed real orthogonal matrix into `ℂ`. -/
noncomputable def mixingRealToComplex (U : Matrix (Fin 3) (Fin 3) ℝ) : MixingMatrix3 :=
  U.map (fun x => (x : ℂ))

/-- CP phase: multiply row 1 (index 1) by exp(−i δ). -/
noncomputable def mixingApplyCPPhase (U : MixingMatrix3) (δ : ℝ) : MixingMatrix3 :=
  Matrix.of fun i j =>
    if i = (1 : Fin 3) then U i j * Complex.exp (-Complex.I * δ)
    else U i j

/--
Jarlskog invariant `J = Im(V_us V_cb V*_ub V*_cs)` in the PDG index convention
(u,d,s,c,b,t) mapped to Fin 3 rows/columns.
For a real orthogonal matrix J = 0; with CP phase δ on row 1, J = sin δ × product of sines.
We use the closed form for the standard parameterization.
-/
noncomputable def jarlskogFromAngles (θ12 θ23 θ13 δ : ℝ) : ℝ :=
  Real.sin θ12 * Real.sin θ23 * Real.sin θ13 * Real.sin δ *
    Real.cos θ12 * Real.cos θ23 * Real.cos θ13

theorem jarlskogFromAngles_eq_neg_self (θ12 θ23 θ13 δ : ℝ) :
    jarlskogFromAngles θ12 θ23 θ13 (-δ) = -jarlskogFromAngles θ12 θ23 θ13 δ := by
  unfold jarlskogFromAngles
  rw [Real.sin_neg]
  ring

/-- Unitarity-triangle angle α (standard PDG: arg(−V_td V*_tb V*_ts V_sl)). -/
noncomputable def unitarityTriangleAlpha (β γ : ℝ) : ℝ := Real.pi - β - γ

/-- Unitarity-triangle angle β from Jarlskog and magnitudes (schematic slot). -/
noncomputable def unitarityTriangleBeta (J Vtd Vtb : ℝ) : ℝ :=
  Real.arcsin (J / (2 * Vtd * Vtb))

/-- Unitarity-triangle angle γ from magnitudes (schematic slot). -/
noncomputable def unitarityTriangleGamma (Vub Vcb : ℝ) : ℝ :=
  Real.arcsin (Vub / (Vcb * Real.sqrt 2))

structure MixingMatrixReadout where
  magnitudeSq : MixingMagnitudeSq
  unitary : MixingMatrix3
  theta12 : ℝ
  theta23 : ℝ
  theta13 : ℝ
  deltaCP : ℝ
  jarlskog : ℝ

/-- Build mixing angles from sin² values (first octant). -/
noncomputable def mixingAngleFromSinSq (sinSq : ℝ) : ℝ :=
  Real.arcsin (Real.sqrt sinSq)

theorem mixingAngleFromSinSq_sin_sq (sinSq : ℝ) (h : 0 ≤ sinSq) (h1 : sinSq ≤ 1) :
    Real.sin (mixingAngleFromSinSq sinSq) ^ 2 = sinSq := by
  unfold mixingAngleFromSinSq
  have hs : 0 ≤ Real.sqrt sinSq := Real.sqrt_nonneg sinSq
  have hle : Real.sqrt sinSq ≤ 1 := by
    nlinarith [Real.sq_sqrt h, sq_nonneg (Real.sqrt sinSq)]
  rw [Real.sin_arcsin (by linarith [hs]) hle, Real.sq_sqrt h]

theorem mixingAngleFromSinSq_sin (sinSq : ℝ) (h : 0 ≤ sinSq) (h1 : sinSq ≤ 1) :
    Real.sin (mixingAngleFromSinSq sinSq) = Real.sqrt sinSq := by
  unfold mixingAngleFromSinSq
  have hs : 0 ≤ Real.sqrt sinSq := Real.sqrt_nonneg sinSq
  have hlower : (-1 : ℝ) ≤ Real.sqrt sinSq := by linarith
  have hle : Real.sqrt sinSq ≤ 1 := by
    nlinarith [Real.sq_sqrt h, sq_nonneg (Real.sqrt sinSq)]
  exact Real.sin_arcsin hlower hle

/--
Jarlskog parameterization factorization when `sin²θ₁₂`, `sin²θ₂₃`, `sin²θ₁₃` are fixed
ledger slots (first-octant angles from `mixingAngleFromSinSq`).
-/
theorem jarlskogFromAngles_eq_sin_delta_slot_factor_cos
    (θ12 θ23 θ13 δ sinSq12 sinSq23 sinSq13 : ℝ)
    (h12 : Real.sin θ12 ^ 2 = sinSq12) (h23 : Real.sin θ23 ^ 2 = sinSq23)
    (h13 : Real.sin θ13 ^ 2 = sinSq13)
    (h12' : θ12 = mixingAngleFromSinSq sinSq12)
    (h23' : θ23 = mixingAngleFromSinSq sinSq23)
    (h13' : θ13 = mixingAngleFromSinSq sinSq13)
    (hs12 : 0 ≤ sinSq12) (hs23 : 0 ≤ sinSq23) (hs13 : 0 ≤ sinSq13)
    (h1_12 : sinSq12 ≤ 1) (h1_23 : sinSq23 ≤ 1) (h1_13 : sinSq13 ≤ 1) :
    jarlskogFromAngles θ12 θ23 θ13 δ =
      Real.sin δ * Real.sqrt sinSq12 * Real.sqrt sinSq23 * Real.sqrt sinSq13 *
      Real.cos θ12 * Real.cos θ23 * Real.cos θ13 := by
  unfold jarlskogFromAngles
  rw [h12', h23', h13']
  rw [mixingAngleFromSinSq_sin sinSq12 hs12 h1_12,
    mixingAngleFromSinSq_sin sinSq23 hs23 h1_23,
    mixingAngleFromSinSq_sin sinSq13 hs13 h1_13]
  ring

end Hqiv.Physics

import HqivSpine.Geometry.Lorentz
import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# `HqivSpine.Physics.ColliderVariables` — rapidity, boost additivity, and transverse mass

The collider-kinematics reading of the spine's Lorentz boost group. A particle's longitudinal motion
is captured by its **rapidity** `y`, and the boost group law `Λ(η)·Λ(ξ)=Λ(η+ξ)` (`boostMatrix_mul`,
already proved in `Geometry.Lorentz`) becomes the additive shift `y ↦ y+η` — the reason rapidity
*differences* are the boost-invariant observable used at every collider.

* **Rapidity parametrisation.** A `1+1` momentum of transverse mass `mT` and rapidity `y` is
  `(mT cosh y, mT sinh y)`; its rapidity readout is exactly `y` (`rapidity_momentum2`).
* **Additivity.** A boost of rapidity `η` shifts the momentum to rapidity `η+y`
  (`rapidity_boost_shift`, `rapidity_additive`), so rapidity *gaps* are boost-invariant
  (`rapidity_difference_boost_invariant`).
* **Invariant & transverse mass.** The Minkowski invariant is `−mT²` (`minkowskiSq_momentum2`), boost
  invariant via `Geometry`’s isometry (`invariantMassSq_boost_invariant`); the transverse mass
  satisfies `mT² = m² + p_T² ≥ m²` (`transverseMassSq_ge_massSq`).

Bundled in `ColliderClosure` / `collider_closure`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.ColliderVariables

open Real HqivSpine.Geometry

/-- A `1+1` four-momentum of transverse mass `mT` and rapidity `y`: `(E, p_z) = (mT cosh y, mT sinh y)`. -/
noncomputable def momentum2 (mT y : ℝ) : Fin 2 → ℝ := ![mT * Real.cosh y, mT * Real.sinh y]

/-- **Rapidity readout** `y = artanh(p_z/E)`. -/
noncomputable def rapidity (p : Fin 2 → ℝ) : ℝ := Real.artanh (p 1 / p 0)

/-- **The rapidity readout recovers the parameter `y`.** -/
theorem rapidity_momentum2 (mT y : ℝ) (h : mT ≠ 0) : rapidity (momentum2 mT y) = y := by
  unfold rapidity momentum2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [mul_div_mul_left _ _ h, ← Real.tanh_eq_sinh_div_cosh, Real.artanh_tanh]

/-- **A boost of rapidity `η` shifts the momentum to rapidity `η+y`.** -/
theorem rapidity_boost_shift (η mT y : ℝ) :
    boostApply η (momentum2 mT y) = momentum2 mT (η + y) := by
  funext i
  fin_cases i <;>
    simp only [boostApply, momentum2, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, Real.cosh_add, Real.sinh_add] <;> ring

/-- **Rapidity is additive under boosts:** `y(Λ(η)p) = η + y(p)`. -/
theorem rapidity_additive (η mT y : ℝ) (h : mT ≠ 0) :
    rapidity (boostApply η (momentum2 mT y)) = η + y := by
  rw [rapidity_boost_shift, rapidity_momentum2 mT (η + y) h]

/-- **Rapidity gaps are boost-invariant** — the workhorse collider observable. -/
theorem rapidity_difference_boost_invariant (η mT1 y1 mT2 y2 : ℝ) (h1 : mT1 ≠ 0) (h2 : mT2 ≠ 0) :
    rapidity (boostApply η (momentum2 mT1 y1)) - rapidity (boostApply η (momentum2 mT2 y2))
      = y1 - y2 := by
  rw [rapidity_additive η mT1 y1 h1, rapidity_additive η mT2 y2 h2]; ring

/-! ## Invariant mass -/

/-- **Physical invariant mass squared** `= −⟨p,p⟩` (the metric has signature `− +`). -/
noncomputable def invariantMassSq (p : Fin 2 → ℝ) : ℝ := - minkowskiSq p

/-- **The invariant of a `(mT, y)` momentum is `mT²`** (independent of rapidity). -/
theorem invariantMassSq_momentum2 (mT y : ℝ) : invariantMassSq (momentum2 mT y) = mT ^ 2 := by
  unfold invariantMassSq minkowskiSq momentum2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have h := Real.cosh_sq_sub_sinh_sq y
  nlinarith [h]

/-- **Invariant mass is boost-invariant** (from `Geometry.Lorentz`'s isometry). -/
theorem invariantMassSq_boost_invariant (η : ℝ) (p : Fin 2 → ℝ) :
    invariantMassSq (boostApply η p) = invariantMassSq p := by
  unfold invariantMassSq
  rw [← boostMatrix_mulVec, minkowskiSq_boost_invariant_mulVec]

/-! ## Transverse mass -/

/-- **Transverse mass squared** `mT² = m² + p_T²`. -/
def transverseMassSq (m pT : ℝ) : ℝ := m ^ 2 + pT ^ 2

/-- **`mT² ≥ m²`** — transverse mass never drops below the rest mass. -/
theorem transverseMassSq_ge_massSq (m pT : ℝ) : m ^ 2 ≤ transverseMassSq m pT := by
  unfold transverseMassSq; nlinarith [sq_nonneg pT]

/-- **`mT = m` at zero transverse momentum.** -/
theorem transverseMassSq_eq_massSq_of_zero_pT (m : ℝ) : transverseMassSq m 0 = m ^ 2 := by
  unfold transverseMassSq; ring

/-! ## Closure -/

/-- **Collider-variable discharge bundle.** -/
structure ColliderClosure : Prop where
  rapidity_readout : ∀ {mT : ℝ}, mT ≠ 0 → ∀ y, rapidity (momentum2 mT y) = y
  boost_shift : ∀ η mT y : ℝ, boostApply η (momentum2 mT y) = momentum2 mT (η + y)
  rapidity_adds : ∀ {mT : ℝ}, mT ≠ 0 → ∀ η y, rapidity (boostApply η (momentum2 mT y)) = η + y
  gap_invariant : ∀ {mT1 mT2 : ℝ}, mT1 ≠ 0 → mT2 ≠ 0 → ∀ η y1 y2,
    rapidity (boostApply η (momentum2 mT1 y1)) - rapidity (boostApply η (momentum2 mT2 y2)) = y1 - y2
  mass_invariant : ∀ η p, invariantMassSq (boostApply η p) = invariantMassSq p
  transverse_floor : ∀ m pT : ℝ, m ^ 2 ≤ transverseMassSq m pT

/-- **The collider-variable story is discharged:** rapidity is the additive boost coordinate, gaps are
boost-invariant, the invariant mass is preserved, and the transverse mass floors at the rest mass —
all from the spine's Lorentz group, PDG-free. -/
theorem collider_closure : ColliderClosure where
  rapidity_readout := fun h y => rapidity_momentum2 _ y h
  boost_shift := rapidity_boost_shift
  rapidity_adds := fun h η y => rapidity_additive η _ y h
  gap_invariant := fun h1 h2 η y1 y2 => rapidity_difference_boost_invariant η _ y1 _ y2 h1 h2
  mass_invariant := invariantMassSq_boost_invariant
  transverse_floor := transverseMassSq_ge_massSq

end HqivSpine.Physics.ColliderVariables

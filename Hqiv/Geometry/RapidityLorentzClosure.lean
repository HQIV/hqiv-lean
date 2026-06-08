import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Matrix.Mul
import Hqiv.Geometry.HQVMMinkowskiSubstrate
import Hqiv.Geometry.SpacetimeMinkowski11Embed4
import Hqiv.Geometry.SpatialSliceRapidityScaffold
import Hqiv.Physics.RapidityZetaPhaseBridge

/-!
# Rapidity phase ↔ Lorentz invariance closure (proved glue)

This module discharges the checklist in `HQVMMinkowskiSubstrate`:

* **(A) Carrier and chart.** `NullLatticeEvent` pairs a rapidity label `η` with a discrete shell
  index `m`. The chart `nullLatticeEmbed` maps events to forward-null vectors in `1+1` Minkowski
  space via the classical rapidity parametrization `Λ(η)(1,1)`.
* **(B) Rapidity action.** `nullLatticeRapidityBoost` adds rapidities on the carrier; the chart is
  **rapidity equivariant** (`nullLatticeChart_rapidity_equivariant`).
* **(C) Auxiliary `φ` rule.** `phiLorentzScalarBoost` is the identity (φ is a Lorentz scalar on the
  flat slice); the polar-angle / zeta phase readout is therefore boost-invariant.
* **(D) Target statement.** Bilinear `minkowskiInner11` invariance, null-cone preservation, and
  `minkowskiSq4` invariance on the embedded `(t,x¹,0,0)` plane under the partial `1+1` boost in
  `Fin 4`.

**Scope.** This is **full Lorentz invariance in the `1+1` null-chart sector** (rapidity boosts) with
honest `3+1` extension only on the embedded Minkowski plane. Spatial rotations on `(x¹,x²,x³)` are
discharged in `Hqiv.Geometry.SpatialRotationLorentzClosure` (`full_lorentz_closure_discharged`).
-/

namespace Hqiv.Geometry

open Real Matrix
open scoped Matrix

/-- Forward lightlike direction in `1+1`. -/
def forwardNull11 : Fin 2 → ℝ :=
  ![1, 1]

theorem forwardNull11_null : minkowskiSq11 forwardNull11 = 0 := by
  simp [forwardNull11, minkowskiSq11, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Discrete null-lattice event: rapidity label plus shell index (metadata for readouts). -/
structure NullLatticeEvent where
  η : ℝ
  m : ℕ

/-- Chart into `1+1` Minkowski coordinates: classical rapidity parametrization of the forward null ray. -/
noncomputable def nullLatticeEmbed (e : NullLatticeEvent) : Fin 2 → ℝ :=
  boostApply11 e.η forwardNull11

/-- Rapidity acts by **addition** on the carrier (rapidity group on the null chart). -/
def nullLatticeRapidityBoost (ξ : ℝ) (e : NullLatticeEvent) : NullLatticeEvent :=
  { η := e.η + ξ, m := e.m }

/-- Canonical `1+1` chart packaging for `NullLatticeEvent`. -/
noncomputable def nullLatticeChart : Minkowski11Chart NullLatticeEvent :=
  ⟨nullLatticeEmbed⟩

theorem boostApply11_add (η ξ : ℝ) (v : Fin 2 → ℝ) :
    boostApply11 (η + ξ) v = boostApply11 η (boostApply11 ξ v) := by
  funext i
  fin_cases i <;> simp [boostApply11] <;> ring_nf <;>
    rw [Real.cosh_add, Real.sinh_add] <;> ring

theorem boostApply11_commute (η ξ : ℝ) (v : Fin 2 → ℝ) :
    boostApply11 η (boostApply11 ξ v) = boostApply11 ξ (boostApply11 η v) := by
  funext i
  fin_cases i <;> simp [boostApply11] <;> ring

/-- Chart–boost compatibility on the null-lattice carrier. -/
theorem nullLatticeChart_rapidity_equivariant :
    nullLatticeChart.RapidityEquivariant nullLatticeRapidityBoost := by
  intro ξ e
  dsimp [nullLatticeChart, Minkowski11Chart.RapidityEquivariant, nullLatticeEmbed,
    nullLatticeRapidityBoost]
  rw [boostApply11_add, boostApply11_commute, boostMatrix11_mulVec]

theorem nullLatticeEmbed_null (e : NullLatticeEvent) : minkowskiSq11 (nullLatticeEmbed e) = 0 := by
  dsimp [nullLatticeEmbed]
  exact minkowskiSq11_boost_invariant e.η forwardNull11 ▸ forwardNull11_null

theorem nullLatticeEmbed_rapidity_add (ξ : ℝ) (e : NullLatticeEvent) :
    nullLatticeEmbed (nullLatticeRapidityBoost ξ e) = boostApply11 ξ (nullLatticeEmbed e) := by
  dsimp [nullLatticeEmbed, nullLatticeRapidityBoost]
  rw [boostApply11_add, boostApply11_commute]

/-- Auxiliary `φ` is unchanged under rapidity boost (Lorentz-scalar rule on the flat slice). -/
def phiLorentzScalarBoost (_η φ : ℝ) : ℝ :=
  φ

theorem phiLorentzScalarBoost_eq (η φ : ℝ) : phiLorentzScalarBoost η φ = φ :=
  rfl

theorem polarAngleFromRapidity_invariant_under_phi_scalar_boost (η φ t : ℝ) (m : ℕ) :
    polarAngleFromRapidity (phiLorentzScalarBoost η φ) t m = polarAngleFromRapidity φ t m := by
  simp [phiLorentzScalarBoost, polarAngleFromRapidity_eq]

theorem rapidityPhaseMonogamyLocked_invariant_under_phi_scalar_boost (η φ t : ℝ) :
    rapidityPhaseMonogamyLocked (phiLorentzScalarBoost η φ) t = rapidityPhaseMonogamyLocked φ t := by
  simp [rapidityPhaseMonogamyLocked, phiLorentzScalarBoost, timeAngle]

/-!
## `3+1` embed: partial boost on the `(t,x¹,0,0)` plane
-/

/-- Orthochronous boost acting only on HQIV components `0` (time) and `1` (first spatial). -/
noncomputable def boostMatrix41 (η : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![cosh η, sinh η, 0, 0; sinh η, cosh η, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

noncomputable def boostApply41 (η : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  boostMatrix41 η *ᵥ x

theorem boostMatrix41_mulVec_lift11 (η : ℝ) (v : Fin 2 → ℝ) :
    boostMatrix41 η *ᵥ lift11ToFin4 v = lift11ToFin4 (boostApply11 η v) := by
  funext i
  fin_cases i <;>
    simp [boostMatrix41, lift11ToFin4, boostApply11, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Pi.single_apply, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]

theorem minkowskiSq4_boost_invariant_on_embedded11 (η : ℝ) (v : Fin 2 → ℝ) :
    minkowskiSq4 (boostApply41 η (lift11ToFin4 v)) = minkowskiSq4 (lift11ToFin4 v) := by
  rw [boostApply41, boostMatrix41_mulVec_lift11, minkowskiSq4_lift11_eq_minkowskiSq11,
    minkowskiSq4_lift11_eq_minkowskiSq11, minkowskiSq11_boost_invariant]

theorem minkowskiSq4_lift_forwardNull_null : minkowskiSq4 (lift11ToFin4 forwardNull11) = 0 := by
  rw [minkowskiSq4_lift11_eq_minkowskiSq11, forwardNull11_null]

theorem minkowskiSq4_null_forward_embed_invariant (η : ℝ) :
    minkowskiSq4 (boostApply41 η (lift11ToFin4 forwardNull11)) = 0 := by
  rw [minkowskiSq4_boost_invariant_on_embedded11, minkowskiSq4_lift_forwardNull_null]

/-!
## Packaged discharge certificate
-/

/-- Main closure bundle: chart equivariance, nullness, bilinear invariance, `3+1` plane invariance. -/
structure RapidityLorentzClosure where
  chart_rapidity_equivariant :
    nullLatticeChart.RapidityEquivariant nullLatticeRapidityBoost
  chart_embed_null : ∀ e : NullLatticeEvent, minkowskiSq11 (nullLatticeEmbed e) = 0
  minkowski_inner_boost_invariant :
    ∀ (η : ℝ) (u v : Fin 2 → ℝ),
      minkowskiInner11 (boostMatrix11 η *ᵥ u) (boostMatrix11 η *ᵥ v) = minkowskiInner11 u v
  minkowskiSq4_embed_boost_invariant :
    ∀ (η : ℝ) (v : Fin 2 → ℝ),
      minkowskiSq4 (boostApply41 η (lift11ToFin4 v)) = minkowskiSq4 (lift11ToFin4 v)
  polar_phase_scalar_invariant :
    ∀ (η φ t : ℝ) (m : ℕ),
      polarAngleFromRapidity (phiLorentzScalarBoost η φ) t m = polarAngleFromRapidity φ t m
  hqvm_flat_g_tt : ∀ t : ℝ, OnFlatHQVMSubstrate 0 0 → HQVM_g_tt (HQVM_lapse 0 0 t) = -1

noncomputable def rapidityLorentzClosureDefault : RapidityLorentzClosure where
  chart_rapidity_equivariant := nullLatticeChart_rapidity_equivariant
  chart_embed_null := nullLatticeEmbed_null
  minkowski_inner_boost_invariant := fun η u v => minkowskiInner11_boost_invariant η u v
  minkowskiSq4_embed_boost_invariant := minkowskiSq4_boost_invariant_on_embedded11
  polar_phase_scalar_invariant := polarAngleFromRapidity_invariant_under_phi_scalar_boost
  hqvm_flat_g_tt := fun t h => HQVM_g_tt_neg_one_of_vanishing 0 0 t h.1 h.2

theorem rapidity_lorentz_closure_discharged : Nonempty RapidityLorentzClosure :=
  ⟨rapidityLorentzClosureDefault⟩

end Hqiv.Geometry

namespace Hqiv.Physics

open Complex
open Hqiv.Geometry

/-- Zeta phase exponent is invariant when `φ` transforms as a Lorentz scalar under rapidity boost. -/
theorem zetaHQIVTerm_phase_invariant_under_phi_scalar_boost (η φ t : ℝ) (m : ℕ) :
    I * (phiLorentzScalarBoost η φ) * t * delta_theta_prime (m : ℝ) =
      I * φ * t * delta_theta_prime (m : ℝ) := by
  simp [phiLorentzScalarBoost]

theorem zetaHQIVTerm_cexp_invariant_under_phi_scalar_boost (η φ t : ℝ) (m : ℕ) :
    cexp (I * (phiLorentzScalarBoost η φ) * t * delta_theta_prime (m : ℝ)) =
      cexp (I * φ * t * delta_theta_prime (m : ℝ)) := by
  rw [zetaHQIVTerm_phase_invariant_under_phi_scalar_boost]

theorem zetaHQIVTerm_cexp_invariant_under_phi_scalar_boost_polar (η φ t : ℝ) (m : ℕ) :
    cexp (I * (polarAngleFromRapidity (phiLorentzScalarBoost η φ) t m : ℂ)) =
      cexp (I * (polarAngleFromRapidity φ t m : ℂ)) := by
  rw [polarAngleFromRapidity_invariant_under_phi_scalar_boost]

end Hqiv.Physics

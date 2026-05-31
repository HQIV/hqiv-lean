import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Order.Monotone.Basic

import Hqiv.Algebra.G2Embedding
import Hqiv.Generators
import Hqiv.GeneratorsFromAxioms
import Hqiv.Geometry.HQVMetric

namespace Hqiv

open Matrix

/-!
# Algebra-first seed for O-Maxwell

This module packages the lightest algebra-facing inputs needed by the Maxwell stack:

- the physical seed set `G₂ ∪ {Δ}`,
- the `4 × 4` electromagnetic / quaternionic block cut from the existing `so(8)` generators,
- the rapidity/tipping angle used in the phase-horizon story,
- an algebra-first coupling slot whose temperature-ladder form can be recovered later as a
  projection hypothesis.

The goal is to keep `ModifiedMaxwell` close to the octonion / `G₂ ∪ Δ` picture while treating
`phi_of_T` as a later readout layer, not the foundational coupling source.

Compact **scalar** Laplace–Beltrami ladders on the quaternion phase sphere `S³` and the
one-step extension shell `S⁴` (spectral data only) live in
`Hqiv.Geometry.QuaternionMaxwellS3OMaxwellS4Spectral`, alongside the larger `S⁷` package in
`Hqiv.Geometry.S7MetahorizonCasimir`.
-/

/-- The algebraic seed set for the O-Maxwell ladder: `G₂ ∪ {Δ}`. -/
def algebraicMaxwellSeedSet : Set (Matrix (Fin 8) (Fin 8) ℝ) :=
  Set.range Hqiv.Algebra.g2Generator ∪ {Hqiv.phaseLiftDelta}

/-- The lower-right `4 × 4` Cayley-Dickson / H-sector block of an `8 × 8` generator. -/
def algebraicMaxwellQuadrantBottomRight (M : Matrix (Fin 8) (Fin 8) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => M ⟨i.val + 4, by omega⟩ ⟨j.val + 4, by omega⟩

/-- The H / electromagnetic block extracted from the `n`-th existing `so(8)` generator. -/
def algebraicMaxwellHBlock (n : ℕ) : Matrix (Fin 4) (Fin 4) ℝ :=
  algebraicMaxwellQuadrantBottomRight
    (Hqiv.so8Generator ⟨n % 28, Nat.mod_lt _ (by norm_num)⟩)

/-- The parent `so(8)` generator whose lower-right block feeds the algebra-first Maxwell seed. -/
def algebraicMaxwellParentGenerator (n : ℕ) : Matrix (Fin 8) (Fin 8) ℝ :=
  Hqiv.so8Generator ⟨n % 28, Nat.mod_lt _ (by norm_num)⟩

theorem algebraicMaxwellParentGenerator_mem_seedSpan (n : ℕ) :
    algebraicMaxwellParentGenerator n ∈ Submodule.span ℝ (Set.range Hqiv.so8Generator) := by
  unfold algebraicMaxwellParentGenerator
  exact Submodule.subset_span (Set.mem_range_self _)

/-- The existing H-block description, repackaged for the algebra-first Maxwell ladder. -/
theorem algebraicMaxwellParentGenerator_block_eq_HBlock (n : ℕ) :
    algebraicMaxwellQuadrantBottomRight (algebraicMaxwellParentGenerator n) =
      algebraicMaxwellHBlock n := by
  rfl

/-- A distinguished scalar entry from the H block used as the algebraic block witness. -/
def algebraicMaxwellBlockSeed (n : ℕ) : ℝ :=
  algebraicMaxwellHBlock n 0 1

/-- Quarter period of the horizon phase. This is the natural scale of the tipping angle. -/
noncomputable def horizonQuarterPeriod : ℝ := twoPi / 4

theorem horizonQuarterPeriod_eq_pi_div_two : horizonQuarterPeriod = Real.pi / 2 := by
  unfold horizonQuarterPeriod twoPi
  ring

/-- Phase-horizon tipping angle from the local electric energy witness. -/
noncomputable def delta_theta_prime (E' : ℝ) : ℝ := Real.arctan E' * horizonQuarterPeriod

theorem delta_theta_prime_eq_arctan_mul_pi_div_two (E' : ℝ) :
    delta_theta_prime E' = Real.arctan E' * (Real.pi / 2) := by
  simp [delta_theta_prime, horizonQuarterPeriod_eq_pi_div_two]

theorem delta_theta_prime_monotone : Monotone (delta_theta_prime : ℝ → ℝ) := by
  intro a b hab
  rw [delta_theta_prime_eq_arctan_mul_pi_div_two, delta_theta_prime_eq_arctan_mul_pi_div_two]
  have hπ : 0 ≤ Real.pi / 2 := by positivity
  exact mul_le_mul_of_nonneg_right (Real.arctan_mono hab) hπ

theorem tipping_delta_theta_zero : delta_theta_prime 0 = 0 := by
  unfold delta_theta_prime
  rw [Real.arctan_zero, zero_mul]

theorem tipping_delta_theta_bounded (E' : ℝ) :
    |delta_theta_prime E'| < horizonQuarterPeriod ^ 2 := by
  unfold delta_theta_prime
  rw [horizonQuarterPeriod_eq_pi_div_two]
  have h₁ := Real.neg_pi_div_two_lt_arctan E'
  have h₂ := Real.arctan_lt_pi_div_two E'
  have hπ2 : 0 < Real.pi / 2 := div_pos Real.pi_pos (by norm_num)
  rw [abs_mul, abs_of_pos hπ2, sq]
  exact mul_lt_mul_of_pos_right (abs_lt.mpr ⟨by linarith, h₂⟩) hπ2

/-- The rapidity/tipping contribution to the algebra-first Maxwell seed. -/
noncomputable def algebraicMaxwellRapiditySeed (m : ℕ) : ℝ :=
  alpha * delta_theta_prime (m : ℝ)

/-- At rest / zero local electric tipping, the rapidity contribution vanishes. -/
theorem algebraicMaxwellRapiditySeed_zero : algebraicMaxwellRapiditySeed 0 = 0 := by
  simp [algebraicMaxwellRapiditySeed, tipping_delta_theta_zero]

/-- The algebra-first exponent: monogamy split + rapidity/tipping + H-block witness. -/
noncomputable def algebraicMaxwellCouplingExponent (m : ℕ) : ℝ :=
  gamma_HQIV + algebraicMaxwellRapiditySeed m + algebraicMaxwellBlockSeed m

/-- Positive algebraic slot used by the Maxwell ladder before any temperature projection. -/
noncomputable def algebraicMaxwellProjectionSlot (m : ℕ) : ℝ :=
  Real.exp (algebraicMaxwellCouplingExponent m)

theorem algebraicMaxwellProjectionSlot_pos (m : ℕ) :
    0 < algebraicMaxwellProjectionSlot m := by
  unfold algebraicMaxwellProjectionSlot
  positivity

/-- The algebra-first log slot used in `ModifiedMaxwell`. -/
noncomputable def algebraicMaxwellCouplingLog (ν : Fin 4) : ℝ :=
  Real.log (algebraicMaxwellProjectionSlot ν.val)

theorem algebraicMaxwellCouplingLog_eq_exponent (ν : Fin 4) :
    algebraicMaxwellCouplingLog ν = algebraicMaxwellCouplingExponent ν.val := by
  unfold algebraicMaxwellCouplingLog algebraicMaxwellProjectionSlot
  rw [Real.log_exp]

/-- Optional projection from the algebraic Maxwell slot back to the temperature ladder. -/
structure AlgebraicMaxwellProjectionHypothesis (m : ℕ) : Prop where
  slot_eq_phi_of_T : algebraicMaxwellProjectionSlot m = phi_of_T (T m)

theorem algebraicMaxwellCouplingLog_eq_phi_of_T (ν : Fin 4)
    (h : AlgebraicMaxwellProjectionHypothesis ν.val) :
    algebraicMaxwellCouplingLog ν = Real.log (phi_of_T (T ν.val)) := by
  unfold algebraicMaxwellCouplingLog
  rw [h.slot_eq_phi_of_T]

end Hqiv

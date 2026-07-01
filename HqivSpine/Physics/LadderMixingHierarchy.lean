import HqivSpine.Physics.FanoMixingWeights
import HqivSpine.Physics.CabibboInterference
import HqivSpine.Physics.MassLadder

/-!
# `HqivSpine.Physics.LadderMixingHierarchy` — bending the democratic baseline with the mass ladder

`FanoMixingWeights` fixed the **democratic** mixing fraction `sin²θ = 1/3` from Fano incidence;
`MixingAngles` showed mixing **shrinks with the mass hierarchy** (`tan²θ = m_light/m_heavy`); and
`MassLadder` *derived* the generation ladder as the `S³` Beltrami spectrum `λ(g) = g + 1`. This module
connects the three: it feeds the **derived ladder eigenvalues** (not free masses) into the
Gatto–Sartori–Tonin mixing fraction, so the hierarchical angles become **derived rationals**.

* **Ladder mixing fraction.** `sin²θ(gₗ,gₕ) = λ(gₗ)/(λ(gₗ)+λ(gₕ)) = (gₗ+1)/((gₗ+1)+(gₕ+1))`
  (`sinθLadder_sq`) — fixed by the spectrum, no fitted parameter.
* **The democratic baseline is the leading ladder rung.** The simplest adjacent pair `λ = 1 : 2`
  gives exactly `1/3` — the Fano overlap value (`democratic_eq_leading_ladder`). The incidence
  baseline and the ladder agree at leading order: two faces of the same structure.
* **The ladder bends it into a hierarchy.** More-separated generations mix strictly less
  (`ladder_mixing_strictAnti`), dropping below the democratic `1/3` once the rungs differ by two or
  more (`ladder_below_democratic`) — the correct *direction* of the fermion mixing hierarchy, derived.
* **A fully derived CKM matrix.** `ckmLadder` plugs the three ladder-pair angles into the unitary
  CKM machinery: unitary (`ckmLadder_unitary`) and CP-violating (`ckmLadder_cp_violation`) with **no
  free mass input** — only the derived spectrum and the holonomy phase.

**Honest scope.** This bends the baseline in the right direction using the *derived* ladder, removing
the "free mass-ratio" caveat for the qualitative hierarchy. It does **not** reproduce the measured CKM
magnitudes: the linear ladder `λ = g+1` gives only mild suppression (e.g. `1/4`, not the steep
observed hierarchy). The true mass-weighting functional (and the phase value `δ`) remain open — the
remaining gap is a *physics* question (which spectral functional drives mixing), not a formal one.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.LadderMixingHierarchy

open HqivSpine.Physics
open HqivSpine.Physics.CabibboInterference
open HqivSpine.Physics.CKMMixingMatrix
open HqivSpine.Physics.CPHolonomyPhase

/-! ## The ladder mixing angle -/

/-- Sine of the mixing angle between generations `gₗ, gₕ`, with the **derived** Beltrami ladder
eigenvalues `λ(g) = g+1` in place of free masses. -/
noncomputable def sinθLadder (gL gH : ℕ) : ℝ :=
  sinθ (beltramiMinEigenvalue gL) (beltramiMinEigenvalue gH)

/-- Cosine of the ladder mixing angle. -/
noncomputable def cosθLadder (gL gH : ℕ) : ℝ :=
  cosθ (beltramiMinEigenvalue gL) (beltramiMinEigenvalue gH)

theorem ladderEigen_pos (g : ℕ) : 0 < beltramiMinEigenvalue g := by
  unfold beltramiMinEigenvalue; positivity

theorem sinθLadder_pos (gL gH : ℕ) : 0 < sinθLadder gL gH := by
  unfold sinθLadder sinθ
  rw [Real.sqrt_pos]
  have := ladderEigen_pos gL
  have := ladderEigen_pos gH
  positivity

theorem cosθLadder_pos (gL gH : ℕ) : 0 < cosθLadder gL gH := by
  unfold cosθLadder cosθ
  rw [Real.sqrt_pos]
  have := ladderEigen_pos gL
  have := ladderEigen_pos gH
  positivity

/-- **The ladder mixing fraction** is the derived spectral ratio
`sin²θ = (gₗ+1)/((gₗ+1)+(gₕ+1))`. -/
theorem sinθLadder_sq (gL gH : ℕ) :
    sinθLadder gL gH ^ 2 = ((gL : ℝ) + 1) / (((gL : ℝ) + 1) + ((gH : ℝ) + 1)) := by
  unfold sinθLadder sinθ beltramiMinEigenvalue
  rw [Real.sq_sqrt (by positivity)]

/-- **Pythagoras** for the ladder angle. -/
theorem ladder_pyth (gL gH : ℕ) : cosθLadder gL gH ^ 2 + sinθLadder gL gH ^ 2 = 1 := by
  have h := sin_sq_add_cos_sq (beltramiMinEigenvalue gL) (beltramiMinEigenvalue gH)
    (ladderEigen_pos gL) (ladderEigen_pos gH)
  unfold sinθLadder cosθLadder
  linarith

/-! ## The democratic baseline is the leading ladder rung -/

/-- **The Fano democratic baseline `1/3` is exactly the leading ladder mixing fraction** (the
adjacent pair `λ = 1 : 2`): the incidence count and the derived spectrum agree at leading order. -/
theorem democratic_eq_leading_ladder :
    FanoMixingWeights.sinθFano ^ 2 = sinθLadder 0 1 ^ 2 := by
  rw [FanoMixingWeights.sinθFano_sq, sinθLadder_sq]; norm_num

/-! ## The ladder bends the baseline into a hierarchy -/

/-- **Mixing shrinks with generational separation:** a more-separated heavy generation gives a
strictly smaller mixing fraction. The derived ladder produces a genuine hierarchy. -/
theorem ladder_mixing_strictAnti {gH gH' : ℕ} (h : gH < gH') :
    sinθLadder 0 gH' ^ 2 < sinθLadder 0 gH ^ 2 := by
  rw [sinθLadder_sq, sinθLadder_sq]
  simp only [Nat.cast_zero, zero_add]
  refine one_div_lt_one_div_of_lt (by positivity) ?_
  have : (gH : ℝ) < (gH' : ℝ) := by exact_mod_cast h
  linarith

/-- **Below the democratic baseline:** once the rungs differ by two or more, the ladder mixing
fraction drops strictly below the Fano value `1/3`. -/
theorem ladder_below_democratic {gH : ℕ} (h : 2 ≤ gH) :
    sinθLadder 0 gH ^ 2 < FanoMixingWeights.sinθFano ^ 2 := by
  rw [democratic_eq_leading_ladder]
  exact ladder_mixing_strictAnti (show (1 : ℕ) < gH by omega)

/-! ## A fully derived (mass-input-free) CKM matrix -/

/-- **CKM matrix from the ladder:** the three plane angles are the ladder mixing angles of the
generation pairs `(0,1), (0,2), (1,2)`, with holonomy phase `δ`. -/
noncomputable def ckmLadder (δ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ckm (cosθLadder 0 1) (sinθLadder 0 1) (cosθLadder 0 2) (sinθLadder 0 2)
    (cosθLadder 1 2) (sinθLadder 1 2) δ

/-- **The ladder CKM matrix is unitary** — angles fixed by the derived spectrum. -/
theorem ckmLadder_unitary (δ : ℝ) : ckmLadder δ ∈ unitary (Matrix (Fin 3) (Fin 3) ℂ) :=
  ckm_unitary (ladder_pyth 0 1) (ladder_pyth 0 2) (ladder_pyth 1 2)

theorem ckmLadder_unitary_apply (δ : ℝ) : star (ckmLadder δ) * ckmLadder δ = 1 :=
  (ckmLadder_unitary δ).1

/-- **CP violation from the fully derived matrix:** non-zero Jarlskog invariant iff the holonomy
phase is genuine — the angles carry no free mass input. -/
theorem ckmLadder_cp_violation (δ : ℝ) (hδ : Real.sin δ ≠ 0) :
    jarlskog (ckmLadder δ 0 1) (ckmLadder δ 1 2) (ckmLadder δ 0 2) (ckmLadder δ 1 1) ≠ 0 := by
  rw [ckmLadder, ckm_jarlskog]
  have hc01 := cosθLadder_pos 0 1
  have hc02 := cosθLadder_pos 0 2
  have hc12 := cosθLadder_pos 1 2
  have hs01 := sinθLadder_pos 0 1
  have hs02 := sinθLadder_pos 0 2
  have hs12 := sinθLadder_pos 1 2
  have hprod : (0 : ℝ) < cosθLadder 0 1 * cosθLadder 0 2 ^ 2 * cosθLadder 1 2
      * sinθLadder 0 1 * sinθLadder 0 2 * sinθLadder 1 2 := by positivity
  exact mul_ne_zero (ne_of_gt hprod) hδ

/-! ## Closure -/

/-- **Ladder-mixing-hierarchy discharge bundle.** -/
structure LadderMixingDischarged : Prop where
  ladder_fraction : ∀ gL gH : ℕ,
    sinθLadder gL gH ^ 2 = ((gL : ℝ) + 1) / (((gL : ℝ) + 1) + ((gH : ℝ) + 1))
  democratic_is_leading_rung : FanoMixingWeights.sinθFano ^ 2 = sinθLadder 0 1 ^ 2
  hierarchy : ∀ {gH gH' : ℕ}, gH < gH' → sinθLadder 0 gH' ^ 2 < sinθLadder 0 gH ^ 2
  ckm_unitary : ∀ δ : ℝ, star (ckmLadder δ) * ckmLadder δ = 1
  cp_violation : ∀ δ : ℝ, Real.sin δ ≠ 0 →
    jarlskog (ckmLadder δ 0 1) (ckmLadder δ 1 2) (ckmLadder δ 0 2) (ckmLadder δ 1 1) ≠ 0

/-- **The mass ladder bends the democratic baseline into a hierarchy:** the derived Beltrami spectrum
gives the mixing fraction as a fixed rational, recovers the Fano `1/3` at the leading rung, and
strictly suppresses mixing with generational separation — assembling a unitary, CP-violating CKM
matrix with no free mass input. -/
theorem ladderMixingDischarged_holds : LadderMixingDischarged where
  ladder_fraction := sinθLadder_sq
  democratic_is_leading_rung := democratic_eq_leading_ladder
  hierarchy := ladder_mixing_strictAnti
  ckm_unitary := ckmLadder_unitary_apply
  cp_violation := ckmLadder_cp_violation

end HqivSpine.Physics.LadderMixingHierarchy

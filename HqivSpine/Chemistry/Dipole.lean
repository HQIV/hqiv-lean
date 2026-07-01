import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# `HqivSpine.Chemistry.Dipole` — molecular dipole from the balanced frame

The molecular dipole is the vector sum of bond dipoles on the VSEPR-balanced frame (`Chemistry.VSEPR`).
Because the frame is symmetric with vector sum zero, the magnitude is the resultant of the **bond**
subset `S` of the `d` domains. The Gram identity gives the closed form

`‖∑_{i∈S} v̂ᵢ‖² = |S| + |S|(|S|−1)·c`, and with the balanced cosine `c = −1/(d−1)` this is
`|S|(d−|S|)/(d−1)`.

When every domain is a bond (`|S| = d`) it vanishes — CO₂, CH₄, BF₃, SF₆ are nonpolar by the *same*
balance that fixes their angles. Lone pairs (`|S| < d`) break the cancellation and give H₂O, NH₃, SO₂
their dipoles.

Mathlib-only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Chemistry.Dipole

open Finset
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Subset Gram identity.** For a symmetric unit frame (pairwise inner product `c`), the squared
resultant of the directions in `S` is `|S| + |S|(|S|−1)·c`. -/
theorem subset_frame_norm_sq
    (d : ℕ) (v : Fin d → E) (S : Finset (Fin d))
    (hunit : ∀ i, ⟪v i, v i⟫ = (1 : ℝ))
    (c : ℝ) (hsym : ∀ i j, i ≠ j → ⟪v i, v j⟫ = c) :
    (⟪∑ i ∈ S, v i, ∑ j ∈ S, v j⟫ : ℝ)
      = (S.card : ℝ) + ((S.card : ℝ) * ((S.card : ℝ) - 1)) * c := by
  rw [sum_inner]
  simp only [inner_sum]
  have row : ∀ i ∈ S, (∑ j ∈ S, (⟪v i, v j⟫ : ℝ)) = 1 + ((S.card : ℝ) - 1) * c := by
    intro i hi
    rw [Finset.sum_eq_add_sum_diff_singleton hi, hunit i]
    have hoff : ∀ j ∈ S \ {i}, (⟪v i, v j⟫ : ℝ) = c := by
      intro j hj
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
      exact hsym i j (fun h => hj.2 h.symm)
    rw [Finset.sum_congr rfl hoff, Finset.sum_const]
    have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨i, hi⟩
    have hcard : (S \ {i}).card = S.card - 1 := by
      rw [← Finset.erase_eq, Finset.card_erase_of_mem hi]
    rw [hcard, nsmul_eq_mul]
    have hc1 : ((S.card - 1 : ℕ) : ℝ) = (S.card : ℝ) - 1 := by
      rw [Nat.cast_sub hpos]; push_cast; ring
    rw [hc1]
  rw [Finset.sum_congr rfl row, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **Resultant factor.** With the balanced cosine `c = −1/(d−1)`, the squared resultant of `|S|`
bonds among `d` domains is `|S|(d−|S|)/(d−1)`. -/
theorem balanced_partial_resultant_sq
    (d : ℕ) (v : Fin d → E) (S : Finset (Fin d))
    (hunit : ∀ i, ⟪v i, v i⟫ = (1 : ℝ))
    (c : ℝ) (hsym : ∀ i j, i ≠ j → ⟪v i, v j⟫ = c)
    (hc : c = -1 / ((d : ℝ) - 1)) (hd : (d : ℝ) ≠ 1) :
    (⟪∑ i ∈ S, v i, ∑ j ∈ S, v j⟫ : ℝ)
      = (S.card : ℝ) * ((d : ℝ) - S.card) / ((d : ℝ) - 1) := by
  rw [subset_frame_norm_sq d v S hunit c hsym, hc]
  have hd1 : (d : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hd
  field_simp
  ring

/-- **Nonpolarity from balance.** When every domain is a bond (`S = univ`), the resultant vanishes —
the dipole cancels by the same `∑ v̂ = 0` that sets the VSEPR angles. -/
theorem all_bonds_resultant_zero
    (d : ℕ) (v : Fin d → E) (hsum : ∑ i, v i = 0) :
    (⟪∑ i ∈ (univ : Finset (Fin d)), v i, ∑ j ∈ univ, v j⟫ : ℝ) = 0 := by
  simp [hsum]

/-- Equal-magnitude bond dipoles on a balanced frame sum to zero: `∑ μ•v̂ᵢ = 0`. -/
theorem symmetric_dipole_vanishes
    (d : ℕ) (v : Fin d → E) (μ : ℝ) (hsum : ∑ i, v i = 0) :
    ∑ i, μ • v i = 0 := by
  rw [← Finset.smul_sum, hsum, smul_zero]

end HqivSpine.Chemistry.Dipole

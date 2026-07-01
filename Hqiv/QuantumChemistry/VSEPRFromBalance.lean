import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic

/-!
# VSEPR is Kirchhoff balance, not a chemistry input

The steric-domain angle `arccos(−1/(d−1))` (sp 180°, sp² 120°, sp³ 109.47°) is *not* an injected
rule.  Model each of an atom's `d` σ-domains as a **unit informational-monogamy contact direction**.
Two facts force the angle:

* **balance** — the centre is in equilibrium, so the contact directions carry no net flux:
  `∑ᵢ vᵢ = 0` (Kirchhoff's node law / momentum balance, already in the HQIV conservation layer);
* **symmetry** — equivalent contacts share one pairwise inner product `c`.

Then `0 = ‖∑ᵢ vᵢ‖² = ∑ᵢ∑ⱼ⟪vᵢ,vⱼ⟫ = d·(1 + (d−1)c)`, so `c = −1/(d−1)` and the angle is
`arccos(−1/(d−1))`.  Nothing about chemistry enters — only equilibrium of unit vectors.  This module
proves the balance identity and the cosine, deriving what was previously stated as the VSEPR rule.
-/

namespace Hqiv.QuantumChemistry.VSEPRFromBalance

open Finset
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Balance identity.** For `d` symmetric unit contact directions whose vector sum is zero,
`d·(1 + (d−1)·c) = 0`, where `c` is the common pairwise inner product.  Pure equilibrium of unit
vectors — the Gram trace of a zero-sum symmetric frame. -/
theorem balanced_unit_contacts_identity
    (d : ℕ) (v : Fin d → E)
    (hunit : ∀ i, ⟪v i, v i⟫ = (1 : ℝ))
    (hsum : ∑ i, v i = 0)
    (c : ℝ) (hsym : ∀ i j, i ≠ j → ⟪v i, v j⟫ = c) :
    (d : ℝ) * (1 + ((d : ℝ) - 1) * c) = 0 := by
  have hzero : (⟪(∑ i, v i), (∑ j, v j)⟫ : ℝ) = 0 := by
    rw [hsum]; simp
  rw [sum_inner] at hzero
  simp only [inner_sum] at hzero
  have inner_row : ∀ i, (∑ j, (⟪v i, v j⟫ : ℝ)) = 1 + ((d : ℝ) - 1) * c := by
    intro i
    have hdpos : 0 < d := lt_of_le_of_lt (Nat.zero_le (i : ℕ)) i.isLt
    rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i), hunit i]
    have hoff : ∀ j ∈ univ \ {i}, (⟪v i, v j⟫ : ℝ) = c := by
      intro j hj
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
      exact hsym i j (fun h => hj.2 h.symm)
    rw [Finset.sum_congr rfl hoff, Finset.sum_const]
    have hcard : (univ \ {i} : Finset (Fin d)).card = d - 1 := by
      rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin, Finset.card_singleton]
    rw [hcard]
    have hd1 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub hdpos]; push_cast; ring
    rw [nsmul_eq_mul, hd1]
  rw [Finset.sum_congr rfl (fun i _ => inner_row i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hzero
  exact hzero

/-- **The VSEPR cosine is forced.** With `d ≥ 2` balanced symmetric unit contacts, the common
pairwise cosine is exactly `−1/(d−1)` — the steric-domain angle, derived from equilibrium alone. -/
theorem balanced_unit_contacts_cos
    (d : ℕ) (hd : 2 ≤ d) (v : Fin d → E)
    (hunit : ∀ i, ⟪v i, v i⟫ = (1 : ℝ))
    (hsum : ∑ i, v i = 0)
    (c : ℝ) (hsym : ∀ i j, i ≠ j → ⟪v i, v j⟫ = c) :
    c = -1 / ((d : ℝ) - 1) := by
  have h := balanced_unit_contacts_identity d v hunit hsum c hsym
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    intro hc; linarith
  have hbal : 1 + ((d : ℝ) - 1) * c = 0 := by
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hd0
    · exact h'
  field_simp
  linarith [hbal]

/-- sp³ tetrahedral: four balanced contacts ⇒ cosine `−1/3` (angle 109.47°). -/
theorem tetrahedral_cos
    (v : Fin 4 → E) (hunit : ∀ i, ⟪v i, v i⟫ = (1 : ℝ)) (hsum : ∑ i, v i = 0)
    (c : ℝ) (hsym : ∀ i j, i ≠ j → ⟪v i, v j⟫ = c) :
    c = -1 / 3 := by
  have := balanced_unit_contacts_cos 4 (by norm_num) v hunit hsum c hsym
  norm_num at this ⊢; linarith [this]

end Hqiv.QuantumChemistry.VSEPRFromBalance

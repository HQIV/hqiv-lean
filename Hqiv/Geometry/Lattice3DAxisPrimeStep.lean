import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import Hqiv.Geometry.LatticeFirstQuadrantEdgeCount

/-!
# 3D axis “prime” steps (ℝ³ / `ℤ³`)

**HQIV design note:** in three real dimensions **`3 * 2 = 6`** axis steps (`hqivMarginalPrimePointCount_three`);
the **six** signed coordinate directions in `ℤ³` are **(±1,0,0), (0,±1,0), (0,0,±1)** — minimal shell,
axis-only in this formalization.

**Classical overlap:** same discrete-ray language touches **classical** lattice / prime-adjacent
questions (geometry of numbers); **no** theorem here identifies these six maps with rational primes.

**Composites at scale:** as in the 2D module, large-`m` **composite** angular separation is
search-heavy; **rapidity** in HQIV is meant to **anchor** phase to shell / ray data — see module docs
in `LatticeFirstQuadrantEdgeCount` and `SpatialSliceRapidityScaffold`.
-/

namespace Hqiv.Geometry

@[simp]
theorem hqivMarginalPrimePointCount_three : hqivMarginalPrimePointCount 3 = 6 :=
  rfl

/-- The six signed axis unit steps in `ℤ³`, indexed by axis `Fin 3` and sign `Fin 2` (`0 ↦ +1`, `1 ↦ -1`). -/
def axisUnitStep3 (p : Fin 3 × Fin 2) : Fin 3 → ℤ :=
  fun k => if k = p.1 then (if p.2.val = 0 then (1 : ℤ) else (-1 : ℤ)) else 0

theorem axisUnitStep3_axis (p : Fin 3 × Fin 2) (k : Fin 3) (hk : k ≠ p.1) : axisUnitStep3 p k = 0 := by
  simp [axisUnitStep3, hk]

theorem axisUnitStep3_nonzero (p : Fin 3 × Fin 2) : axisUnitStep3 p p.1 ≠ 0 := by
  dsimp [axisUnitStep3]
  rcases (show p.2.val = 0 ∨ p.2.val = 1 by omega) with h0 | h1
  · rw [h0]; norm_num
  · rw [h1]; norm_num

/-- The six axis steps as a finite set of lattice points. -/
def axisUnitSteps3 : Finset (Fin 3 → ℤ) :=
  Finset.univ.image axisUnitStep3

theorem Fintype_card_fin_three_prod_fin_two : Fintype.card (Fin 3 × Fin 2) = 6 := by
  simp

theorem axisUnitStep3_injective : Function.Injective axisUnitStep3 := by
  rintro ⟨i, si⟩ ⟨j, sj⟩ h
  have hij : i = j := by
    by_contra hne
    have hji := congr_fun h j
    simp [axisUnitStep3, Ne.symm hne] at hji
    rcases (show sj.val = 0 ∨ sj.val = 1 by omega) with h0 | h1
    · have hsj : sj = 0 := Fin.ext h0
      rw [hsj] at hji
      simp at hji
    · have hsj : sj = 1 := Fin.ext h1
      rw [hsj] at hji
      simp at hji
  subst hij
  have hi := congr_fun h i
  simp [axisUnitStep3] at hi
  have hval : si.val = sj.val := by
    rcases (show si.val = 0 ∨ si.val = 1 by omega) with hvi0 | hvi1 <;>
      rcases (show sj.val = 0 ∨ sj.val = 1 by omega) with hvj0 | hvj1
    · simp [hvi0, hvj0] at hi ⊢
    · simp [hvi0, hvj1] at hi ⊢; omega
    · simp [hvi1, hvj0] at hi ⊢; omega
    · simp [hvi1, hvj1] at hi ⊢
  have hsv : si = sj := Fin.ext hval
  simp [hsv]

theorem axisUnitSteps3_card : axisUnitSteps3.card = 6 := by
  dsimp [axisUnitSteps3]
  rw [Finset.card_image_of_injective _ axisUnitStep3_injective]
  exact Fintype_card_fin_three_prod_fin_two

/-- Off-axis coordinates are zero (only the axis `p.1` is nonzero). -/
theorem axisUnitStep3_off_axis_zero (p : Fin 3 × Fin 2) (l : Fin 3) (hl : l ≠ p.1) :
    axisUnitStep3 p l = 0 :=
  axisUnitStep3_axis p l hl

end Hqiv.Geometry

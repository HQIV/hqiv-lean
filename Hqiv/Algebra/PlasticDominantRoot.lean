import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Plastic dominant real root

Third milestone: prove existence of a real root `ρ` of `x^3 - x - 1` in `(1,2)`.
-/

namespace Hqiv.Algebra

/-- Real cubic whose dominant real root is the plastic constant. -/
def plasticCubic (x : ℝ) : ℝ := x ^ 3 - x - 1

lemma plasticCubic_one : plasticCubic 1 = -1 := by
  norm_num [plasticCubic]

lemma plasticCubic_two : plasticCubic 2 = 5 := by
  norm_num [plasticCubic]

/-- There exists a real root of `x^3 - x - 1` in `(1,2)`. -/
theorem exists_plastic_root_Ioo :
    ∃ ρ : ℝ, ρ ∈ Set.Ioo (1 : ℝ) 2 ∧ plasticCubic ρ = 0 := by
  let f : ℝ → ℝ := plasticCubic
  have hcont' : Continuous f := by
    unfold f plasticCubic
    continuity
  have hcont : ContinuousOn f (Set.Icc (1 : ℝ) 2) := hcont'.continuousOn
  have hsub : Set.Icc (f 1) (f 2) ⊆ f '' Set.Icc (1 : ℝ) 2 :=
    intermediate_value_Icc (a := (1 : ℝ)) (b := 2) (by norm_num) hcont
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (f 1) (f 2) := by
    simp [f, plasticCubic_one, plasticCubic_two]
  rcases hsub hzero_mem with ⟨ρ, hρIcc, hρeq⟩
  have hρne1 : ρ ≠ (1 : ℝ) := by
    intro h
    subst h
    simp [f, plasticCubic_one] at hρeq
  have hρne2 : ρ ≠ (2 : ℝ) := by
    intro h
    subst h
    simp [f, plasticCubic_two] at hρeq
  refine ⟨ρ, ?_, ?_⟩
  · exact ⟨lt_of_le_of_ne hρIcc.1 (Ne.symm hρne1), lt_of_le_of_ne hρIcc.2 hρne2⟩
  · simpa [f] using hρeq

/-- `x^3 - x - 1` is strictly increasing on `[1,2]` (indeed on `[1,∞)`). -/
theorem plasticCubic_strictMonoOn_Icc :
    StrictMonoOn plasticCubic (Set.Icc (1 : ℝ) 2) := by
  intro a ha b hb hab
  have hba : 0 < b - a := sub_pos.mpr hab
  have ha1 : (1 : ℝ) ≤ a := ha.1
  have hb1 : (1 : ℝ) ≤ b := hb.1
  have hsq : 0 < (b ^ 2 + b * a + a ^ 2 - 1) := by
    have hsq1 : (1 : ℝ) ≤ a ^ 2 := by
      nlinarith [sq_nonneg a, ha1]
    have hsq2 : (1 : ℝ) ≤ b ^ 2 := by
      nlinarith [sq_nonneg b, hb1]
    have hba1 : (1 : ℝ) ≤ b * a := by
      nlinarith [ha1, hb1]
    nlinarith
  have hfac :
      plasticCubic b - plasticCubic a = (b - a) * (b ^ 2 + b * a + a ^ 2 - 1) := by
    unfold plasticCubic
    ring
  have hpos : 0 < plasticCubic b - plasticCubic a := by
    rw [hfac]
    exact mul_pos hba hsq
  linarith

/-- The root in `[1,2]` is unique. -/
theorem plastic_root_unique_Icc {x y : ℝ}
    (hxI : x ∈ Set.Icc (1 : ℝ) 2) (hyI : y ∈ Set.Icc (1 : ℝ) 2)
    (hx0 : plasticCubic x = 0) (hy0 : plasticCubic y = 0) :
    x = y := by
  by_contra hxy
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · have hmono := plasticCubic_strictMonoOn_Icc hxI hyI hlt
    rw [hx0, hy0] at hmono
    exact lt_irrefl 0 hmono
  · have hmono := plasticCubic_strictMonoOn_Icc hyI hxI hgt
    rw [hy0, hx0] at hmono
    exact lt_irrefl 0 hmono

/-- A canonical choice of the plastic root in `(1,2)`. -/
noncomputable def plasticRoot : ℝ := Classical.choose exists_plastic_root_Ioo

theorem plasticRoot_mem_Ioo : plasticRoot ∈ Set.Ioo (1 : ℝ) 2 :=
  (Classical.choose_spec exists_plastic_root_Ioo).1

theorem plasticRoot_eq_zero : plasticCubic plasticRoot = 0 :=
  (Classical.choose_spec exists_plastic_root_Ioo).2

theorem plasticRoot_mem_Icc : plasticRoot ∈ Set.Icc (1 : ℝ) 2 := by
  exact ⟨le_of_lt plasticRoot_mem_Ioo.1, le_of_lt plasticRoot_mem_Ioo.2⟩

/-- Characterization: any root in `[1,2]` equals `plasticRoot`. -/
theorem eq_plasticRoot_of_mem_Icc_root {x : ℝ}
    (hxI : x ∈ Set.Icc (1 : ℝ) 2) (hx0 : plasticCubic x = 0) :
    x = plasticRoot := by
  exact plastic_root_unique_Icc hxI plasticRoot_mem_Icc hx0 plasticRoot_eq_zero

end Hqiv.Algebra


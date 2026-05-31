import Hqiv.Algebra.CliffordSixImaginaryScaffold
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Order.Extension.Well
import Mathlib.Order.SupIndep

/-!
# Real dimension of abstract `Cl(0,6)` (`CliffordCl06Six`)

Over `ℝ`, `2` is invertible, so `CliffordAlgebra.equivExterior` identifies **any** Clifford
algebra on a finite free module with the exterior algebra on the same module **as a real vector
space**.  For `M = ℝ⁶`, `⋀[ℝ]^k M` has dimension `Nat.choose 6 k`, hence total dimension
`∑_{k=0}^6 \binom{6}{k} = 2^6 = 64`.

This is the algebraic backbone for Furey-style **minimal left ideal** counting: once a faithful
`8`-dimensional real representation is packaged, minimal ideals have real dimension `8`; that
layer is *not* proved here (it needs an explicit simple-algebra certificate, e.g. a chosen
`Mat₈(ℝ)` model), but the ambient `Cl(0,6)` dimension `64` is unconditional in this file.
-/

namespace Hqiv.Algebra

open scoped DirectSum

open DirectSum Submodule Module Finset CompleteLattice

abbrev Cl06Carrier : Type := Fin 6 → ℝ

abbrev ExtCl06 := ExteriorAlgebra ℝ Cl06Carrier

/-- The `Fin 7`-indexed exterior grading pieces `⋀^k ℝ⁶` for `k = 0,…,6`. -/
def extPowGraded (i : Fin 7) : Submodule ℝ ExtCl06 :=
  ⋀[ℝ]^(i.val : ℕ) Cl06Carrier

noncomputable instance extPowGraded_moduleFinite (i : Fin 7) :
    Module.Finite ℝ (extPowGraded i) := by
  let b := Module.Free.chooseBasis ℝ Cl06Carrier
  letI : LinearOrder (Module.Free.ChooseBasisIndex ℝ Cl06Carrier) :=
    IsWellFounded.wellOrderExtension emptyWf.rel
  simpa [extPowGraded, ExteriorAlgebra.exteriorPower] using
    Module.Finite.of_basis (b.exteriorPower (i.val : ℕ))

lemma extPowGraded_eq_exteriorPower (i : Fin 7) :
    extPowGraded i = ExteriorAlgebra.exteriorPower ℝ (i.val : ℕ) Cl06Carrier :=
  rfl

lemma exteriorPower_nat_succ_bot (n : ℕ) (hn : 6 < n) :
    ExteriorAlgebra.exteriorPower ℝ n Cl06Carrier = ⊥ :=
  Submodule.finrank_eq_zero.1 <| by
    have hf : finrank ℝ Cl06Carrier = 6 := by rw [Module.finrank_pi, Fintype.card_fin]
    rw [exteriorPower.finrank_eq (R := ℝ) (M := Cl06Carrier), hf, Nat.choose_eq_zero_of_lt hn]

lemma iSup_extPowGraded_eq_iSup_nat :
    (⨆ i : Fin 7, extPowGraded i) = ⨆ n : ℕ, (⋀[ℝ]^n Cl06Carrier : Submodule ℝ ExtCl06) := by
  refine le_antisymm (iSup_le fun i => ?_) (iSup_le fun n => ?_)
  · exact le_iSup _ (i.val : ℕ)
  · by_cases hn : n ≤ 6
    · let i : Fin 7 := ⟨n, Nat.lt_succ_iff.mpr hn⟩
      exact le_iSup (fun j : Fin 7 => extPowGraded j) i
    · push_neg at hn
      rw [exteriorPower_nat_succ_bot n hn]
      exact bot_le

lemma iSup_nat_exterior_pow_eq_top :
    (⨆ n : ℕ, (⋀[ℝ]^n Cl06Carrier : Submodule ℝ ExtCl06)) = ⊤ := by
  let 𝒜 : ℕ → Submodule ℝ ExtCl06 := fun n => ⋀[ℝ]^n Cl06Carrier
  haveI : DirectSum.Decomposition 𝒜 :=
    inferInstanceAs (DirectSum.Decomposition 𝒜)
  exact IsInternal.submodule_iSup_eq_top (DirectSum.Decomposition.isInternal 𝒜)

lemma iSup_extPowGraded_eq_top : (⨆ i : Fin 7, extPowGraded i) = ⊤ := by
  rw [iSup_extPowGraded_eq_iSup_nat, iSup_nat_exterior_pow_eq_top]

lemma iSupIndep_extPowGraded : iSupIndep extPowGraded := by
  let 𝒜 : ℕ → Submodule ℝ ExtCl06 := fun n => ⋀[ℝ]^n Cl06Carrier
  haveI : DirectSum.Decomposition 𝒜 :=
    inferInstanceAs (DirectSum.Decomposition 𝒜)
  exact iSupIndep.comp (IsInternal.submodule_iSupIndep (DirectSum.Decomposition.isInternal 𝒜))
    Fin.val_injective

lemma isInternal_extPowGraded : IsInternal extPowGraded :=
  (isInternal_submodule_iff_iSupIndep_and_iSup_eq_top extPowGraded).mpr
    ⟨iSupIndep_extPowGraded, iSup_extPowGraded_eq_top⟩

noncomputable def extPowDecomposeLinearEquiv : ExtCl06 ≃ₗ[ℝ] ⨁ i : Fin 7, extPowGraded i :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap extPowGraded) isInternal_extPowGraded).symm

lemma finrank_extPowGraded (i : Fin 7) :
    finrank ℝ (extPowGraded i) = Nat.choose 6 i.val := by
  rw [extPowGraded_eq_exteriorPower, exteriorPower.finrank_eq (R := ℝ) (M := Cl06Carrier),
    Module.finrank_pi, Fintype.card_fin]

noncomputable def extGradingBasis :
    Basis (Σ i : Fin 7, Module.Free.ChooseBasisIndex ℝ (extPowGraded i)) ℝ ExtCl06 :=
  IsInternal.collectedBasis isInternal_extPowGraded fun i =>
    Module.Free.chooseBasis ℝ (extPowGraded i)

lemma finrank_extCl06 : finrank ℝ ExtCl06 = 64 := by
  classical
  rw [Module.finrank_eq_card_basis extGradingBasis, Fintype.card_sigma]
  simp_rw [← Module.finrank_eq_card_chooseBasisIndex ℝ (extPowGraded _), finrank_extPowGraded]
  simp +decide

noncomputable instance invertibleTwoReal : Invertible (2 : ℝ) :=
  invertibleOfNonzero (two_ne_zero : (2 : ℝ) ≠ 0)

noncomputable def cliffordCl06SixLinearEquivExterior :
    CliffordCl06Six ≃ₗ[ℝ] ExtCl06 :=
  haveI := invertibleTwoReal
  CliffordAlgebra.equivExterior quadFormCl06Six

theorem cliffordCl06Six_finrank : finrank ℝ CliffordCl06Six = 64 := by
  haveI := invertibleTwoReal
  rw [LinearEquiv.finrank_eq cliffordCl06SixLinearEquivExterior, finrank_extCl06]

end Hqiv.Algebra

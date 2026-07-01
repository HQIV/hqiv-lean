import HqivSpine.Algebra.SkewChartBridge
import HqivSpine.Algebra.StrongColorSu3LieLaw
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Real `su(3) ⊂ 𝔰𝔬(6)` — Lie-homomorphism closure

Transport `halfGellMannFull_lieBracket_eq_I_smul_f_sum` through one `6 × 6` realification
(same pattern as `StrongColorEmbed.colorGellMannEmbed_lieBracket`). No per-generator matrix
certificate.
-/

namespace HqivSpine.Algebra

noncomputable section

open Complex Matrix Finset
open scoped BigOperators
open StrongColor
open Su3RealSkew

namespace Su3RealSkew

private lemma sum_fin6 (f : Fin 6 → ℝ) : ∑ k, f k = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp [Fin.sum_univ_six]

/-! ### `complexToReal6` Lie homomorphism -/

theorem complexToReal6_add (X Y : Matrix (Fin 3) (Fin 3) ℂ) :
    complexToReal6 (X + Y) = complexToReal6 X + complexToReal6 Y := by
  ext i j
  dsimp only [complexToReal6, block6, fin6to3, Matrix.add_apply, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;> simp [Complex.add_re, Complex.add_im] <;> ring

theorem complexToReal6_zero : complexToReal6 (0 : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
  ext i j
  dsimp only [complexToReal6, block6, fin6to3, Matrix.of_apply, zero_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem complexToReal6_neg (X : Matrix (Fin 3) (Fin 3) ℂ) :
    complexToReal6 (-X) = -complexToReal6 X := by
  ext i j
  dsimp only [complexToReal6, block6, fin6to3, Matrix.neg_apply, Matrix.of_apply, neg_apply]
  fin_cases i <;> fin_cases j <;> simp [Complex.neg_re, Complex.neg_im]

theorem complexToReal6_smul_real (r : ℝ) (X : Matrix (Fin 3) (Fin 3) ℂ) :
    complexToReal6 (r • X) = r • complexToReal6 X := by
  ext i j
  dsimp only [complexToReal6, block6, fin6to3, Matrix.smul_apply, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;> simp [Complex.smul_re, Complex.smul_im, Complex.ofReal_re,
    Complex.ofReal_im]

theorem complexToReal6_ofReal_smul (r : ℝ) (X : Matrix (Fin 3) (Fin 3) ℂ) :
    complexToReal6 ((Complex.ofReal r) • X) = r • complexToReal6 X := by
  ext i j
  dsimp only [complexToReal6, block6, fin6to3, Matrix.smul_apply, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Complex.ofReal_mul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]

theorem complexToReal6_smul_ofReal (r : ℝ) (X : Matrix (Fin 3) (Fin 3) ℂ) :
    complexToReal6 ((r : ℂ) • X) = r • complexToReal6 X := by
  ext i j
  dsimp only [complexToReal6, block6, fin6to3, Matrix.smul_apply, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Complex.ofReal_mul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]

theorem complexToReal6_sub (X Y : Matrix (Fin 3) (Fin 3) ℂ) :
    complexToReal6 (X - Y) = complexToReal6 X - complexToReal6 Y := by
  rw [sub_eq_add_neg, complexToReal6_add, complexToReal6_neg, sub_eq_add_neg]

private lemma re_mul_entry (X Y : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) :
    (∑ x, X i x * Y x j).re =
      (X i 0 * Y 0 j).re + (X i 1 * Y 1 j).re + (X i 2 * Y 2 j).re := by
  rw [Fin.sum_univ_three, Complex.add_re, Complex.add_re]

private lemma im_mul_entry (X Y : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) :
    (∑ x, X i x * Y x j).im =
      (X i 0 * Y 0 j).im + (X i 1 * Y 1 j).im + (X i 2 * Y 2 j).im := by
  rw [Fin.sum_univ_three, Complex.add_im, Complex.add_im]

private lemma complexToReal6_mul_entry (X Y : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 6) :
    complexToReal6 (X * Y) i j = (complexToReal6 X * complexToReal6 Y) i j := by
  fin_cases i <;>
  fin_cases j <;>
  simp only [complexToReal6, block6, fin6to3, Matrix.mul_apply, Matrix.of_apply, sum_fin6,
    Complex.mul_re, Complex.mul_im] <;>
  (try rw [re_mul_entry X Y _ _] <;> simp [Complex.mul_re] <;> ring) <;>
  (try rw [Fin.sum_univ_three, neg_add, neg_add, Complex.add_im, Complex.mul_re, Complex.mul_im] <;>
    ring) <;>
  (try rw [im_mul_entry X Y _ _] <;> simp [Complex.mul_im] <;> ring)

theorem complexToReal6_mul (X Y : Matrix (Fin 3) (Fin 3) ℂ) :
    complexToReal6 (X * Y) = complexToReal6 X * complexToReal6 Y := by
  ext i j
  exact complexToReal6_mul_entry X Y i j

theorem complexToReal6_lieBracket (X Y : Matrix (Fin 3) (Fin 3) ℂ) :
    complexToReal6 (lieBracketMat3 X Y) =
      bracket (complexToReal6 X) (complexToReal6 Y) := by
  simp [lieBracketMat3, bracket, complexToReal6_sub, complexToReal6_mul]

noncomputable def complexToReal6AddHom : Matrix (Fin 3) (Fin 3) ℂ →+ Matrix (Fin 6) (Fin 6) ℝ where
  toFun := complexToReal6
  map_zero' := complexToReal6_zero
  map_add' := complexToReal6_add

theorem complexToReal6_sum (f : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ) :
    complexToReal6 (∑ c, f c) = ∑ c, complexToReal6 (f c) :=
  map_sum complexToReal6AddHom f Finset.univ

private lemma complexToReal6_antiHermitian_entry {X : Matrix (Fin 3) (Fin 3) ℂ}
    (hX : X.conjTranspose = -X) (i j : Fin 6) :
    (complexToReal6 X) j i = -(complexToReal6 X) i j := by
  have hre : (X (fin6to3 j) (fin6to3 i)).re = -(X (fin6to3 i) (fin6to3 j)).re := by
    simpa [Matrix.conjTranspose_apply, Complex.conj_re, Complex.neg_re] using
      congrArg Complex.re (congrFun (congrFun hX (fin6to3 i)) (fin6to3 j))
  have him : (X (fin6to3 j) (fin6to3 i)).im = (X (fin6to3 i) (fin6to3 j)).im := by
    simpa [Matrix.conjTranspose_apply, Complex.conj_im, Complex.neg_im] using
      congrArg Complex.im (congrFun (congrFun hX (fin6to3 i)) (fin6to3 j))
  fin_cases i <;>
  fin_cases j <;>
  simp only [complexToReal6, block6, fin6to3, Matrix.of_apply, neg_apply] at hre him ⊢ <;>
  (try rfl) <;> linarith

theorem complexToReal6_antiHermitian_mem {X : Matrix (Fin 3) (Fin 3) ℂ}
    (hX : X.conjTranspose = -X) : complexToReal6 X ∈ skewMatrices 6 := by
  rw [mem_skewMatrices]
  ext i j
  exact complexToReal6_antiHermitian_entry hX i j

theorem su3RealGen_mem (a : Fin 8) : su3RealGen a ∈ skewMatrices 6 :=
  complexToReal6_antiHermitian_mem (halfGellMannFull_I_antiHermitian a)

theorem su3RealGenPad_mem (n : ℕ) (hn : 6 ≤ n) (a : Fin 8) :
    su3RealGenPad n hn a ∈ skewMatrices n :=
  SkewPad.skewPad_mem hn (su3RealGen_mem a)

theorem su3RealSkewDischarged_mem (a : Fin 8) : su3RealGen a ∈ skewMatrices 6 :=
  su3RealGen_mem a

private theorem I_smul_sum_real (f : Fin 8 → ℝ) (g : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ) :
    Complex.I • ∑ c, (f c : ℂ) • g c = ∑ c, (f c : ℂ) • (Complex.I • g c) := by
  refine Matrix.ext fun i j => ?_
  simp [Matrix.sum_apply]
  rw [Finset.mul_sum (s := Finset.univ) (a := Complex.I)
    (f := fun c => (f c : ℂ) * g c i j)]
  congr 1
  ext c
  ring

private theorem complexToReal6_neg_I_smul_sum (a b : Fin 8) :
    complexToReal6 (-Complex.I • ∑ c : Fin 8, (su3fStructure a b c : ℂ) • halfGellMannFull c) =
      ∑ c : Fin 8, (-su3fStructure a b c : ℝ) • su3RealGen c := by
  rw [neg_smul, complexToReal6_neg, I_smul_sum_real, complexToReal6_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [complexToReal6_smul_ofReal, neg_smul, su3RealGen_eq_complexToReal6]

theorem su3RealGen_lieBracket (a b : Fin 8) :
    bracket (su3RealGen a) (su3RealGen b) =
      ∑ c : Fin 8, (-su3fStructure a b c : ℝ) • su3RealGen c := by
  have hchart := halfGellMannFull_lieBracket_eq_I_smul_f_sum a b
  have hI := lieBracketMat3_I_smul (halfGellMannFull a) (halfGellMannFull b)
  calc
    bracket (su3RealGen a) (su3RealGen b)
        = complexToReal6 (lieBracketMat3 (Complex.I • halfGellMannFull a)
            (Complex.I • halfGellMannFull b)) := by
            rw [su3RealGen_eq_complexToReal6, su3RealGen_eq_complexToReal6, complexToReal6_lieBracket]
    _ = complexToReal6 (-Complex.I • ∑ c, (su3fStructure a b c : ℂ) • halfGellMannFull c) := by
          rw [hI, hchart, neg_smul]
    _ = ∑ c, (-su3fStructure a b c : ℝ) • su3RealGen c := complexToReal6_neg_I_smul_sum a b

theorem su3RealSkewDischarged_holds :
    (∀ a, su3RealGen a ∈ skewMatrices 6) ∧
      (∀ a b,
        bracket (su3RealGen a) (su3RealGen b) =
          ∑ c : Fin 8, (-su3fStructure a b c : ℝ) • su3RealGen c) :=
  ⟨fun a => su3RealGen_mem a, fun a b => su3RealGen_lieBracket a b⟩

end Su3RealSkew

end

end HqivSpine.Algebra

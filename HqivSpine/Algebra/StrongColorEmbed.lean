import HqivSpine.Algebra.StrongColorSu3
import HqivSpine.Algebra.StrongColorSu3LieLaw
import HqivSpine.Physics.Forces
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic

/-!
# `HqivSpine.Algebra.StrongColorEmbed` — lift the `su(3)` chart to `8 × 8` on the carrier

Mirrors legacy `StrongColorCarrierClosure` / electroweak `weakPauliEmbed`, disentangled onto
the clean spine:

* **`colorTripletOctonionSlot`** — colour chart on octonion slots `{2,3,4}` (disjoint from `{0,1}`
  used by the weak doublet in the legacy EW layer);
* **`colorTripletB`** — orthonormal `8 × 3` inclusion matrix (`Bᴴ B = 1₃`);
* **`colorGellMannEmbed`** — conjugate any `3 × 3` operator: `M ↦ B M Bᴴ`;
* **`lieBracketMat8`** — matrix commutator on the carrier;
* **Lie homomorphism** — `[embed A, embed B] = embed [A,B]`;
* **Generic lift** — chart identity ` [A,B] = Complex.I • R` ⇒ carrier identity with `embed R`;
* **Full SU(3) closure on the carrier** — all 64 generator pairs from
  `halfGellMannFull_lieBracket_eq_I_smul_f_sum`.

Honest scope: the **complex Hermitian** Gell–Mann embed on `ℂ^{8×8}`; identifying the image
with a real `𝔰𝔬(8)` subalgebra or Spin(8) triality orbit is separate from this conjugation
homomorphism. Colour slots `{2,3}` lie in the weak mask and `{4}` in the strong mask.
-/

namespace HqivSpine.Algebra.StrongColor

noncomputable section

open Complex Matrix Finset
open scoped BigOperators
open HqivSpine.Physics

/-- Octonion slots carrying the colour triplet (`2,3,4`; disjoint from weak doublet slots `0,1`). -/
def colorTripletOctonionSlot : Fin 3 → Fin 8
  | ⟨0, _⟩ => ⟨2, by decide⟩
  | ⟨1, _⟩ => ⟨3, by decide⟩
  | ⟨2, _⟩ => ⟨4, by decide⟩

/-- Coefficient inclusion `ℂ³ → (Fin 8 → ℂ)` on slots `2,3,4` only. -/
def colorTripletInclCoeff (ψ : Fin 3 → ℂ) : Fin 8 → ℂ
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩ => 0
  | ⟨2, _⟩ => ψ 0
  | ⟨3, _⟩ => ψ 1
  | ⟨4, _⟩ => ψ 2

/-- Orthonormal `8 × 3` inclusion matrix (`B` in `B M Bᴴ`). -/
def colorTripletB : Matrix (Fin 8) (Fin 3) ℂ :=
  Matrix.of fun (r : Fin 8) (c : Fin 3) => if r = colorTripletOctonionSlot c then (1 : ℂ) else 0

theorem colorTripletB_mulVec_eq_inclCoeff (ψ : Fin 3 → ℂ) :
    colorTripletB.mulVec ψ = colorTripletInclCoeff ψ := by
  funext r
  fin_cases r <;> simp [colorTripletB, Matrix.mulVec, dotProduct, colorTripletInclCoeff,
    colorTripletOctonionSlot, Fin.sum_univ_three]

theorem colorTripletB_conjTranspose_mul_self :
    colorTripletB.conjTranspose * colorTripletB = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colorTripletB, Matrix.conjTranspose, Matrix.mul_apply, Matrix.of_apply,
      colorTripletOctonionSlot, mul_ite, mul_one, mul_zero]

/-- Matrix commutator on the `8 × 8` carrier chart. -/
def lieBracketMat8 (A B : Matrix (Fin 8) (Fin 8) ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  A * B - B * A

/-- Conjugate a `3 × 3` colour operator into `8 × 8` on the octonion carrier. -/
def colorGellMannEmbed (M : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  colorTripletB * M * colorTripletB.conjTranspose

private theorem colorGellMannEmbed_map_mul (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    colorTripletB * A * colorTripletB.conjTranspose * colorTripletB * B * colorTripletB.conjTranspose =
      colorTripletB * (A * B) * colorTripletB.conjTranspose := by
  rw [Matrix.mul_assoc (colorTripletB * A), colorTripletB_conjTranspose_mul_self, Matrix.mul_one,
    Matrix.mul_assoc colorTripletB A B]

theorem colorGellMannEmbed_mul (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    colorGellMannEmbed A * colorGellMannEmbed B = colorGellMannEmbed (A * B) := by
  simpa [colorGellMannEmbed, Matrix.mul_assoc] using colorGellMannEmbed_map_mul A B

theorem colorGellMannEmbed_add (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    colorGellMannEmbed (A + B) = colorGellMannEmbed A + colorGellMannEmbed B := by
  unfold colorGellMannEmbed
  simp only [Matrix.mul_add, Matrix.add_mul]

theorem colorGellMannEmbed_smul (c : ℂ) (M : Matrix (Fin 3) (Fin 3) ℂ) :
    colorGellMannEmbed (c • M) = c • colorGellMannEmbed M := by
  unfold colorGellMannEmbed
  simp [Matrix.mul_smul, Matrix.smul_mul]

noncomputable def colorGellMannEmbedAddHom : Matrix (Fin 3) (Fin 3) ℂ →+ Matrix (Fin 8) (Fin 8) ℂ where
  toFun := colorGellMannEmbed
  map_zero' := by unfold colorGellMannEmbed; simp
  map_add' := colorGellMannEmbed_add

theorem colorGellMannEmbed_sum (g : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ) :
    colorGellMannEmbed (∑ c, g c) = ∑ c, colorGellMannEmbed (g c) :=
  map_sum colorGellMannEmbedAddHom g Finset.univ

theorem colorGellMannEmbed_map_sub (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    colorGellMannEmbed (A - B) = colorGellMannEmbed A - colorGellMannEmbed B := by
  simp [colorGellMannEmbed, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

theorem colorGellMannEmbed_lieBracket (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    colorGellMannEmbed (lieBracketMat3 A B) =
      lieBracketMat8 (colorGellMannEmbed A) (colorGellMannEmbed B) := by
  simp [lieBracketMat3, lieBracketMat8, colorGellMannEmbed_map_sub, colorGellMannEmbed_mul]

theorem colorGellMannEmbed_mulVec_intertwine (M : Matrix (Fin 3) (Fin 3) ℂ) (v : Fin 3 → ℂ) :
    colorTripletB.mulVec (M.mulVec v) = (colorGellMannEmbed M).mulVec (colorTripletB.mulVec v) := by
  unfold colorGellMannEmbed
  have hmat :
      colorTripletB * M = colorTripletB * M * colorTripletB.conjTranspose * colorTripletB := by
    simp [Matrix.mul_assoc, colorTripletB_conjTranspose_mul_self]
  calc
    colorTripletB.mulVec (M.mulVec v) = (colorTripletB * M).mulVec v :=
      Matrix.mulVec_mulVec v colorTripletB M
    _ = (colorTripletB * M * colorTripletB.conjTranspose * colorTripletB).mulVec v := by rw [← hmat]
    _ = (colorTripletB * M * colorTripletB.conjTranspose).mulVec (colorTripletB.mulVec v) :=
      (Matrix.mulVec_mulVec v (colorTripletB * M * colorTripletB.conjTranspose) colorTripletB).symm

theorem colorGellMannEmbed_mulVec_inclCoeff (M : Matrix (Fin 3) (Fin 3) ℂ) (ψ : Fin 3 → ℂ) :
    (colorGellMannEmbed M).mulVec (colorTripletInclCoeff ψ) = colorTripletInclCoeff (M.mulVec ψ) := by
  simpa [← colorTripletB_mulVec_eq_inclCoeff ψ, ← colorTripletB_mulVec_eq_inclCoeff (M.mulVec ψ)] using
    (colorGellMannEmbed_mulVec_intertwine M ψ).symm

/-- Lift any chart commutator ` [A,B] = Complex.I • R` to the `8 × 8` carrier. -/
theorem colorGellMannEmbed_chart_lieBracket_smul {A B R : Matrix (Fin 3) (Fin 3) ℂ}
    (h : lieBracketMat3 A B = Complex.I • R) :
    lieBracketMat8 (colorGellMannEmbed A) (colorGellMannEmbed B) = Complex.I • colorGellMannEmbed R := by
  calc
    lieBracketMat8 (colorGellMannEmbed A) (colorGellMannEmbed B)
        = colorGellMannEmbed (lieBracketMat3 A B) :=
          (colorGellMannEmbed_lieBracket A B).symm
    _ = colorGellMannEmbed (Complex.I • R) := by rw [h]
    _ = Complex.I • colorGellMannEmbed R := colorGellMannEmbed_smul Complex.I R

theorem colorGellMannEmbed_halfGellMann_comm_12 :
    lieBracketMat8 (colorGellMannEmbed (halfGellMann 0)) (colorGellMannEmbed (halfGellMann 1)) =
      Complex.I • colorGellMannEmbed (halfGellMann 2) :=
  colorGellMannEmbed_chart_lieBracket_smul halfGellMann_comm_12

theorem colorGellMannEmbed_sum_smul (f : Fin 8 → ℂ) :
    colorGellMannEmbed (∑ c : Fin 8, f c • halfGellMannFull c) =
      ∑ c : Fin 8, f c • colorGellMannEmbed (halfGellMannFull c) := by
  rw [colorGellMannEmbed_sum]
  refine Finset.sum_congr rfl fun c _ => (colorGellMannEmbed_smul (f c) (halfGellMannFull c))

/-- **Full SU(3) Lie law on the `8 × 8` carrier** (all generator pairs). -/
theorem halfGellMannEmbed_carrier_lieBracket_eq_I_smul_f_sum (a b : Fin 8) :
    lieBracketMat8 (colorGellMannEmbed (halfGellMannFull a)) (colorGellMannEmbed (halfGellMannFull b)) =
      Complex.I • ∑ c : Fin 8, (su3fStructure a b c : ℂ) • colorGellMannEmbed (halfGellMannFull c) := by
  have hchart := halfGellMannFull_lieBracket_eq_I_smul_f_sum a b
  calc
    lieBracketMat8 (colorGellMannEmbed (halfGellMannFull a)) (colorGellMannEmbed (halfGellMannFull b))
        = Complex.I • colorGellMannEmbed (∑ c : Fin 8, (su3fStructure a b c : ℂ) • halfGellMannFull c) :=
          colorGellMannEmbed_chart_lieBracket_smul hchart
    _ = Complex.I • ∑ c : Fin 8, (su3fStructure a b c : ℂ) • colorGellMannEmbed (halfGellMannFull c) := by
      rw [colorGellMannEmbed_sum_smul]

/-! ## Force-sector alignment (honest cross-mask placement) -/

theorem colorTripletOctonionSlot_zero_mem_weak :
    colorTripletOctonionSlot ⟨0, by decide⟩ ∈ weakComponents := by
  simp [colorTripletOctonionSlot, weakComponents]

theorem colorTripletOctonionSlot_one_mem_weak :
    colorTripletOctonionSlot ⟨1, by decide⟩ ∈ weakComponents := by
  simp [colorTripletOctonionSlot, weakComponents]

theorem colorTripletOctonionSlot_two_mem_strong :
    colorTripletOctonionSlot ⟨2, by decide⟩ ∈ strongComponents := by
  simp [colorTripletOctonionSlot, strongComponents]

structure strongColorEmbedDischarged : Prop where
  orthonormal_B : colorTripletB.conjTranspose * colorTripletB = 1
  lie_hom :
    ∀ A B, colorGellMannEmbed (lieBracketMat3 A B) =
      lieBracketMat8 (colorGellMannEmbed A) (colorGellMannEmbed B)
  carrier_lie_law :
    ∀ a b : Fin 8,
      lieBracketMat8 (colorGellMannEmbed (halfGellMannFull a))
          (colorGellMannEmbed (halfGellMannFull b)) =
        Complex.I • ∑ c : Fin 8, (su3fStructure a b c : ℂ) • colorGellMannEmbed (halfGellMannFull c)
  triplet_intertwine :
    ∀ (M : Matrix (Fin 3) (Fin 3) ℂ) (ψ : Fin 3 → ℂ),
      (colorGellMannEmbed M).mulVec (colorTripletInclCoeff ψ) = colorTripletInclCoeff (M.mulVec ψ)

theorem strongColorEmbedDischarged_holds : strongColorEmbedDischarged where
  orthonormal_B := colorTripletB_conjTranspose_mul_self
  lie_hom := colorGellMannEmbed_lieBracket
  carrier_lie_law := halfGellMannEmbed_carrier_lieBracket_eq_I_smul_f_sum
  triplet_intertwine := colorGellMannEmbed_mulVec_inclCoeff

end

end HqivSpine.Algebra.StrongColor

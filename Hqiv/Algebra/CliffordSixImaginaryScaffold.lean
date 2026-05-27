import Hqiv.Algebra.OctonionBasics
import Hqiv.Algebra.OctonionLeftMulSquare
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.QuadraticForm.Basic

open QuadraticMap

/-!
# `Cl(0,6)` scaffold on six imaginary octonion directions (`e₁`–`e₆`)

This file fixes the **signature and carrier** for the higher Clifford layer from
`AGENTS/FUREY_PROOF_ROADMAP.md`:

* **Quadratic space:** `Fin 6 → ℝ` with **negative-definite** diagonal form
  `Q(v) = -∑_k v_k²`, i.e. the standard split for **\(\mathrm{Cl}(0,6)\)** on an
  orthonormal basis.
* **Octonion alignment:** the standard basis `δⱼ : Fin 6 → ℝ` is identified with
  the octonion basis vectors `e_{j+1}` for `j = 0,…,5` (`e₁..e₆`), i.e. the six
  imaginary directions **excluding** the colour-preferred `e₇` axis used in HQIV
  colour narratives.
* **Clifford algebra:** `CliffordCl06Six = CliffordAlgebra quadFormCl06Six`.
* **Abstract ideal layer:** `Hqiv.Algebra.CliffordCl06SixDimension` (`finrank = 64`),
  `Hqiv.Algebra.CliffordCl06SixIdeal` (principal left ideals / idempotents), and
  `Hqiv.Algebra.CliffordCl06SixSpinorBridge` (representation-conditional map into
  `OctonionSpinorCarrier`) — orthogonal to the naive matrix lift below.
* **Standard spinor `ρ`:** `Hqiv.Algebra.CliffordCl06SixStandardSpinorRho` builds
  `ρ : CliffordCl06Six →ₐ[ℝ] End(OctonionSpinorCarrier)` via explicit `8×8` Kronecker `γ` matrices
  satisfying the `quadFormCl06Six` lift (not the obstructed octonion left-mult matrices).

## Proved inputs toward a matrix lift

`Hqiv.Algebra.OctonionLeftMulSquare` proves each **individual** left-multiplication
matrix `L(e_k)` squares to `-1` for `k = 1,…,7`.

## Explicit obstruction for the *naive* linear lift

A **`CliffordAlgebra.lift`** to `Matrix (Fin 8) (Fin 8) ℝ` requires, for the
linear map `f : (Fin 6 → ℝ) →ₗ[ℝ] Mat₈(ℝ)` extending `δⱼ ↦ L(e_{j+1})`, the
identity `(f v) * (f v) = algebraMap ℝ _ (Q v)` for **every** `v`, not just
basis vectors.  For mixed `v = δⱼ + δₖ`, this expands using **cross-terms** and
forces the same anticommutation relations as in the abstract Clifford algebra.
Those cross-terms **fail** for naive octonion **left** matrices: see
`Hqiv.Algebra.OctonionLeftMulCliffordObstruction` (e.g. entry `(3,3)` of
`L(e₁)L(e₂)+L(e₂)L(e₁)` is `2`, and `(L(e₁)+L(e₂))²` disagrees with `-2` on the
diagonal).  A matrix `CliffordAlgebra.lift` along `δⱼ ↦ L(e_{j+1})` is therefore
ruled out; minimal-ideal / spinor packaging must use a **different** linear model.
-/

namespace Hqiv.Algebra

/-- Orthonormal imaginary indices `e₁,…,e₆` as `Fin 8` positions (skip `e₀` and `e₇`). -/
def imaginarySixIndex (j : Fin 6) : Fin 8 :=
  ⟨j.val + 1, by omega⟩

@[simp]
theorem imaginarySixIndex_val (j : Fin 6) : (imaginarySixIndex j).val = j.val + 1 :=
  rfl

/-- Negative-definite diagonal form on `ℝ⁶` — `\mathrm{Cl}(0,6)` on an orthonormal basis. -/
noncomputable def quadFormCl06Six : QuadraticForm ℝ (Fin 6 → ℝ) :=
  weightedSumSquares ℝ (fun _ : Fin 6 => (-1 : ℝ))

/-- The Clifford algebra \(\mathrm{Cl}(0,6)\) on the six imaginary coordinates. -/
abbrev CliffordCl06Six :=
  CliffordAlgebra quadFormCl06Six

/-- The six octonion basis directions used above, as `OctonionVec`. -/
noncomputable def imaginarySixOctonionBasis (j : Fin 6) : OctonionVec :=
  octonionBasis (imaginarySixIndex j)

/-- Matrix `L(e_{j+1})` for `j : Fin 6`, aligned with `imaginarySixIndex`. -/
noncomputable def imaginarySixLeftMulMatrix (j : Fin 6) : Matrix (Fin 8) (Fin 8) ℝ :=
  leftMulMatrix (imaginarySixIndex j)

theorem imaginarySixLeftMulMatrix_eq_octonionLeftMul_N (j : Fin 6) :
    imaginarySixLeftMulMatrix j = Hqiv.octonionLeftMul_N ⟨j.val, by omega⟩ := by
  unfold imaginarySixLeftMulMatrix leftMulMatrix
  fin_cases j <;> rfl

theorem imaginarySix_leftMul_matrix_mul_self (j : Fin 6) :
    imaginarySixLeftMulMatrix j * imaginarySixLeftMulMatrix j =
      (-1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  rw [imaginarySixLeftMulMatrix_eq_octonionLeftMul_N]
  exact Hqiv.octonionLeftMul_N_mul_self ⟨j.val, by omega⟩

/-- Standard-basis vector `δⱼ ∈ ℝ⁶` (Kronecker delta, avoids `Pi.single` elaboration issues). -/
def cl06SixBasisVec (j : Fin 6) : Fin 6 → ℝ :=
  fun i => if i = j then (1 : ℝ) else 0

theorem quadFormCl06Six_basisVec (j : Fin 6) : quadFormCl06Six (cl06SixBasisVec j) = -1 := by
  classical
  fin_cases j <;> simp [quadFormCl06Six, weightedSumSquares_apply, cl06SixBasisVec]

/-- Clifford generator `ι(δⱼ)` in `CliffordCl06Six`. -/
noncomputable def cliffordCl06Six_iota (j : Fin 6) : CliffordCl06Six :=
  CliffordAlgebra.ι quadFormCl06Six (cl06SixBasisVec j)

theorem cliffordCl06Six_iota_sq (j : Fin 6) :
    cliffordCl06Six_iota j * cliffordCl06Six_iota j =
      algebraMap ℝ CliffordCl06Six (quadFormCl06Six (cl06SixBasisVec j)) :=
  CliffordAlgebra.ι_sq_scalar _ _

theorem cliffordCl06Six_iota_sq_eval (j : Fin 6) :
    cliffordCl06Six_iota j * cliffordCl06Six_iota j = algebraMap ℝ CliffordCl06Six (-1) := by
  rw [cliffordCl06Six_iota_sq, quadFormCl06Six_basisVec j]

end Hqiv.Algebra

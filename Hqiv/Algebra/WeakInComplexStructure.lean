import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Star.BigOperators
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Logic.Equiv.Basic
import Hqiv.Algebra.WeakFromLeftMulOctonion

/-!
# Weak isospin on the complexified / projected carrier

This module separates two layers:

1. **Abstract left-handed doublet (`Fin 2 → ℂ`)** with standard ladder / diagonal Pauli matrices.
   Commutators close **by explicit 2×2 calculation** — this is the effective SM complex picture.

2. **Octonion carrier complexified** as the Mathlib Hermitian space `EuclideanSpace ℂ (Fin 8) = PiLp 2 (Fin 8 → ℂ)`
   (`WeakComplexOctonionCarrier`), with `weakJComplex := weakComplexStructureJ.map Complex.ofRealHom` acting on
   coefficient vectors via `ofLp` / `toLp 2`. The `+i` eigenspace of `weakJComplex` is a genuine `ℂ`-submodule
   (`weakJEigenspaceI`). The slotwise pairing `weakCarrierCinner` agrees with Mathlib's `inner` (`weakCarrierCinner_eq_inner`).

**Compatibility with frozen real data.** `weakJComplex_mulVec_complexOfReal` packages the fact that
complexifying vectors commutes with applying the **same** real matrix `weakComplexStructureJ`.

**Important dimension fact.** Over `ℂ`, the `+i` eigenspace `weakJEigenspaceI` is **one-dimensional**
(the same holds for the `-i` eigenspace). Therefore there is **no** `OrthonormalBasis (Fin 2) ℂ weakJEigenspaceI`:
a length-2 orthonormal family cannot live in a `1`-dimensional submodule. The SM weak doublet is
matched to the **two-dimensional** plane `weakJComplexDoublet := span{u⁺, u⁻}` built from the
explicit `±i` **pattern** vectors `weakDoubletVecPlusI`, `weakDoubletVecMinusI` (orthonormal under
the Mathlib Hermitian inner product, aliased as `weakCarrierCinner`). The linear equivalence
`weakDoubletEquiv` packages `Fin 2 → ℂ ≃ₗ[ℂ] weakJComplexDoublet`, and `weakPauliEmbed` conjugates
`2 × 2` Pauli matrices into `8 × 8` matrices on the carrier, with `weakPauliEmbed_mulVec_intertwine`
and `weakDoubletEquiv_Pauli_mulVec` recording the intertwining along `weakDoubletB`.

**Coordinate note (octonion index `7`).** In `weakDoubletUnscaledPlusI` / `weakDoubletUnscaledMinusI`,
the last coefficient (`Fin 8` index `7`) is `∓ i`, i.e. the “`e₇` slot” carries the neutral imaginary
phase; the `+i` / `-i` pattern is fixed up to the overall normalization `weakDoubletNormScale`.

**Roadmap.** (1) Higgs VEV direction `higgsVevOfReal` and the `Fin 2` coefficient chart (`higgsDoubletFin2Coeff`,
`weakDoubletEquiv_symm_higgsVevOfReal`) feed the Pauli Gram / covariant scaffolding in
`Hqiv.Physics.WeakDoubletCarrierGaugeQuadratic`. (2) Fermion doublets per generation via triality cycling,
reusing the same Gram normalization for Yukawa bookkeeping.

For **matrix-level** `𝔰𝔲(2)_L` inside the octonion Lie closure, keep using `Hqiv.Algebra.SMEmbedding`.

See also `Hqiv.Algebra.WeakFromLeftMulOctonion` for the real-matrix sandbox definitions.
-/

open Matrix Complex Finset
open scoped BigOperators InnerProductSpace
open EuclideanSpace PiLp WithLp
namespace Hqiv.Algebra

/-! ## Pauli ladder on the abstract weak doublet (`Fin 2 → ℂ`) -/

/-- Ladder operator `σ⁺` on the standard weak doublet. -/
def weakPauliPlus : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), 1; 0, 0]

/-- Ladder operator `σ⁻`. -/
def weakPauliMinus : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), 0; 1, 0]

/-- Third Pauli generator `σ₃ = diag(1,-1)` (Hermitian). -/
def weakPauliZ3 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 : ℂ), 0; 0, (-1 : ℂ)]

/-- Matrix commutator on `2 × 2` complex matrices. -/
noncomputable def lieBracketMat₂ (A B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  A * B - B * A

theorem weakPauliZ3_isHermitian : weakPauliZ3.IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [weakPauliZ3, Matrix.of_apply]

theorem weakPauliPlus_conjTranspose : weakPauliPlusᴴ = weakPauliMinus := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [weakPauliPlus, weakPauliMinus, Matrix.conjTranspose, Matrix.map_apply]

theorem weakPauliMinus_conjTranspose : weakPauliMinusᴴ = weakPauliPlus := by
  rw [← weakPauliPlus_conjTranspose, conjTranspose_conjTranspose]

/-- `[σ⁺, σ⁻] = σ₃` on the abstract doublet. -/
theorem weakPauli_ladder_comm : lieBracketMat₂ weakPauliPlus weakPauliMinus = weakPauliZ3 := by
  unfold lieBracketMat₂ weakPauliPlus weakPauliMinus weakPauliZ3
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.of_apply]; try ring)

/-- `[σ₃, σ⁺] = 2 σ⁺`. -/
theorem weakPauli_Z_plus_comm : lieBracketMat₂ weakPauliZ3 weakPauliPlus = 2 • weakPauliPlus := by
  unfold lieBracketMat₂ weakPauliZ3 weakPauliPlus
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.of_apply]; try ring)

/-- `[σ₃, σ⁻] = -2 σ⁻`. -/
theorem weakPauli_Z_minus_comm : lieBracketMat₂ weakPauliZ3 weakPauliMinus = (-2 : ℂ) • weakPauliMinus := by
  unfold lieBracketMat₂ weakPauliZ3 weakPauliMinus
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.of_apply]; try ring)

/-! ## Complexified octonion carrier and the `+i` eigenspace of `J` -/

/-- Octonion carrier after complexifying coefficients: Mathlib `L²` model on `Fin 8` (`PiLp 2`). -/
abbrev WeakComplexOctonionCarrier :=
  EuclideanSpace ℂ (Fin 8)

/-- `J` as a `ℂ`-linear operator on `ℂ⁸` (coefficient-wise extension of the real matrix). -/
noncomputable def weakJComplex : Matrix (Fin 8) (Fin 8) ℂ :=
  weakComplexStructureJ.map Complex.ofRealHom

/-- Embed a real octonion vector into the complexified carrier. -/
noncomputable def complexOfRealOctonion (v : Fin 8 → ℝ) : WeakComplexOctonionCarrier :=
  toLp 2 fun i => (v i : ℂ)

theorem weakJComplex_mulVec_complexOfReal (v : Fin 8 → ℝ) :
    toLp 2 (weakJComplex.mulVec (ofLp (complexOfRealOctonion v))) =
      complexOfRealOctonion (weakComplexStructureJ.mulVec v) := by
  have hof : ofLp (complexOfRealOctonion v) = (fun i : Fin 8 => (v i : ℂ)) := by
    simp [complexOfRealOctonion, ofLp_toLp]
  rw [hof]
  dsimp [complexOfRealOctonion]
  refine congrArg (toLp 2) ?_
  funext i
  simpa [weakJComplex, Function.comp] using
    (RingHom.map_mulVec Complex.ofRealHom weakComplexStructureJ v i).symm

/-- Predicate for the `+i` eigenspace of `J` on the carrier (coefficient action via `ofLp`). -/
def memWeakJEigenspaceI (v : WeakComplexOctonionCarrier) : Prop :=
  toLp 2 (weakJComplex.mulVec (ofLp v)) = Complex.I • v

/-- The `+i` eigenspace of `weakJComplex` is a `ℂ`-submodule of the carrier. -/
def weakJEigenspaceI : Submodule ℂ WeakComplexOctonionCarrier where
  carrier := {v | memWeakJEigenspaceI v}
  zero_mem' := by
    simp [memWeakJEigenspaceI, Matrix.mulVec_zero, map_zero]
  add_mem' := by
    intro v w hv hw
    simp only [Set.mem_setOf_eq, memWeakJEigenspaceI] at hv hw ⊢
    simp [ofLp_add, Matrix.mulVec_add, toLp_add, hv, hw, smul_add]
  smul_mem' := by
    intro c v hv
    simp only [Set.mem_setOf_eq, memWeakJEigenspaceI] at hv ⊢
    simp [ofLp_smul, Matrix.mulVec_smul, toLp_smul, hv, smul_smul, mul_comm]

/-! ## `±i` eigenvectors and the weak-doublet plane in `ℂ⁸` -/

/-- Predicate for the `-i` eigenspace. -/
def memWeakJEigenspaceNegI (v : WeakComplexOctonionCarrier) : Prop :=
  toLp 2 (weakJComplex.mulVec (ofLp v)) = (-Complex.I) • v

/-- The `-i` eigenspace of `weakJComplex`. -/
def weakJEigenspaceNegI : Submodule ℂ WeakComplexOctonionCarrier where
  carrier := {v | memWeakJEigenspaceNegI v}
  zero_mem' := by
    simp [memWeakJEigenspaceNegI, Matrix.mulVec_zero, map_zero]
  add_mem' := by
    intro v w hv hw
    simp only [Set.mem_setOf_eq, memWeakJEigenspaceNegI] at hv hw ⊢
    simp [ofLp_add, Matrix.mulVec_add, toLp_add, hv, hw, smul_add]
  smul_mem' := by
    intro c v hv
    simp only [Set.mem_setOf_eq, memWeakJEigenspaceNegI] at hv ⊢
    simp [ofLp_smul, Matrix.mulVec_smul, toLp_smul, hv, smul_smul, mul_comm]

/-- Pattern matching the numerically certified `+i` eigenvector of `weakJComplex` on the HQIV tables
(same coordinates as the closed-form complex vector used in the electroweak narrative). -/
noncomputable def weakDoubletUnscaledPlusI : WeakComplexOctonionCarrier :=
  toLp 2 ![(1 : ℂ), -Complex.I, 1, Complex.I, 1, -Complex.I, (-1 : ℂ), -Complex.I]

/-- Pattern matching the numerically certified `-i` eigenvector (orthogonal to `weakDoubletUnscaledPlusI`). -/
noncomputable def weakDoubletUnscaledMinusI : WeakComplexOctonionCarrier :=
  toLp 2 ![(1 : ℂ), Complex.I, 1, -Complex.I, 1, Complex.I, (-1 : ℂ), Complex.I]

/-- Normalization `1 / √8` so the explicit `±i` eigenvectors become **orthonormal**. -/
noncomputable def weakDoubletNormScale : ℂ :=
  (Complex.ofReal (Real.sqrt (8 : ℝ)))⁻¹

theorem weakDoubletNormScale_mul_conj :
    star weakDoubletNormScale * weakDoubletNormScale = (8 : ℂ)⁻¹ := by
  let s : ℂ := Complex.ofReal (Real.sqrt (8 : ℝ))
  have h8 : (0 : ℝ) ≤ (8 : ℝ) := by norm_num
  have hs0 : (0 : ℝ) < Real.sqrt (8 : ℝ) := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (8 : ℝ))
  have hne : s ≠ 0 := by
    intro h
    have h0 : Real.sqrt (8 : ℝ) = 0 := Complex.ofReal_eq_zero.mp (by simp [s] at h ⊢)
    rw [h0] at hs0
    exact lt_irrefl _ hs0
  have hstar : star s = s := by
    simp [s, Complex.conj_ofReal]
  have hsq : s * s = (8 : ℂ) := by
    simp [s, ← Complex.ofReal_mul, Real.mul_self_sqrt h8]
  have hinv : weakDoubletNormScale = s⁻¹ := rfl
  rw [hinv, star_def, Complex.conj_inv]
  have hc : (starRingEnd ℂ) s = s := by simpa [star_def] using hstar
  rw [hc]
  calc
    s⁻¹ * s⁻¹ = (s * s)⁻¹ := (mul_inv_rev s s).symm
    _ = (8 : ℂ)⁻¹ := by rw [hsq]

/-- Unit-norm `+i` eigenvector in `ℂ⁸`. -/
noncomputable def weakDoubletVecPlusI : WeakComplexOctonionCarrier :=
  weakDoubletNormScale • weakDoubletUnscaledPlusI

/-- Unit-norm `-i` eigenvector in `ℂ⁸`. -/
noncomputable def weakDoubletVecMinusI : WeakComplexOctonionCarrier :=
  weakDoubletNormScale • weakDoubletUnscaledMinusI

/-- Hermitian pairing on the carrier (same convention as the standard `inner` on `PiLp 2`). -/
noncomputable def weakCarrierCinner (u v : WeakComplexOctonionCarrier) : ℂ :=
  ∑ i : Fin 8, star (u i) * v i

theorem weakCarrierCinner_smul_left (a : ℂ) (u v : WeakComplexOctonionCarrier) :
    weakCarrierCinner (a • u) v = star a * weakCarrierCinner u v := by
  simp [weakCarrierCinner, Pi.smul_apply, StarMul.star_mul, Finset.mul_sum, mul_left_comm, mul_comm]

theorem weakCarrierCinner_smul_right (a : ℂ) (u v : WeakComplexOctonionCarrier) :
    weakCarrierCinner u (a • v) = a * weakCarrierCinner u v := by
  simp [weakCarrierCinner, Pi.smul_apply, Finset.mul_sum, mul_assoc, mul_comm]

theorem weakCarrierCinner_conj_symm (u v : WeakComplexOctonionCarrier) :
    star (weakCarrierCinner u v) = weakCarrierCinner v u := by
  simp [weakCarrierCinner, star_sum, StarMul.star_mul, mul_comm]

/-- Agreement with Mathlib's Hermitian inner product on `EuclideanSpace ℂ (Fin 8)`. -/
theorem weakCarrierCinner_eq_inner (u v : WeakComplexOctonionCarrier) :
    weakCarrierCinner u v = inner ℂ u v := by
  simp [weakCarrierCinner, PiLp.inner_apply, RCLike.inner_apply', mul_comm]

/-- For bare `Fin 8 → ℂ` coefficients, `weakCarrierCinner` matches `inner` after `toLp 2`. -/
theorem weakCarrierCinner_eq_inner_toLp (u v : Fin 8 → ℂ) :
    weakCarrierCinner (toLp 2 u) (toLp 2 v) = inner ℂ (toLp 2 u) (toLp 2 v) := by
  simpa [weakCarrierCinner] using (weakCarrierCinner_eq_inner (toLp 2 u) (toLp 2 v))

theorem weakDoublet_inner_plus_self : weakCarrierCinner weakDoubletVecPlusI weakDoubletVecPlusI = 1 := by
  have hun :
      weakCarrierCinner weakDoubletUnscaledPlusI weakDoubletUnscaledPlusI = (8 : ℂ) := by
    simp [weakCarrierCinner, weakDoubletUnscaledPlusI, PiLp.toLp_apply, Finset.sum_fin_eq_sum_range,
      Finset.sum_range_succ, conj_I, mul_one, mul_neg, neg_mul]
    norm_num
  have hscale := weakDoubletNormScale_mul_conj
  calc
    weakCarrierCinner weakDoubletVecPlusI weakDoubletVecPlusI
        = star weakDoubletNormScale * weakDoubletNormScale * (8 : ℂ) := by
      simp [weakDoubletVecPlusI, weakCarrierCinner_smul_left, weakCarrierCinner_smul_right, hun,
        mul_left_comm, mul_comm]
    _ = (8 : ℂ)⁻¹ * (8 : ℂ) := by rw [hscale]
    _ = 1 := by field_simp

/-- The normalized `+i` pattern vector has unit carrier norm (used for Higgs VEV bookkeeping). -/
theorem weakDoubletVecPlusI_norm : ‖weakDoubletVecPlusI‖ = 1 := by
  have hi : inner ℂ weakDoubletVecPlusI weakDoubletVecPlusI = 1 := by
    rw [← weakCarrierCinner_eq_inner]
    exact weakDoublet_inner_plus_self
  have hn : ‖weakDoubletVecPlusI‖ ^ 2 = 1 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ) weakDoubletVecPlusI, hi]
    simp
  nlinarith [hn, norm_nonneg weakDoubletVecPlusI]

theorem weakDoublet_inner_minus_self : weakCarrierCinner weakDoubletVecMinusI weakDoubletVecMinusI = 1 := by
  have hun :
      weakCarrierCinner weakDoubletUnscaledMinusI weakDoubletUnscaledMinusI = (8 : ℂ) := by
    simp [weakCarrierCinner, weakDoubletUnscaledMinusI, PiLp.toLp_apply, Finset.sum_fin_eq_sum_range,
      Finset.sum_range_succ, conj_I, mul_one, mul_neg, neg_mul]
    norm_num
  have hscale := weakDoubletNormScale_mul_conj
  calc
    weakCarrierCinner weakDoubletVecMinusI weakDoubletVecMinusI
        = star weakDoubletNormScale * weakDoubletNormScale * (8 : ℂ) := by
      simp [weakDoubletVecMinusI, weakCarrierCinner_smul_left, weakCarrierCinner_smul_right, hun,
        mul_left_comm, mul_comm]
    _ = (8 : ℂ)⁻¹ * (8 : ℂ) := by rw [hscale]
    _ = 1 := by field_simp

theorem weakDoubletVecPlusI_orth_weakDoubletVecMinusI :
    weakCarrierCinner weakDoubletVecPlusI weakDoubletVecMinusI = 0 := by
  have hun : weakCarrierCinner weakDoubletUnscaledPlusI weakDoubletUnscaledMinusI = 0 := by
    simp [weakCarrierCinner, weakDoubletUnscaledPlusI, weakDoubletUnscaledMinusI, PiLp.toLp_apply,
      Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, conj_I, mul_one, mul_neg, neg_mul]
  simp [weakDoubletVecPlusI, weakDoubletVecMinusI, weakCarrierCinner_smul_left,
    weakCarrierCinner_smul_right, hun, mul_comm]

theorem weakDoubletVecMinusI_orth_weakDoubletVecPlusI :
    weakCarrierCinner weakDoubletVecMinusI weakDoubletVecPlusI = 0 := by
  calc
    weakCarrierCinner weakDoubletVecMinusI weakDoubletVecPlusI
        = star (weakCarrierCinner weakDoubletVecPlusI weakDoubletVecMinusI) :=
      (weakCarrierCinner_conj_symm weakDoubletVecPlusI weakDoubletVecMinusI).symm
    _ = star (0 : ℂ) := by rw [weakDoubletVecPlusI_orth_weakDoubletVecMinusI]
    _ = 0 := by simp

/-- The **weak-doublet plane**: complex span of the orthonormal `±i` eigenvectors. -/
noncomputable def weakJComplexDoublet : Submodule ℂ WeakComplexOctonionCarrier :=
  Submodule.span ℂ ({weakDoubletVecPlusI, weakDoubletVecMinusI} : Set WeakComplexOctonionCarrier)

theorem weakDoubletVecPlus_mem_doublet : weakDoubletVecPlusI ∈ weakJComplexDoublet :=
  Submodule.subset_span (Set.mem_insert _ _)

theorem weakDoubletVecMinus_mem_doublet : weakDoubletVecMinusI ∈ weakJComplexDoublet :=
  Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-! ### Orthonormal `Fin 2` family spanning the weak-doublet plane

The carrier is already `EuclideanSpace ℂ (Fin 8)`, so `weakDoubletEuclI` is just the explicit orthonormal
pair inside that space, and `weakJComplexDoubletEucl` is provably equal to `weakJComplexDoublet`
(`weakJComplexDoubletEucl_eq_weakJComplexDoublet`).
`weakDoubletOrthonormalBasisEucl` is `OrthonormalBasis.span` reindexed to `Fin 2`.
-/

/-- Orthonormal `±i` directions as a `Fin 2`-indexed family in `EuclideanSpace ℂ (Fin 8)`. -/
noncomputable def weakDoubletEuclI : Fin 2 → EuclideanSpace ℂ (Fin 8) :=
  ![weakDoubletVecPlusI, weakDoubletVecMinusI]

lemma weakDoubletEuclI_zero : weakDoubletEuclI 0 = weakDoubletVecPlusI := by
  simp [weakDoubletEuclI, Matrix.cons_val_zero]

lemma weakDoubletEuclI_one : weakDoubletEuclI 1 = weakDoubletVecMinusI := by
  simp [weakDoubletEuclI, Matrix.cons_val_one]

/-- The weak-doublet plane in the standard Hermitian `L²` model of the carrier. -/
noncomputable def weakJComplexDoubletEucl : Submodule ℂ (EuclideanSpace ℂ (Fin 8)) :=
  Submodule.span ℂ (Finset.univ.image weakDoubletEuclI : Set (EuclideanSpace ℂ (Fin 8)))

theorem mem_weakDoubletEuclI (i : Fin 2) : weakDoubletEuclI i ∈ weakJComplexDoubletEucl := by
  refine Submodule.subset_span ?_
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem weakDoubletEuclI_image_univ :
    (Finset.univ.image weakDoubletEuclI : Set (EuclideanSpace ℂ (Fin 8))) =
      ({weakDoubletVecPlusI, weakDoubletVecMinusI} : Set (EuclideanSpace ℂ (Fin 8))) := by
  ext x
  simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, heq⟩
    rw [← heq]
    fin_cases i <;> simp [weakDoubletEuclI, Matrix.cons_val_zero, Matrix.cons_val_one]
  · rintro (h | h)
    · exact ⟨0, weakDoubletEuclI_zero.trans h.symm⟩
    · exact ⟨1, weakDoubletEuclI_one.trans h.symm⟩

/-- The explicit `Fin 2` family `weakDoubletEuclI` is orthonormal in `EuclideanSpace ℂ (Fin 8)`. -/
theorem weakDoubletEuclI_orthonormal : Orthonormal ℂ weakDoubletEuclI := by
  classical
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i
    · change ‖weakDoubletVecPlusI‖ = 1
      have hi : inner ℂ weakDoubletVecPlusI weakDoubletVecPlusI = 1 := by
        rw [← weakCarrierCinner_eq_inner]
        exact weakDoublet_inner_plus_self
      have hn : ‖weakDoubletVecPlusI‖ ^ 2 = 1 := by
        rw [norm_sq_eq_re_inner (𝕜 := ℂ) weakDoubletVecPlusI, hi]
        simp
      nlinarith [hn, norm_nonneg weakDoubletVecPlusI]
    · change ‖weakDoubletVecMinusI‖ = 1
      have hi : inner ℂ weakDoubletVecMinusI weakDoubletVecMinusI = 1 := by
        rw [← weakCarrierCinner_eq_inner]
        exact weakDoublet_inner_minus_self
      have hn : ‖weakDoubletVecMinusI‖ ^ 2 = 1 := by
        rw [norm_sq_eq_re_inner (𝕜 := ℂ) weakDoubletVecMinusI, hi]
        simp
      nlinarith [hn, norm_nonneg weakDoubletVecMinusI]
  · rintro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · rw [← weakCarrierCinner_eq_inner]
      simpa [weakDoubletEuclI, Matrix.cons_val_zero, Matrix.cons_val_one] using
        weakDoubletVecPlusI_orth_weakDoubletVecMinusI
    · rw [← weakCarrierCinner_eq_inner]
      simpa [weakDoubletEuclI, Matrix.cons_val_zero, Matrix.cons_val_one] using
        weakDoubletVecMinusI_orth_weakDoubletVecPlusI
    · exact (hij rfl).elim

/-- Orthonormal basis of the Euclidean doublet plane `weakJComplexDoubletEucl`. -/
noncomputable def weakDoubletOrthonormalBasisEucl : OrthonormalBasis (Fin 2) ℂ weakJComplexDoubletEucl :=
  (OrthonormalBasis.span weakDoubletEuclI_orthonormal (Finset.univ : Finset (Fin 2))).reindex
    (Equiv.subtypeUnivEquiv (fun _ : Fin 2 => Finset.mem_univ _))

theorem weakJComplexDoublet_eq_span_insert :
    weakJComplexDoubletEucl =
      Submodule.span ℂ ({weakDoubletVecPlusI, weakDoubletVecMinusI} :
        Set (EuclideanSpace ℂ (Fin 8))) := by
  dsimp [weakJComplexDoubletEucl]
  rw [weakDoubletEuclI_image_univ]

theorem weakJComplexDoubletEucl_eq_weakJComplexDoublet :
    weakJComplexDoubletEucl = weakJComplexDoublet := by
  rw [weakJComplexDoublet_eq_span_insert, weakJComplexDoublet]

/-- The same orthonormal pair as `weakDoubletEuclI`, but typed inside `weakJComplexDoublet`. -/
noncomputable def weakDoubletCarrierI : Fin 2 → weakJComplexDoublet
  | 0 => ⟨weakDoubletVecPlusI, weakDoubletVecPlus_mem_doublet⟩
  | 1 => ⟨weakDoubletVecMinusI, weakDoubletVecMinus_mem_doublet⟩

theorem weakDoubletCarrierI_orthonormal : Orthonormal ℂ weakDoubletCarrierI := by
  classical
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i
    · change ‖(⟨weakDoubletVecPlusI, weakDoubletVecPlus_mem_doublet⟩ : weakJComplexDoublet)‖ = 1
      rw [Submodule.coe_norm]
      have hi : inner ℂ weakDoubletVecPlusI weakDoubletVecPlusI = 1 := by
        rw [← weakCarrierCinner_eq_inner]
        exact weakDoublet_inner_plus_self
      have hn : ‖weakDoubletVecPlusI‖ ^ 2 = 1 := by
        rw [norm_sq_eq_re_inner (𝕜 := ℂ) weakDoubletVecPlusI, hi]
        simp
      calc
        ‖weakDoubletVecPlusI‖ = Real.sqrt (‖weakDoubletVecPlusI‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg weakDoubletVecPlusI)).symm
        _ = Real.sqrt 1 := by rw [hn]
        _ = 1 := Real.sqrt_one
    · change ‖(⟨weakDoubletVecMinusI, weakDoubletVecMinus_mem_doublet⟩ : weakJComplexDoublet)‖ = 1
      rw [Submodule.coe_norm]
      have hi : inner ℂ weakDoubletVecMinusI weakDoubletVecMinusI = 1 := by
        rw [← weakCarrierCinner_eq_inner]
        exact weakDoublet_inner_minus_self
      have hn : ‖weakDoubletVecMinusI‖ ^ 2 = 1 := by
        rw [norm_sq_eq_re_inner (𝕜 := ℂ) weakDoubletVecMinusI, hi]
        simp
      calc
        ‖weakDoubletVecMinusI‖ = Real.sqrt (‖weakDoubletVecMinusI‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg weakDoubletVecMinusI)).symm
        _ = Real.sqrt 1 := by rw [hn]
        _ = 1 := Real.sqrt_one
  · rintro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simp [weakDoubletCarrierI, Submodule.coe_inner]
      rw [← weakCarrierCinner_eq_inner]
      exact weakDoubletVecPlusI_orth_weakDoubletVecMinusI
    · simp [weakDoubletCarrierI, Submodule.coe_inner]
      rw [← weakCarrierCinner_eq_inner]
      exact weakDoubletVecMinusI_orth_weakDoubletVecPlusI
    · exact (hij rfl).elim

/-- Column matrix `B` with orthonormal columns `weakDoubletVecPlusI`, `weakDoubletVecMinusI`. -/
noncomputable def weakDoubletB : Matrix (Fin 8) (Fin 2) ℂ :=
  Matrix.of fun (r : Fin 8) (c : Fin 2) =>
    match c with
    | 0 => weakDoubletVecPlusI r
    | 1 => weakDoubletVecMinusI r

theorem weakDoubletB_mulVec_eq_combo (v : Fin 2 → ℂ) :
    toLp 2 (weakDoubletB.mulVec v) = v 0 • weakDoubletVecPlusI + v 1 • weakDoubletVecMinusI := by
  refine congrArg (toLp 2) ?_
  funext r
  simp [weakDoubletB, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply,
    mul_comm]

/-! ### Gram matrix `Bᴴ * B = 1₂` and the linear equivalence `Fin 2 → ℂ ≃ₗ weakJComplexDoublet` -/

theorem weakDoubletB_conjTranspose_mul_self : weakDoubletBᴴ * weakDoubletB = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, weakDoubletB, dotProduct, weakCarrierCinner,
      Fin.sum_univ_two] using weakDoublet_inner_plus_self
  · simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, weakDoubletB, dotProduct, weakCarrierCinner,
      Fin.sum_univ_two] using weakDoubletVecPlusI_orth_weakDoubletVecMinusI
  · simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, weakDoubletB, dotProduct, weakCarrierCinner,
      Fin.sum_univ_two] using weakDoubletVecMinusI_orth_weakDoubletVecPlusI
  · simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, weakDoubletB, dotProduct, weakCarrierCinner,
      Fin.sum_univ_two] using weakDoublet_inner_minus_self

/-- Conjugate the abstract `2 × 2` Pauli matrix into an `8 × 8` operator on the carrier. -/
noncomputable def weakPauliEmbed (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  weakDoubletB * M * weakDoubletBᴴ

noncomputable def lieBracketMat₈ (A B : Matrix (Fin 8) (Fin 8) ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  A * B - B * A

theorem weakPauliEmbed_map_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    weakDoubletB * A * weakDoubletBᴴ * weakDoubletB * B * weakDoubletBᴴ = weakDoubletB * (A * B) * weakDoubletBᴴ := by
  rw [Matrix.mul_assoc (weakDoubletB * A), weakDoubletB_conjTranspose_mul_self, Matrix.mul_one,
    Matrix.mul_assoc weakDoubletB A B]

theorem weakPauliEmbed_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    weakPauliEmbed A * weakPauliEmbed B = weakPauliEmbed (A * B) := by
  simpa [weakPauliEmbed, Matrix.mul_assoc] using weakPauliEmbed_map_mul A B

theorem weakPauliEmbed_map_sub (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    weakPauliEmbed (A - B) = weakPauliEmbed A - weakPauliEmbed B := by
  simp [weakPauliEmbed, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

theorem weakPauliEmbed_lieBracket (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    weakPauliEmbed (lieBracketMat₂ A B) = lieBracketMat₈ (weakPauliEmbed A) (weakPauliEmbed B) := by
  simp [lieBracketMat₂, lieBracketMat₈, weakPauliEmbed_map_sub, weakPauliEmbed_mul]

theorem weakDoubletB_mulVec_mem_doublet (v : Fin 2 → ℂ) :
    toLp 2 (weakDoubletB.mulVec v) ∈ weakJComplexDoublet := by
  rw [weakDoubletB_mulVec_eq_combo]
  refine Submodule.add_mem _ ?_ ?_
  · refine Submodule.smul_mem _ _ weakDoubletVecPlus_mem_doublet
  · refine Submodule.smul_mem _ _ weakDoubletVecMinus_mem_doublet

theorem weakDoubletB_H_mulVec_plus : weakDoubletBᴴ.mulVec (ofLp weakDoubletVecPlusI) = ![(1 : ℂ), 0] := by
  funext i
  fin_cases i
  · simpa [Matrix.mulVec, Matrix.conjTranspose, weakDoubletB, dotProduct, Fin.sum_univ_two,
      weakDoubletVecPlusI, weakCarrierCinner] using weakDoublet_inner_plus_self
  · simpa [Matrix.mulVec, Matrix.conjTranspose, weakDoubletB, dotProduct, Fin.sum_univ_two,
      weakDoubletVecPlusI, weakDoubletVecMinusI, weakCarrierCinner] using
      weakDoubletVecMinusI_orth_weakDoubletVecPlusI

theorem weakDoubletB_H_mulVec_minus : weakDoubletBᴴ.mulVec (ofLp weakDoubletVecMinusI) = ![(0 : ℂ), 1] := by
  funext i
  fin_cases i
  · simpa [Matrix.mulVec, Matrix.conjTranspose, weakDoubletB, dotProduct, Fin.sum_univ_two,
      weakDoubletVecPlusI, weakDoubletVecMinusI, weakCarrierCinner] using
      weakDoubletVecPlusI_orth_weakDoubletVecMinusI
  · simpa [Matrix.mulVec, Matrix.conjTranspose, weakDoubletB, dotProduct, Fin.sum_univ_two,
      weakDoubletVecMinusI, weakCarrierCinner] using weakDoublet_inner_minus_self

/-- Linear identification of the abstract doublet with the `J`-stable `±i` plane in `ℂ⁸`. -/
noncomputable def weakDoubletEquiv : (Fin 2 → ℂ) ≃ₗ[ℂ] weakJComplexDoublet where
  toFun v := ⟨toLp 2 (weakDoubletB.mulVec v), weakDoubletB_mulVec_mem_doublet v⟩
  map_add' v w := by
    apply Subtype.ext
    simp [Matrix.mulVec_add, toLp_add]
  map_smul' c v := by
    apply Subtype.ext
    simp [Matrix.mulVec_smul, toLp_smul]
  invFun x := weakDoubletBᴴ.mulVec (ofLp x.val)
  left_inv v := by
    change weakDoubletBᴴ.mulVec (ofLp (toLp 2 (weakDoubletB.mulVec v))) = v
    rw [ofLp_toLp, Matrix.mulVec_mulVec v weakDoubletBᴴ weakDoubletB, weakDoubletB_conjTranspose_mul_self,
      Matrix.one_mulVec]
  right_inv x := by
    rcases x with ⟨y, hy⟩
    apply Subtype.ext
    change toLp 2 (weakDoubletB.mulVec (weakDoubletBᴴ.mulVec (ofLp y))) = y
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro z (rfl | rfl)
      · rw [weakDoubletB_H_mulVec_plus]
        simpa [Matrix.cons_val_zero, Matrix.cons_val_one] using weakDoubletB_mulVec_eq_combo ![(1 : ℂ), 0]
      · rw [weakDoubletB_H_mulVec_minus]
        simpa [Matrix.cons_val_zero, Matrix.cons_val_one] using weakDoubletB_mulVec_eq_combo ![(0 : ℂ), 1]
    · simp [Matrix.mulVec_zero, toLp_zero]
    · intro a b _ _ iha ihb
      calc
        toLp 2 (weakDoubletB.mulVec (weakDoubletBᴴ.mulVec (ofLp (a + b))))
            = toLp 2 (weakDoubletB.mulVec (weakDoubletBᴴ.mulVec (ofLp a + ofLp b))) := by
              rw [ofLp_add]
        _ = toLp 2 (weakDoubletB.mulVec (weakDoubletBᴴ.mulVec (ofLp a) + weakDoubletBᴴ.mulVec (ofLp b))) := by
              simp [Matrix.mulVec_add]
        _ = toLp 2
              (weakDoubletB.mulVec (weakDoubletBᴴ.mulVec (ofLp a)) +
                weakDoubletB.mulVec (weakDoubletBᴴ.mulVec (ofLp b))) := by
              simp [Matrix.mulVec_add]
        _ = toLp 2 (weakDoubletB.mulVec (weakDoubletBᴴ.mulVec (ofLp a))) +
              toLp 2 (weakDoubletB.mulVec (weakDoubletBᴴ.mulVec (ofLp b))) := by
              rw [toLp_add]
        _ = a + b := by rw [iha, ihb]
    · intro c a _ iha
      calc
        toLp 2 (weakDoubletB.mulVec (weakDoubletBᴴ.mulVec (ofLp (c • a)))) =
            toLp 2 (weakDoubletB.mulVec (weakDoubletBᴴ.mulVec (c • ofLp a))) := by
              rw [ofLp_smul]
        _ = toLp 2 (c • weakDoubletB.mulVec (weakDoubletBᴴ.mulVec (ofLp a))) := by
              rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
        _ = c • toLp 2 (weakDoubletB.mulVec (weakDoubletBᴴ.mulVec (ofLp a))) := by
              rw [toLp_smul]
        _ = c • a := by rw [iha]

theorem weakDoubletEquiv_coe_apply (v : Fin 2 → ℂ) :
    ↑(weakDoubletEquiv v) = toLp 2 (weakDoubletB.mulVec v) :=
  rfl

theorem weakPauliEmbed_mulVec_intertwine (M : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    weakDoubletB.mulVec (M.mulVec v) = (weakPauliEmbed M).mulVec (weakDoubletB.mulVec v) := by
  unfold weakPauliEmbed
  have hmat :
      weakDoubletB * M = weakDoubletB * M * weakDoubletBᴴ * weakDoubletB := by
    simp [Matrix.mul_assoc, weakDoubletB_conjTranspose_mul_self]
  calc
    weakDoubletB.mulVec (M.mulVec v) = (weakDoubletB * M).mulVec v := Matrix.mulVec_mulVec v weakDoubletB M
    _ = (weakDoubletB * M * weakDoubletBᴴ * weakDoubletB).mulVec v := by rw [← hmat]
    _ = (weakDoubletB * M * weakDoubletBᴴ).mulVec (weakDoubletB.mulVec v) :=
      (Matrix.mulVec_mulVec v (weakDoubletB * M * weakDoubletBᴴ) weakDoubletB).symm

theorem weakDoubletEquiv_Pauli_mulVec (M : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    ↑(weakDoubletEquiv (M.mulVec v)) = toLp 2 ((weakPauliEmbed M).mulVec (weakDoubletB.mulVec v)) := by
  simpa [weakDoubletEquiv, weakPauliEmbed, weakDoubletEquiv_coe_apply] using
    congrArg (toLp 2) (weakPauliEmbed_mulVec_intertwine M v)

/-- Pauli action on the carrier agrees with matrix multiplication after `weakDoubletEquiv`. -/
theorem weakPauliEmbed_Pauli_mulVec (M : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    toLp 2 ((weakPauliEmbed M).mulVec (weakDoubletB.mulVec v)) = ↑(weakDoubletEquiv (M.mulVec v)) :=
  (weakDoubletEquiv_Pauli_mulVec M v).symm

/-- Higgs VEV along the `u⁺` direction with real magnitude `v / √2` (standard unit-length convention).
Physically instantiate `v` with `lockinVev` (`Hqiv.Physics.WeakHiggsFromOMaxwellScaffold`) or the
outer-horizon `vacuumExpectationValue` family (`Hqiv.Physics.DerivedGaugeAndLeptonSector`). -/
noncomputable def higgsVevOfReal (v : ℝ) : weakJComplexDoublet :=
  (Complex.ofReal (v / Real.sqrt 2)) • ⟨weakDoubletVecPlusI, weakDoubletVecPlus_mem_doublet⟩

theorem higgsVevOfReal_coe (v : ℝ) :
    ↑(higgsVevOfReal v) = (Complex.ofReal (v / Real.sqrt 2)) • weakDoubletVecPlusI := by
  simp [higgsVevOfReal]

/-- Coefficients of `higgsVevOfReal v` in the abstract `Fin 2 → ℂ` chart (`weakDoubletEquiv`). -/
noncomputable def higgsDoubletFin2Coeff (v : ℝ) : Fin 2 → ℂ :=
  ![Complex.ofReal (v / Real.sqrt 2), 0]

theorem weakDoubletEquiv_symm_higgsVevOfReal (v : ℝ) :
    weakDoubletEquiv.symm (higgsVevOfReal v) = higgsDoubletFin2Coeff v := by
  funext i
  have hcarrier :
      (higgsVevOfReal v : WeakComplexOctonionCarrier) =
        (Complex.ofReal (v / Real.sqrt 2)) • weakDoubletVecPlusI :=
    higgsVevOfReal_coe v
  change weakDoubletBᴴ.mulVec (ofLp (higgsVevOfReal v).val) i = higgsDoubletFin2Coeff v i
  have hval : (higgsVevOfReal v).val = (higgsVevOfReal v : WeakComplexOctonionCarrier) := rfl
  rw [hval, hcarrier, ofLp_smul, Matrix.mulVec_smul, weakDoubletB_H_mulVec_plus]
  fin_cases i <;> simp [higgsDoubletFin2Coeff, Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Coefficient-level inclusion `ℂ² → (Fin 8 → ℂ)` (zeros outside indices `0` and `1`). -/
noncomputable def weakDoubletInclCoeff (v : Fin 2 → ℂ) : Fin 8 → ℂ :=
  fun i => if h : (i : ℕ) < 2 then v ⟨i.val, h⟩ else 0

theorem weakDoubletInclCoeff_linear (c d : ℂ) (v w : Fin 2 → ℂ) :
    weakDoubletInclCoeff (c • v + d • w) = c • weakDoubletInclCoeff v + d • weakDoubletInclCoeff w := by
  funext i
  by_cases h : (i : ℕ) < 2
  · simp [weakDoubletInclCoeff, h, if_pos, Pi.add_apply, Pi.smul_apply]
  · simp [weakDoubletInclCoeff, h, Pi.add_apply, Pi.smul_apply]

/-- Coordinate inclusion `ℂ² → ℂ⁸` placing amplitudes on indices `0` and `1` only.
This is a **chart-level** convenience; it is **not** asserted to land in `weakJEigenspaceI`. -/
noncomputable def weakDoubletInclusion (v : Fin 2 → ℂ) : WeakComplexOctonionCarrier :=
  toLp 2 (weakDoubletInclCoeff v)

theorem weakDoubletInclusion_linear (c d : ℂ) (v w : Fin 2 → ℂ) :
    weakDoubletInclusion (c • v + d • w) = c • weakDoubletInclusion v + d • weakDoubletInclusion w := by
  simp [weakDoubletInclusion, weakDoubletInclCoeff_linear, toLp_add, toLp_smul]

end Hqiv.Algebra

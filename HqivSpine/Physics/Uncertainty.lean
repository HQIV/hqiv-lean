import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Positivity

/-!
# `HqivSpine.Physics.Uncertainty` — the spin-½ Robertson/Heisenberg uncertainty bound

The **dynamical** companion to `Physics.SpinStatistics`: there spin is the `Spin(8)`
double-cover sign and the statistics of identical carriers; here it is the statement that
**non-commuting spin observables cannot be simultaneously sharp** — the quantum-mechanical
reason a carrier's quantum numbers carry irreducible spread (the "entropy" floor that
resists collapse).

On the one-qubit Hilbert space `H = ℂ²` with its `L²` inner product we prove, with **no new
axioms** (Mathlib core only):

* the **Pauli** matrices `σₓ, σᵧ, σ_z` and the commutator `[σₓ, σ_z] = −2i σᵧ`;
* **Robertson (Pauli):** `Var(σₓ)·Var(σ_z) ≥ |⟨σᵧ⟩|²` for every unit `ψ`
  (`pauli_robertson`) — the Cauchy–Schwarz/commutator skeleton behind Heisenberg,
  specialised to the spin-½ algebra;
* the **Heisenberg product form** `Δσₓ · Δσ_z ≥ |Re⟨σᵧ⟩|` (`pauli_heisenberg_product`).

Finite-dimensionally there is *no* pair of Hermitian operators with `[x,p] = iħ` (a trace
obstruction), so this is the honest finite-dim carrier of the uncertainty mechanism rather
than a literal position–momentum representation. The proof is the textbook one: the real
quadratic `t ↦ ‖(σₓ−⟨σₓ⟩)ψ + i t (σ_z−⟨σ_z⟩)ψ‖² ≥ 0` has nonpositive discriminant, and a
direct `ℂ²` expansion identifies `(Im cov)² = |⟨σᵧ⟩|²`.

Mathlib-only; no legacy `Hqiv.*` imports, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Physics.Qubit

open scoped InnerProductSpace BigOperators Matrix
open InnerProductSpace EuclideanSpace Matrix Complex ComplexConjugate PiLp WithLp

-- `im_inner_fluct_linX_linZ` ends with a large `simp`/`ring` normalization in `ℝ` after the
-- full `ℂ²` expansion; the default `maxHeartbeats` can time out during it.
set_option maxHeartbeats 0
-- `Matrix.toEuclideanLin_apply` is deprecated in favour of `toLpLin_apply`; the automated
-- `simp` set here still normalises more reliably with the Euclidean shorthand.
set_option linter.deprecated false

/-- The usual one-qubit Hilbert space `ℂ²` with `L²` inner product. -/
abbrev H := EuclideanSpace ℂ (Fin 2)

noncomputable section

/-- Pauli `σₓ`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- Pauli `σ_z`. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/-- Pauli `σᵧ` (Hermitian). -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -I; I, 0]

/-- `σₓ`, `σ_z`, `σᵧ` as `ℂ`-linear maps on `H`. -/
noncomputable def linX : H →ₗ[ℂ] H := Matrix.toEuclideanLin pauliX
noncomputable def linZ : H →ₗ[ℂ] H := Matrix.toEuclideanLin pauliZ
noncomputable def linY : H →ₗ[ℂ] H := Matrix.toEuclideanLin pauliY

/-- Expectation `⟨A⟩_ψ = ⟪ψ, A ψ⟫`. -/
noncomputable def expect (A : H →ₗ[ℂ] H) (ψ : H) : ℂ :=
  inner ℂ ψ (A ψ)

/-- Fluctuation vector `(A - ⟨A⟩ I) ψ`. -/
noncomputable def fluct (A : H →ₗ[ℂ] H) (ψ : H) : H :=
  A ψ - expect A ψ • ψ

/-- Variance `‖(A - ⟨A⟩) ψ‖²` (real). -/
noncomputable def var (A : H →ₗ[ℂ] H) (ψ : H) : ℝ :=
  ‖fluct A ψ‖ ^ 2

theorem pauliX_mul_pauliZ : pauliX * pauliZ = !![0, -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, pauliZ, Matrix.mul_apply, Matrix.of_apply,
    Fin.sum_univ_succ]

theorem pauliZ_mul_pauliX : pauliZ * pauliX = !![0, 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, pauliZ, Matrix.mul_apply, Matrix.of_apply,
    Fin.sum_univ_succ]

theorem pauli_comm_xz : pauliX * pauliZ - pauliZ * pauliX = (-2 * I) • pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX_mul_pauliZ, pauliZ_mul_pauliX, pauliY, sub_eq_add_neg, smul_eq_mul, mul_assoc] <;>
      norm_num

theorem mulVec_pauliY (v : Fin 2 → ℂ) :
    pauliY *ᵥ v = ![(-I) * v 1, I * v 0] := by
  funext i
  fin_cases i <;> simp [pauliY, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem inner_sigmaY_eq (ψ : H) :
    inner ℂ ψ (linY ψ) = (conj (ψ 0) * ((-I) * ψ 1) + conj (ψ 1) * (I * ψ 0)) := by
  classical
  rw [PiLp.inner_apply, linY, Matrix.toEuclideanLin_apply, toLp_apply]
  simp [mulVec_pauliY, Fin.sum_univ_succ, mul_assoc, mul_comm]

theorem inner_sigmaY_re (a b c d : ℝ) (ψ : H) (h0 : ψ 0 = a + I * b) (h1 : ψ 1 = c + I * d) :
    (inner ℂ ψ (linY ψ)).re = 2 * (a * d - b * c) := by
  rw [inner_sigmaY_eq, h0, h1]
  simp [map_add, map_mul, conj_ofReal, conj_I, mul_add, add_mul, mul_assoc, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm]
  ring

theorem inner_sigmaY_im (a b c d : ℝ) (ψ : H) (h0 : ψ 0 = a + I * b) (h1 : ψ 1 = c + I * d) :
    (inner ℂ ψ (linY ψ)).im = 0 := by
  rw [inner_sigmaY_eq, h0, h1]
  simp [map_add, map_mul, conj_ofReal, conj_I, mul_add, add_mul, mul_assoc, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm]
  ring

theorem norm_sq_eq_sum (ψ : H) : ‖ψ‖ ^ 2 = ‖ψ 0‖ ^ 2 + ‖ψ 1‖ ^ 2 := by
  simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]

/-- Explicit `L²(μ)` inner product on `H = ℂ²`. -/
theorem inner_piL2 (u v : H) : inner ℂ u v = conj (u 0) * v 0 + conj (u 1) * v 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ, mul_comm]

/-- Sesquilinear expansion of `⟪(A-⟨A⟩)ψ,(B-⟨B⟩)ψ⟫` (conjugate-linear in the first slot). -/
theorem inner_fluct_expand (A B : H →ₗ[ℂ] H) (ψ : H) :
    inner ℂ (fluct A ψ) (fluct B ψ) =
      inner ℂ (A ψ) (B ψ) - conj (expect A ψ) * inner ℂ ψ (B ψ) - expect B ψ * inner ℂ (A ψ) ψ
        + conj (expect A ψ) * expect B ψ * inner ℂ ψ ψ := by
  simp only [fluct, expect, inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
    inner_smul_left, inner_smul_right, sub_eq_add_neg, neg_add_rev, mul_add, add_assoc, add_comm,
    mul_assoc]
  ring

/-- Expansion of `‖u + i t v‖²` used in the discriminant proof of Robertson.

With Mathlib's convention (conjugate-linear in the **first** slot),
`‖u + (I·t)v‖² = ‖u‖² + t²‖v‖² − 2t·Im⟪u,v⟫` for real `t`. -/
theorem norm_sq_add_I_smul_t (u v : H) (t : ℝ) :
    ‖u + (I * (t : ℂ)) • v‖ ^ 2 =
      ‖u‖ ^ 2 + t ^ 2 * ‖v‖ ^ 2 - 2 * t * (inner ℂ u v).im := by
  have hinner : inner ℂ u v = conj (u 0) * v 0 + conj (u 1) * v 1 := by
    simp [PiLp.inner_apply, Fin.sum_univ_succ, mul_comm]
  have coord (a b : ℂ) (tr : ℝ) :
      ‖a + I * (tr : ℂ) * b‖ ^ 2 =
        ‖a‖ ^ 2 + tr ^ 2 * ‖b‖ ^ 2 - 2 * tr * (conj a * b).im := by
    rw [Complex.sq_norm, Complex.normSq_add]
    have hmul : normSq ((I * (tr : ℂ)) * b) = tr ^ 2 * normSq b := by
      rw [normSq_mul (I * (tr : ℂ)) b, normSq_mul I (tr : ℂ), normSq_I, normSq_ofReal, one_mul]
      simp [pow_two, mul_assoc]
    rw [hmul]
    have hcross :
        2 * (a * conj ((I * (tr : ℂ)) * b)).re = -(2 * tr * (conj a * b).im) := by
      simp [conj_I, conj_ofReal, mul_assoc, mul_comm, mul_left_comm, map_mul, Complex.mul_re,
        Complex.mul_im, I_re, I_im, sub_eq_add_neg, add_comm]
      ring_nf
    rw [hcross, ← Complex.sq_norm, ← Complex.sq_norm]
    ring
  rw [norm_sq_eq_sum]
  have hs0 : (u + (I * (t : ℂ)) • v) 0 = u 0 + I * (t : ℂ) * v 0 := by
    simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hs1 : (u + (I * (t : ℂ)) • v) 1 = u 1 + I * (t : ℂ) * v 1 := by
    simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [show ‖(u + (I * (t : ℂ)) • v) 0‖ ^ 2 = ‖u 0 + I * (t : ℂ) * v 0‖ ^ 2 by rw [hs0]]
  rw [show ‖(u + (I * (t : ℂ)) • v) 1‖ ^ 2 = ‖u 1 + I * (t : ℂ) * v 1‖ ^ 2 by rw [hs1]]
  rw [coord (u 0) (v 0) t, coord (u 1) (v 1) t, norm_sq_eq_sum u, norm_sq_eq_sum v, hinner]
  simp_rw [Complex.add_im]
  ring_nf

/-- `Im ⟪fluct linX ψ, fluct linZ ψ⟫ = -(Re ⟨linY⟩)` (Pauli `σₓ/σ_z` fluctuations vs `σᵧ`). -/
theorem im_inner_fluct_linX_linZ (ψ : H) :
    (inner ℂ (fluct linX ψ) (fluct linZ ψ)).im = -(expect linY ψ).re := by
  let a := (ψ 0).re
  let b := (ψ 0).im
  let c := (ψ 1).re
  let d := (ψ 1).im
  have h0 : ψ 0 = a + I * b := by
    dsimp [a, b]; rw [← Complex.re_add_im (ψ 0)]; simp [mul_comm]
  have h1 : ψ 1 = c + I * d := by
    dsimp [c, d]; rw [← Complex.re_add_im (ψ 1)]; simp [mul_comm]
  have hre := inner_sigmaY_re a b c d ψ h0 h1
  rw [eq_neg_iff_add_eq_zero, expect, hre]
  have mulX0 : (linX ψ) 0 = ψ 1 := by
    simp [linX, Matrix.toEuclideanLin_apply, toLp_apply, dotProduct, pauliX, Fin.sum_univ_succ]
  have mulX1 : (linX ψ) 1 = ψ 0 := by
    simp [linX, Matrix.toEuclideanLin_apply, toLp_apply, dotProduct, pauliX, Fin.sum_univ_succ]
  have mulZ0 : (linZ ψ) 0 = ψ 0 := by
    simp [linZ, Matrix.toEuclideanLin_apply, toLp_apply, dotProduct, pauliZ, Fin.sum_univ_succ]
  have mulZ1 : (linZ ψ) 1 = -ψ 1 := by
    simp [linZ, Matrix.toEuclideanLin_apply, toLp_apply, dotProduct, pauliZ, Fin.sum_univ_succ]
  have hexX : expect linX ψ = conj (ψ 0) * ψ 1 + conj (ψ 1) * ψ 0 := by
    simp [expect, linX, Matrix.toEuclideanLin_apply, PiLp.inner_apply, dotProduct, pauliX,
      Fin.sum_univ_succ]
    simp_rw [mul_comm]
  have hexZ : expect linZ ψ = conj (ψ 0) * ψ 0 - conj (ψ 1) * ψ 1 := by
    simp [expect, linZ, Matrix.toEuclideanLin_apply, PiLp.inner_apply, dotProduct, pauliZ,
      Fin.sum_univ_succ, sub_eq_add_neg]
    simp_rw [mul_comm]
  have imX : (expect linX ψ).im = 0 := by
    rw [hexX, h0, h1]
    simp [map_add, map_mul, conj_ofReal, conj_I, mul_add, add_mul, mul_assoc, sub_eq_add_neg,
      Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_im, I_im, I_re]
    ring
  have imZ : (expect linZ ψ).im = 0 := by
    rw [hexZ, h0, h1]
    simp [map_add, map_mul, conj_ofReal, conj_I, mul_add, add_mul, mul_assoc, sub_eq_add_neg,
      Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_im, I_im, I_re]
    ring
  have conj_exX : conj (expect linX ψ) = expect linX ψ := (conj_eq_iff_im.mpr imX)
  have hXZ : inner ℂ ψ (linZ ψ) = expect linZ ψ := rfl
  have hXψ : inner ℂ (linX ψ) ψ = conj (expect linX ψ) := by
    simp [expect, inner_conj_symm]
  have hXZmat : inner ℂ (linX ψ) (linZ ψ) = conj (ψ 1) * ψ 0 - conj (ψ 0) * ψ 1 := by
    simp [inner_piL2, mulX0, mulX1, mulZ0, mulZ1, mul_comm, sub_eq_add_neg]
  have hXψ' : inner ℂ (linX ψ) ψ = expect linX ψ := by rw [hXψ, conj_exX]
  have himψ : (inner ℂ ψ ψ).im = 0 := by
    rw [inner_piL2, h0, h1]
    simp [map_add, map_mul, conj_ofReal, conj_I, mul_add, add_mul, mul_assoc, sub_eq_add_neg,
      Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_im, I_im, I_re]
    ring
  have im_mul₀ (z w : ℂ) (hz : z.im = 0) (hw : w.im = 0) : (z * w).im = 0 := by
    simp [Complex.mul_im, hz, hw]
  have him_exZZ : (expect linX ψ * expect linZ ψ * inner ℂ ψ ψ).im = 0 := by
    have hEE : (expect linX ψ * expect linZ ψ).im = 0 := im_mul₀ _ _ imX imZ
    simpa [mul_assoc] using im_mul₀ (expect linX ψ * expect linZ ψ) (inner ℂ ψ ψ) hEE himψ
  have him_corr :
      (-(expect linX ψ * expect linZ ψ) + (-(expect linZ ψ * expect linX ψ))
          + expect linX ψ * expect linZ ψ * inner ℂ ψ ψ).im = 0 := by
    have hEE : (expect linX ψ * expect linZ ψ).im = 0 := im_mul₀ _ _ imX imZ
    have hEE' : (expect linZ ψ * expect linX ψ).im = 0 := im_mul₀ _ _ imZ imX
    simp_rw [Complex.add_im, Complex.neg_im, hEE, hEE', him_exZZ, neg_zero, zero_add]
  have hsplit :
      inner ℂ (fluct linX ψ) (fluct linZ ψ) =
        (conj (ψ 1) * ψ 0 - conj (ψ 0) * ψ 1)
          + (-(expect linX ψ * expect linZ ψ) + (-(expect linZ ψ * expect linX ψ))
              + expect linX ψ * expect linZ ψ * inner ℂ ψ ψ) := by
    rw [inner_fluct_expand linX linZ ψ, hXZmat, hXZ, hXψ', conj_exX]
    ring
  have him_fluct :
      (inner ℂ (fluct linX ψ) (fluct linZ ψ)).im = (conj (ψ 1) * ψ 0 - conj (ψ 0) * ψ 1).im := by
    rw [hsplit, Complex.add_im, him_corr]
    simp
  rw [him_fluct, h0, h1]
  simp [map_add, map_mul, conj_ofReal, conj_I, mul_add, add_mul, mul_assoc, sub_eq_add_neg,
    Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_im, I_im, I_re]
  ring

/-- **Robertson (Pauli):** for unit `ψ`, `Var(σₓ) Var(σ_z) ≥ |⟨σᵧ⟩|²`.

Proof: `t ↦ ‖(σₓ-⟨σₓ⟩)ψ + i t (σ_z-⟨σ_z⟩)ψ‖²` is a nonnegative quadratic; discriminant
nonpositivity gives `Var(σₓ) Var(σ_z) ≥ (Im cov)²`, and a direct `ℂ²` expansion identifies
`(Im cov)² = |⟨σᵧ⟩|²`. The hypothesis `‖ψ‖ = 1` matches the textbook normalisation
(but is not used in this algebraic argument). -/
theorem pauli_robertson (ψ : H) (_hψ : ‖ψ‖ = 1) :
    var linX ψ * var linZ ψ ≥ Complex.normSq (expect linY ψ) := by
  let u := fluct linX ψ
  let v := fluct linZ ψ
  have hquad (x : ℝ) :
      0 ≤ var linZ ψ * (x * x) + (-2 * (inner ℂ u v).im) * x + var linX ψ := by
    have hn := sq_nonneg ‖u + (I * (x : ℂ)) • v‖
    rw [norm_sq_add_I_smul_t u v x] at hn
    dsimp [u, v, var] at hn ⊢
    simpa [mul_assoc, mul_comm, mul_left_comm, add_assoc, add_left_comm, add_comm, sub_eq_add_neg,
      pow_two] using hn
  have hdisc :=
    discrim_le_zero (K := ℝ) (a := var linZ ψ) (b := -2 * (inner ℂ u v).im) (c := var linX ψ) hquad
  dsimp [discrim] at hdisc
  have himY : (expect linY ψ).im = 0 := by
    let a := (ψ 0).re
    let b := (ψ 0).im
    let c := (ψ 1).re
    let d := (ψ 1).im
    have h0 : ψ 0 = a + I * b := by
      dsimp [a, b]; rw [← Complex.re_add_im (ψ 0)]; simp [mul_comm]
    have h1 : ψ 1 = c + I * d := by
      dsimp [c, d]; rw [← Complex.re_add_im (ψ 1)]; simp [mul_comm]
    simp [expect, inner_sigmaY_im a b c d ψ h0 h1]
  have hnormSq_re : Complex.normSq (expect linY ψ) = (expect linY ψ).re ^ 2 := by
    rw [Complex.normSq_apply, himY]
    ring
  have him_sq : (inner ℂ u v).im ^ 2 = Complex.normSq (expect linY ψ) := by
    rw [hnormSq_re, im_inner_fluct_linX_linZ ψ]
    ring
  nlinarith [hdisc, him_sq, sq_nonneg (var linZ ψ), sq_nonneg (var linX ψ)]

/-- Standard deviations `ΔA = √Var(A)` for nonnegative variance. -/
noncomputable nonrec def stdDev (A : H →ₗ[ℂ] H) (ψ : H) : ℝ := Real.sqrt (var A ψ)

/-- **Heisenberg product form:** `Δσₓ · Δσ_z ≥ |Re⟨σᵧ⟩|` for unit `ψ`. -/
theorem pauli_heisenberg_product (ψ : H) (hψ : ‖ψ‖ = 1) :
    stdDev linX ψ * stdDev linZ ψ ≥ |Complex.re (expect linY ψ)| := by
  let a := (ψ 0).re
  let b := (ψ 0).im
  let c := (ψ 1).re
  let d := (ψ 1).im
  have h0 : ψ 0 = a + I * b := by
    dsimp [a, b]
    rw [← Complex.re_add_im (ψ 0)]
    simp [mul_comm]
  have h1 : ψ 1 = c + I * d := by
    dsimp [c, d]
    rw [← Complex.re_add_im (ψ 1)]
    simp [mul_comm]
  have him : (expect linY ψ).im = 0 := by
    simp [expect, inner_sigmaY_im a b c d ψ h0 h1]
  have hreSq : Complex.normSq (expect linY ψ) = (Complex.re (expect linY ψ)) ^ 2 := by
    rw [Complex.normSq_apply, him]
    ring
  have hsq : (Complex.re (expect linY ψ)) ^ 2 ≤ var linX ψ * var linZ ψ := by
    rw [← hreSq]
    exact pauli_robertson ψ hψ
  have hvx : 0 ≤ var linX ψ := sq_nonneg _
  have hvz : 0 ≤ var linZ ψ := sq_nonneg _
  calc
    |Complex.re (expect linY ψ)| = Real.sqrt ((Complex.re (expect linY ψ)) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (var linX ψ * var linZ ψ) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (var linX ψ) * Real.sqrt (var linZ ψ) :=
        Real.sqrt_mul hvx (var linZ ψ)
    _ = stdDev linX ψ * stdDev linZ ψ := rfl

end

end HqivSpine.Physics.Qubit

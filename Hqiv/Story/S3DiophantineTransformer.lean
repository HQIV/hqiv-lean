import Hqiv.Story.S3TuftNestedFrameTower
import Mathlib.Analysis.PSeriesComplex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# The Diophantine transformer: a concrete operator behind the tower

The frame tower, the spectral lines, and the FE pairing assemble into a
single concrete object: the level-`N` **Diophantine transformer**
\[
  D_N(s) \;=\; \mathrm{diag}\big(1^{-s},\,2^{-s},\,\dots,\,N^{-s}\big),
\]
an integer-indexed, prime-generated diagonal operator on `ℂ^N`.  This module
proves its laws — and they are exactly the Hilbert–Pólya-flavored statements
the construction has been pointing at.

## Proved operator laws

* **Trace ladder → ζ** (`diophantineTransformer_trace`,
  `diophantineTransformer_trace_tendsto`): the trace of `D_N(s)` is the
  `N`-th Dirichlet partial sum, and on the product region `Re s > 1` the
  trace ladder converges to `ζ(s)`.  The zeta function is the trace of the
  transformer tower.
* **Hilbert–Schmidt norm = frame radius**
  (`diophantineTransformer_hs_normSq`): the squared HS norm of `D_N(s)` is
  `spectralFrameNormSq N s` — the TUFT tower radius.  The harmonic radius
  law becomes: the transformer is harmonically normalized (`HS² = H_N`)
  exactly on the critical line.
* **FE composition is the fixed rational harmonic operator**
  (`diophantineTransformer_fe_product`): for *every* `s`,
  \[
    D_N(s)\cdot D_N(1-s) \;=\; \mathrm{diag}\big(1,\tfrac12,\dots,\tfrac1N\big),
  \]
  a pure Diophantine object — rational entries, no `s` left.  Its trace is
  the harmonic backbone `H_N` (`feProduct_trace_eq_harmonic`).
* **Adjoint law characterizes the line**
  (`transformer_entry_adjoint_iff`, `diophantineTransformer_adjoint_iff`):
  `D_N(1−s) = D_N(s)ᴴ ⟺ Re s = 1/2`.  The functional-equation reflection
  agrees with the operator adjoint exactly on the critical line; there the
  transformer is a scaled isometry with
  `D_N(s)·D_N(s)ᴴ = diag(1/n)`
  (`transformer_scaled_isometry_on_line`).
* **RH in operator language** (`RH_iff_transformer_adjoint_at_zeros`):
  RH ⟺ at every nontrivial zero the FE-reflected transformer *is* the
  adjoint, at every level.  The Hilbert–Pólya dream in its honest, provable
  form: not "a self-adjoint operator whose spectrum is the zeros", but
  "RH ⟺ the concrete transformer family is self-adjoint-across-FE at the
  zeros".

## Honest scope

Everything here is unconditional operator algebra; the adjoint law adds the
operator face to the equivalence stack (tangent, weights, height, polar,
tower — now adjoint).  It is one more zero-slack reformulation, not a
discharge: self-adjointness across FE at the zeros is exactly RH.
-/

namespace Hqiv.Story

open Complex Filter Matrix

noncomputable section

/-- The level-`N` Diophantine transformer: the diagonal operator of the
first `N` spectral lines, `diag(1^{−s}, …, N^{−s})`. -/
noncomputable def diophantineTransformer (N : ℕ) (s : ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun i => so4SpectralLine ((i : ℕ) + 1) s

/-! ## Trace ladder -/

/-- The trace of the transformer is the `N`-th Dirichlet partial sum. -/
theorem diophantineTransformer_trace (N : ℕ) (s : ℂ) :
    (diophantineTransformer N s).trace =
      ∑ n ∈ Finset.range N, so4SpectralLine (n + 1) s := by
  unfold diophantineTransformer
  rw [Matrix.trace_diagonal]
  exact Fin.sum_univ_eq_sum_range (fun n => so4SpectralLine (n + 1) s) N

/-- **The trace ladder converges to ζ** on the product region: `ζ(s)` is
the trace of the transformer tower. -/
theorem diophantineTransformer_trace_tendsto {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N => (diophantineTransformer N s).trace) atTop
      (nhds (riemannZeta s)) := by
  have hsum : Summable (fun n : ℕ => 1 / (n + 1 : ℂ) ^ s) := by
    have h0 : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
      Complex.summable_one_div_nat_cpow.mpr hs
    exact_mod_cast (summable_nat_add_iff 1).mpr h0
  have hHasSum : HasSum (fun n : ℕ => 1 / (n + 1 : ℂ) ^ s) (riemannZeta s) := by
    rw [shell_sum_eq_riemannZeta s hs]
    exact hsum.hasSum
  have htend := hHasSum.tendsto_sum_nat
  have heq : (fun N => (diophantineTransformer N s).trace) =
      fun N => ∑ n ∈ Finset.range N, 1 / (n + 1 : ℂ) ^ s := by
    funext N
    rw [diophantineTransformer_trace]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold so4SpectralLine
    rw [cpow_neg, one_div]
    norm_num
  rw [heq]
  exact htend

/-! ## Hilbert–Schmidt norm = tower radius -/

/-- The squared Hilbert–Schmidt norm of the transformer is the TUFT frame
radius: the tower IS the operator's norm ladder. -/
theorem diophantineTransformer_hs_normSq (N : ℕ) (s : ℂ) :
    ∑ i : Fin N, ‖diophantineTransformer N s i i‖ ^ 2 =
      spectralFrameNormSq N s := by
  unfold diophantineTransformer spectralFrameNormSq
  simp only [Matrix.diagonal_apply_eq]
  exact Fin.sum_univ_eq_sum_range
    (fun n => ‖so4SpectralLine (n + 1) s‖ ^ 2) N

/-! ## FE composition: the fixed rational harmonic operator -/

/-- **FE composition law**: for every `s`, the product of the transformer
with its FE reflection is the fixed Diophantine harmonic operator
`diag(1, 1/2, …, 1/N)` — rational entries, no `s` left. -/
theorem diophantineTransformer_fe_product (N : ℕ) (s : ℂ) :
    diophantineTransformer N s * diophantineTransformer N (1 - s) =
      Matrix.diagonal (fun i : Fin N => (((i : ℕ) : ℂ) + 1)⁻¹) := by
  unfold diophantineTransformer
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  unfold so4SpectralLine
  have hne : (((i : ℕ) : ℂ) + 1) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  push_cast
  rw [← cpow_add _ _ hne]
  rw [show -s + -(1 - s) = (-1 : ℂ) by ring, cpow_neg_one]

/-- The trace of the FE composition is the harmonic backbone `H_N`. -/
theorem feProduct_trace_eq_harmonic (N : ℕ) (s : ℂ) :
    (diophantineTransformer N s * diophantineTransformer N (1 - s)).trace =
      ((harmonicPartialSum N : ℝ) : ℂ) := by
  rw [diophantineTransformer_fe_product, Matrix.trace_diagonal,
    Fin.sum_univ_eq_sum_range (fun n => (((n : ℕ) : ℂ) + 1)⁻¹) N]
  unfold harmonicPartialSum
  push_cast
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [one_div]

/-! ## The adjoint law characterizes the line -/

/-- **Entry-level adjoint law**: the FE-reflected spectral line equals the
conjugated line exactly on the critical line. -/
theorem transformer_entry_adjoint_iff {n : ℕ} (hn : 2 ≤ n) {s : ℂ} :
    so4SpectralLine n (1 - s) = starRingEnd ℂ (so4SpectralLine n s) ↔
      s.re = (1 / 2 : ℝ) := by
  have hpos : 0 < n := by omega
  have hb : (1 : ℝ) < n := by exact_mod_cast hn
  constructor
  · intro h
    have hnorm := congrArg Norm.norm h
    rw [RCLike.norm_conj, so4SpectralLine_norm hpos, so4SpectralLine_norm hpos]
      at hnorm
    have h2 : (1 - s).re = 1 - s.re := by
      simp [Complex.sub_re, Complex.one_re]
    rw [h2] at hnorm
    have := rpow_left_inj_of_one_lt hb hnorm
    linarith
  · intro hσ
    unfold so4SpectralLine
    have harg : ((n : ℂ)).arg ≠ Real.pi := by
      rw [Complex.natCast_arg]
      exact Real.pi_ne_zero.symm
    have key := Complex.conj_cpow ((n : ℂ)) (-(1 - s)) harg
    rw [Complex.conj_natCast] at key
    rw [key]
    congr 1
    have hsc : starRingEnd ℂ s = 1 - s := by
      apply Complex.ext
      · rw [Complex.conj_re, Complex.sub_re, Complex.one_re, hσ]
        norm_num
      · rw [Complex.conj_im, Complex.sub_im, Complex.one_im]
        ring
    rw [map_neg, map_sub, map_one, hsc]
    congr 1
    ring

/-- **Operator adjoint law**: the FE-reflected transformer equals the
conjugate-transpose exactly on the critical line. -/
theorem diophantineTransformer_adjoint_iff {N : ℕ} (hN : 2 ≤ N) {s : ℂ} :
    diophantineTransformer N (1 - s) = (diophantineTransformer N s)ᴴ ↔
      s.re = (1 / 2 : ℝ) := by
  unfold diophantineTransformer
  rw [Matrix.diagonal_conjTranspose]
  constructor
  · intro h
    have := congrArg (fun M => M ⟨1, by omega⟩ ⟨1, by omega⟩) h
    simp only [Matrix.diagonal_apply_eq, Pi.star_apply] at this
    exact (transformer_entry_adjoint_iff (le_refl 2)).mp this
  · intro hσ
    congr 1
    funext i
    simp only [Pi.star_apply]
    by_cases hi : (i : ℕ) + 1 = 1
    · -- the constant line `1^{−s} = 1` is self-conjugate
      rw [hi]
      unfold so4SpectralLine
      norm_num
    · have hi2 : 2 ≤ (i : ℕ) + 1 := by omega
      exact (transformer_entry_adjoint_iff hi2).mpr hσ

/-- On the critical line the transformer is a **scaled isometry**: its
unitarity defect is exactly the fixed Diophantine harmonic operator. -/
theorem transformer_scaled_isometry_on_line {N : ℕ} (hN : 2 ≤ N) {s : ℂ}
    (hs : s.re = (1 / 2 : ℝ)) :
    diophantineTransformer N s * (diophantineTransformer N s)ᴴ =
      Matrix.diagonal (fun i : Fin N => (((i : ℕ) : ℂ) + 1)⁻¹) := by
  rw [← (diophantineTransformer_adjoint_iff hN).mpr hs]
  exact diophantineTransformer_fe_product N s

/-! ## RH in operator language -/

/-- **RH ⟺ the transformer family is self-adjoint across FE at the
zeros**: at every nontrivial zero and every level, the FE-reflected
transformer is the adjoint.  The honest Hilbert–Pólya statement. -/
theorem RH_iff_transformer_adjoint_at_zeros :
    RiemannHypothesis ↔
      ∀ ρ : ℂ, IsNontrivialZetaZero ρ → ∀ N : ℕ, 2 ≤ N →
        diophantineTransformer N (1 - ρ) = (diophantineTransformer N ρ)ᴴ := by
  constructor
  · intro hRH ρ hz N hN
    exact (diophantineTransformer_adjoint_iff hN).mpr
      (hRH ρ hz.1 hz.2.1 hz.2.2)
  · intro hA ρ hz hnt h1
    exact (diophantineTransformer_adjoint_iff (le_refl 2)).mp
      (hA ρ ⟨hz, hnt, h1⟩ 2 (le_refl 2))

end

end Hqiv.Story

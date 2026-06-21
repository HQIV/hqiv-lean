import Hqiv.Story.S3HarmonicHolonomyCriticalLineFrontier
import Hqiv.Story.S3OctonionicAssociatorChannel
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Associator perturbation of the cascade holonomy transformer

`M_N(s) = D_N(s) + P_N(s)` with anti-Hermitian associator sheet on cascade slots
`(6,5,11) = (harmonicCascadeTrial 0, 1, 2)`.

**Critical-line pin (proved):** `perturbed_holonomy_defect_and_adjoint_forces_critical_line`
shows defect cancellation + full perturbed adjoint ⇒ `Re ρ = 1/2` with no RH input.

**Route-4 target (named, not discharged):** `AssociatorDefectAtZeroForcesCriticalLine` and
`NontrivialZeroForcesPerturbedHolonomyAdjoint` package the zero-level upgrade from the HQIV
coupling + non-normality certificates to that adjoint/defect split.
-/

namespace Hqiv.Story

open Hqiv.Geometry Hqiv.Algebra Complex Real Matrix

noncomputable section

def harmonicCascadeAssociatorTriple : ℕ × ℕ × ℕ :=
  (harmonicCascadeTrial 0, harmonicCascadeTrial 1, harmonicCascadeTrial 2)

theorem harmonicCascadeAssociatorTriple_eq :
    harmonicCascadeAssociatorTriple = (6, 5, 11) := by
  native_decide

noncomputable def cascadeAssociatorHolonomyWeight (s : ℂ) : ℂ :=
  Complex.I * Real.sqrt (octAssociatorChannel 6 5 11 s) * so4SpectralLine 6 s * so4SpectralLine 5 s

theorem cascadeAssociatorHolonomyWeight_ne_zero {s : ℂ}
    (hch : 0 < octAssociatorChannel 6 5 11 s) :
    cascadeAssociatorHolonomyWeight s ≠ 0 := by
  intro hz
  have hpos : 0 < ‖cascadeAssociatorHolonomyWeight s‖ := by
    rw [cascadeAssociatorHolonomyWeight]
    rw [norm_mul, norm_mul, norm_mul, norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.mpr hch), so4SpectralLine_norm (by decide : 0 < 6) s,
      so4SpectralLine_norm (by decide : 0 < 5) s]
    positivity
  rw [hz, norm_zero] at hpos
  exact hpos.false

noncomputable def cascadeAssociatorHolonomyPerturb (N : ℕ) (_hN3 : 3 ≤ N) (s : ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  let z := cascadeAssociatorHolonomyWeight s
  Matrix.of fun i j =>
    if (i : ℕ) = 0 ∧ (j : ℕ) = 1 then z
    else if (i : ℕ) = 1 ∧ (j : ℕ) = 0 then -star z
    else 0

noncomputable def harmonicCascadeHolonomyTransformerAssociatorPerturb (N : ℕ) (hN3 : 3 ≤ N)
    (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  harmonicCascadeHolonomyTransformer N (Nat.le_of_succ_le hN3) s +
    cascadeAssociatorHolonomyPerturb N hN3 s

private theorem two_le_of_three_le {N : ℕ} (h : 3 ≤ N) : 2 ≤ N := by omega

theorem cascadeAssociatorHolonomyPerturb_neg_conjTranspose (N : ℕ) (hN3 : 3 ≤ N) (s : ℂ) :
    (cascadeAssociatorHolonomyPerturb N hN3 s)ᴴ =
      -cascadeAssociatorHolonomyPerturb N hN3 s := by
  ext i j
  simp only [cascadeAssociatorHolonomyPerturb, Matrix.conjTranspose_apply, Matrix.of_apply,
    Pi.neg_apply]
  by_cases hij01 : (i : ℕ) = 0 ∧ (j : ℕ) = 1
  · rcases hij01 with ⟨hi0, hj1⟩
    simp [hi0, hj1, star, star_neg, star_star, Complex.ext_iff, Complex.neg_re, Complex.neg_im]
  · by_cases hij10 : (i : ℕ) = 1 ∧ (j : ℕ) = 0
    · rcases hij10 with ⟨hi1, hj0⟩
      simp [hi1, hj0, star, star_neg, star_star, neg_neg, Complex.ext_iff, Complex.neg_re,
        Complex.neg_im]
    · have hi0j1 : ¬((i : ℕ) = 0 ∧ (j : ℕ) = 1) := hij01
      have hi1j0 : ¬((i : ℕ) = 1 ∧ (j : ℕ) = 0) := hij10
      have hj0i1 : ¬((j : ℕ) = 0 ∧ (i : ℕ) = 1) := by
        intro h
        rcases h with ⟨hj0, hi1⟩
        exact hij10 ⟨hi1, hj0⟩
      have hj1i0 : ¬((j : ℕ) = 1 ∧ (i : ℕ) = 0) := by
        intro h
        rcases h with ⟨hj1, hi0⟩
        exact hij01 ⟨hi0, hj1⟩
      simp [hi0j1, hi1j0, hj0i1, hj1i0]

private def fin0 (N : ℕ) (hN3 : 3 ≤ N) : Fin N := ⟨0, by omega⟩

private def fin1 (N : ℕ) (hN3 : 3 ≤ N) : Fin N := ⟨1, by omega⟩

theorem cascadeAssociatorHolonomyPerturb_off_diagonal (N : ℕ) (hN3 : 3 ≤ N) (s : ℂ)
    (hch : 0 < octAssociatorChannel 6 5 11 s) :
    cascadeAssociatorHolonomyPerturb N hN3 s (fin0 N hN3) (fin1 N hN3) ≠ 0 :=
  cascadeAssociatorHolonomyWeight_ne_zero hch

/-! ## N = 3 entry calculus (explicit escape from diagonal saturation)

Use `cascadeAssociatorHolonomyPerturb_not_commute_diagonal_three`,
`harmonic_cascade_associator_perturb_not_commute_three`, and
`harmonic_cascade_associator_perturb_det_ne_diagonal_product` together as the
escape bundle (requires `hspec_ne : so4SpectralLine 6 s ≠ so4SpectralLine 5 s`).
-/

private def fin0₃ : Fin 3 := 0
private def fin1₃ : Fin 3 := 1
private def fin2₃ : Fin 3 := 2

private theorem perturb_mul_diagonal_01_three (s : ℂ) :
    (cascadeAssociatorHolonomyPerturb 3 (by decide) s *
        harmonicCascadeHolonomyTransformer 3 (by decide) s) fin0₃ fin1₃ =
      cascadeAssociatorHolonomyWeight s * so4SpectralLine 5 s := by
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp [cascadeAssociatorHolonomyPerturb, Matrix.of_apply, fin0₃, fin1₃, fin2₃,
    harmonicCascadeHolonomyTransformer, Matrix.diagonal_apply_eq, harmonicCascadeTrial_zero,
    harmonicCascadeTrial_one, harmonicCascadeTrial_two, so4SpectralLine, mul_comm, mul_left_comm,
    mul_assoc]

private theorem diagonal_mul_perturb_01_three (s : ℂ) :
    (harmonicCascadeHolonomyTransformer 3 (by decide) s *
        cascadeAssociatorHolonomyPerturb 3 (by decide) s) fin0₃ fin1₃ =
      so4SpectralLine 6 s * cascadeAssociatorHolonomyWeight s := by
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp [cascadeAssociatorHolonomyPerturb, Matrix.of_apply, fin0₃, fin1₃, fin2₃,
    harmonicCascadeHolonomyTransformer, Matrix.diagonal_apply_eq, harmonicCascadeTrial_zero,
    harmonicCascadeTrial_one, harmonicCascadeTrial_two, so4SpectralLine, mul_comm, mul_left_comm,
    mul_assoc]

theorem cascadeAssociatorHolonomyPerturb_not_commute_diagonal_three (s : ℂ)
    (hch : 0 < octAssociatorChannel 6 5 11 s)
    (hspec : so4SpectralLine 6 s ≠ so4SpectralLine 5 s) :
    cascadeAssociatorHolonomyPerturb 3 (by decide) s *
        harmonicCascadeHolonomyTransformer 3 (by decide) s ≠
      harmonicCascadeHolonomyTransformer 3 (by decide) s *
        cascadeAssociatorHolonomyPerturb 3 (by decide) s := by
  intro heq
  have h01 := perturb_mul_diagonal_01_three s
  have h10 := diagonal_mul_perturb_01_three s
  have heq01 := congrArg (fun M => M fin0₃ fin1₃) heq
  simp at heq01
  rw [h01, h10] at heq01
  have hz := cascadeAssociatorHolonomyWeight_ne_zero hch
  rw [mul_comm (so4SpectralLine 6 s) (cascadeAssociatorHolonomyWeight s)] at heq01
  exact absurd (mul_left_cancel₀ hz heq01.symm) hspec

theorem harmonic_cascade_associator_perturb_not_commute_three (s : ℂ)
    (hch : 0 < octAssociatorChannel 6 5 11 s)
    (hspec : so4SpectralLine 6 s ≠ so4SpectralLine 5 s) :
    harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) s *
        cascadeAssociatorHolonomyPerturb 3 (by decide) s ≠
      cascadeAssociatorHolonomyPerturb 3 (by decide) s *
        harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) s := by
  intro heq
  have heq01 := congrArg (fun M => M fin0₃ fin1₃) heq
  simp [harmonicCascadeHolonomyTransformerAssociatorPerturb, Matrix.mul_add, Matrix.add_mul,
    perturb_mul_diagonal_01_three, diagonal_mul_perturb_01_three] at heq01
  have hz := cascadeAssociatorHolonomyWeight_ne_zero hch
  rw [mul_comm (cascadeAssociatorHolonomyWeight s) (so4SpectralLine 5 s)] at heq01
  exact absurd (mul_right_cancel₀ hz heq01) hspec

theorem harmonic_cascade_associator_perturb_diagonal_adjoint_on_critical_line {N : ℕ}
    (hN3 : 3 ≤ N) {s : ℂ} (hs : s.re = (1 / 2 : ℝ)) :
    harmonicCascadeHolonomyTransformer N (two_le_of_three_le hN3) (1 - s) =
      (harmonicCascadeHolonomyTransformer N (two_le_of_three_le hN3) s)ᴴ :=
  (harmonic_cascade_holonomy_transformer_adjoint_iff (two_le_of_three_le hN3)).mpr hs

theorem harmonic_cascade_associator_perturb_fe_on_critical_line {N : ℕ} (hN3 : 3 ≤ N)
    (s : ℂ) :
    (harmonicCascadeHolonomyTransformer N (two_le_of_three_le hN3) s *
        harmonicCascadeHolonomyTransformer N (two_le_of_three_le hN3) (1 - s) =
      Matrix.diagonal fun i : Fin N => ((harmonicCascadeTrial (i : ℕ) : ℂ))⁻¹) ∧
      (octAssociatorChannel 6 5 11 s * octAssociatorChannel 6 5 11 (1 - s) =
        4 / ((6 * 5 * 11 : ℕ) : ℝ) ^ (2 : ℕ)) := by
  refine ⟨?_, octAssociatorChannel_fe_product (by decide) (by decide) (by decide) s⟩
  exact harmonic_cascade_holonomy_fe_product (two_le_of_three_le hN3) s

theorem harmonic_cascade_associator_perturb_adjoint_defect_on_critical_line {N : ℕ}
    (hN3 : 3 ≤ N) {s : ℂ} (hs : s.re = (1 / 2 : ℝ)) :
    harmonicCascadeHolonomyTransformerAssociatorPerturb N hN3 (1 - s) -
        (harmonicCascadeHolonomyTransformerAssociatorPerturb N hN3 s)ᴴ =
      cascadeAssociatorHolonomyPerturb N hN3 (1 - s) +
        cascadeAssociatorHolonomyPerturb N hN3 s := by
  have hD := harmonic_cascade_associator_perturb_diagonal_adjoint_on_critical_line hN3 hs
  have hP := cascadeAssociatorHolonomyPerturb_neg_conjTranspose N hN3 s
  unfold harmonicCascadeHolonomyTransformerAssociatorPerturb
  rw [Matrix.conjTranspose_add, hP, hD]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply]
  ring_nf
  simp [sub_neg_eq_add]

/-! ## Defect predicates and critical-line pinning (algebraic core) -/

/--
**Associator defect vanishes at `ρ`:** the anti-Hermitian sheet cancels across FE,
`P(1-ρ) + P(ρ) = 0`.
-/
def associatorHolonomyDefectVanishesAt (N : ℕ) (hN3 : 3 ≤ N) (ρ : ℂ) : Prop :=
  cascadeAssociatorHolonomyPerturb N hN3 (1 - ρ) + cascadeAssociatorHolonomyPerturb N hN3 ρ = 0

/--
**Full perturbed adjoint across FE** at `ρ`: `M(1-ρ) = M(ρ)ᴴ` for the associator-perturbed
cascade holonomy operator.
-/
def perturbedHolonomyFullAdjointAt (N : ℕ) (hN3 : 3 ≤ N) (ρ : ℂ) : Prop :=
  harmonicCascadeHolonomyTransformerAssociatorPerturb N hN3 (1 - ρ) =
    (harmonicCascadeHolonomyTransformerAssociatorPerturb N hN3 ρ)ᴴ

/--
**Non-normality certificate regime** at `ρ`: positive `(6,5,11)` associator channel and
spectral conjugate separation on cascade slots `(5,6)`.
-/
def associatorPerturbNonNormalityWitnessAt (ρ : ℂ) : Prop :=
  0 < octAssociatorChannel 6 5 11 ρ ∧
    star (so4SpectralLine 5 ρ) + so4SpectralLine 5 ρ ≠
      star (so4SpectralLine 6 ρ) + so4SpectralLine 6 ρ

private theorem perturb_adjoint_01_weight_eq_neg {N : ℕ} (hN3 : 3 ≤ N) {ρ : ℂ}
    (hAdj : perturbedHolonomyFullAdjointAt N hN3 ρ) :
    cascadeAssociatorHolonomyWeight (1 - ρ) = -cascadeAssociatorHolonomyWeight ρ := by
  unfold perturbedHolonomyFullAdjointAt at hAdj
  have h01 := congrArg (fun M => M (fin0 N hN3) (fin1 N hN3)) hAdj
  simp [harmonicCascadeHolonomyTransformerAssociatorPerturb, Matrix.add_apply,
    cascadeAssociatorHolonomyPerturb, Matrix.of_apply, fin0, fin1,
    harmonicCascadeHolonomyTransformer, Matrix.diagonal_apply_eq,
    harmonicCascadeTrial_zero, harmonicCascadeTrial_one, Matrix.conjTranspose_apply,
    star, star_neg, star_star] at h01
  exact h01

/--
**Sparse-sheet defect cancellation:** full perturbed adjoint forces
`P(1-ρ) + P(ρ) = 0` because the `(0,1)` entry gives
`z(1-ρ) = -z(ρ)` and `P` is supported only on `(0,1)` / `(1,0)`.
-/
theorem perturbed_holonomy_full_adjoint_implies_defect_vanishes {N : ℕ} (hN3 : 3 ≤ N)
    {ρ : ℂ} (hAdj : perturbedHolonomyFullAdjointAt N hN3 ρ) :
    associatorHolonomyDefectVanishesAt N hN3 ρ := by
  unfold associatorHolonomyDefectVanishesAt
  have hz := perturb_adjoint_01_weight_eq_neg hN3 hAdj
  ext i j
  simp only [cascadeAssociatorHolonomyPerturb, Matrix.add_apply, Matrix.of_apply]
  by_cases hij01 : (i : ℕ) = 0 ∧ (j : ℕ) = 1
  · rcases hij01 with ⟨hi0, hj1⟩
    simp [hi0, hj1, hz, add_neg_cancel]
  · by_cases hij10 : (i : ℕ) = 1 ∧ (j : ℕ) = 0
    · rcases hij10 with ⟨hi1, hj0⟩
      have h10 :
          -star (cascadeAssociatorHolonomyWeight (1 - ρ)) +
            -star (cascadeAssociatorHolonomyWeight ρ) = 0 := by
        rw [hz, star_neg, neg_neg, add_neg_cancel]
      simpa [hi1, hj0] using h10
    · have hi0j1 : ¬((i : ℕ) = 0 ∧ (j : ℕ) = 1) := hij01
      have hi1j0 : ¬((i : ℕ) = 1 ∧ (j : ℕ) = 0) := hij10
      have hj0i1 : ¬((j : ℕ) = 0 ∧ (i : ℕ) = 1) := by
        intro h; rcases h with ⟨hj0, hi1⟩; exact hi1j0 ⟨hi1, hj0⟩
      have hj1i0 : ¬((j : ℕ) = 1 ∧ (i : ℕ) = 0) := by
        intro h; rcases h with ⟨hj1, hi0⟩; exact hi0j1 ⟨hi0, hj1⟩
      simp [hi0j1, hi1j0, hj0i1, hj1i0]

/--
**Defect ↔ weight oppositeness:** for the sparse `(0,1)` associator sheet, defect
cancellation is exactly `z(1-ρ) = -z(ρ)`.
-/
theorem associator_holonomy_defect_vanishes_iff_weight_opposite {N : ℕ} (hN3 : 3 ≤ N)
    {ρ : ℂ} :
    associatorHolonomyDefectVanishesAt N hN3 ρ ↔
      cascadeAssociatorHolonomyWeight (1 - ρ) = -cascadeAssociatorHolonomyWeight ρ := by
  constructor
  · intro hDefect
    have h01 := congrArg (fun M => M (fin0 N hN3) (fin1 N hN3)) hDefect
    simp [associatorHolonomyDefectVanishesAt, cascadeAssociatorHolonomyPerturb, Matrix.add_apply,
      Matrix.of_apply, fin0, fin1] at h01
    exact eq_neg_iff_add_eq_zero.mpr h01
  · intro hz
    unfold associatorHolonomyDefectVanishesAt
    ext i j
    simp only [cascadeAssociatorHolonomyPerturb, Matrix.add_apply, Matrix.of_apply]
    by_cases hij01 : (i : ℕ) = 0 ∧ (j : ℕ) = 1
    · rcases hij01 with ⟨hi0, hj1⟩
      simp [hi0, hj1, hz, add_neg_cancel]
    · by_cases hij10 : (i : ℕ) = 1 ∧ (j : ℕ) = 0
      · rcases hij10 with ⟨hi1, hj0⟩
        have h10 :
            -star (cascadeAssociatorHolonomyWeight (1 - ρ)) +
              -star (cascadeAssociatorHolonomyWeight ρ) = 0 := by
          rw [hz, star_neg, neg_neg, add_neg_cancel]
        simpa [hi1, hj0] using h10
      · have hi0j1 : ¬((i : ℕ) = 0 ∧ (j : ℕ) = 1) := hij01
        have hi1j0 : ¬((i : ℕ) = 1 ∧ (j : ℕ) = 0) := hij10
        have hj0i1 : ¬((j : ℕ) = 0 ∧ (i : ℕ) = 1) := by
          intro h; rcases h with ⟨hj0, hi1⟩; exact hi1j0 ⟨hi1, hj0⟩
        have hj1i0 : ¬((j : ℕ) = 1 ∧ (i : ℕ) = 0) := by
          intro h; rcases h with ⟨hj1, hi0⟩; exact hi0j1 ⟨hi0, hj1⟩
        simp [hi0j1, hi1j0, hj0i1, hj1i0]

/--
On the critical line, `z(1-ρ)` reflects the `(6,5)` spectral lines across FE while the
channel modulus is height-blind (`Re(1-ρ) = Re ρ = 1/2`).
-/
theorem cascade_associator_holonomy_weight_at_one_minus_on_line {ρ : ℂ}
    (hs : ρ.re = (1 / 2 : ℝ)) :
    cascadeAssociatorHolonomyWeight (1 - ρ) =
      Complex.I * Real.sqrt (octAssociatorChannel 6 5 11 ρ) *
        star (so4SpectralLine 6 ρ) * star (so4SpectralLine 5 ρ) := by
  unfold cascadeAssociatorHolonomyWeight
  have h6 := (transformer_entry_adjoint_iff (by decide : 2 ≤ 6)).mpr hs
  have h5 := (transformer_entry_adjoint_iff (by decide : 2 ≤ 5)).mpr hs
  have hch :
      octAssociatorChannel 6 5 11 (1 - ρ) = octAssociatorChannel 6 5 11 ρ := by
    rw [octAssociatorChannel_eq (by decide) (by decide) (by decide),
      octAssociatorChannel_eq (by decide) (by decide) (by decide)]
    have hσ1 : (1 - ρ).re = (1 / 2 : ℝ) := by
      calc (1 - ρ).re = 1 - ρ.re := by simp [Complex.sub_re, Complex.one_re]
        _ = 1 / 2 := by rw [hs]; norm_num
    rw [hσ1, hs]
  rw [hch, h6, h5]
  simp only [starRingEnd_apply, star, mul_comm (so4SpectralLine 5 ρ)]

/--
After cancelling the shared `I·sqrt(channel)` factor on the line, weight oppositeness
is equivalent to the `(0,1)` star-factor identity on cascade slots `(6,5)`.
-/
theorem cascade_weight_opposite_iff_star_spectral_opposed {ρ : ℂ}
    (hs : ρ.re = (1 / 2 : ℝ)) (hch : 0 < octAssociatorChannel 6 5 11 ρ) :
    cascadeAssociatorHolonomyWeight (1 - ρ) = -cascadeAssociatorHolonomyWeight ρ ↔
      star (so4SpectralLine 6 ρ) * star (so4SpectralLine 5 ρ) =
        -(so4SpectralLine 6 ρ * so4SpectralLine 5 ρ) := by
  rw [cascade_associator_holonomy_weight_at_one_minus_on_line hs]
  unfold cascadeAssociatorHolonomyWeight
  have hsqrt : 0 < Real.sqrt (octAssociatorChannel 6 5 11 ρ) :=
    Real.sqrt_pos.mpr hch
  have hIz : Complex.I * Real.sqrt (octAssociatorChannel 6 5 11 ρ) ≠ 0 := by
    simpa using mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hsqrt.ne')
  constructor
  · intro h
    exact mul_left_cancel₀ hIz (by simpa [mul_assoc, mul_left_comm, mul_comm] using h)
  · intro h
    rw [mul_assoc (Complex.I * Real.sqrt (octAssociatorChannel 6 5 11 ρ)), h,
      mul_neg, mul_assoc (Complex.I * Real.sqrt (octAssociatorChannel 6 5 11 ρ))]

/--
**Proved algebraic pin (no RH input):** if the perturbed operator is adjoint-across-FE and
the associator defect cancels, the diagonal backbone is adjoint-across-FE, hence
`Re ρ = 1/2`.
-/
theorem perturbed_holonomy_defect_and_adjoint_forces_critical_line {N : ℕ} (hN3 : 3 ≤ N)
    {ρ : ℂ} (hAdj : perturbedHolonomyFullAdjointAt N hN3 ρ)
    (hDefect : associatorHolonomyDefectVanishesAt N hN3 ρ) :
    ρ.re = (1 / 2 : ℝ) := by
  unfold perturbedHolonomyFullAdjointAt at hAdj
  have hP := cascadeAssociatorHolonomyPerturb_neg_conjTranspose N hN3 ρ
  rw [harmonicCascadeHolonomyTransformerAssociatorPerturb, harmonicCascadeHolonomyTransformerAssociatorPerturb,
    Matrix.conjTranspose_add, hP] at hAdj
  have hpin :
      harmonicCascadeHolonomyTransformer N (two_le_of_three_le hN3) (1 - ρ) -
          (harmonicCascadeHolonomyTransformer N (two_le_of_three_le hN3) ρ)ᴴ +
        (cascadeAssociatorHolonomyPerturb N hN3 (1 - ρ) +
          cascadeAssociatorHolonomyPerturb N hN3 ρ) = 0 := by
    have hrearr :=
      congrArg
        (fun M =>
          M - (harmonicCascadeHolonomyTransformer N (two_le_of_three_le hN3) ρ)ᴴ +
            cascadeAssociatorHolonomyPerturb N hN3 ρ)
        hAdj
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hrearr
  rw [hDefect, add_zero] at hpin
  exact (harmonic_cascade_holonomy_transformer_adjoint_iff (two_le_of_three_le hN3)).mp
    (sub_eq_zero.mp hpin)

/--
**Single-hypothesis pin:** full perturbed adjoint already forces defect cancellation,
hence diagonal adjoint across FE and `Re ρ = 1/2`.  Off-line points cannot carry
full perturbed adjoint because the diagonal defect is nonzero there.
-/
theorem perturbed_holonomy_full_adjoint_forces_critical_line {N : ℕ} (hN3 : 3 ≤ N)
    {ρ : ℂ} (hAdj : perturbedHolonomyFullAdjointAt N hN3 ρ) :
    ρ.re = (1 / 2 : ℝ) :=
  perturbed_holonomy_defect_and_adjoint_forces_critical_line hN3 hAdj
    (perturbed_holonomy_full_adjoint_implies_defect_vanishes hN3 hAdj)

theorem off_line_excludes_perturbed_holonomy_full_adjoint {N : ℕ} (hN3 : 3 ≤ N)
    {ρ : ℂ} (hOff : ρ.re ≠ (1 / 2 : ℝ)) :
    ¬ perturbedHolonomyFullAdjointAt N hN3 ρ := by
  intro hAdj
  exact hOff (perturbed_holonomy_full_adjoint_forces_critical_line hN3 hAdj)

theorem harmonic_cascade_associator_perturb_det_formula (s : ℂ) :
    Matrix.det (harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) s) =
      so4SpectralLine 11 s *
        (so4SpectralLine 6 s * so4SpectralLine 5 s +
          cascadeAssociatorHolonomyWeight s * star (cascadeAssociatorHolonomyWeight s)) := by
  simp [harmonicCascadeHolonomyTransformerAssociatorPerturb, Matrix.det_fin_three,
    harmonicCascadeHolonomyTransformer, Matrix.diagonal_apply_eq, cascadeAssociatorHolonomyPerturb,
    Matrix.of_apply, harmonicCascadeTrial_zero, harmonicCascadeTrial_one, harmonicCascadeTrial_two,
    Matrix.add_apply, mul_comm, mul_left_comm, mul_assoc]
  ring

theorem harmonic_cascade_associator_perturb_det_ne_diagonal_product (s : ℂ)
    (hch : 0 < octAssociatorChannel 6 5 11 s) :
    Matrix.det (harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) s) ≠
      so4SpectralLine 6 s * so4SpectralLine 5 s * so4SpectralLine 11 s := by
  intro heq
  have hz := cascadeAssociatorHolonomyWeight_ne_zero hch
  rw [harmonic_cascade_associator_perturb_det_formula] at heq
  have hw : cascadeAssociatorHolonomyWeight s * star (cascadeAssociatorHolonomyWeight s) ≠ 0 := by
    intro h0
    exact hz ((mul_eq_zero.mp h0).resolve_right (star_ne_zero.mpr hz))
  have hd11ne : so4SpectralLine 11 s ≠ 0 := by
    intro h0
    have hpos : 0 < ‖so4SpectralLine 11 s‖ := by
      rw [so4SpectralLine_norm (Nat.zero_lt_of_lt (show 0 < 11 by decide)) s]
      exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 11) _
    rw [h0, norm_zero] at hpos
    exact hpos.false
  have hfactor :
      so4SpectralLine 6 s * so4SpectralLine 5 s +
          cascadeAssociatorHolonomyWeight s * star (cascadeAssociatorHolonomyWeight s) =
        so4SpectralLine 6 s * so4SpectralLine 5 s :=
    mul_left_cancel₀ hd11ne (by
      calc so4SpectralLine 11 s *
            (so4SpectralLine 6 s * so4SpectralLine 5 s +
              cascadeAssociatorHolonomyWeight s * star (cascadeAssociatorHolonomyWeight s))
          = so4SpectralLine 6 s * so4SpectralLine 5 s * so4SpectralLine 11 s := heq
        _ = so4SpectralLine 11 s * (so4SpectralLine 6 s * so4SpectralLine 5 s) := by
          ring)
  have hzero : cascadeAssociatorHolonomyWeight s * star (cascadeAssociatorHolonomyWeight s) = 0 := by
    have := congrArg (fun t => t - so4SpectralLine 6 s * so4SpectralLine 5 s) hfactor
    simpa [add_sub_cancel_right, sub_self] using this
  exact hw hzero

private theorem complex_neg_eq (z : ℂ) : -z = { re := -z.re, im := -z.im } := by
  simp [Complex.ext_iff]

private theorem M_perturb_00 (s : ℂ) :
    harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) s 0 0 =
      so4SpectralLine 6 s := by
  simp [harmonicCascadeHolonomyTransformerAssociatorPerturb, Matrix.add_apply,
    harmonicCascadeHolonomyTransformer, Matrix.diagonal_apply_eq, harmonicCascadeTrial_zero,
    cascadeAssociatorHolonomyPerturb, Matrix.of_apply, fin0₃, fin1₃]

private theorem M_perturb_01 (s : ℂ) :
    harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) s 0 1 =
      cascadeAssociatorHolonomyWeight s := by
  simp [harmonicCascadeHolonomyTransformerAssociatorPerturb, Matrix.add_apply,
    harmonicCascadeHolonomyTransformer, Matrix.diagonal_apply_eq, harmonicCascadeTrial_zero,
    harmonicCascadeTrial_one, cascadeAssociatorHolonomyPerturb, Matrix.of_apply, fin0₃, fin1₃]

private theorem M_perturb_10 (s : ℂ) :
    harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) s 1 0 =
      -star (cascadeAssociatorHolonomyWeight s) := by
  simp [harmonicCascadeHolonomyTransformerAssociatorPerturb, Matrix.add_apply,
    harmonicCascadeHolonomyTransformer, Matrix.diagonal_apply_eq, harmonicCascadeTrial_one,
    cascadeAssociatorHolonomyPerturb, Matrix.of_apply, fin0₃, fin1₃]

private theorem M_perturb_11 (s : ℂ) :
    harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) s 1 1 =
      so4SpectralLine 5 s := by
  simp [harmonicCascadeHolonomyTransformerAssociatorPerturb, Matrix.add_apply,
    harmonicCascadeHolonomyTransformer, Matrix.diagonal_apply_eq, harmonicCascadeTrial_one,
    cascadeAssociatorHolonomyPerturb, Matrix.of_apply, fin0₃, fin1₃]

private theorem M_perturb_02 (s : ℂ) :
    harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) s 0 2 = 0 := by
  simp [harmonicCascadeHolonomyTransformerAssociatorPerturb, Matrix.add_apply,
    harmonicCascadeHolonomyTransformer, Matrix.diagonal_apply_eq, harmonicCascadeTrial_two,
    cascadeAssociatorHolonomyPerturb, Matrix.of_apply, fin0₃, fin2₃]

private theorem M_perturb_12 (s : ℂ) :
    harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) s 1 2 = 0 := by
  simp [harmonicCascadeHolonomyTransformerAssociatorPerturb, Matrix.add_apply,
    harmonicCascadeHolonomyTransformer, Matrix.diagonal_apply_eq, harmonicCascadeTrial_two,
    cascadeAssociatorHolonomyPerturb, Matrix.of_apply, fin1₃, fin2₃]

private theorem M_perturb_20 (s : ℂ) :
    harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) s 2 0 = 0 := by
  simp [harmonicCascadeHolonomyTransformerAssociatorPerturb, Matrix.add_apply,
    harmonicCascadeHolonomyTransformer, Matrix.diagonal_apply_eq, harmonicCascadeTrial_two,
    cascadeAssociatorHolonomyPerturb, Matrix.of_apply, fin2₃]

private theorem M_perturb_21 (s : ℂ) :
    harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) s 2 1 = 0 := by
  simp [harmonicCascadeHolonomyTransformerAssociatorPerturb, Matrix.add_apply,
    harmonicCascadeHolonomyTransformer, Matrix.diagonal_apply_eq, harmonicCascadeTrial_two,
    cascadeAssociatorHolonomyPerturb, Matrix.of_apply, fin2₃, fin1₃]

private theorem associator_perturb_mmConj_01_three (s : ℂ) :
    (harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) s *
        (harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) s)ᴴ) fin0₃ fin1₃ =
      cascadeAssociatorHolonomyWeight s *
        (star (so4SpectralLine 5 s) - so4SpectralLine 6 s) := by
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp [fin0₃, fin1₃, Matrix.conjTranspose_apply, M_perturb_00, M_perturb_01, M_perturb_02,
    M_perturb_10, M_perturb_11, M_perturb_12, star, star_neg, star_star, so4SpectralLine]
  rw [← complex_neg_eq (cascadeAssociatorHolonomyWeight s)]
  ring

private theorem associator_perturb_conjM_01_three (s : ℂ) :
    ((harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) s)ᴴ *
        harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) s) fin0₃ fin1₃ =
      cascadeAssociatorHolonomyWeight s *
        (star (so4SpectralLine 6 s) - so4SpectralLine 5 s) := by
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp [fin0₃, fin1₃, Matrix.conjTranspose_apply, M_perturb_00, M_perturb_01, M_perturb_02,
    M_perturb_10, M_perturb_11, M_perturb_12, M_perturb_20, M_perturb_21, star, star_neg, star_star,
    so4SpectralLine]
  rw [← complex_neg_eq (cascadeAssociatorHolonomyWeight s)]
  ring

theorem harmonic_cascade_associator_perturb_commutator_01_three (s : ℂ) :
    ((harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) s *
          (harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) s)ᴴ) fin0₃ fin1₃ -
        ((harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) s)ᴴ *
            harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) s) fin0₃ fin1₃) =
      cascadeAssociatorHolonomyWeight s *
        (star (so4SpectralLine 5 s) + so4SpectralLine 5 s -
          star (so4SpectralLine 6 s) - so4SpectralLine 6 s) := by
  rw [associator_perturb_mmConj_01_three, associator_perturb_conjM_01_three]
  ring

theorem harmonic_cascade_associator_perturb_not_normal_01_three (s : ℂ)
    (hch : 0 < octAssociatorChannel 6 5 11 s)
    (hspec_conj :
      star (so4SpectralLine 5 s) + so4SpectralLine 5 s ≠
        star (so4SpectralLine 6 s) + so4SpectralLine 6 s) :
    (harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) s *
        (harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) s)ᴴ) fin0₃ fin1₃ ≠
      ((harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) s)ᴴ *
          harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) s) fin0₃ fin1₃ := by
  rw [associator_perturb_mmConj_01_three, associator_perturb_conjM_01_three]
  have hz := cascadeAssociatorHolonomyWeight_ne_zero hch
  intro heq
  have hsum :
      star (so4SpectralLine 5 s) + so4SpectralLine 5 s =
        star (so4SpectralLine 6 s) + so4SpectralLine 6 s := by
    have hcancel := mul_left_cancel₀ hz heq
    have hzero :
        star (so4SpectralLine 5 s) + so4SpectralLine 5 s -
          (star (so4SpectralLine 6 s) + so4SpectralLine 6 s) = 0 := by
      have hstep :
          star (so4SpectralLine 5 s) + so4SpectralLine 5 s -
            (star (so4SpectralLine 6 s) + so4SpectralLine 6 s) =
          (star (so4SpectralLine 5 s) - so4SpectralLine 6 s) -
            (star (so4SpectralLine 6 s) - so4SpectralLine 5 s) := by ring
      rw [hstep, hcancel, sub_self]
    exact sub_eq_zero.mp hzero
  exact hspec_conj (by rw [← sub_eq_zero, hsum, sub_self])

theorem harmonic_cascade_associator_perturb_not_normal_three (s : ℂ)
    (hch : 0 < octAssociatorChannel 6 5 11 s)
    (hspec_conj :
      star (so4SpectralLine 5 s) + so4SpectralLine 5 s ≠
        star (so4SpectralLine 6 s) + so4SpectralLine 6 s) :
    harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) s *
        (harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) s)ᴴ ≠
      (harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) s)ᴴ *
        harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) s := by
  intro heq
  exact harmonic_cascade_associator_perturb_not_normal_01_three s hch hspec_conj
    (congrArg (fun M => M fin0₃ fin1₃) heq)

theorem associator_perturb_non_normal_at_of_witness {ρ : ℂ}
    (h : associatorPerturbNonNormalityWitnessAt ρ) :
    harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) ρ *
        (harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) ρ)ᴴ ≠
      (harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) ρ)ᴴ *
        harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) ρ := by
  rcases h with ⟨hch, hspec⟩
  exact harmonic_cascade_associator_perturb_not_normal_three ρ hch hspec

structure HarmonicHolonomyAssociatorPerturbBundle (N : ℕ) (hN3 : 3 ≤ N) where
  perturb_antHermitian :
    ∀ s, (cascadeAssociatorHolonomyPerturb N hN3 s)ᴴ = -cascadeAssociatorHolonomyPerturb N hN3 s
  diagonal_adjoint_on_line :
    ∀ {s}, s.re = (1 / 2 : ℝ) →
      harmonicCascadeHolonomyTransformer N (two_le_of_three_le hN3) (1 - s) =
        (harmonicCascadeHolonomyTransformer N (two_le_of_three_le hN3) s)ᴴ
  fe_backbone :
    ∀ s,
      (harmonicCascadeHolonomyTransformer N (two_le_of_three_le hN3) s *
          harmonicCascadeHolonomyTransformer N (two_le_of_three_le hN3) (1 - s) =
        Matrix.diagonal fun i : Fin N => ((harmonicCascadeTrial (i : ℕ) : ℂ))⁻¹) ∧
        (octAssociatorChannel 6 5 11 s * octAssociatorChannel 6 5 11 (1 - s) =
          4 / ((6 * 5 * 11 : ℕ) : ℝ) ^ (2 : ℕ))

noncomputable def harmonicHolonomyAssociatorPerturbBundle_default (N : ℕ) (hN3 : 3 ≤ N) :
    HarmonicHolonomyAssociatorPerturbBundle N hN3 where
  perturb_antHermitian := cascadeAssociatorHolonomyPerturb_neg_conjTranspose N hN3
  diagonal_adjoint_on_line := harmonic_cascade_associator_perturb_diagonal_adjoint_on_critical_line hN3
  fe_backbone := harmonic_cascade_associator_perturb_fe_on_critical_line hN3

/-! ## Route 4 — associator perturbation wired to the holonomy frontier -/

/--
**Associator route bundle:** octonionic associator sheet + diagonal adjoint on the line +
FE backbone for the cascade prefix `(6,5,11,…)`.
-/
def HarmonicHolonomyAssociatorPerturbRoute (N : ℕ) (hN3 : 3 ≤ N) : Prop :=
  Nonempty (HarmonicHolonomyAssociatorPerturbBundle N hN3)

theorem harmonic_holonomy_associator_perturb_route_three :
    HarmonicHolonomyAssociatorPerturbRoute 3 (by decide) :=
  ⟨harmonicHolonomyAssociatorPerturbBundle_default 3 (by decide)⟩

/--
**Four-route holonomy frontier:** the original three-route stack plus the associator
perturbation certificates on the cascade prefix.
-/
def HarmonicHolonomyAssociatorCriticalLineFrontier : Prop :=
  HarmonicHolonomyCriticalLineFrontier ∧
    HarmonicHolonomyAssociatorPerturbRoute 3 (by decide)

theorem harmonic_holonomy_associator_critical_line_frontier :
    HarmonicHolonomyAssociatorCriticalLineFrontier :=
  ⟨harmonic_holonomy_critical_line_frontier, harmonic_holonomy_associator_perturb_route_three⟩

/--
**Refined Hilbert–Pólya face at zeros:** RH still pins the diagonal adjoint across FE;
the associator defect is the explicit split `M(1-ρ) - M(ρ)ᴴ = P(1-ρ) + P(ρ)` on the line.
Full perturbed adjoint holds exactly when the associator sheet cancels (`P(1-ρ)+P(ρ)=0`).
-/
theorem RH_iff_holonomy_associator_diagonal_adjoint_at_zeros {N : ℕ} (hN3 : 3 ≤ N) :
    RiemannHypothesis ↔
      ∀ ρ : ℂ, IsNontrivialZetaZero ρ →
        harmonicCascadeHolonomyTransformer N (two_le_of_three_le hN3) (1 - ρ) =
          (harmonicCascadeHolonomyTransformer N (two_le_of_three_le hN3) ρ)ᴴ :=
  RH_iff_holonomy_cascade_adjoint_at_zeros (two_le_of_three_le hN3)

theorem perturbed_holonomy_adjoint_defect_on_critical_line {N : ℕ} (hN3 : 3 ≤ N)
    {ρ : ℂ} (hs : ρ.re = (1 / 2 : ℝ)) :
    harmonicCascadeHolonomyTransformerAssociatorPerturb N hN3 (1 - ρ) -
        (harmonicCascadeHolonomyTransformerAssociatorPerturb N hN3 ρ)ᴴ =
      cascadeAssociatorHolonomyPerturb N hN3 (1 - ρ) +
        cascadeAssociatorHolonomyPerturb N hN3 ρ :=
  harmonic_cascade_associator_perturb_adjoint_defect_on_critical_line hN3 hs

theorem perturbed_holonomy_full_adjoint_at_zero_iff_defect_vanishes {N : ℕ} (hN3 : 3 ≤ N)
    {ρ : ℂ} (hs : ρ.re = (1 / 2 : ℝ)) :
    harmonicCascadeHolonomyTransformerAssociatorPerturb N hN3 (1 - ρ) =
        (harmonicCascadeHolonomyTransformerAssociatorPerturb N hN3 ρ)ᴴ ↔
      cascadeAssociatorHolonomyPerturb N hN3 (1 - ρ) +
          cascadeAssociatorHolonomyPerturb N hN3 ρ =
        0 := by
  have hdef := harmonic_cascade_associator_perturb_adjoint_defect_on_critical_line hN3 hs
  constructor
  · intro hAdj
    have hzero :
        harmonicCascadeHolonomyTransformerAssociatorPerturb N hN3 (1 - ρ) -
            (harmonicCascadeHolonomyTransformerAssociatorPerturb N hN3 ρ)ᴴ = 0 := by
      rw [hAdj, sub_self]
    exact hdef.symm.trans hzero
  · intro hP
    rw [hP] at hdef
    exact sub_eq_zero.mp hdef

theorem perturbed_holonomy_on_line_defect_vanishes_iff_full_adjoint {N : ℕ} (hN3 : 3 ≤ N)
    {ρ : ℂ} (hs : ρ.re = (1 / 2 : ℝ)) :
    perturbedHolonomyFullAdjointAt N hN3 ρ ↔
      associatorHolonomyDefectVanishesAt N hN3 ρ :=
  perturbed_holonomy_full_adjoint_at_zero_iff_defect_vanishes hN3 hs

/--
**User-facing pin (conditional on full adjoint):** defect cancellation at a nontrivial
zero together with σ–t coupling data forces the critical line once perturbed adjoint
across FE is available.  Coupling alone is not used in the proof — it packages the
HQIV axiom stack for the missing zero-level adjoint upgrade.
-/
theorem defect_vanishes_at_zero_implies_critical_line {N : ℕ} (hN3 : 3 ≤ N) {ρ : ℂ}
    (_hζ : IsNontrivialZetaZero ρ)
    (_hDefect : associatorHolonomyDefectVanishesAt N hN3 ρ)
    (_hCoupling : SigmaTPhaseCouplingAt ρ)
    (hAdj : perturbedHolonomyFullAdjointAt N hN3 ρ) :
    ρ.re = (1 / 2 : ℝ) :=
  perturbed_holonomy_full_adjoint_forces_critical_line hN3 hAdj

/--
**Route-4 discharge target (RH-hard):** at a nontrivial zero, defect cancellation together
with σ–t coupling and the non-normality witness should force the critical line.
(Once full adjoint is available, `perturbed_holonomy_full_adjoint_forces_critical_line`
already pins the line; defect vanishing is then automatic.)
-/
def AssociatorDefectAtZeroForcesCriticalLine : Prop :=
  ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ →
    associatorHolonomyDefectVanishesAt 3 (by decide) ρ →
      SigmaTPhaseCouplingAt ρ →
        associatorPerturbNonNormalityWitnessAt ρ →
          ρ.re = (1 / 2 : ℝ)

/--
**Zero-level adjoint target:** nontrivial zero + HQIV coupling witness + non-normality
certificate should imply full perturbed adjoint across FE.  Together with
`perturbed_holonomy_full_adjoint_forces_critical_line`, this discharges RH once the
non-normality witness holds at every zero.
-/
def NontrivialZeroForcesPerturbedHolonomyAdjoint : Prop :=
  ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ →
    SigmaTPhaseCouplingAt ρ →
      associatorPerturbNonNormalityWitnessAt ρ →
        perturbedHolonomyFullAdjointAt 3 (by decide) ρ

theorem associator_defect_at_zero_forces_critical_line_of_adjoint_target
    (hAdjTarget : NontrivialZeroForcesPerturbedHolonomyAdjoint) :
    AssociatorDefectAtZeroForcesCriticalLine := by
  intro ρ hζ _hDefect hCoupling hNon
  exact perturbed_holonomy_full_adjoint_forces_critical_line (by decide)
    (hAdjTarget hζ hCoupling hNon)

theorem RH_of_nontrivial_zero_forces_perturbed_holonomy_adjoint
    (hWitnessAll :
      ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → associatorPerturbNonNormalityWitnessAt ρ)
    (hAdjTarget : NontrivialZeroForcesPerturbedHolonomyAdjoint) :
    RiemannHypothesis := by
  intro ρ hzz hnt h1
  have hζ : IsNontrivialZetaZero ρ := ⟨hzz, hnt, h1⟩
  exact perturbed_holonomy_full_adjoint_forces_critical_line (by decide)
    (hAdjTarget hζ (sigma_t_coupling_at_every_nontrivial_zero hζ) (hWitnessAll hζ))

theorem RH_of_associator_frontier_and_adjoint_target
    (_hFront : HarmonicHolonomyAssociatorCriticalLineFrontier)
    (hWitnessAll :
      ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → associatorPerturbNonNormalityWitnessAt ρ)
    (hAdjTarget : NontrivialZeroForcesPerturbedHolonomyAdjoint) :
    RiemannHypothesis :=
  RH_of_nontrivial_zero_forces_perturbed_holonomy_adjoint hWitnessAll hAdjTarget

theorem RH_of_associator_frontier_and_defect_at_zero_forcing
    (hFront : HarmonicHolonomyAssociatorCriticalLineFrontier)
    (hDefectAll :
      ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ →
        associatorHolonomyDefectVanishesAt 3 (by decide) ρ)
    (hWitnessAll :
      ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → associatorPerturbNonNormalityWitnessAt ρ)
    (hTarget : AssociatorDefectAtZeroForcesCriticalLine) :
    RiemannHypothesis := by
  intro ρ hzz hnt h1
  have hζ : IsNontrivialZetaZero ρ := ⟨hzz, hnt, h1⟩
  exact hTarget hζ (hDefectAll hζ)
    (sigma_t_coupling_witness_from_hqiv_axiom_stack hFront.1.1 hζ) (hWitnessAll hζ)

theorem RH_of_associator_frontier_defect_witness_and_adjoint_target
    (hFront : HarmonicHolonomyAssociatorCriticalLineFrontier)
    (hWitnessAll :
      ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → associatorPerturbNonNormalityWitnessAt ρ)
    (hAdjTarget : NontrivialZeroForcesPerturbedHolonomyAdjoint) :
    RiemannHypothesis :=
  RH_of_associator_frontier_and_adjoint_target hFront hWitnessAll hAdjTarget

theorem RH_of_harmonic_holonomy_associator_frontier_and_sigma_t_forcing
    (h : HarmonicHolonomyAssociatorCriticalLineFrontier)
    (hForce : SigmaTPhaseCouplingForcesCriticalLine) :
    RiemannHypothesis :=
  RH_of_harmonic_holonomy_frontier_and_sigma_t_forcing h.1 hForce

end

end Hqiv.Story

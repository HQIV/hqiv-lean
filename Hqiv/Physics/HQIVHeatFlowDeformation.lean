import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Norm
import Hqiv.Physics.DivisionAlgebraZetaScaffold

/-!
# Discrete heat-flow weight (general) and HQIV shell sums

## General construction (not HQIV-specific)

On any discrete index `m : ℕ`, a **nonnegative “time” surrogate** `u m : ℝ` and a deformation parameter
`τ : ℝ` give the Gaussian factor

`exp (-τ * u m)`.

This is the same **functional form** used in the heat-flow / de Bruijn–Newman picture for `ξ` (time
evolution / deformation of a completed zeta object), as developed and popularized in work of
**Terence Tao** and others. It answers a general bookkeeping question: *how to damp a sequence of
terms along an effective time coordinate without changing the τ = 0 object.* We credit that line of
work for the idea; nothing here proves classical statements about `Λ` or a heat equation for `ξ`.

The general definition is `Hqiv.Physics.discreteHeatKernelWeight` (and the optional alias
`taoDiscreteHeatKernelWeight`).

## HQIV instantiation

Here `u m` is taken from the existing ladder surrogate `tHQIV T_ref m` (`DivisionAlgebraZetaScaffold`),
and the damped terms are `zetaHQIVTerm`. The aggregate `HQIVDeformedSum` is therefore this general
deformation **specialized** to HQIV data — not an extra axiom.

**Proved ladder link:** `tempLadderConserved T_ref m * tHQIV T_ref (m + 1) = 1` and, on successor shells,
`hqivHeatKernelWeight τ … (m + 1) = exp (-τ / tempLadderConserved T_ref m)` (see
`tempLadderConserved_mul_tHQIV_succ_eq_one`, `hqivHeatKernelWeight_succ_eq_exp_neg_div_tempLadderConserved`).
So the heat factor is not an ad hoc extra: it ties directly to the conserved-temperature bookkeeping.

**Not** claimed: classical de Bruijn–Newman `Λ`, a functional equation, or zero locations for the
deformed sum.

The probe parameter `lambdaHQIV` from `TempLadderForcesLambdaHQIVZero` remains a **separate** HQIV
boundary-lock slot (`τ ↔ λ` is motivational only unless you add explicit axioms).
-/

namespace Hqiv.Physics

open scoped Topology
open Complex Filter

noncomputable section

/-- General discrete heat kernel: `exp (-τ * u)` for real `τ` and surrogate time `u`.

Same functional form as the Gaussian factor in the heat-flow / de Bruijn–Newman deformation
picture (Terry Tao and others); not tied to HQIV data. -/
noncomputable def discreteHeatKernelWeight (τ u : ℝ) : ℝ :=
  Real.exp (-τ * u)

/-- Optional naming alias emphasizing provenance (same function as `discreteHeatKernelWeight`). -/
noncomputable abbrev taoDiscreteHeatKernelWeight (τ u : ℝ) : ℝ :=
  discreteHeatKernelWeight τ u

theorem discreteHeatKernelWeight_pos (τ u : ℝ) : 0 < discreteHeatKernelWeight τ u :=
  Real.exp_pos _

theorem discreteHeatKernelWeight_nonneg (τ u : ℝ) : 0 ≤ discreteHeatKernelWeight τ u :=
  (discreteHeatKernelWeight_pos τ u).le

theorem discreteHeatKernelWeight_eq_one_of_tau_zero (u : ℝ) : discreteHeatKernelWeight 0 u = 1 := by
  simp [discreteHeatKernelWeight]

theorem discreteHeatKernelWeight_le_one_of_nonneg (τ u : ℝ) (hτ : 0 ≤ τ) (hu : 0 ≤ u) :
    discreteHeatKernelWeight τ u ≤ 1 := by
  dsimp [discreteHeatKernelWeight]
  have hneg : -τ * u ≤ 0 := by nlinarith
  exact (Real.exp_le_one_iff.mpr hneg)

/-- More deformation time `τ` (fixed `u ≥ 0`) ⇒ **smaller** weight: `exp` is monotone and `-τ u` is
antitone in `τ`. -/
theorem discreteHeatKernelWeight_antitone_nonneg_u (u : ℝ) (hu : 0 ≤ u) {τ₁ τ₂ : ℝ}
    (hτ : τ₁ ≤ τ₂) : discreteHeatKernelWeight τ₂ u ≤ discreteHeatKernelWeight τ₁ u := by
  dsimp [discreteHeatKernelWeight]
  have hcmp : -τ₂ * u ≤ -τ₁ * u := by nlinarith
  exact Real.exp_le_exp.mpr hcmp

/-- HQIV: compose the general heat weight with `tHQIV T_ref m` (0 at `m = 0`, else `m / T_ref`). -/
noncomputable def hqivHeatKernelWeight (τ T_ref : ℝ) (m : ℕ) : ℝ :=
  discreteHeatKernelWeight τ (tHQIV T_ref m)

theorem hqivHeatKernelWeight_eq_discrete (τ T_ref : ℝ) (m : ℕ) :
    hqivHeatKernelWeight τ T_ref m = discreteHeatKernelWeight τ (tHQIV T_ref m) :=
  rfl

theorem hqivHeatKernelWeight_pos (τ T_ref : ℝ) (m : ℕ) : 0 < hqivHeatKernelWeight τ T_ref m := by
  simpa [hqivHeatKernelWeight] using discreteHeatKernelWeight_pos τ (tHQIV T_ref m)

theorem hqivHeatKernelWeight_nonneg (τ T_ref : ℝ) (m : ℕ) : 0 ≤ hqivHeatKernelWeight τ T_ref m :=
  (hqivHeatKernelWeight_pos τ T_ref m).le

theorem hqivHeatKernelWeight_eq_one_of_tau_zero (T_ref : ℝ) (m : ℕ) :
    hqivHeatKernelWeight 0 T_ref m = 1 := by
  simp [hqivHeatKernelWeight, discreteHeatKernelWeight_eq_one_of_tau_zero]

theorem tHQIV_nonneg (T_ref : ℝ) (m : ℕ) (hT : 0 < T_ref) : 0 ≤ tHQIV T_ref m := by
  cases m with
  | zero => simp [tHQIV]
  | succ m =>
    simp [tHQIV]
    positivity

/-- **Ladder reciprocity:** conserved temperature at shell `m` times `tHQIV` on the *next* shell is `1`.
This is the pure algebra behind “`tempLadderConserved` and `tHQIV` are dual coordinates” on `m+1`. -/
theorem tempLadderConserved_mul_tHQIV_succ_eq_one (T_ref : ℝ) (m : ℕ) (hT : T_ref ≠ 0) :
    tempLadderConserved T_ref m * tHQIV T_ref (Nat.succ m) = 1 := by
  simp [tempLadderConserved, tHQIV]
  have hm1 : (m + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hT, hm1]

/-- On `m + 1`, the heat exponent is `-τ` divided by `tempLadderConserved T_ref m` (horizon shell uses
`tHQIV = 0`, so this form starts at `m = 0` → `Nat.succ m`). -/
theorem hqivHeatKernelWeight_succ_eq_exp_neg_div_tempLadderConserved (τ T_ref : ℝ) (m : ℕ)
    (hT : T_ref ≠ 0) :
    hqivHeatKernelWeight τ T_ref (Nat.succ m) =
      Real.exp (-τ / tempLadderConserved T_ref m) := by
  have hm1 : (m + 1 : ℝ) ≠ 0 := by positivity
  have hexp :
      -τ * tHQIV T_ref (Nat.succ m) = -τ / tempLadderConserved T_ref m := by
    simp [tHQIV, tempLadderConserved, Nat.succ_eq_add_one]
    field_simp [hT, hm1]
  calc
    hqivHeatKernelWeight τ T_ref (Nat.succ m)
        = Real.exp (-τ * tHQIV T_ref (Nat.succ m)) := by simp [hqivHeatKernelWeight, discreteHeatKernelWeight]
    _ = Real.exp (-τ / tempLadderConserved T_ref m) := by rw [hexp]

/-- Fixed shell `m` and `T_ref > 0`: larger `τ` ⇒ smaller HQIV heat weight (pointwise monotonicity in
the deformation parameter). -/
theorem hqivHeatKernelWeight_antitone_in_tau (τ₁ τ₂ : ℝ) (T_ref : ℝ) (m : ℕ) (hT : 0 < T_ref)
    (hτ : τ₁ ≤ τ₂) : hqivHeatKernelWeight τ₂ T_ref m ≤ hqivHeatKernelWeight τ₁ T_ref m := by
  rw [hqivHeatKernelWeight_eq_discrete, hqivHeatKernelWeight_eq_discrete]
  exact discreteHeatKernelWeight_antitone_nonneg_u (tHQIV T_ref m) (tHQIV_nonneg T_ref m hT) hτ

theorem hqivHeatKernelWeight_le_one (τ T_ref : ℝ) (m : ℕ) (hτ : 0 ≤ τ) (hT : 0 < T_ref) :
    hqivHeatKernelWeight τ T_ref m ≤ 1 := by
  rw [hqivHeatKernelWeight_eq_discrete]
  exact discreteHeatKernelWeight_le_one_of_nonneg τ (tHQIV T_ref m) hτ (tHQIV_nonneg T_ref m hT)

/-- One shell term: general heat weight × HQIV lattice term. -/
noncomputable def hqivDeformedLatticeTerm (τ T_ref : ℝ) (δ : ℝ) (φ t : ℝ) (s : ℂ) (m : ℕ) : ℂ :=
  (hqivHeatKernelWeight τ T_ref m : ℂ) * zetaHQIVTerm δ φ t s m

/-- Total deformed sum over shells (HQIV specialization of the discrete heat deformation). -/
noncomputable def HQIVDeformedSum (τ T_ref : ℝ) (δ : ℝ) (φ t : ℝ) (s : ℂ) : ℂ :=
  ∑' m : ℕ, hqivDeformedLatticeTerm τ T_ref δ φ t s m

theorem HQIVDeformedSum_eq_tsum (τ T_ref : ℝ) (δ : ℝ) (φ t : ℝ) (s : ℂ) :
    HQIVDeformedSum τ T_ref δ φ t s = ∑' m : ℕ, hqivDeformedLatticeTerm τ T_ref δ φ t s m :=
  rfl

theorem hqivDeformedLatticeTerm_eq_zetaHQIVTerm_of_tau_zero (T_ref : ℝ) (δ : ℝ) (φ t : ℝ) (s : ℂ)
    (m : ℕ) : hqivDeformedLatticeTerm 0 T_ref δ φ t s m = zetaHQIVTerm δ φ t s m := by
  simp [hqivDeformedLatticeTerm, hqivHeatKernelWeight_eq_one_of_tau_zero, one_mul]

theorem norm_hqivDeformedLatticeTerm_eq (τ T_ref : ℝ) (δ : ℝ) (φ t : ℝ) (s : ℂ) (m : ℕ) :
    ‖hqivDeformedLatticeTerm τ T_ref δ φ t s m‖ =
      hqivHeatKernelWeight τ T_ref m * ‖zetaHQIVTerm δ φ t s m‖ := by
  have hw : ‖(hqivHeatKernelWeight τ T_ref m : ℂ)‖ = hqivHeatKernelWeight τ T_ref m := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hqivHeatKernelWeight_nonneg τ T_ref m)]
  rw [hqivDeformedLatticeTerm, Complex.norm_mul, hw]

theorem norm_hqivDeformedLatticeTerm_le_norm_zeta (τ T_ref : ℝ) (δ : ℝ) (φ t : ℝ) (s : ℂ) (m : ℕ)
    (hτ : 0 ≤ τ) (hT : 0 < T_ref) :
    ‖hqivDeformedLatticeTerm τ T_ref δ φ t s m‖ ≤ ‖zetaHQIVTerm δ φ t s m‖ := by
  rw [norm_hqivDeformedLatticeTerm_eq τ T_ref δ φ t s m]
  have hw : hqivHeatKernelWeight τ T_ref m ≤ 1 := hqivHeatKernelWeight_le_one τ T_ref m hτ hT
  have hnm : 0 ≤ ‖zetaHQIVTerm δ φ t s m‖ := norm_nonneg _
  nlinarith [hqivHeatKernelWeight_nonneg τ T_ref m]

theorem hqivDeformedLatticeTerm_summable_of_re_gt_one (τ T_ref : ℝ) (δ : ℝ) (φ t : ℝ) (s : ℂ)
    (hτ : 0 ≤ τ) (hT : 0 < T_ref) (_hδ : 0 ≤ δ) (hden : ∀ m : ℕ, RindlerDenDeltaPos δ m)
    (hs : 1 < s.re) : Summable (hqivDeformedLatticeTerm τ T_ref δ φ t s) := by
  have h1 : 1 < s.re := hs
  have hps :
      Summable fun m : ℕ => (1 : ℝ) / ((m + 1 : ℝ) ^ s.re) := by
    have h0 := (Real.summable_one_div_nat_add_rpow (a := (1 : ℝ)) (s := s.re)).mpr h1
    refine Summable.congr h0 ?_
    intro n
    have habs : |(n : ℝ) + 1| = (n : ℝ) + 1 :=
      abs_of_nonneg (Nat.cast_add_one_pos n).le
    simp [div_eq_mul_inv, habs]
  have hg :
      Summable fun m : ℕ => (4 : ℝ) ^ (-s.re) * (1 / ((m + 1 : ℝ) ^ s.re)) :=
    Summable.mul_left ((4 : ℝ) ^ (-s.re)) hps
  refine Summable.of_norm_bounded_eventually_nat hg ?_
  filter_upwards [eventually_norm_zeta_le_mul_rpow δ φ t s hden hs] with m hm
  have hde := norm_hqivDeformedLatticeTerm_le_norm_zeta τ T_ref δ φ t s m hτ hT
  exact le_trans hde hm

theorem HQIVDeformedSum_eq_zeta_HQIV_of_tau_zero (h : GlobalDetuningHypothesis) (T_ref : ℝ)
    (φ t β_cum : ℝ) (s : ℂ) :
    HQIVDeformedSum 0 T_ref (delta_auxiliary_phi_per_shell h φ t β_cum) φ t s =
      zeta_HQIV h φ t β_cum s := by
  dsimp [HQIVDeformedSum, zeta_HQIV]
  refine tsum_congr ?_
  intro m
  exact hqivDeformedLatticeTerm_eq_zetaHQIVTerm_of_tau_zero T_ref _ _ _ _ m

end

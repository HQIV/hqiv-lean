import Mathlib.Data.Complex.Basic

import Hqiv.Geometry.GeneralRiemannianRapidityOracle
import Hqiv.Story.S3FortyFiveProjection

/-!
# Higher twiddles as factorization-engine probes

This module formalizes **linear and cubic plastic readouts** as controlled
alternatives to the paper's `45°` equator factor — not as competing zero
locators.  The intended use is a **multi-channel factorization laboratory**:
compare interior assemblies `h_c` when the geometric factor is `free_c` or
`so4PlasticCubicFree` instead of `so4CriticalFactor` (see paper
§`sec:higher-twiddle-probes`).  Cross-talk to critical-line points is expected
to be **semiprime mediated** (Goldbach §); that coupling is not formalized here.

A **linear twiddle** with coefficient `c ∈ (0,1)` reads
`free_c(σ) = c·σ + (1-c)·(1-σ) = (2c-1)σ + (1-c)`.
Its zero (when `2c-1 ≠ 0`) is the vertical line
`σ_c = (c-1)/(2c-1)`; this is the same number as `-(1-c)/(2c-1)` and differs
from the `(1-c)/(2c-1)` form only when one writes the root without simplifying
signs.

Replacing `c` by `1-c` mirrors the zero across `σ = 1/2`:
`σ_{1-c} = 1 - σ_c`.

The **plastic cubic** channel uses the canonical plastic number `ρ > 1` from
`Hqiv.Geometry.GeneralRiemannianRapidityOracle` and the coefficient
`c_ρ = (ρ-1)/ρ = 1 - ρ⁻¹`, with `ρ⁻¹ = ρ² - 1` in `ℤ[ρ]`.

Normalized readouts divide by `N_c = √(c² + (1-c)²)` to match the paper's
`√2` normalization at the quadratic 45° rotation.

## Proved here

* Closed linear form, zero locus, FE swap `free_c(1-σ) = free_{1-c}(σ)`.
* Mirror zero loci `linearTwiddleZero (1-c) = 1 - linearTwiddleZero c`.
* Plastic coefficient in `(0,1)`, inv identity, closed `σ_ρ`, mirror partner.
* Normalized `so4CubicFree` / `so4CubicFreeMirror` and
  `so4CubicFree_one_sub_re` (FE reflection on real parts).
* At `c = 1/√2` the zero is `-1/√2`, not `1/2`; the paper's normalized 45°
  rotation factor is a different readout (`rot45Free`).

## Honest scope

Plastic twiddles relocate the vanishing locus off `σ = 1/2`; they do not prove RH
or locate zeros.  Finite-frame assemblies `h_c^{(N)}` and semiprime explicit-formula
mediation are in `S3HigherTwiddleFactorizationProbe` and
`S3SemiprimeExplicitFormulaMediation`.
-/

namespace Hqiv.Story

noncomputable section

open Hqiv.Geometry

/-! ## Linear twiddle -/

/-- Unnormalized linear free readout: `c·σ + (1-c)·(1-σ)`. -/
noncomputable def linearTwiddleFree (c σ : ℝ) : ℝ :=
  c * σ + (1 - c) * (1 - σ)

theorem linearTwiddleFree_eq (c σ : ℝ) :
    linearTwiddleFree c σ = (2 * c - 1) * σ + (1 - c) := by
  unfold linearTwiddleFree
  ring

/-- Vertical zero of the linear twiddle when `2c-1 ≠ 0`. -/
noncomputable def linearTwiddleZero (c : ℝ) : ℝ :=
  (c - 1) / (2 * c - 1)

theorem linearTwiddle_zero_iff {c σ : ℝ} (h : 2 * c - 1 ≠ 0) :
    linearTwiddleFree c σ = 0 ↔ σ = linearTwiddleZero c := by
  rw [linearTwiddleFree_eq]
  have hden : (2 * c - 1) ≠ 0 := h
  constructor
  · intro h0
    have hmul : σ * (2 * c - 1) = c - 1 := by
      rw [mul_comm]
      linarith
    simpa [linearTwiddleZero] using (eq_div_iff hden).mpr hmul
  · intro hσ
    rw [hσ, linearTwiddleZero]
    field_simp [hden]
    ring

/-- Functional-equation swap on real `σ`: `free_c(1-σ) = free_{1-c}(σ)`. -/
theorem linearTwiddleFree_fe_swap (c σ : ℝ) :
    linearTwiddleFree c (1 - σ) = linearTwiddleFree (1 - c) σ := by
  unfold linearTwiddleFree
  ring

/-- Mirror symmetry of zero loci across `σ = 1/2`. -/
theorem linearTwiddleZero_mirror {c : ℝ}
    (h : 2 * c - 1 ≠ 0) (h' : 2 * (1 - c) - 1 ≠ 0) :
    linearTwiddleZero (1 - c) = 1 - linearTwiddleZero c := by
  have hz : linearTwiddleFree c (linearTwiddleZero c) = 0 :=
    (linearTwiddle_zero_iff h).mpr rfl
  have hz' : linearTwiddleFree (1 - c) (1 - linearTwiddleZero c) = 0 := by
    rw [← linearTwiddleFree_fe_swap]
    simpa [linearTwiddleZero] using hz
  exact (linearTwiddle_zero_iff h').mp hz' |>.symm

/-! ## Normalization -/

noncomputable def linearTwiddleNorm (c : ℝ) : ℝ :=
  Real.sqrt (c ^ 2 + (1 - c) ^ 2)

theorem linearTwiddleNorm_pos {c : ℝ} :
    0 < linearTwiddleNorm c := by
  unfold linearTwiddleNorm
  have hpos : 0 < c ^ 2 + (1 - c) ^ 2 := by
    nlinarith [sq_nonneg c, sq_nonneg (1 - c), sq_nonneg (c - 1)]
  exact Real.sqrt_pos.mpr hpos

structure CubicTwiddle where
  c : ℝ
  norm : ℝ

/-- Normalized cubic/linear free readout at a complex point (depends only on `Re s`). -/
noncomputable def so4CubicFree (tw : CubicTwiddle) (s : ℂ) : ℝ :=
  linearTwiddleFree tw.c s.re / tw.norm

/-- Mirrored partner: coefficient `1-c` with the same normalization. -/
noncomputable def so4CubicFreeMirror (tw : CubicTwiddle) (s : ℂ) : ℝ :=
  so4CubicFree { c := 1 - tw.c, norm := tw.norm } s

theorem so4CubicFree_mirror (tw : CubicTwiddle) (s : ℂ) :
    so4CubicFree tw (1 - s) = so4CubicFreeMirror tw s := by
  unfold so4CubicFree so4CubicFreeMirror
  rw [Complex.sub_re, Complex.one_re, linearTwiddleFree_fe_swap]
  rfl

theorem so4CubicFree_zero_iff {tw : CubicTwiddle} {s : ℂ}
    (h : 2 * tw.c - 1 ≠ 0) (hn : tw.norm ≠ 0) :
    so4CubicFree tw s = 0 ↔ s.re = linearTwiddleZero tw.c := by
  unfold so4CubicFree
  constructor
  · intro h0
    rcases div_eq_zero_iff.mp h0 with hfree | hnorm
    · exact (linearTwiddle_zero_iff h).mp hfree
    · exact (hn hnorm).elim
  · intro hσ
    have hfree : linearTwiddleFree tw.c (linearTwiddleZero tw.c) = 0 :=
      (linearTwiddle_zero_iff h).mpr rfl
    rw [hσ, hfree, zero_div]

/-! ## Plastic coefficient -/

/-- Plastic twiddle coefficient `c_ρ = (ρ-1)/ρ`. -/
noncomputable def plasticTwiddleCoefficient : ℝ :=
  (plasticNumber - 1) / plasticNumber

theorem plasticTwiddleCoefficient_eq_one_sub_inv :
    plasticTwiddleCoefficient = 1 - 1 / plasticNumber := by
  unfold plasticTwiddleCoefficient
  field_simp [plasticNumber_ne_zero]

theorem plasticNumber_inv_eq_sq_sub_one :
    1 / plasticNumber = plasticNumber ^ 2 - 1 := by
  have h := plasticNumber_cubic_eq_zero
  have hp := plasticNumber_pos
  field_simp [ne_of_gt hp]
  nlinarith [sq_nonneg (plasticNumber - 1)]

theorem plasticTwiddleCoefficient_eq_two_sub_sq :
    plasticTwiddleCoefficient = 2 - plasticNumber ^ 2 := by
  rw [plasticTwiddleCoefficient_eq_one_sub_inv, plasticNumber_inv_eq_sq_sub_one]
  ring

theorem plasticTwiddleCoefficient_mem_Ioo :
    plasticTwiddleCoefficient ∈ Set.Ioo (0 : ℝ) 1 := by
  rcases plasticNumber_mem_Ioo_one_two with ⟨hρ1, hρ2⟩
  unfold plasticTwiddleCoefficient
  constructor
  · apply div_pos
    · linarith
    · exact plasticNumber_pos
  · have hρ : plasticNumber > 1 := plasticNumber_mem_Ioo_one_two.1
    exact (div_lt_one plasticNumber_pos).mpr (by linarith)

theorem plasticTwiddle_two_c_minus_one_ne_zero :
    2 * plasticTwiddleCoefficient - 1 ≠ 0 := by
  rw [plasticTwiddleCoefficient_eq_two_sub_sq]
  intro h
  have hρ := plasticNumber_cubic_eq_zero
  have hρ2eq : plasticNumber ^ 2 = 3 / 2 := by nlinarith
  have hρ3 : plasticNumber ^ 3 = plasticNumber * (3 / 2) := by
    calc
      plasticNumber ^ 3 = plasticNumber * plasticNumber ^ 2 := by ring
      _ = plasticNumber * (3 / 2) := by rw [hρ2eq]
  rw [hρ3] at hρ
  nlinarith

/-- Default plastic normalization `N_ρ`. -/
noncomputable def plasticTwiddleNorm : ℝ :=
  linearTwiddleNorm plasticTwiddleCoefficient

theorem plasticTwiddleNorm_pos : 0 < plasticTwiddleNorm :=
  linearTwiddleNorm_pos

/-- Canonical plastic cubic twiddle record. -/
noncomputable def plasticCubicTwiddle : CubicTwiddle :=
  { c := plasticTwiddleCoefficient
    norm := plasticTwiddleNorm }

noncomputable def so4PlasticCubicFree (s : ℂ) : ℝ :=
  so4CubicFree plasticCubicTwiddle s

noncomputable def so4PlasticCubicFreeMirror (s : ℂ) : ℝ :=
  so4CubicFreeMirror plasticCubicTwiddle s

theorem so4PlasticCubicFree_one_sub (s : ℂ) :
    so4PlasticCubicFree (1 - s) = so4PlasticCubicFreeMirror s :=
  so4CubicFree_mirror plasticCubicTwiddle s

/-! ## Plastic zero locus -/

noncomputable def plasticTwiddleZero : ℝ :=
  linearTwiddleZero plasticTwiddleCoefficient

theorem plasticTwiddleZero_eq :
    plasticTwiddleZero =
      (plasticTwiddleCoefficient - 1) /
        (2 * plasticTwiddleCoefficient - 1) := by
  rfl

theorem plasticTwiddleZero_mirror :
    linearTwiddleZero (1 - plasticTwiddleCoefficient) =
      1 - plasticTwiddleZero := by
  refine linearTwiddleZero_mirror ?_ ?_
  · exact plasticTwiddle_two_c_minus_one_ne_zero
  · have h := plasticTwiddleCoefficient_mem_Ioo
    have hc : 0 < plasticTwiddleCoefficient := h.1
    have hc1 : plasticTwiddleCoefficient < 1 := h.2
    intro hEq
    have hcomm :
        2 * (1 - plasticTwiddleCoefficient) - 1 =
          -(2 * plasticTwiddleCoefficient - 1) := by ring
    rw [hcomm, neg_eq_zero] at hEq
    exact plasticTwiddle_two_c_minus_one_ne_zero hEq

/-! ## Quadratic 45° comparison -/

private theorem one_div_sqrt_two_eq_sqrt_two_div_two :
    (1 / Real.sqrt 2) = Real.sqrt 2 / 2 := by
  have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  field_simp [hpos.ne']
  rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- Paper coefficient `c = 1/√2` (cos/sin weight at `π/4`, not the rotation slope). -/
noncomputable def quadraticTwiddleCoefficient : ℝ :=
  1 / Real.sqrt 2

theorem quadraticTwiddleCoefficient_eq_one_div_sqrt_two :
    quadraticTwiddleCoefficient = Real.cos (Real.pi / 4) := by
  rw [quadraticTwiddleCoefficient, Real.cos_pi_div_four, one_div_sqrt_two_eq_sqrt_two_div_two]

/-- At `c = 1/√2` the zero locus is `-1/√2`, not the critical line `1/2`. -/
theorem linearTwiddleZero_quadratic_twiddle :
    linearTwiddleZero quadraticTwiddleCoefficient = -1 / Real.sqrt 2 := by
  have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt2 : 2 / Real.sqrt 2 = Real.sqrt 2 := by
    field_simp [hpos.ne']
    rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hden : 2 / Real.sqrt 2 ≠ 1 := by
    rw [hsqrt2]
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hden' : 2 * quadraticTwiddleCoefficient - 1 ≠ 0 := by
    unfold quadraticTwiddleCoefficient
    intro h0
    apply hden
    field_simp [hpos.ne'] at h0 ⊢
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hz : linearTwiddleFree quadraticTwiddleCoefficient (-1 / Real.sqrt 2) = 0 := by
    rw [linearTwiddleFree_eq, quadraticTwiddleCoefficient]
    field_simp [hpos.ne']
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  exact ((linearTwiddle_zero_iff hden').mp hz).symm

theorem linearTwiddleZero_quadratic_ne_half :
    linearTwiddleZero quadraticTwiddleCoefficient ≠ (1 / 2 : ℝ) := by
  rw [linearTwiddleZero_quadratic_twiddle]
  have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hneg : (-1 : ℝ) / Real.sqrt 2 < 0 :=
    div_neg_of_neg_of_pos (by norm_num) hpos
  linarith

end

end Hqiv.Story

import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Hqiv.Story.S3DBNLatticeInheritance

/-!
# Discrete/continuum comparison: `|HQIVDeformedSum| ≥ c · |dbnHeatFamily|`

`S3DBNLatticeInheritance` named the inheritance frontier `lattice_dominates :
Λ ≤ lambdaHQIV` and proved it is *equivalent to RH* given the classical
imports.  This module proves the requested **one-sided comparison inequality**
and **phase-alignment statement** between the discrete HQIV deformed sum and
the continuum de Bruijn–Newman heat family, in the region where both sides are
under analytic control.

## What is proved (no hypotheses beyond parameter ranges)

* **Analytic control of the classical side.**
  - `dbnPhi_pos`: the dBN density `Φ(u)` is *strictly* positive for `u ≥ 0`.
  - `dbnPhi_continuousOn` / `dbnPhi_integrableOn`: `Φ` is continuous on
    `u ≥ 0` and Lebesgue-integrable on `(0, ∞)` (super-exponential decay
    `Φ(u) ≤ C·e^{−3u}`, `dbnPhi_le_decay`).
  - `dbnHeatFamily_norm_le`: for every backward-deformation time `t ≤ 0` and
    every **real** `z`, `‖H_t(z)‖ ≤ ∫_{u>0} Φ` — a uniform bound on the
    backward continuum family.  (`t ≤ 0` is exactly the backprojection side
    that the lattice arrow forbids; forward `t > 0` is unbounded by
    `dbn_forward_factor_unbounded`.)
  - `dbnWeightedIntegral_pos` / `dbnHeatFamily_arg_at_zero`: at the anchor
    `z = 0` the backward family is a *strictly positive real*, so its phase is
    exactly `0`.

* **Analytic control of the discrete side.**
  - `hqivHeatKernelWeight_horizon`: the horizon shell `m = 0` carries weight
    `1` for **every** deformation time `τ` — the heat flow fixes the horizon.
  - `HQIVDeformedSum_real_anchor`: at trivial twist (`φ = 0`) and real
    `s = σ`, the deformed sum is the coercion of a convergent positive real
    series.
  - `HQIVDeformedSum_anchor_lower`: the flow-invariant horizon term gives the
    unconditional lower bound `eff₀^{−σ} ≤ ‖HQIVDeformedSum τ … σ‖`.

* **The requested comparison inequality**
  (`discrete_dominates_continuum_anchor`): for `τ ≥ 0`, `t ≤ 0`, `σ > 1`,
  and **all real** `z`,
  `c · ‖dbnHeatFamily t z‖ ≤ ‖HQIVDeformedSum τ T_ref δ 0 t' σ‖`
  with the explicit constant `c = eff₀^{−σ} / (∫Φ + 1) > 0`.

* **The requested phase alignment** (`phase_alignment_anchor` /
  `phase_alignment_cos_ge_half`): at the anchor the arguments of the discrete
  sum and the continuum integral coincide (`cos(Δarg) = 1 ≥ 1/2`).

## Honest scope

The comparison and alignment are proved on the region `Re s > 1` (discrete)
× `z` real (continuum) — where the discrete series converges absolutely and
the backward continuum family is uniformly bounded.  The growth sign is
preserved there: the discrete side can never be outshouted by any backward
(`t ≤ 0`) continuum deformation.  Extending the comparison *into the critical
strip with zero-tracking* is precisely the content of `lattice_dominates`,
which `lattice_dominates_iff_RiemannHypothesis` shows is RH itself: this
module pushes the proved boundary up to that frontier, it does not cross it.
-/

namespace Hqiv.Story

open Hqiv.Physics MeasureTheory Set

noncomputable section

/-! ## Strict positivity of the dBN density -/

/-- Every term of the dBN density is **strictly** positive for `u ≥ 0`:
the quartic shell term strictly dominates since `2π m² e^{4u} ≥ 2π > 3`. -/
theorem dbnPhiTerm_pos {u : ℝ} (hu : 0 ≤ u) (n : ℕ) : 0 < dbnPhiTerm u n := by
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hm : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hm2 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  have he : (1 : ℝ) ≤ Real.exp (4 * u) := by
    have := Real.add_one_le_exp (4 * u)
    linarith
  have hexp9 : Real.exp (9 * u) = Real.exp (4 * u) * Real.exp (5 * u) := by
    rw [← Real.exp_add]; ring_nf
  have hP : (0 : ℝ) < Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (5 * u) := by
    have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
    positivity
  have hfac : (3 : ℝ) < 2 * Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u) := by
    nlinarith [mul_le_mul_of_nonneg_left hm2 (by linarith : (0:ℝ) ≤ 2 * Real.pi),
      mul_le_mul_of_nonneg_left he
        (by nlinarith : (0:ℝ) ≤ 2 * Real.pi * ((n : ℝ) + 1) ^ 2)]
  have hAB :
      0 < 2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u)
          - 3 * Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (5 * u) := by
    rw [hexp9]
    nlinarith [mul_pos
      (by linarith : (0:ℝ) < 2 * Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u) - 3) hP]
  exact mul_pos hAB (Real.exp_pos _)

/-- The dBN density is nonnegative on `u ≥ 0`. -/
theorem dbnPhi_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ dbnPhi u :=
  tsum_nonneg fun n => dbnPhiTerm_nonneg hu n

/-- **Strict positivity of the dBN density** on `u ≥ 0`. -/
theorem dbnPhi_pos {u : ℝ} (hu : 0 ≤ u) : 0 < dbnPhi u :=
  (dbnPhi_summable hu).tsum_pos (fun n => dbnPhiTerm_nonneg hu n) 0 (dbnPhiTerm_pos hu 0)

/-! ## Super-exponential decay of the dBN density -/

/-- Shell-decay coefficient `2π² m⁴ e^{−π(m²−1)}` (with `m = n + 1`). -/
def dbnDecayCoeff (n : ℕ) : ℝ :=
  2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (-(Real.pi * (((n : ℝ) + 1) ^ 2 - 1)))

theorem dbnDecayCoeff_nonneg (n : ℕ) : 0 ≤ dbnDecayCoeff n := by
  unfold dbnDecayCoeff
  have := Real.pi_pos
  positivity

/-- **Uniform exponential-decay bound on each term**: for `u ≥ 0`,
`dbnPhiTerm u n ≤ dbnDecayCoeff n · e^{−π} · e^{−3u}`.  Uses
`e^{−πm²e^{4u}} ≤ e^{−π(m²−1)}e^{−πe^{4u}}` (since `e^{4u} ≥ 1`) and
`9u − πe^{4u} ≤ −π − 3u` (since `π > 3`). -/
theorem dbnPhiTerm_le_decay {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    dbnPhiTerm u n ≤ dbnDecayCoeff n * (Real.exp (-Real.pi) * Real.exp (-(3 * u))) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hm : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hm2 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  have he : (1 : ℝ) ≤ Real.exp (4 * u) := by
    have := Real.add_one_le_exp (4 * u)
    linarith
  -- Step 1: drop the negative part of the bracket.
  have hB : (0 : ℝ) ≤ 3 * Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (5 * u) := by positivity
  have hE : (0 : ℝ) < Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u))) :=
    Real.exp_pos _
  have hstep1 : dbnPhiTerm u n ≤
      2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u) *
        Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u))) := by
    unfold dbnPhiTerm
    nlinarith [mul_nonneg hB hE.le]
  -- Step 2: single exponent inequality
  -- `9u − πm²e^{4u} ≤ −π(m²−1) − π − 3u`.
  have hexp : 9 * u - Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u) ≤
      -(Real.pi * (((n : ℝ) + 1) ^ 2 - 1)) - Real.pi - 3 * u := by
    nlinarith [mul_nonneg hπ.le
        (mul_nonneg (sub_nonneg.mpr hm2) (sub_nonneg.mpr he)),
      mul_le_mul_of_nonneg_left (Real.add_one_le_exp (4 * u)) hπ.le,
      mul_nonneg (sub_nonneg.mpr hπ3.le) hu]
  calc dbnPhiTerm u n
      ≤ 2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u) *
          Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u))) := hstep1
    _ = 2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 *
          Real.exp (9 * u - Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
    _ ≤ 2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 *
          Real.exp (-(Real.pi * (((n : ℝ) + 1) ^ 2 - 1)) - Real.pi - 3 * u) := by
        have hpos : (0 : ℝ) ≤ 2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 := by positivity
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hpos
    _ = dbnDecayCoeff n * (Real.exp (-Real.pi) * Real.exp (-(3 * u))) := by
        unfold dbnDecayCoeff
        rw [show -(Real.pi * (((n : ℝ) + 1) ^ 2 - 1)) - Real.pi - 3 * u
            = -(Real.pi * (((n : ℝ) + 1) ^ 2 - 1)) + (-Real.pi + -(3 * u)) by ring,
          Real.exp_add, Real.exp_add]
        ring

/-- The decay coefficients are summable (poly × Gaussian-in-shell tail). -/
theorem dbnDecayCoeff_summable : Summable dbnDecayCoeff := by
  set r : ℝ := Real.exp (-Real.pi) with hr_def
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr_def, show (1 : ℝ) = Real.exp 0 by simp]
    exact Real.exp_lt_exp.mpr (by linarith [Real.pi_pos])
  have h1 : Summable (fun k : ℕ => (k : ℝ) ^ 4 * r ^ k) :=
    summable_pow_mul_geometric_of_norm_lt_one 4
      (by rwa [Real.norm_eq_abs, abs_of_pos hr0])
  have h2 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 4 * r ^ (n + 1)) :=
    h1.comp_injective Nat.succ_injective
  have h3 : Summable
      (fun n : ℕ => (2 * Real.pi ^ 2 * Real.exp Real.pi) *
        (((n + 1 : ℕ) : ℝ) ^ 4 * r ^ (n + 1))) :=
    h2.mul_left _
  refine Summable.of_nonneg_of_le (fun n => dbnDecayCoeff_nonneg n) (fun n => ?_) h3
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hrpow : r ^ (n + 1) = Real.exp (((n + 1 : ℕ) : ℝ) * -Real.pi) := by
    rw [hr_def, ← Real.exp_nat_mul]
  have hexp_le : Real.exp (-(Real.pi * (((n : ℝ) + 1) ^ 2 - 1))) ≤
      Real.exp Real.pi * Real.exp (((n + 1 : ℕ) : ℝ) * -Real.pi) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith [sq_nonneg ((n : ℝ)), mul_nonneg (mul_nonneg hπ.le hn) hn]
  have hm4 : (0 : ℝ) ≤ 2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 := by positivity
  unfold dbnDecayCoeff
  calc 2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 *
        Real.exp (-(Real.pi * (((n : ℝ) + 1) ^ 2 - 1)))
      ≤ 2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 *
          (Real.exp Real.pi * Real.exp (((n + 1 : ℕ) : ℝ) * -Real.pi)) :=
        mul_le_mul_of_nonneg_left hexp_le hm4
    _ = (2 * Real.pi ^ 2 * Real.exp Real.pi) *
          (((n + 1 : ℕ) : ℝ) ^ 4 * r ^ (n + 1)) := by
        rw [hrpow]
        push_cast
        ring

/-- Total decay constant `∑ₙ dbnDecayCoeff n`. -/
def dbnPhiDecaySum : ℝ :=
  ∑' n : ℕ, dbnDecayCoeff n

theorem dbnPhiDecaySum_nonneg : 0 ≤ dbnPhiDecaySum :=
  tsum_nonneg fun n => dbnDecayCoeff_nonneg n

/-- **Super-exponential decay of the dBN density**:
`Φ(u) ≤ (∑ coeff) · e^{−π} · e^{−3u}` for `u ≥ 0`. -/
theorem dbnPhi_le_decay {u : ℝ} (hu : 0 ≤ u) :
    dbnPhi u ≤ dbnPhiDecaySum * Real.exp (-Real.pi) * Real.exp (-(3 * u)) := by
  unfold dbnPhi
  have hsum2 : Summable
      (fun n : ℕ => dbnDecayCoeff n * (Real.exp (-Real.pi) * Real.exp (-(3 * u)))) :=
    dbnDecayCoeff_summable.mul_right _
  calc (∑' n : ℕ, dbnPhiTerm u n)
      ≤ ∑' n : ℕ, dbnDecayCoeff n * (Real.exp (-Real.pi) * Real.exp (-(3 * u))) :=
        Summable.tsum_le_tsum (fun n => dbnPhiTerm_le_decay hu n) (dbnPhi_summable hu) hsum2
    _ = (∑' n : ℕ, dbnDecayCoeff n) * (Real.exp (-Real.pi) * Real.exp (-(3 * u))) :=
        tsum_mul_right
    _ = dbnPhiDecaySum * Real.exp (-Real.pi) * Real.exp (-(3 * u)) := by
        rw [dbnPhiDecaySum]; ring

/-! ## Continuity and integrability of the dBN density -/

theorem dbnPhiTerm_continuous (n : ℕ) : Continuous fun u : ℝ => dbnPhiTerm u n := by
  unfold dbnPhiTerm
  fun_prop

/-- `Φ` is continuous on `u ≥ 0` (Weierstrass M-test with the decay coefficients). -/
theorem dbnPhi_continuousOn : ContinuousOn dbnPhi (Set.Ici (0 : ℝ)) := by
  have h : ContinuousOn (fun u : ℝ => ∑' n : ℕ, dbnPhiTerm u n) (Set.Ici (0 : ℝ)) := by
    refine continuousOn_tsum (fun n => (dbnPhiTerm_continuous n).continuousOn)
      (dbnDecayCoeff_summable.mul_right (Real.exp (-Real.pi))) ?_
    intro n x hx
    have hx0 : (0 : ℝ) ≤ x := Set.mem_Ici.mp hx
    rw [Real.norm_eq_abs, abs_of_nonneg (dbnPhiTerm_nonneg hx0 n)]
    have hc : 0 ≤ dbnDecayCoeff n * Real.exp (-Real.pi) :=
      mul_nonneg (dbnDecayCoeff_nonneg n) (Real.exp_pos _).le
    have hexp1 : Real.exp (-(3 * x)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    calc dbnPhiTerm x n
        ≤ dbnDecayCoeff n * (Real.exp (-Real.pi) * Real.exp (-(3 * x))) :=
          dbnPhiTerm_le_decay hx0 n
      _ = (dbnDecayCoeff n * Real.exp (-Real.pi)) * Real.exp (-(3 * x)) := by ring
      _ ≤ dbnDecayCoeff n * Real.exp (-Real.pi) := mul_le_of_le_one_right hc hexp1
  exact h

/-- **Integrability of the dBN density** on `(0, ∞)`. -/
theorem dbnPhi_integrableOn : IntegrableOn dbnPhi (Set.Ioi (0 : ℝ)) := by
  have hg : IntegrableOn
      (fun u : ℝ => (dbnPhiDecaySum * Real.exp (-Real.pi)) * Real.exp (-(3 : ℝ) * u))
      (Set.Ioi (0 : ℝ)) :=
    (exp_neg_integrableOn_Ioi 0 (by norm_num : (0:ℝ) < 3)).const_mul _
  refine Integrable.mono' hg ?_ ?_
  · exact (dbnPhi_continuousOn.mono Set.Ioi_subset_Ici_self).aestronglyMeasurable
      measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) ≤ u := (Set.mem_Ioi.mp hu).le
    rw [Real.norm_eq_abs, abs_of_nonneg (dbnPhi_nonneg hu0)]
    calc dbnPhi u ≤ dbnPhiDecaySum * Real.exp (-Real.pi) * Real.exp (-(3 * u)) :=
          dbnPhi_le_decay hu0
      _ = (dbnPhiDecaySum * Real.exp (-Real.pi)) * Real.exp (-(3 : ℝ) * u) := by
          rw [show -(3 * u) = (-(3:ℝ)) * u by ring]

/-- The backward (`t ≤ 0`) weighted density `e^{tu²}Φ(u)` is integrable on `(0, ∞)`. -/
theorem dbnWeighted_integrableOn {t : ℝ} (ht : t ≤ 0) :
    IntegrableOn (fun u => dbnGaussianFactor t u * dbnPhi u) (Set.Ioi (0 : ℝ)) := by
  refine Integrable.mono' dbnPhi_integrableOn ?_ ?_
  · refine AEStronglyMeasurable.mul ?_ ?_
    · exact (Continuous.aestronglyMeasurable (by unfold dbnGaussianFactor; fun_prop))
    · exact (dbnPhi_continuousOn.mono Set.Ioi_subset_Ici_self).aestronglyMeasurable
        measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) ≤ u := (Set.mem_Ioi.mp hu).le
    have hg0 : 0 ≤ dbnGaussianFactor t u := (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hg0 (dbnPhi_nonneg hu0))]
    have h1 : dbnGaussianFactor t u ≤ 1 := dbn_backward_factor_le_one ht u
    nlinarith [dbnPhi_nonneg hu0]

/-! ## The backward continuum family at the anchor: positive, bounded, phase 0 -/

/-- **Positivity of the backward weighted integral**: for `t ≤ 0`,
`∫_{u>0} e^{tu²} Φ(u) du > 0`. -/
theorem dbnWeightedIntegral_pos {t : ℝ} (ht : t ≤ 0) :
    0 < ∫ u in Set.Ioi (0 : ℝ), dbnGaussianFactor t u * dbnPhi u := by
  have hIoc : IntegrableOn (fun u => dbnGaussianFactor t u * dbnPhi u)
      (Set.Ioc (0 : ℝ) 1) :=
    (dbnWeighted_integrableOn ht).mono_set Set.Ioc_subset_Ioi_self
  have hII : IntervalIntegrable (fun u => dbnGaussianFactor t u * dbnPhi u)
      volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr hIoc
  have h01 : 0 < ∫ u in (0 : ℝ)..1, dbnGaussianFactor t u * dbnPhi u := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on hII ?_ zero_lt_one
    intro x hx
    exact mul_pos (Real.exp_pos _) (dbnPhi_pos hx.1.le)
  have heq : (∫ u in (0 : ℝ)..1, dbnGaussianFactor t u * dbnPhi u)
      = ∫ u in Set.Ioc (0 : ℝ) 1, dbnGaussianFactor t u * dbnPhi u :=
    intervalIntegral.integral_of_le zero_le_one
  have hmono : (∫ u in Set.Ioc (0 : ℝ) 1, dbnGaussianFactor t u * dbnPhi u)
      ≤ ∫ u in Set.Ioi (0 : ℝ), dbnGaussianFactor t u * dbnPhi u := by
    refine setIntegral_mono_set (dbnWeighted_integrableOn ht) ?_
      Set.Ioc_subset_Ioi_self.eventuallyLE
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (Real.exp_pos _).le (dbnPhi_nonneg (Set.mem_Ioi.mp hu).le)
  linarith [heq ▸ h01]

/-- At the anchor `z = 0` the dBN family is the coercion of the real
weighted integral (the cosine readout is `1`). -/
theorem dbnHeatFamily_at_zero (t : ℝ) :
    dbnHeatFamily t 0 =
      ((∫ u in Set.Ioi (0 : ℝ), dbnGaussianFactor t u * dbnPhi u : ℝ) : ℂ) := by
  unfold dbnHeatFamily
  have h1 : (∫ u in Set.Ioi (0 : ℝ),
        ((dbnGaussianFactor t u * dbnPhi u : ℝ) : ℂ) * Complex.cos ((0 : ℂ) * (u : ℂ)))
      = ∫ u in Set.Ioi (0 : ℝ), ((dbnGaussianFactor t u * dbnPhi u : ℝ) : ℂ) :=
    integral_congr_ae (Filter.Eventually.of_forall fun u => by simp)
  rw [h1, integral_complex_ofReal]

/-- **Phase of the backward family at the anchor is exactly `0`**:
`H_t(0)` is a strictly positive real for every `t ≤ 0`. -/
theorem dbnHeatFamily_arg_at_zero {t : ℝ} (ht : t ≤ 0) :
    Complex.arg (dbnHeatFamily t 0) = 0 := by
  rw [dbnHeatFamily_at_zero]
  exact Complex.arg_ofReal_of_nonneg (dbnWeightedIntegral_pos ht).le

/-- The total mass of the dBN density: the uniform bound for the backward family. -/
def dbnPhiIntegralBound : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ), dbnPhi u

theorem dbnPhiIntegralBound_nonneg : 0 ≤ dbnPhiIntegralBound :=
  setIntegral_nonneg measurableSet_Ioi fun _ hu => dbnPhi_nonneg (Set.mem_Ioi.mp hu).le

/-- **Uniform bound on the backward continuum family**: for `t ≤ 0` and every
real `z`, `‖H_t(z)‖ ≤ ∫_{u>0} Φ`.  The backward Gaussian factor contracts and
the cosine readout has unit modulus on the real axis. -/
theorem dbnHeatFamily_norm_le {t : ℝ} (ht : t ≤ 0) (z : ℝ) :
    ‖dbnHeatFamily t (z : ℂ)‖ ≤ dbnPhiIntegralBound := by
  unfold dbnHeatFamily dbnPhiIntegralBound
  refine norm_integral_le_of_norm_le dbnPhi_integrableOn ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : (0 : ℝ) ≤ u := (Set.mem_Ioi.mp hu).le
  have hg0 : 0 ≤ dbnGaussianFactor t u := (Real.exp_pos _).le
  have hgp : 0 ≤ dbnGaussianFactor t u * dbnPhi u :=
    mul_nonneg hg0 (dbnPhi_nonneg hu0)
  rw [norm_mul]
  have h1 : ‖((dbnGaussianFactor t u * dbnPhi u : ℝ) : ℂ)‖ =
      dbnGaussianFactor t u * dbnPhi u := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgp]
  have h2 : ‖Complex.cos ((z : ℂ) * (u : ℂ))‖ ≤ 1 := by
    rw [show ((z : ℂ) * (u : ℂ)) = ((z * u : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  calc ‖((dbnGaussianFactor t u * dbnPhi u : ℝ) : ℂ)‖ * ‖Complex.cos ((z : ℂ) * (u : ℂ))‖
      ≤ ‖((dbnGaussianFactor t u * dbnPhi u : ℝ) : ℂ)‖ * 1 :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = dbnGaussianFactor t u * dbnPhi u := by rw [mul_one, h1]
    _ ≤ 1 * dbnPhi u :=
        mul_le_mul_of_nonneg_right (dbn_backward_factor_le_one ht u) (dbnPhi_nonneg hu0)
    _ = dbnPhi u := one_mul _

/-! ## The discrete side at the anchor: flow-invariant horizon term -/

/-- **The heat flow fixes the horizon shell**: the `m = 0` weight is `1` for
*every* deformation time `τ` (since `tHQIV T_ref 0 = 0`). -/
theorem hqivHeatKernelWeight_horizon (τ T_ref : ℝ) :
    hqivHeatKernelWeight τ T_ref 0 = 1 := by
  simp [hqivHeatKernelWeight, discreteHeatKernelWeight, tHQIV]

/-- Real shell term of the deformed sum at trivial twist and real `s = σ`. -/
def hqivDeformedRealTerm (τ T_ref δ σ : ℝ) (m : ℕ) : ℝ :=
  hqivHeatKernelWeight τ T_ref m * effCorrected δ m ^ (-σ)

theorem hqivDeformedRealTerm_nonneg (τ T_ref δ σ : ℝ) (m : ℕ)
    (hden : RindlerDenDeltaPos δ m) :
    0 ≤ hqivDeformedRealTerm τ T_ref δ σ m :=
  mul_nonneg (hqivHeatKernelWeight_nonneg τ T_ref m)
    (Real.rpow_pos_of_pos (effCorrected_pos δ m hden) (-σ)).le

/-- At trivial twist (`φ = 0`) and real `s = σ`, each deformed lattice term is
the coercion of the corresponding positive real term. -/
theorem hqivDeformedLatticeTerm_real (τ T_ref δ t σ : ℝ) (m : ℕ)
    (hden : RindlerDenDeltaPos δ m) :
    hqivDeformedLatticeTerm τ T_ref δ 0 t (σ : ℂ) m =
      ((hqivDeformedRealTerm τ T_ref δ σ m : ℝ) : ℂ) := by
  have heff : (0 : ℝ) ≤ effCorrected δ m := (effCorrected_pos δ m hden).le
  unfold hqivDeformedLatticeTerm zetaHQIVTerm hqivDeformedRealTerm
  rw [show (Complex.I * ((0 : ℝ) : ℂ) * ((t : ℝ) : ℂ) *
      ((delta_theta_prime (m : ℝ) : ℝ) : ℂ)) = 0 by push_cast; ring,
    Complex.exp_zero, mul_one, Complex.ofReal_mul,
    Complex.ofReal_cpow heff, Complex.ofReal_neg]

/-- Real-term summability at the anchor, inherited from the complex theorem. -/
theorem hqivDeformedRealTerm_summable (τ T_ref δ t σ : ℝ)
    (hτ : 0 ≤ τ) (hT : 0 < T_ref) (hδ : 0 ≤ δ)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos δ m) (hσ : 1 < σ) :
    Summable (hqivDeformedRealTerm τ T_ref δ σ) := by
  have hC : Summable (hqivDeformedLatticeTerm τ T_ref δ 0 t (σ : ℂ)) :=
    hqivDeformedLatticeTerm_summable_of_re_gt_one τ T_ref δ 0 t (σ : ℂ) hτ hT hδ hden
      (by simpa using hσ)
  have hC' : Summable (fun m : ℕ => ((hqivDeformedRealTerm τ T_ref δ σ m : ℝ) : ℂ)) :=
    hC.congr fun m => hqivDeformedLatticeTerm_real τ T_ref δ t σ m (hden m)
  exact Complex.summable_ofReal.mp hC'

/-- **The deformed sum at the anchor is a positive real series**: at trivial
twist and real `s = σ > 1` the full complex sum is the coercion of the real
sum. -/
theorem HQIVDeformedSum_real_anchor (τ T_ref δ t σ : ℝ)
    (hτ : 0 ≤ τ) (hT : 0 < T_ref) (hδ : 0 ≤ δ)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos δ m) (hσ : 1 < σ) :
    HQIVDeformedSum τ T_ref δ 0 t (σ : ℂ) =
      ((∑' m : ℕ, hqivDeformedRealTerm τ T_ref δ σ m : ℝ) : ℂ) := by
  unfold HQIVDeformedSum
  rw [tsum_congr fun m => hqivDeformedLatticeTerm_real τ T_ref δ t σ m (hden m)]
  have hsum := hqivDeformedRealTerm_summable τ T_ref δ t σ hτ hT hδ hden hσ
  calc (∑' m : ℕ, ((hqivDeformedRealTerm τ T_ref δ σ m : ℝ) : ℂ))
      = ∑' m : ℕ, Complex.ofRealCLM (hqivDeformedRealTerm τ T_ref δ σ m) := by
        simp [Complex.ofRealCLM_apply]
    _ = Complex.ofRealCLM (∑' m : ℕ, hqivDeformedRealTerm τ T_ref δ σ m) :=
        (Complex.ofRealCLM.map_tsum hsum).symm
    _ = ((∑' m : ℕ, hqivDeformedRealTerm τ T_ref δ σ m : ℝ) : ℂ) := by
        simp [Complex.ofRealCLM_apply]

/-- **Unconditional lower bound from the flow-invariant horizon term**: for all
`τ ≥ 0`, `eff₀^{−σ} ≤ ‖HQIVDeformedSum τ T_ref δ 0 t σ‖`.  The heat flow
cannot dim the horizon shell, and every other shell only adds positive mass. -/
theorem HQIVDeformedSum_anchor_lower (τ T_ref δ t σ : ℝ)
    (hτ : 0 ≤ τ) (hT : 0 < T_ref) (hδ : 0 ≤ δ)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos δ m) (hσ : 1 < σ) :
    effCorrected δ 0 ^ (-σ) ≤ ‖HQIVDeformedSum τ T_ref δ 0 t (σ : ℂ)‖ := by
  rw [HQIVDeformedSum_real_anchor τ T_ref δ t σ hτ hT hδ hden hσ,
    Complex.norm_real, Real.norm_eq_abs]
  have hsum := hqivDeformedRealTerm_summable τ T_ref δ t σ hτ hT hδ hden hσ
  have hnn : ∀ m : ℕ, 0 ≤ hqivDeformedRealTerm τ T_ref δ σ m :=
    fun m => hqivDeformedRealTerm_nonneg τ T_ref δ σ m (hden m)
  have h0 : hqivDeformedRealTerm τ T_ref δ σ 0 = effCorrected δ 0 ^ (-σ) := by
    unfold hqivDeformedRealTerm
    rw [hqivHeatKernelWeight_horizon, one_mul]
  have hle : hqivDeformedRealTerm τ T_ref δ σ 0 ≤
      ∑' m : ℕ, hqivDeformedRealTerm τ T_ref δ σ m :=
    hsum.le_tsum 0 fun j _ => hnn j
  rw [abs_of_nonneg (tsum_nonneg hnn)]
  linarith [h0 ▸ hle]

/-! ## The requested comparison inequality and phase alignment -/

/--
**Discrete-dominates-continuum comparison (anchor region).**  For every
backward continuum time `t ≤ 0`, every forward lattice time `τ ≥ 0`, every
real readout point `z`, and every anchor `σ > 1`, there is an **explicit**
constant `c > 0` with

`c · ‖dbnHeatFamily t z‖ ≤ ‖HQIVDeformedSum τ T_ref δ 0 t' σ‖`,

namely `c = eff₀^{−σ} / (∫_{u>0}Φ + 1)`.  The discrete side is bounded below
by its flow-invariant horizon term; the backward continuum side is bounded
above by the total dBN mass.  No backward deformation of the continuum family
can outgrow the lattice sum in this region: the growth sign is preserved.
-/
theorem discrete_dominates_continuum_anchor (τ T_ref δ t' t σ : ℝ)
    (hτ : 0 ≤ τ) (hT : 0 < T_ref) (hδ : 0 ≤ δ)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos δ m) (hσ : 1 < σ)
    (ht : t ≤ 0) (z : ℝ) :
    ∃ c : ℝ, 0 < c ∧
      c * ‖dbnHeatFamily t (z : ℂ)‖ ≤ ‖HQIVDeformedSum τ T_ref δ 0 t' (σ : ℂ)‖ := by
  have he0 : 0 < effCorrected δ 0 ^ (-σ) :=
    Real.rpow_pos_of_pos (effCorrected_pos δ 0 (hden 0)) (-σ)
  have hB : 0 ≤ dbnPhiIntegralBound := dbnPhiIntegralBound_nonneg
  refine ⟨effCorrected δ 0 ^ (-σ) / (dbnPhiIntegralBound + 1), by positivity, ?_⟩
  have hH := dbnHeatFamily_norm_le ht z
  have hS := HQIVDeformedSum_anchor_lower τ T_ref δ t' σ hτ hT hδ hden hσ
  have hc : 0 < effCorrected δ 0 ^ (-σ) / (dbnPhiIntegralBound + 1) := by positivity
  have h1 : effCorrected δ 0 ^ (-σ) / (dbnPhiIntegralBound + 1) *
      ‖dbnHeatFamily t (z : ℂ)‖ ≤
      effCorrected δ 0 ^ (-σ) / (dbnPhiIntegralBound + 1) * dbnPhiIntegralBound :=
    mul_le_mul_of_nonneg_left hH hc.le
  have h2 : effCorrected δ 0 ^ (-σ) / (dbnPhiIntegralBound + 1) * dbnPhiIntegralBound ≤
      effCorrected δ 0 ^ (-σ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : (0:ℝ) < dbnPhiIntegralBound + 1)]
    nlinarith
  linarith

/--
**Phase alignment at the anchor (exact).**  The argument of the discrete
deformed sum and the argument of the backward continuum family coincide at
the anchor — both are `0` — so the cosine of their difference is exactly `1`.
This is the strongest possible form of the "angle close to 0" statement.
-/
theorem phase_alignment_anchor (τ T_ref δ t' t σ : ℝ)
    (hτ : 0 ≤ τ) (hT : 0 < T_ref) (hδ : 0 ≤ δ)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos δ m) (hσ : 1 < σ) (ht : t ≤ 0) :
    Real.cos (Complex.arg (HQIVDeformedSum τ T_ref δ 0 t' (σ : ℂ)) -
      Complex.arg (dbnHeatFamily t 0)) = 1 := by
  have hargS : Complex.arg (HQIVDeformedSum τ T_ref δ 0 t' (σ : ℂ)) = 0 := by
    rw [HQIVDeformedSum_real_anchor τ T_ref δ t' σ hτ hT hδ hden hσ]
    exact Complex.arg_ofReal_of_nonneg
      (tsum_nonneg fun m => hqivDeformedRealTerm_nonneg τ T_ref δ σ m (hden m))
  have hargH : Complex.arg (dbnHeatFamily t 0) = 0 := dbnHeatFamily_arg_at_zero ht
  rw [hargS, hargH, sub_zero, Real.cos_zero]

/-- The phase-alignment cosine is bounded below by the positive constant
`1/2` — the requested quantitative form. -/
theorem phase_alignment_cos_ge_half (τ T_ref δ t' t σ : ℝ)
    (hτ : 0 ≤ τ) (hT : 0 < T_ref) (hδ : 0 ≤ δ)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos δ m) (hσ : 1 < σ) (ht : t ≤ 0) :
    (1 / 2 : ℝ) ≤ Real.cos (Complex.arg (HQIVDeformedSum τ T_ref δ 0 t' (σ : ℂ)) -
      Complex.arg (dbnHeatFamily t 0)) := by
  rw [phase_alignment_anchor τ T_ref δ t' t σ hτ hT hδ hden hσ ht]
  norm_num

end

end Hqiv.Story

import Hqiv.Story.S3TuftNestedFrameTower
import Hqiv.Story.S3SO4ZetaProjectionClosedForm
import Hqiv.Foundation.MonogamyProjection
import Mathlib.NumberTheory.ZetaValues

/-!
# ζ(3) through the SO(4) frame projection: Bernoulli pinch and monogamy weights

This module tests the claim *"the SO(4) construction should give a closed form
for ζ(3), most likely with the 3/5–2/5 monogamy exponents"* and formalizes the
sharpest statements that are provable today.

## Projection reads the zeta ladder (proved)

The odd-sphere frame radius `spectralFrameNormSq N s` converges on every
vertical line to the corresponding zeta value:

* `σ = 1`  → `ζ(2) = π²/6`  (`frame_radius_tendsto_zeta_two`);
* `σ = 3/2` → `ζ(3)`         (`frame_radius_tendsto_zeta_three`);
* `σ = 2`  → `ζ(4) = π⁴/90` (`frame_radius_tendsto_zeta_four`).

"To find a value of zeta, project through this construction" is a theorem.

## m = 4 stability is the Bernoulli symmetry (proved, re-export)

Even lines close in π-power/Bernoulli form (`hasSum_zeta_nat`,
`zeta_even_so4_closed_form` in `S3SO4ZetaProjectionClosedForm`).  The even
channel is the *stable* one; the odd lines have no such closure (Apéry slot).

## Monogamy weights: a provable parity obstruction (the calibration)

The physical monogamy row has `imprint = 3/5`, `overlap = 2/5`
(`MonogamyProjection.physical_imprint`).  A monogamy-weighted combination of
two even (Bernoulli-closed) channels can **never** reach the cube channel:

`(3/5)·a + (2/5)·b = 3` with `a, b` even forces `3a + 2b = 15` — even = odd,
impossible (`monogamy_weights_cannot_reach_cube_channel`).

It is the **half-slope weights** `(1/2, 1/2)` — the same `1/2` that runs the
whole RH–Goldbach bridge — that reach the cube channel, and they select the
Bernoulli pair `(2, 4)` **uniquely** (`balanced_half_slope_pair_unique`).

(For the record: the monogamy split does appear analytically as the Hölder
bound `ζ(3) ≤ ζ(2)^{3/5}·ζ(9/2)^{2/5}` via `n⁻³ = n^{−6/5}·n^{−9/5}`, but the
second channel `s = 9/2` is off the Bernoulli lattice — the same obstruction
in analytic clothing.  Not formalized here.)

## The Bernoulli pinch (proved)

Through the uniquely selected half-slope pair, Cauchy–Schwarz on the frame
vectors pinches the odd value between its Bernoulli-closed neighbours:

`π⁴/90 ≤ ζ(3)`  and  `ζ(3)² ≤ ζ(2)·ζ(4) = π⁶/540`

(`zeta_three_bernoulli_pinch`).  Numerically: `1.0823 ≤ 1.20206 ≤ 1.33434`.

## Honest scope

No closed form for ζ(3) is claimed.  The naive target `ζ(3) = q·π³` (`q ∈ ℚ`)
is named (`ZetaThreeRationalPiCubeForm`) and is widely conjectured **false**
(ζ(3)/π³ is expected irrational).  The classical exact expression is the
Ramanujan–Lerch form `ζ(3) = 7π³/180 − 2∑_{k≥1} 1/(k³(e^{2πk}−1))` — a π³
term plus an exponentially small correction, which is the precise sense in
which the odd channel "almost" closes; formalizing it needs Eisenstein/modular
machinery not yet available here.
-/

namespace Hqiv.Story

open Complex Real Filter

noncomputable section

/-! ## ζ(3) as the odd frame line -/

/-- **Apéry's constant** as the odd frame-line readout: `ζ(3) = ∑ 1/n³`
(the `n = 0` term is `0` by convention, matching Mathlib's `hasSum_zeta_*`). -/
def zetaThree : ℝ :=
  ∑' n : ℕ, 1 / (n : ℝ) ^ 3

theorem summable_one_div_nat_cube :
    Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
  Real.summable_one_div_nat_pow.mpr (by norm_num)

theorem hasSum_zetaThree :
    HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 3) zetaThree :=
  summable_one_div_nat_cube.hasSum

theorem zetaThree_nonneg : 0 ≤ zetaThree :=
  tsum_nonneg fun n => by positivity

/-! ## The frame radius reads the zeta ladder -/

/-- Shift a Mathlib zeta-value sum from `1/n^k` to the frame indexing
`1/(n+1)^k` (the `n = 0` term vanishes). -/
theorem hasSum_shift_one {k : ℕ} (hk : k ≠ 0) {a : ℝ}
    (h : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ k) a) :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ k) a := by
  have h1 : HasSum (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ)) ^ k) a := by
    refine (hasSum_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ k) 1).mpr ?_
    simpa [Finset.sum_range_one, zero_pow hk] using h
  simpa [Nat.cast_add, Nat.cast_one] using h1

/-- On a real vertical line `σ` with `2σ = k`, the SO(4) frame radius is the
partial sum of the `k`-th power line. -/
theorem spectralFrameNormSq_real_line_eq {σ : ℝ} {k : ℕ}
    (hσ : 2 * σ = (k : ℝ)) (N : ℕ) :
    spectralFrameNormSq N ((σ : ℂ)) =
      ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1) ^ k := by
  rw [spectralFrameNormSq_eq]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [Complex.ofReal_re, hσ, Real.rpow_neg hpos.le, Real.rpow_natCast, one_div]

/-- Generic projection readout: the frame radius on the line `2σ = k`
converges to the sum of the `k`-th power line. -/
theorem frame_radius_tendsto_of_hasSum {σ : ℝ} {k : ℕ}
    (hσ : 2 * σ = (k : ℝ)) (hk : k ≠ 0) {a : ℝ}
    (h : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ k) a) :
    Tendsto (fun N => spectralFrameNormSq N ((σ : ℂ))) atTop (nhds a) := by
  have hs := (hasSum_shift_one hk h).tendsto_sum_nat
  have heq : (fun N => spectralFrameNormSq N ((σ : ℂ))) =
      fun N => ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1) ^ k :=
    funext (spectralFrameNormSq_real_line_eq hσ)
  rw [heq]
  exact hs

/-- `σ = 1`: the frame radius reads `ζ(2) = π²/6` (Bernoulli-closed). -/
theorem frame_radius_tendsto_zeta_two :
    Tendsto (fun N => spectralFrameNormSq N (((1 : ℝ) : ℂ))) atTop
      (nhds (π ^ 2 / 6)) :=
  frame_radius_tendsto_of_hasSum (k := 2) (by norm_num) (by norm_num)
    hasSum_zeta_two

/-- `σ = 3/2`: the frame radius reads `ζ(3)` (the odd Apéry line). -/
theorem frame_radius_tendsto_zeta_three :
    Tendsto (fun N => spectralFrameNormSq N (((3 / 2 : ℝ) : ℂ))) atTop
      (nhds zetaThree) :=
  frame_radius_tendsto_of_hasSum (k := 3) (by norm_num) (by norm_num)
    hasSum_zetaThree

/-- `σ = 2`: the frame radius reads `ζ(4) = π⁴/90` (the m = 4 Bernoulli
anchor). -/
theorem frame_radius_tendsto_zeta_four :
    Tendsto (fun N => spectralFrameNormSq N (((2 : ℝ) : ℂ))) atTop
      (nhds (π ^ 4 / 90)) :=
  frame_radius_tendsto_of_hasSum (k := 4) (by norm_num) (by norm_num)
    hasSum_zeta_four

/--
**Projection reads the zeta ladder.**  The SO(4) odd-sphere frame radius on
the vertical lines `σ = 1, 3/2, 2` converges to `ζ(2), ζ(3), ζ(4)`
respectively — finding a zeta value *is* projecting through the construction.
-/
theorem so4_frame_projection_reads_zeta_ladder :
    Tendsto (fun N => spectralFrameNormSq N (((1 : ℝ) : ℂ))) atTop
        (nhds (π ^ 2 / 6)) ∧
      Tendsto (fun N => spectralFrameNormSq N (((3 / 2 : ℝ) : ℂ))) atTop
        (nhds zetaThree) ∧
      Tendsto (fun N => spectralFrameNormSq N (((2 : ℝ) : ℂ))) atTop
        (nhds (π ^ 4 / 90)) :=
  ⟨frame_radius_tendsto_zeta_two, frame_radius_tendsto_zeta_three,
    frame_radius_tendsto_zeta_four⟩

/-! ## Monogamy weights versus half-slope weights on the Bernoulli lattice -/

/-- Re-export: the physical monogamy row is `(imprint, overlap) = (3/5, 2/5)`. -/
theorem monogamy_physical_weights :
    Hqiv.Foundation.MonogamyProjection.physical.imprint = 3 / 5 ∧
      Hqiv.Foundation.MonogamyProjection.physical.overlap = 2 / 5 :=
  ⟨Hqiv.Foundation.MonogamyProjection.physical_imprint,
    Hqiv.Foundation.MonogamyProjection.physical_overlap⟩

/--
**Parity obstruction.**  The monogamy weights `(3/5, 2/5)` can never combine
two even (Bernoulli-closed) channels into the cube channel `s = 3`: clearing
denominators forces `3a + 2b = 15`, even = odd.
-/
theorem monogamy_weights_cannot_reach_cube_channel :
    ∀ a b : ℕ, Even a → Even b →
      Hqiv.Foundation.MonogamyProjection.physical.imprint * (a : ℚ) +
        Hqiv.Foundation.MonogamyProjection.physical.overlap * (b : ℚ) ≠ 3 := by
  rintro a b ⟨x, rfl⟩ ⟨y, rfl⟩ h
  rw [Hqiv.Foundation.MonogamyProjection.physical_imprint,
    Hqiv.Foundation.MonogamyProjection.physical_overlap] at h
  have hq : 6 * (x : ℚ) + 4 * (y : ℚ) = 15 := by
    push_cast at h
    linarith
  have hn : 6 * x + 4 * y = 15 := by exact_mod_cast hq
  omega

/-- The half-slope weights `(1/2, 1/2)` reach the cube channel through the
even pair `(2, 4)`. -/
theorem balanced_half_slope_hits_bernoulli_pair :
    (1 / 2 : ℚ) * ((2 : ℕ) : ℚ) + (1 / 2 : ℚ) * ((4 : ℕ) : ℚ) = 3 := by
  norm_num

/--
**Uniqueness.**  The half-slope weights select the Bernoulli pair `(2, 4)`
uniquely among even Dirichlet channels `2 ≤ a ≤ b`: the `m = 4` anchor pair
`(ζ(2), ζ(4))` is the only even-closed pair the balanced split can use.
-/
theorem balanced_half_slope_pair_unique :
    ∀ a b : ℕ, Even a → Even b → 2 ≤ a → a ≤ b →
      (1 / 2 : ℚ) * (a : ℚ) + (1 / 2 : ℚ) * (b : ℚ) = 3 →
      a = 2 ∧ b = 4 := by
  rintro a b ⟨x, rfl⟩ ⟨y, rfl⟩ ha hab h
  have hq : (x : ℚ) + (y : ℚ) = 3 := by
    push_cast at h
    linarith
  have hn : x + y = 3 := by exact_mod_cast hq
  omega

/-! ## The Bernoulli pinch on ζ(3) -/

/-- **Lower Bernoulli wall**: `ζ(4) = π⁴/90 ≤ ζ(3)` (termwise domination). -/
theorem zeta_four_le_zetaThree : π ^ 4 / 90 ≤ zetaThree := by
  rw [← hasSum_zeta_four.tsum_eq]
  refine Summable.tsum_le_tsum (fun n => ?_) hasSum_zeta_four.summable
    hasSum_zetaThree.summable
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hp : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
    exact one_div_le_one_div_of_le hp (pow_le_pow_right₀ h1 (by norm_num))

/--
**Upper Bernoulli wall (Cauchy–Schwarz through the frame pair).**  Splitting
the cube line as `n⁻³ = n⁻¹ · n⁻²` and applying Cauchy–Schwarz against the
uniquely selected half-slope pair `(ζ(2), ζ(4))`:
`ζ(3) ≤ √(ζ(2)·ζ(4)) = √(π⁶/540)`.
-/
theorem zetaThree_le_sqrt : zetaThree ≤ Real.sqrt (π ^ 6 / 540) := by
  refine Summable.tsum_le_of_sum_le hasSum_zetaThree.summable fun s => ?_
  have hfg : ∀ n : ℕ, (1 / (n : ℝ)) * (1 / (n : ℝ) ^ 2) = 1 / (n : ℝ) ^ 3 := by
    intro n
    rw [div_mul_div_comm, one_mul, ← pow_succ']
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun n => 1 / (n : ℝ)) (fun n => 1 / (n : ℝ) ^ 2)
  have hsq1 : ∀ n : ℕ, ((1 : ℝ) / (n : ℝ)) ^ 2 = 1 / (n : ℝ) ^ 2 := by
    intro n
    rw [div_pow, one_pow]
  have hsq2 : ∀ n : ℕ, ((1 : ℝ) / (n : ℝ) ^ 2) ^ 2 = 1 / (n : ℝ) ^ 4 := by
    intro n
    rw [div_pow, one_pow, ← pow_mul]
  simp only [hfg, hsq1, hsq2] at hCS
  have h2 : ∑ n ∈ s, 1 / (n : ℝ) ^ 2 ≤ π ^ 2 / 6 := by
    rw [← hasSum_zeta_two.tsum_eq]
    exact hasSum_zeta_two.summable.sum_le_tsum s fun i _ => by positivity
  have h4 : ∑ n ∈ s, 1 / (n : ℝ) ^ 4 ≤ π ^ 4 / 90 := by
    rw [← hasSum_zeta_four.tsum_eq]
    exact hasSum_zeta_four.summable.sum_le_tsum s fun i _ => by positivity
  have hnn4 : (0 : ℝ) ≤ ∑ n ∈ s, 1 / (n : ℝ) ^ 4 :=
    Finset.sum_nonneg fun i _ => by positivity
  have hnn3 : (0 : ℝ) ≤ ∑ n ∈ s, 1 / (n : ℝ) ^ 3 :=
    Finset.sum_nonneg fun i _ => by positivity
  have hbound : (∑ n ∈ s, 1 / (n : ℝ) ^ 3) ^ 2 ≤ π ^ 6 / 540 := by
    calc (∑ n ∈ s, 1 / (n : ℝ) ^ 3) ^ 2
        ≤ (∑ n ∈ s, 1 / (n : ℝ) ^ 2) * ∑ n ∈ s, 1 / (n : ℝ) ^ 4 := hCS
      _ ≤ (π ^ 2 / 6) * (π ^ 4 / 90) := mul_le_mul h2 h4 hnn4 (by positivity)
      _ = π ^ 6 / 540 := by ring
  calc ∑ n ∈ s, 1 / (n : ℝ) ^ 3
      = Real.sqrt ((∑ n ∈ s, 1 / (n : ℝ) ^ 3) ^ 2) := (Real.sqrt_sq hnn3).symm
    _ ≤ Real.sqrt (π ^ 6 / 540) := Real.sqrt_le_sqrt hbound

/-- Squared form of the upper wall: `ζ(3)² ≤ ζ(2)·ζ(4) = π⁶/540`. -/
theorem zetaThree_sq_le : zetaThree ^ 2 ≤ π ^ 6 / 540 := by
  have hC : (0 : ℝ) ≤ π ^ 6 / 540 := by positivity
  calc zetaThree ^ 2
      ≤ Real.sqrt (π ^ 6 / 540) ^ 2 := by
        gcongr
        exacts [zetaThree_nonneg, zetaThree_le_sqrt]
    _ = π ^ 6 / 540 := Real.sq_sqrt hC

/--
**The Bernoulli pinch.**  The odd frame line is sandwiched between its two
Bernoulli-closed half-slope neighbours:

`π⁴/90 ≤ ζ(3)` and `ζ(3)² ≤ π⁶/540`  (so `ζ(3) ≤ π³/√540 ≈ 1.3343`).

This is the closed-form *sandwich* the construction delivers; a closed-form
*value* would require closing the odd channel itself.
-/
theorem zeta_three_bernoulli_pinch :
    π ^ 4 / 90 ≤ zetaThree ∧ zetaThree ^ 2 ≤ π ^ 6 / 540 :=
  ⟨zeta_four_le_zetaThree, zetaThree_sq_le⟩

/-! ## The honest open slot -/

/--
**Naive closed-form target (open, expected FALSE).**  `ζ(3) = q·π³` for some
rational `q`.  This is the only shape a "Bernoulli-analogy" closed form could
take, and ζ(3)/π³ is widely conjectured irrational — so this Prop is named to
*calibrate* the target, not to pursue it.  The classical exact expression is
Ramanujan–Lerch: `ζ(3) = 7π³/180 − 2∑_{k≥1} 1/(k³(e^{2πk}−1))`, a π³ term
minus an exponentially small correction; the correction is precisely the odd
channel's failure to close.
-/
def ZetaThreeRationalPiCubeForm : Prop :=
  ∃ q : ℚ, zetaThree = (q : ℝ) * π ^ 3

/-- Any rational-π³ form would be pinched by the Bernoulli walls. -/
theorem zeta_three_rational_pi_cube_form_pinched
    (h : ZetaThreeRationalPiCubeForm) :
    ∃ q : ℚ, zetaThree = (q : ℝ) * π ^ 3 ∧
      π ^ 4 / 90 ≤ (q : ℝ) * π ^ 3 ∧
      ((q : ℝ) * π ^ 3) ^ 2 ≤ π ^ 6 / 540 := by
  obtain ⟨q, hq⟩ := h
  exact ⟨q, hq, hq ▸ zeta_four_le_zetaThree, hq ▸ zetaThree_sq_le⟩

/--
**Capstone.**  The half-slope weights uniquely select the `(ζ(2), ζ(4))`
Bernoulli pair (the `m = 4` anchor), the monogamy weights provably cannot
reach the cube channel through the Bernoulli lattice, and the selected pair
pinches ζ(3) between closed forms.
-/
theorem half_slope_selects_and_pinches_zeta_three :
    ((1 / 2 : ℚ) * ((2 : ℕ) : ℚ) + (1 / 2 : ℚ) * ((4 : ℕ) : ℚ) = 3) ∧
      (∀ a b : ℕ, Even a → Even b →
        Hqiv.Foundation.MonogamyProjection.physical.imprint * (a : ℚ) +
          Hqiv.Foundation.MonogamyProjection.physical.overlap * (b : ℚ) ≠ 3) ∧
      (π ^ 4 / 90 ≤ zetaThree ∧ zetaThree ^ 2 ≤ π ^ 6 / 540) :=
  ⟨balanced_half_slope_hits_bernoulli_pair,
    monogamy_weights_cannot_reach_cube_channel,
    zeta_three_bernoulli_pinch⟩

end

end Hqiv.Story

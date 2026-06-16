import Hqiv.Story.S3ZeroHolonomyGoldbachChain
import Mathlib.Analysis.PSeries

/-!
# TUFT nested frame tower: odd spheres `S^{2N−1}` and the harmonic radius
# ladder

This module formalizes what the TUFT nested fibration — odd spheres
`S^{2n+1}` for every `n` — buys for the zeta story.

## The frame tower

At level `N`, the first `N` spectral lines assemble into the frame vector
`(1^{−s}, 2^{−s}, …, N^{−s}) ∈ ℂ^N`; its normalized version lives on the
odd sphere `S^{2N−1}`.  The provable structure is carried by the squared
radius `spectralFrameNormSq N s = ∑_{n≤N} ‖n^{−s}‖²`:

* **Nesting** (`spectralFrameNormSq_succ`): each level embeds in the next,
  with the new line's weight as the increment — the tower recursion of the
  nested fibration.
* **σ-blindness** (`spectralFrameNormSq_eq_of_re_eq`): the radius reads only
  `Re s`; the vertical flow `s ↦ s + it` moves the frame along an
  anisotropic torus orbit *on the sphere of fixed radius* — every level of
  the tower is rigid under the flow.
* **Positivity** (`spectralFrameNormSq_pos`): the radius never degenerates;
  the normalized frame always lands on a genuine `S^{2N−1}`.

## What the further rigidity buys: a ladder of locators

**The harmonic radius law** (`frame_radius_eq_harmonic_iff`): for every
level `N ≥ 2`,
\[
  \texttt{spectralFrameNormSq}\,N\,s = H_N
  \quad\Longleftrightarrow\quad
  \Re s = \tfrac12,
\]
where `H_N = harmonicPartialSum N` is the harmonic backbone of the closure
story.  The critical line is the unique vertical line on which the nested
sphere radii reproduce the harmonic ladder — *the divergent series that
forced `Δ` and closed `so(3)+Δ` to `so(4)` in the first place*.  The loop
closes: the geometry the harmonic divergence created is pinned back to the
line by the same harmonic values, level by level, for all `N`.

Consequences:

* `RH_iff_zero_frame_tower_harmonic`: **RH ⟺ at every nontrivial zero the
  whole tower carries harmonic radii** — an infinite ladder of equivalent
  reformulations, one per level, all collapsing to the single bit.
* `frame_tower_diverges_on_line`: on the critical line the radius ladder
  diverges (`H_N → ∞`, Mathlib) — the tower at `σ = 1/2` rebuilds the
  harmonic divergence.
* `frame_radius_le_curvature_on_line`: on the line the radii are dominated
  by the curvature channel, `spectralFrameNormSq N s = H_N ≤ K(N)` — the
  closure paper's `H_n ≤ K(n)` now reads as a curvature bound on the nested
  sphere radii.

## Honest scope

The tower adds *consistency rigidity*: infinitely many independent locators
(one per level) provably name the same line, and the on-line radii are
exactly the closure backbone.  It does not add a forcing mechanism beyond
the single-channel statement already proved equivalent to RH — each new
level is RH-equivalent, not RH-implying.
-/

namespace Hqiv.Story

open Complex Filter

noncomputable section

/-! ## The frame radius -/

/-- Squared radius of the level-`N` spectral frame
`(1^{−s}, …, N^{−s}) ∈ ℂ^N`. -/
noncomputable def spectralFrameNormSq (N : ℕ) (s : ℂ) : ℝ :=
  ∑ n ∈ Finset.range N, ‖so4SpectralLine (n + 1) s‖ ^ 2

/-- The radius in closed form: `∑_{n<N} (n+1)^{−2σ}`. -/
theorem spectralFrameNormSq_eq (N : ℕ) (s : ℂ) :
    spectralFrameNormSq N s =
      ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-(2 * s.re)) := by
  unfold spectralFrameNormSq
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [spectral_weights_consistent_at_any_sigma (Nat.succ_pos n)]
  norm_cast

/-- **Nesting recursion**: level `N+1` is level `N` plus the new line's
weight — the tower step of the nested fibration. -/
theorem spectralFrameNormSq_succ (N : ℕ) (s : ℂ) :
    spectralFrameNormSq (N + 1) s =
      spectralFrameNormSq N s + ‖so4SpectralLine (N + 1) s‖ ^ 2 :=
  Finset.sum_range_succ _ _

/-- **σ-blindness of the whole tower**: each level's radius reads only
`Re s`; the vertical flow moves the frame on a sphere of fixed radius. -/
theorem spectralFrameNormSq_eq_of_re_eq {s t : ℂ} (h : s.re = t.re)
    (N : ℕ) : spectralFrameNormSq N s = spectralFrameNormSq N t := by
  rw [spectralFrameNormSq_eq, spectralFrameNormSq_eq, h]

/-- The radius never degenerates: the normalized frame always lands on a
genuine odd sphere `S^{2N−1}`. -/
theorem spectralFrameNormSq_pos {N : ℕ} (hN : 1 ≤ N) (s : ℂ) :
    0 < spectralFrameNormSq N s := by
  rw [spectralFrameNormSq_eq]
  refine Finset.sum_pos (fun n _ => ?_) ?_
  · exact Real.rpow_pos_of_pos (by positivity) _
  · exact ⟨0, Finset.mem_range.mpr (by omega)⟩

/-! ## The harmonic radius law -/

/-- On the critical line, the level-`N` radius is exactly the harmonic
partial sum `H_N` — the closure backbone. -/
theorem frame_radius_on_line {s : ℂ} (hs : s.re = (1 / 2 : ℝ)) (N : ℕ) :
    spectralFrameNormSq N s = harmonicPartialSum N := by
  rw [spectralFrameNormSq_eq]
  unfold harmonicPartialSum
  refine Finset.sum_congr rfl fun n _ => ?_
  have hexp : -(2 * s.re) = (-1 : ℝ) := by rw [hs]; norm_num
  rw [hexp, Real.rpow_neg_one, one_div]

/-- **The harmonic radius law (locator at every level).**  For each level
`N ≥ 2`, the radius equals the harmonic backbone `H_N` exactly on the
critical line.  An infinite ladder of locators, all naming the same line. -/
theorem frame_radius_eq_harmonic_iff {N : ℕ} (hN : 2 ≤ N) {s : ℂ} :
    spectralFrameNormSq N s = harmonicPartialSum N ↔
      s.re = (1 / 2 : ℝ) := by
  constructor
  · intro h
    by_contra hσ
    rcases lt_or_gt_of_ne hσ with hlt | hgt
    · -- σ < 1/2 : every term ≥ harmonic, strictly at the base-2 line
      have hgtsum : harmonicPartialSum N < spectralFrameNormSq N s := by
        rw [spectralFrameNormSq_eq]
        unfold harmonicPartialSum
        refine Finset.sum_lt_sum (fun i _ => ?_) ⟨1, Finset.mem_range.mpr (by omega), ?_⟩
        · have hb : (1 : ℝ) ≤ (i : ℝ) + 1 := by
            have := Nat.cast_nonneg (α := ℝ) i
            linarith
          have hexp : (-1 : ℝ) ≤ -(2 * s.re) := by linarith
          calc (1 : ℝ) / ((i : ℝ) + 1)
              = ((i : ℝ) + 1) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, one_div]
            _ ≤ ((i : ℝ) + 1) ^ (-(2 * s.re)) :=
                Real.rpow_le_rpow_of_exponent_le hb hexp
        · have hb : (1 : ℝ) < ((1 : ℕ) : ℝ) + 1 := by norm_num
          have hexp : (-1 : ℝ) < -(2 * s.re) := by linarith
          calc (1 : ℝ) / (((1 : ℕ) : ℝ) + 1)
              = (((1 : ℕ) : ℝ) + 1) ^ (-1 : ℝ) := by
                rw [Real.rpow_neg_one, one_div]
            _ < (((1 : ℕ) : ℝ) + 1) ^ (-(2 * s.re)) :=
                Real.rpow_lt_rpow_of_exponent_lt hb hexp
      linarith
    · -- σ > 1/2 : every term ≤ harmonic, strictly at the base-2 line
      have hltsum : spectralFrameNormSq N s < harmonicPartialSum N := by
        rw [spectralFrameNormSq_eq]
        unfold harmonicPartialSum
        refine Finset.sum_lt_sum (fun i _ => ?_) ⟨1, Finset.mem_range.mpr (by omega), ?_⟩
        · have hb : (1 : ℝ) ≤ (i : ℝ) + 1 := by
            have := Nat.cast_nonneg (α := ℝ) i
            linarith
          have hexp : -(2 * s.re) ≤ (-1 : ℝ) := by linarith
          calc ((i : ℝ) + 1) ^ (-(2 * s.re))
              ≤ ((i : ℝ) + 1) ^ (-1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hb hexp
            _ = (1 : ℝ) / ((i : ℝ) + 1) := by rw [Real.rpow_neg_one, one_div]
        · have hb : (1 : ℝ) < ((1 : ℕ) : ℝ) + 1 := by norm_num
          have hexp : -(2 * s.re) < (-1 : ℝ) := by linarith
          calc (((1 : ℕ) : ℝ) + 1) ^ (-(2 * s.re))
              < (((1 : ℕ) : ℝ) + 1) ^ (-1 : ℝ) :=
                Real.rpow_lt_rpow_of_exponent_lt hb hexp
            _ = (1 : ℝ) / (((1 : ℕ) : ℝ) + 1) := by
                rw [Real.rpow_neg_one, one_div]
      linarith
  · intro hs
    exact frame_radius_on_line hs N

/-! ## Consequences -/

/-- **RH ⟺ the whole tower carries harmonic radii at every zero.**  One
RH-equivalent locator per level of the TUFT tower, all collapsing to the
same bit. -/
theorem RH_iff_zero_frame_tower_harmonic :
    RiemannHypothesis ↔
      ∀ ρ : ℂ, IsNontrivialZetaZero ρ → ∀ N : ℕ, 2 ≤ N →
        spectralFrameNormSq N ρ = harmonicPartialSum N := by
  constructor
  · intro hRH ρ hz N hN
    exact (frame_radius_eq_harmonic_iff hN).mpr (hRH ρ hz.1 hz.2.1 hz.2.2)
  · intro hW ρ hz hnt h1
    exact (frame_radius_eq_harmonic_iff (le_refl 2)).mp
      (hW ρ ⟨hz, hnt, h1⟩ 2 (le_refl 2))

/-- **The tower rebuilds the harmonic divergence on the line**: the radius
ladder tends to infinity — the same divergence that forced `Δ`. -/
theorem frame_tower_diverges_on_line {s : ℂ} (hs : s.re = (1 / 2 : ℝ)) :
    Tendsto (fun N => spectralFrameNormSq N s) atTop atTop := by
  have heq : (fun N => spectralFrameNormSq N s) = harmonicPartialSum := by
    funext N
    exact frame_radius_on_line hs N
  rw [heq, show harmonicPartialSum =
      fun n => ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1) : ℝ) from
    funext fun n => rfl]
  exact Real.tendsto_sum_range_one_div_nat_succ_atTop

/-- **Curvature dominates the tower on the line**: the closure inequality
`H_N ≤ K(N)` reads as a curvature bound on the nested sphere radii. -/
theorem frame_radius_le_curvature_on_line {s : ℂ}
    (hs : s.re = (1 / 2 : ℝ)) (N : ℕ) :
    spectralFrameNormSq N s ≤ Hqiv.curvature_integral N := by
  rw [frame_radius_on_line hs N]
  exact harmonicPartialSum_le_curvatureChannel N

end

end Hqiv.Story

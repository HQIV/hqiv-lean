import Hqiv.Story.S3TwiddleRigidityForcesLine
import Hqiv.Story.S3ClosureDeltaLiftBridge
import Hqiv.Story.S3FESlotDischarge
import Hqiv.Story.S3RHZeroSetBridge
import Hqiv.Algebra.CliffordHQIVSlotRefinement
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Δ ≠ 0: full orbits accumulate residual off the critical strip

The closure spine forces a **nonzero phase-lift connector** `Δ` (`phaseLiftDelta_ne_zero`):
the harmonic channel diverges (`curvatureChannel_strictly_increasing`), `SO(3)+Δ`
closes to `SO(4)`, and the twiddle orbit does not merely erase data — it **relocates**
the real σ-line where the projection vanishes (`projectionLine`, `twiddle_shift_avoids_critical_center`).

On the arithmetic side, nontrivial zeros cannot live where `Re(s) > 1` (Mathlib
nonvanishing). Reflecting across the functional equation `s ↦ 1-s` sends `Re(s) < 0`
to `Re(1-s) > 1`, so the same nonvanishing excludes nontrivial zeros on the left as
well. What remains is the open strip `0 ≤ Re(s) ≤ 1`, where exact 45° twiddle
pins zeros to `Re = 1/2`.

This is the easy global half of the witness: **off-strip ⇒ nonzero ζ**; **in-strip +
exact twiddle + zero ⇒ on line** (already in `S3TwiddleRigidityForcesLine`).
-/

namespace Hqiv.Story

noncomputable section

open Complex

/-! ### Δ is always nonzero (phase-lift connector) -/

/-- Re-export: the phase-lift / connector generator is never zero. -/
theorem delta_always_nonzero : Hqiv.phaseLiftDelta ≠ 0 :=
  Hqiv.Algebra.phaseLiftDelta_ne_zero

/-- Re-export: harmonic divergence forces the closure carrier including `Δ₄`. -/
theorem harmonic_divergence_forces_delta_lift :
    StrictMono Hqiv.curvature_integral ∧
      SO4So3DeltaLie = SO4Lie :=
  ⟨curvatureChannel_strictly_increasing, so3_delta_lifts_to_so4⟩

/-! ### Projection readout is nonzero off the critical line -/

/-- Exact 45° readout cannot vanish away from `Re = 1/2`. -/
theorem exact_twiddle_nonzero_off_line (s : ℂ) (h : s.re ≠ (1 / 2 : ℝ)) :
    exactTwiddleReadout s ≠ 0 :=
  fun h0 => h ((exact_twiddle_zero_iff_on_line s).mp h0)

/-! ### Mathlib: no nontrivial zeros with `Re > 1` -/

/-- A zero of `ζ` reflects to a zero at `1 - s` (functional equation factor kills). -/
theorem riemannZeta_zero_reflects (s : ℂ) (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1)
    (hz : riemannZeta s = 0) :
    riemannZeta (1 - s) = 0 := by
  rw [riemannZeta_one_sub hs hs', hz, mul_zero]

/-- Nontrivial zeros cannot lie to the right of the strip. -/
theorem nontrivial_zero_not_right_of_strip (s : ℂ) (h : IsNontrivialZetaZero s) :
    ¬ 1 < s.re :=
  fun hs => (riemannZeta_ne_zero_of_one_lt_re hs) h.1

/-- Zeros with `Re < 0` reflect to `Re > 1`, contradicting nonvanishing. -/
theorem zeta_zero_not_left_of_strip (s : ℂ) (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1)
    (hz : riemannZeta s = 0) : ¬ s.re < 0 := by
  intro hneg
  have hz1s : riemannZeta (1 - s) = 0 := riemannZeta_zero_reflects s hs hs' hz
  have hgt : 1 < (1 - s).re := by
    simp only [sub_re, one_re]
    linarith
  exact (riemannZeta_ne_zero_of_one_lt_re hgt) hz1s

/-- Nontrivial zeros cannot lie to the left of the strip (FE + right nonvanishing). -/
theorem nontrivial_zero_not_left_of_strip (s : ℂ) (h : IsNontrivialZetaZero s)
    (hFE : ∀ n : ℕ, s ≠ -n) : ¬ s.re < 0 :=
  zeta_zero_not_left_of_strip s hFE h.2.2 h.1

/-- Nontrivial zeros sit in the closed strip `0 ≤ Re ≤ 1` once the FE slot is available. -/
theorem nontrivial_zero_in_closed_strip (s : ℂ) (h : IsNontrivialZetaZero s)
    (hFE : ∀ n : ℕ, s ≠ -n) :
    0 ≤ s.re ∧ s.re ≤ 1 := by
  constructor
  · exact le_of_not_gt (fun hneg => nontrivial_zero_not_left_of_strip s h hFE hneg)
  · exact le_of_not_gt (fun hgt => nontrivial_zero_not_right_of_strip s h hgt)

/-- Left-strip exclusion without an explicit FE hypothesis (discharged in `S3FESlotDischarge`). -/
theorem nontrivial_zero_not_left_unconditional (s : ℂ) (h : IsNontrivialZetaZero s) :
    ¬ s.re < 0 :=
  nontrivial_zero_not_left_of_strip s h (nontrivial_zero_fe_slot s h)

/-- Closed-strip confinement without an explicit FE hypothesis. -/
theorem nontrivial_zero_in_closed_strip_unconditional (s : ℂ) (h : IsNontrivialZetaZero s) :
    0 ≤ s.re ∧ s.re ≤ 1 :=
  nontrivial_zero_in_closed_strip s h (nontrivial_zero_fe_slot s h)

/-- Nontrivial zeros cannot sit on `Re = 0`. -/
theorem nontrivial_zero_re_pos (s : ℂ) (h : IsNontrivialZetaZero s) : 0 < s.re := by
  by_contra hnonpos
  have hre0 : s.re ≤ 0 := le_of_not_gt hnonpos
  rcases le_iff_eq_or_lt.mp hre0 with hre0 | hneg
  · by_cases h0 : s = 0
    · subst h0
      simpa [riemannZeta_zero] using h.1
    have hz1s : riemannZeta (1 - s) = 0 :=
      riemannZeta_zero_reflects s (nontrivial_zero_fe_slot s h) h.2.2 h.1
    have h1le : (1 : ℝ) ≤ (1 - s).re := by
      simp only [sub_re, one_re, hre0]
      norm_num
    exact absurd hz1s (riemannZeta_ne_zero_of_one_le_re h1le)
  · exact nontrivial_zero_not_left_unconditional s h hneg

/-- Nontrivial zeros cannot sit on `Re = 1`. -/
theorem nontrivial_zero_re_lt_one (s : ℂ) (h : IsNontrivialZetaZero s) : s.re < 1 := by
  by_contra hnot
  have hge : (1 : ℝ) ≤ s.re := le_of_not_gt hnot
  exact absurd h.1 (riemannZeta_ne_zero_of_one_le_re hge)

/-- Nontrivial zeros lie in the open critical strip. -/
theorem nontrivial_zero_open_strip (s : ℂ) (h : IsNontrivialZetaZero s) :
    0 < s.re ∧ s.re < 1 :=
  ⟨nontrivial_zero_re_pos s h, nontrivial_zero_re_lt_one s h⟩

/--
**Geometric + arithmetic packaging.** `Δ` is always active; twiddle orbits shift the
projection line; off the critical line the exact readout is nonzero; off the strip
`ζ` itself is nonzero for nontrivial zeros.
-/
theorem delta_orbit_off_strip_nonzero_layer :
    Hqiv.phaseLiftDelta ≠ 0 ∧
      (∀ δ : ℝ, Real.sin δ ≠ 0 →
        ∀ σ : ℝ, rotFree (Real.pi / 4 + δ) (functionalPair σ) = 0 → σ ≠ (1 / 2 : ℝ)) ∧
      (∀ s : ℂ, s.re ≠ (1 / 2 : ℝ) → exactTwiddleReadout s ≠ 0) ∧
      (∀ s : ℂ, IsNontrivialZetaZero s → ¬ 1 < s.re) :=
  ⟨delta_always_nonzero,
   fun δ hδ => twiddle_shift_avoids_critical_center δ hδ,
   exact_twiddle_nonzero_off_line,
   nontrivial_zero_not_right_of_strip⟩

end

end Hqiv.Story

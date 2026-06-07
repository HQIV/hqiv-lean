import Hqiv.Story.S3ClosureDeltaLiftBridge
import Hqiv.Story.S3HarmonicPrimeZetaPath
import Hqiv.Story.S3SO4ZetaProjectionClosedForm
import Hqiv.Geometry.OctonionicLightCone

/-!
# Δ as harmonic orbit: the `1/3` slot and the `~1.2` projection

`Δ` is **not** identical to the harmonic partial sum `H_n`, but it is **forced by it**:
the closure spine proves `H_n ≤ K(n)` and

`K(n) = H_n + α · ∑ log(i+1)/(i+1)`,

so every orbit step of the SO(4) carrier carries the harmonic divergence plus the
`α`-weighted log channel (`curvature_integral_eq_harmonic_plus_alpha_log`).

On the **8-shell** (`OctonionSphereConstruction`), the unit sphere area is `π⁴/3`.
Orbiting the 45° equator **against that `/3`** halves it to `π⁴/6` — the same
`/6` Bernoulli slot as `ζ(2) = π²/6`, but at **π⁴** power on the even sphere
sector (`so4EquatorHalfArea_eq_pi_four_sixths`).

The **third harmonic orbit** is where the `1/3` term first enters `H_3`.  At that
shell the curvature/harmonic **projection ratio** crosses **~1.2**:

* **exact HQIV multiplier:** `1 + α/3 = 1 + (3/5)/3 = 6/5 = 1.2`;
* **numeric orbit ratio:** `K(3)/H(3) ≈ 1.23` (curvature integral over harmonic sum).

The even channel in `S3SO4InteriorWitness` is still additively degenerate on the
open strip (`oddStripChannel = ζ` forces `evenStripChannel = 0` for `even + odd = ζ`).
This module records the **harmonic–Δ orbit multiplier** that the even sector carries
before that degenerate split.
-/

namespace Hqiv.Story

noncomputable section

open Real Complex

/-! ## Δ sits on top of the harmonic series -/

/-- Re-export: `K(n)` dominates the harmonic partial sum at every shell. -/
theorem delta_forced_by_harmonic (n : ℕ) :
    harmonicPartialSum n ≤ Hqiv.curvature_integral n :=
  harmonic_channel_lower_bound n

/-- Re-export: `K(n) = H_n + α · log-weighted harmonic tail`. -/
theorem curvature_is_harmonic_plus_alpha_log (n : ℕ) :
    Hqiv.curvature_integral n =
      harmonicPartialSum n + Hqiv.alpha * Hqiv.logWeightedSum n :=
  Hqiv.curvature_integral_eq_harmonic_plus_alpha_log n

/-! ## Third orbit: the `1/3` slot -/

/-- Shell index where `H_n` first includes the `1/3` harmonic term (`H_3 = 11/6`). -/
def harmonicThirdShell : ℕ := 3

theorem harmonicPartialSum_three :
    harmonicPartialSum 3 = 11 / 6 := by
  unfold harmonicPartialSum
  norm_num [Finset.sum_range_succ]

/-- Curvature/harmonic projection ratio at orbit step `n`. -/
noncomputable def harmonicOrbitProjection (n : ℕ) (hn : 0 < n) : ℝ :=
  Hqiv.curvature_integral n / harmonicPartialSum n

theorem harmonicOrbitProjection_three_pos :
    0 < harmonicOrbitProjection harmonicThirdShell (by decide : 0 < 3) := by
  unfold harmonicOrbitProjection harmonicThirdShell
  have hHpos : (0 : ℝ) < harmonicPartialSum 3 := by
    rw [harmonicPartialSum_three]
    norm_num
  have hK : (0 : ℝ) < Hqiv.curvature_integral 3 := Hqiv.curvature_integral_pos (by decide)
  exact div_pos hK hHpos

/-! ## The `~1.2` projection against `1/3` -/

/--
**Exact HQIV readout.** Orbiting the SO(4) carrier against the `1/3` slot with
`α = 3/5` gives the projection multiplier `1 + α/3 = 6/5 = 1.2`.
-/
noncomputable def so4HarmonicThirdProjection : ℝ :=
  1 + Hqiv.alpha / 3

theorem so4HarmonicThirdProjection_eq_six_fifths :
    so4HarmonicThirdProjection = 6 / 5 := by
  unfold so4HarmonicThirdProjection Hqiv.alpha
  norm_num

theorem so4HarmonicThirdProjection_eq_one_point_two :
    so4HarmonicThirdProjection = 1.2 := by
  rw [so4HarmonicThirdProjection_eq_six_fifths]
  norm_num

/--
**α–third identity.** The `1/3` orbit against `α = 3/5` contributes exactly `1/5`
to the projection above unity.
-/
theorem alpha_third_orbit_is_one_fifth :
    Hqiv.alpha / 3 = 1 / 5 := by
  unfold Hqiv.alpha
  norm_num

/--
**Sphere halving against `/3`.** The `π⁴/3` unit 7-sphere area halves at the
45° equator to `π⁴/6`; this is the even-sector `/6` parallel to `ζ(2) = π²/6`.
-/
theorem pi_four_thirds_halved_is_pi_four_sixths :
    (Real.pi ^ 4 / 3) / 2 = Real.pi ^ 4 / 6 := by
  ring

/-! ## Even-sector packaging -/

/--
Harmonic–Δ even-sector multiplier on the third orbit (`6/5`).

On `Re > 1` the even channel is the Dirichlet/Euler shell sum (`zetaEvenDirichletSO4`).
On the open strip the **physical** even content is this orbit multiplier against the
`π⁴/3` sphere; the additive `evenStripChannel` in `S3SO4InteriorWitness` stays `0`
only because the proved FE closed form already packages the full `ζ` in the odd slot.
-/
noncomputable def harmonicEvenOrbitMultiplier : ℝ :=
  so4HarmonicThirdProjection

theorem harmonicEvenOrbitMultiplier_eq_six_fifths :
    harmonicEvenOrbitMultiplier = 6 / 5 :=
  so4HarmonicThirdProjection_eq_six_fifths

/-- On `Re > 1`, the even channel is the shell/Euler sum (= `ζ`). -/
theorem even_dirichlet_is_zeta_on_right_half {s : ℂ} (hs : 1 < s.re) :
    zetaEvenDirichletSO4 s = riemannZeta s :=
  zeta_even_dirichlet_so4_eq_zeta hs

end

end Hqiv.Story

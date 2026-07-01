import Hqiv.Story.S3FortyFiveProjection
import Hqiv.Geometry.AlphaGammaForcedByLattice
import Hqiv.Foundation.MonogamyProjection

/-!
# Dimension-indexed imprint projection and the unit-split symmetry axis

This module separates two projection planes that are easy to conflate:

1. **Functional-equation plane** `(σ, 1 − σ)` — the 45° rotation in
   `S3FortyFiveProjection` sends the free coordinate to zero exactly on
   `Re(s) = 1/2` (the critical-line equator).

2. **Imprint–overlap budget plane** `(α_d, γ_d)` with `α_d + γ_d = 1` and
   `α_d = d / (2d − 1)`, `γ_d = (d − 1) / (2d − 1)` for transverse dimension `d ≥ 1`.

On the budget plane the same diagonal/free rotation separates **total unit budget**
(fixed diagonal) from **imprint–overlap skew** (free axis). The skew magnitude is
`1 / (2d − 1)` — the same denominator that forces `α_d`.

## What is proved here

* Closed forms at `d = 1, 2, 3, 4` and the general unit-split identity.
* The free-axis skew `|α_d − γ_d| = 1 / (2d − 1)`.
* The **2D–3D coupling** `α₂ · α₃ = γ₃` (special; not generic in `d`).
* Compatibility: `α₃ = 3/5` matches the octonion-lattice `alpha` from
  `AlphaGammaForcedByLattice`.
* The **4D Hodge/BSD-facing row** `α₄ = 4/7`, `γ₄ = 3/7`, with skew denominator
  `7` for the four-dimensional fibre upgrade.

## What is *not* claimed

* No proof that projecting `SO(n)` at angles `arccos(α_d)` yields Navier–Stokes
  regularity (2D or 3D) or Bekenstein–Hawking entropy.
* Those readings are recorded only as conjecture/coherence slots for future bridges
  (`NSRemainingObligations`, 3d-causal-growth thermodynamic appendix).
-/

namespace Hqiv.Story

noncomputable section

open Hqiv

/-! ## Dimension-indexed imprint family (rational spine) -/

/-- Transverse null dimension must be at least one. -/
def TransverseDim := { d : ℕ // 1 ≤ d }

namespace TransverseDim

@[simp] def val (d : TransverseDim) : ℕ := d.1

@[simp] theorem one_le_val (d : TransverseDim) : 1 ≤ d.val := d.2

/-- Rational denominator `2d − 1` (avoids nat-subtraction cast mismatches). -/
def imprintDenQ (d : TransverseDim) : ℚ :=
  (2 * (d.val : ℚ)) - 1

/-- Common denominator `2d − 1` for the imprint family (natural audit form). -/
def imprintDenom (d : TransverseDim) : ℕ :=
  2 * d.val - 1

theorem imprintDenQ_eq_cast (d : TransverseDim) :
    imprintDenQ d = (imprintDenom d : ℚ) := by
  unfold imprintDenQ imprintDenom
  have h2 : 1 ≤ 2 * d.val := by
    calc
      (1 : ℕ) ≤ d.val := d.2
      _ ≤ 2 * d.val := by omega
  rw [Nat.cast_sub h2]
  push_cast
  ring

theorem imprintDenom_pos (d : TransverseDim) : 0 < imprintDenom d := by
  have : 1 ≤ d.val := d.2
  unfold imprintDenom
  omega

theorem imprintDenom_ne_zero (d : TransverseDim) : imprintDenom d ≠ 0 :=
  Nat.ne_of_gt (imprintDenom_pos d)

@[simp] theorem imprintDenom_one : imprintDenom ⟨1, by decide⟩ = 1 := by
  unfold imprintDenom
  rfl

@[simp] theorem imprintDenom_two : imprintDenom ⟨2, by decide⟩ = 3 := by
  unfold imprintDenom
  rfl

@[simp] theorem imprintDenom_three : imprintDenom ⟨3, by decide⟩ = 5 := by
  unfold imprintDenom
  rfl

@[simp] theorem imprintDenom_four : imprintDenom ⟨4, by decide⟩ = 7 := by
  unfold imprintDenom
  rfl

/-- Imprint fraction `α_d = d / (2d − 1)` (rational form for audit). -/
def imprintAlpha (d : TransverseDim) : ℚ :=
  (d.val : ℚ) / imprintDenQ d

/-- Overlap (monogamy) fraction `γ_d = (d − 1) / (2d − 1)`. -/
def overlapGamma (d : TransverseDim) : ℚ :=
  ((d.val : ℚ) - 1) / imprintDenQ d

@[simp] theorem imprintAlpha_one : imprintAlpha ⟨1, by decide⟩ = 1 := by
  unfold imprintAlpha imprintDenQ
  norm_num

@[simp] theorem overlapGamma_one : overlapGamma ⟨1, by decide⟩ = 0 := by
  unfold overlapGamma imprintDenQ
  norm_num

@[simp] theorem imprintAlpha_two : imprintAlpha ⟨2, by decide⟩ = 2 / 3 := by
  unfold imprintAlpha imprintDenQ
  norm_num

@[simp] theorem overlapGamma_two : overlapGamma ⟨2, by decide⟩ = 1 / 3 := by
  unfold overlapGamma imprintDenQ
  norm_num

@[simp] theorem imprintAlpha_three : imprintAlpha ⟨3, by decide⟩ = 3 / 5 := by
  unfold imprintAlpha imprintDenQ
  norm_num

@[simp] theorem overlapGamma_three : overlapGamma ⟨3, by decide⟩ = 2 / 5 := by
  unfold overlapGamma imprintDenQ
  norm_num

@[simp] theorem imprintAlpha_four : imprintAlpha ⟨4, by decide⟩ = 4 / 7 := by
  unfold imprintAlpha imprintDenQ
  norm_num

@[simp] theorem overlapGamma_four : overlapGamma ⟨4, by decide⟩ = 3 / 7 := by
  unfold overlapGamma imprintDenQ
  norm_num

theorem imprintAlpha_add_overlapGamma (d : TransverseDim) :
    imprintAlpha d + overlapGamma d = 1 := by
  unfold imprintAlpha overlapGamma imprintDenQ
  have hden : imprintDenQ d ≠ 0 := by
    have : (1 : ℚ) ≤ d.val := by exact_mod_cast d.2
    unfold imprintDenQ
    linarith
  rw [← add_div]
  rw [show (d.val : ℚ) + ((d.val : ℚ) - 1) = imprintDenQ d from by unfold imprintDenQ; ring]
  exact div_self hden

/-- Midpoint of imprint and overlap is always `1/2` on the unit-split line. -/
theorem imprint_overlap_midpoint (d : TransverseDim) :
    (imprintAlpha d + overlapGamma d) / 2 = (1 / 2 : ℚ) := by
  rw [imprintAlpha_add_overlapGamma]

/-- **2D–3D coupling:** `α₂ · α₃ = γ₃` (not a generic identity in `d`). -/
theorem alpha_two_mul_alpha_three_eq_gamma_three :
    imprintAlpha ⟨2, by decide⟩ * imprintAlpha ⟨3, by decide⟩ =
      overlapGamma ⟨3, by decide⟩ := by
  rw [imprintAlpha_two, imprintAlpha_three, overlapGamma_three]
  norm_num

/-- At `d = 3` the family matches the locked octonion-lattice imprint. -/
theorem imprintAlpha_three_eq_alpha :
    (imprintAlpha ⟨3, by decide⟩ : ℝ) = alpha := by
  have h := imprintAlpha_three
  rw [h, alpha_eq_3_5]
  norm_num

theorem overlapGamma_three_eq_gamma :
    (overlapGamma ⟨3, by decide⟩ : ℝ) = gamma_HQIV := by
  have h := overlapGamma_three
  rw [h, gamma_eq_2_5]
  norm_num

/-! ## Unit-split rotation (generalizes the 45° functional-equation plane) -/

/-- Budget pair `(α, 1 − α)` on the imprint–overlap plane. -/
def unitSplitPair (α : ℝ) : ℝ × ℝ :=
  (α, 1 - α)

/-- Same diagonal coordinate as `rot45Diag` on any pair summing to one. -/
def rotUnitSplitDiag (p : ℝ × ℝ) : ℝ :=
  (p.1 + p.2) / Real.sqrt 2

/-- Same free/skew coordinate as `rot45Free` on any pair summing to one. -/
def rotUnitSplitFree (p : ℝ × ℝ) : ℝ :=
  (p.1 - p.2) / Real.sqrt 2

theorem rotUnitSplitDiag_unitSplitPair (α : ℝ) :
    rotUnitSplitDiag (unitSplitPair α) = 1 / Real.sqrt 2 := by
  unfold rotUnitSplitDiag unitSplitPair
  ring

theorem rotUnitSplitFree_unitSplitPair (α : ℝ) :
    rotUnitSplitFree (unitSplitPair α) = (2 * α - 1) / Real.sqrt 2 := by
  unfold rotUnitSplitFree unitSplitPair
  ring

theorem rot45Diag_eq_rotUnitSplitDiag (σ : ℝ) :
    rot45Diag (functionalPair σ) = rotUnitSplitDiag (unitSplitPair σ) := by
  unfold rot45Diag rotUnitSplitDiag functionalPair unitSplitPair
  ring

theorem rot45Free_eq_rotUnitSplitFree (σ : ℝ) :
    rot45Free (functionalPair σ) = rotUnitSplitFree (unitSplitPair σ) := by
  unfold rot45Free rotUnitSplitFree functionalPair unitSplitPair
  ring

/-- On the budget plane the free coordinate vanishes iff imprint equals overlap (`α = 1/2`).
    No row of the `(α_d, γ_d)` family with `d ≥ 1` sits on this equator except the degenerate
    limit — compare `imprintAlpha_one` (`α₁ = 1`). -/
theorem rotUnitSplitFree_unitSplitPair_eq_zero_iff (α : ℝ) :
    rotUnitSplitFree (unitSplitPair α) = 0 ↔ α = 1 / 2 := by
  rw [rotUnitSplitFree_unitSplitPair]
  constructor
  · intro h
    have hnum : 2 * α - 1 = 0 := by
      exact (div_eq_zero_iff.mp h).resolve_right (by positivity)
    linarith
  · intro h
    subst h
    norm_num

theorem imprint_skew_denominator (d : TransverseDim) :
    (2 : ℝ) * (imprintAlpha d : ℝ) - 1 = 1 / (imprintDenom d : ℝ) := by
  have hsub : (imprintAlpha d : ℝ) - (overlapGamma d : ℝ) = 1 / (imprintDenQ d : ℝ) := by
    unfold imprintAlpha overlapGamma imprintDenQ
    push_cast
    have hden : imprintDenQ d ≠ 0 := by
      have : (1 : ℚ) ≤ d.val := by exact_mod_cast d.2
      unfold imprintDenQ
      linarith
    field_simp [hden]
    ring
  have hsum : (imprintAlpha d : ℝ) + (overlapGamma d : ℝ) = 1 := by
    exact_mod_cast imprintAlpha_add_overlapGamma d
  have hcast : (imprintDenQ d : ℝ) = (imprintDenom d : ℝ) := by
    exact_mod_cast imprintDenQ_eq_cast d
  have hlin : (2 : ℝ) * (imprintAlpha d : ℝ) - 1 = 1 / (imprintDenQ d : ℝ) := by
    linarith [hsub, hsum]
  rw [hcast] at hlin
  exact hlin

/-- Imprint–overlap skew on the unit-split axis: `|α_d − γ_d| = 1 / (2d − 1)`. -/
theorem rotUnitSplitFree_imprint_dim (d : TransverseDim) :
    rotUnitSplitFree (unitSplitPair ((imprintAlpha d : ℚ))) =
      (1 / ((imprintDenom d : ℝ) * Real.sqrt 2)) := by
  rw [rotUnitSplitFree_unitSplitPair, imprint_skew_denominator d]
  field_simp

/-! ## SO(n) bookkeeping (Lie dimension — not identical to transverse `d`) -/

/-- Lie algebra dimension `dim so(n) = n(n−1)/2`. -/
def soLieDim (n : ℕ) : ℕ :=
  n * (n - 1) / 2

@[simp] theorem soLieDim_two : soLieDim 2 = 1 := by
  norm_num [soLieDim]

@[simp] theorem soLieDim_three : soLieDim 3 = 3 := by
  norm_num [soLieDim]

@[simp] theorem soLieDim_four : soLieDim 4 = 6 := by
  norm_num [soLieDim]

/-- Projection angle suggestion: `θ_d = arccos(α_d)` in the imprint–overlap plane.
    This is **not** the 45° critical-line angle (`arccos(1/√2)`). -/
noncomputable def imprintProjectionAngle (d : TransverseDim) : ℝ :=
  Real.arccos (imprintAlpha d)

/-! ## Conjecture / coherence slots (no PDE or horizon proof) -/

/-- **Coherence slot:** 2D transverse budget uses `α₂ = 2/3` (paper: complex / planar channel). -/
structure PlanarImprintBudgetWitness : Prop where
  alpha_two : imprintAlpha ⟨2, by decide⟩ = 2 / 3
  gamma_two : overlapGamma ⟨2, by decide⟩ = 1 / 3

theorem planarImprintBudgetWitness_holds : PlanarImprintBudgetWitness where
  alpha_two := imprintAlpha_two
  gamma_two := overlapGamma_two

/-- **Coherence slot:** 3D physical HQIV row matches lattice `alpha`. -/
structure SpatialImprintBudgetWitness : Prop where
  alpha_three : imprintAlpha ⟨3, by decide⟩ = 3 / 5
  gamma_three : overlapGamma ⟨3, by decide⟩ = 2 / 5
  alpha_three_eq_lattice : (imprintAlpha ⟨3, by decide⟩ : ℝ) = alpha

theorem spatialImprintBudgetWitness_holds : SpatialImprintBudgetWitness where
  alpha_three := imprintAlpha_three
  gamma_three := overlapGamma_three
  alpha_three_eq_lattice := imprintAlpha_three_eq_alpha

/--
**Coherence slot:** 4D fibre/Hodge row.  This is the natural dimension-indexed
upgrade `α₄ = 4/7`, `γ₄ = 3/7`; it is not a replacement for the physical
3D octonion-lattice row `α₃ = 3/5`.
-/
structure FourDimHodgeImprintBudgetWitness : Prop where
  alpha_four : imprintAlpha ⟨4, by decide⟩ = 4 / 7
  gamma_four : overlapGamma ⟨4, by decide⟩ = 3 / 7
  denom_four : imprintDenom ⟨4, by decide⟩ = 7
  skew_four :
    rotUnitSplitFree (unitSplitPair ((imprintAlpha ⟨4, by decide⟩ : ℚ))) =
      (1 / ((7 : ℝ) * Real.sqrt 2))

theorem fourDimHodgeImprintBudgetWitness_holds : FourDimHodgeImprintBudgetWitness where
  alpha_four := imprintAlpha_four
  gamma_four := overlapGamma_four
  denom_four := imprintDenom_four
  skew_four := by
    simpa using rotUnitSplitFree_imprint_dim ⟨4, by decide⟩

/--
**Conjecture slot (NS):** 2D global regularity and 3D Millennium gap might align with
distinct rows of the imprint family — recorded for future PDE bridges, not proved here.
See `TUFTBeltramiHQIVPDEBridge` (functional coincidence only) and
`NSRemainingObligations` (Clay handoff).
-/
structure NavierStokesDimImprintReading : Prop where
  planar : PlanarImprintBudgetWitness
  spatial : SpatialImprintBudgetWitness
  two_three_coupling :
    imprintAlpha ⟨2, by decide⟩ * imprintAlpha ⟨3, by decide⟩ =
      overlapGamma ⟨3, by decide⟩

theorem navierStokesDimImprintReading_holds : NavierStokesDimImprintReading where
  planar := planarImprintBudgetWitness_holds
  spatial := spatialImprintBudgetWitness_holds
  two_three_coupling := alpha_two_mul_alpha_three_eq_gamma_three

/--
**Coherence slot (horizon thermodynamics):** Jacobson/Brodie reading of `(α_d, γ_d)` as
imprint vs monogamy overlap on a discrete horizon — narrative in the 3d-causal-growth
thermodynamic appendix; no Bekenstein–Hawking area law proof in Lean yet.
-/
structure HorizonImprintThermoReading (d : TransverseDim) : Prop where
  unit_split : imprintAlpha d + overlapGamma d = 1
  skew : rotUnitSplitFree (unitSplitPair ((imprintAlpha d : ℚ))) =
    (1 / ((imprintDenom d : ℝ) * Real.sqrt 2))

theorem horizonImprintThermoReading_holds (d : TransverseDim) :
    HorizonImprintThermoReading d where
  unit_split := imprintAlpha_add_overlapGamma d
  skew := rotUnitSplitFree_imprint_dim d

/-! ## Bridge to the canonical `MonogamyProjection` readout (foundation layer)

The story plane above and the foundation-layer `Hqiv.Foundation.MonogamyProjection` API describe the
**same** unit split. These lemmas make the identification explicit, so the geometric rotation picture
here and the octonion-derivation tree (`Hqiv.Algebra.G2LadderProjection`) read one projection object
rather than two numerically-coincident families. -/

/-- The story imprint fraction is the foundation `MonogamyProjection` imprint of the same row. -/
theorem imprintAlpha_eq_monogamy (d : TransverseDim) :
    imprintAlpha d = (Hqiv.Foundation.MonogamyProjection.ofDim d.val d.2).imprint := rfl

/-- The story overlap fraction is the foundation `MonogamyProjection` overlap of the same row. -/
theorem overlapGamma_eq_monogamy (d : TransverseDim) :
    overlapGamma d = (Hqiv.Foundation.MonogamyProjection.ofDim d.val d.2).overlap := rfl

/-- The story free/skew readout agrees with the foundation projection's `free` coordinate. -/
theorem monogamy_free_eq_skew_denominator (d : TransverseDim) :
    (Hqiv.Foundation.MonogamyProjection.ofDim d.val d.2).free = 1 / (2 * (d.val : ℚ) - 1) :=
  Hqiv.Foundation.MonogamyProjection.ofDim_free d.val d.2

/-- **Capstone:** the story-plane `d = 3` row and the foundation carrier's `physical` projection
agree on both imprint (`3/5`) and overlap (`2/5`). The geometric unit-split plane and the
octonion-derivation projection are the same physical row. -/
theorem physical_projection_matches_story_row :
    Hqiv.Foundation.MonogamyProjection.physical.imprint = imprintAlpha ⟨3, by decide⟩ ∧
      Hqiv.Foundation.MonogamyProjection.physical.overlap = overlapGamma ⟨3, by decide⟩ := by
  refine ⟨?_, ?_⟩
  · rw [Hqiv.Foundation.MonogamyProjection.physical_imprint, imprintAlpha_three]
  · rw [Hqiv.Foundation.MonogamyProjection.physical_overlap, overlapGamma_three]

end TransverseDim

end
end Hqiv.Story

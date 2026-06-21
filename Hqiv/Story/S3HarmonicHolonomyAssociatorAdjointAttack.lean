import Hqiv.Story.S3HarmonicHolonomyAssociatorPerturb
import Hqiv.Story.S3LogPhaseAssociatorCoupling
import Hqiv.Story.S3OctonionicAssociatorChannel
import Hqiv.Story.S3GoldbachSlotPhaseCouplingBridge
import Hqiv.Story.S3HarmonicHolonomyCriticalLineFrontier
import Hqiv.Story.S3EulerSO4PrimeAxisBridge

/-!
# Route 4 adjoint attack — `NontrivialZeroForcesPerturbedHolonomyAdjoint`

**Proved upstream (no zero input).**

* `perturbed_holonomy_full_adjoint_implies_defect_vanishes` — `(0,1)` entry
  `z(1-ρ) = -z(ρ)` forces `P(1-ρ)+P(ρ)=0`.
* `perturbed_holonomy_full_adjoint_forces_critical_line` — full adjoint ⇒ `Re ρ = 1/2`.
* `associator_holonomy_defect_vanishes_iff_weight_opposite` — defect vanishing **is**
  the weight oppositeness identity.
* `cascade_associator_holonomy_weight_at_one_minus_on_line` — on the line,
  `z(1-ρ)` uses reflected `(6,5)` spectral lines with shared channel modulus.

**Millennium target (still open).**

`NontrivialZeroForcesPerturbedHolonomyAdjoint`:
  nontrivial zero + `SigmaTPhaseCouplingAt` + non-normality witness ⇒ full perturbed adjoint.

**Refined on-line attack (current focus).**

On the line the sub-target reduces to proving
`z(1-ρ) = -z(ρ)`, equivalently
`star (d₆ d₅) = -(d₆ d₅)` for cascade slots `(6,5)`.
The named main lemma is `on_line_zero_height_phase_lock_from_coupling` in
`S3OnLineZeroHeightPhaseCouplingBridge`; under `GoldbachParity` it reduces to
`OnLineZeroHeightPhaseLockFromSlotBudget`.  The attack decomposition and `on_line_half_complete` live in
`S3OnLineZeroHeightPhaseSlotBudgetAttack`; the **finest open pin** is
`OnLineZeroSharedSlotFiveForcesCascadeWeightOpposite` in
`S3OnLineSharedSlotFiveDischarge` (polar bridge in
`S3OnLineCascadeTripletHeightPhaseBridge`); the parallel off-line half is
`S3OffLineAssociatorAdjointAttack`.
-/

namespace Hqiv.Story

open Hqiv.Geometry Complex Real Matrix

noncomputable section

/-! ## Zero-level inputs already unconditional -/

theorem zero_cascade_associator_channel_pos {ρ : ℂ} (hζ : IsNontrivialZetaZero ρ) :
    0 < octAssociatorChannel 6 5 11 ρ :=
  zero_keeps_associator_torsion hζ (by decide) (by decide) (by decide)

theorem zero_cascade_associator_non_normal_matrix {ρ : ℂ}
    (_hζ : IsNontrivialZetaZero ρ) (hspec : associatorPerturbNonNormalityWitnessAt ρ) :
    harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) ρ *
        (harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) ρ)ᴴ ≠
      (harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) ρ)ᴴ *
        harmonicCascadeHolonomyTransformerAssociatorPerturb 3 (by decide) ρ :=
  associator_perturb_non_normal_at_of_witness hspec

/-! ## On-line reduction (proved) -/

theorem on_line_associator_defect_vanishes_iff_weight_opposite {ρ : ℂ}
    (hs : ρ.re = (1 / 2 : ℝ)) :
    associatorHolonomyDefectVanishesAt 3 (by decide) ρ ↔
      cascadeAssociatorHolonomyWeight (1 - ρ) = -cascadeAssociatorHolonomyWeight ρ :=
  associator_holonomy_defect_vanishes_iff_weight_opposite (by decide)

/--
On the critical line, weight oppositeness for `(6,5)` cascade slots is equivalent to
the spectral product being minus its conjugate — the `(0,1)` sheet content after
cancelling the shared `I·sqrt(channel)` factor.
-/
theorem on_line_weight_opposite_iff_spectral_product_opposed {ρ : ℂ}
    (hs : ρ.re = (1 / 2 : ℝ)) (hch : 0 < octAssociatorChannel 6 5 11 ρ) :
    cascadeAssociatorHolonomyWeight (1 - ρ) = -cascadeAssociatorHolonomyWeight ρ ↔
      star (so4SpectralLine 6 ρ) * star (so4SpectralLine 5 ρ) =
        -(so4SpectralLine 6 ρ * so4SpectralLine 5 ρ) :=
  cascade_weight_opposite_iff_star_spectral_opposed hs hch

/--
Named height-phase lock at critical-line height `t` — the scalar target behind
`OnLineZeroSpectralProductOpposedFromSlotBudget` / coupling discharge.
Uses the same `(0,1)` factorization as `on_line_weight_opposite_iff_spectral_product_opposed`.
-/
def OnLineHeightPhaseLockAt (t : ℝ) : Prop :=
  let ρ := criticalLinePointAtHeight t
  star (so4SpectralLine 6 ρ) * star (so4SpectralLine 5 ρ) =
    -(so4SpectralLine 6 ρ * so4SpectralLine 5 ρ)

/--
**Discrete height ladder (proved).** On the line, spectral-product oppositeness is equivalent
to `exp(2 i t log 30) = -1`, i.e. heights on a π/`log 30` arithmetic progression.
See `Hqiv.Story.S3OnLineSpectralProductHeightPhaseLadder`.
-/
def OnLineSpectralProductOpposedIffHeightPhase : Prop :=
  ∀ t : ℝ,
    OnLineHeightPhaseLockAt t ↔
      ∃ k : ℤ, (2 : ℝ) * t * Real.log 30 = Real.pi + (2 * (k : ℝ)) * Real.pi

theorem on_line_height_phase_lock_iff (hLadder : OnLineSpectralProductOpposedIffHeightPhase) {t : ℝ} :
    OnLineHeightPhaseLockAt t ↔
      ∃ k : ℤ, (2 : ℝ) * t * Real.log 30 = Real.pi + (2 * (k : ℝ)) * Real.pi :=
  hLadder t

theorem on_line_point_eq_critical_height {ρ : ℂ} (hs : ρ.re = (1 / 2 : ℝ)) :
    ρ = criticalLinePointAtHeight ρ.im := by
  apply Complex.ext
  · simp [hs, criticalLinePointAtHeight]
  · simp [criticalLinePointAtHeight]

theorem on_line_zero_spectral_product_opposed_of_height_phase {ρ : ℂ}
    (hs : ρ.re = (1 / 2 : ℝ)) (hLock : OnLineHeightPhaseLockAt ρ.im) :
    star (so4SpectralLine 6 ρ) * star (so4SpectralLine 5 ρ) =
      -(so4SpectralLine 6 ρ * so4SpectralLine 5 ρ) := by
  rw [on_line_point_eq_critical_height hs]
  exact hLock

theorem on_line_zero_weight_opposite_of_height_phase {ρ : ℂ}
    (hs : ρ.re = (1 / 2 : ℝ)) (hch : 0 < octAssociatorChannel 6 5 11 ρ)
    (hLock : OnLineHeightPhaseLockAt ρ.im) :
    cascadeAssociatorHolonomyWeight (1 - ρ) = -cascadeAssociatorHolonomyWeight ρ :=
  (on_line_weight_opposite_iff_spectral_product_opposed hs hch).mpr
    (on_line_zero_spectral_product_opposed_of_height_phase hs hLock)

theorem on_line_zero_defect_of_height_phase {ρ : ℂ}
    (hs : ρ.re = (1 / 2 : ℝ)) (hch : 0 < octAssociatorChannel 6 5 11 ρ)
    (hLock : OnLineHeightPhaseLockAt ρ.im) :
    associatorHolonomyDefectVanishesAt 3 (by decide) ρ :=
  (on_line_associator_defect_vanishes_iff_weight_opposite hs).mpr
    (on_line_zero_weight_opposite_of_height_phase hs hch hLock)

theorem on_line_zero_perturbed_adjoint_of_height_phase {ρ : ℂ}
    (hs : ρ.re = (1 / 2 : ℝ)) (hLock : OnLineHeightPhaseLockAt ρ.im) :
    perturbedHolonomyFullAdjointAt 3 (by decide) ρ := by
  have hch := octAssociatorChannel_pos (by decide : 0 < 6) (by decide : 0 < 5)
    (by decide : 0 < 11) ρ
  exact (perturbed_holonomy_on_line_defect_vanishes_iff_full_adjoint (by decide) hs).mpr
    (on_line_zero_defect_of_height_phase hs hch hLock)

/-! ## Named sub-targets for the attack -/

/--
**On-line sub-target:** at a critical-line zero, σ–t coupling + non-normality should force
associator defect cancellation `P(1-ρ)+P(ρ)=0`, hence full perturbed adjoint.
-/
def OnLineZeroAssociatorDefectVanishesFromCoupling : Prop :=
  ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → ρ.re = (1 / 2 : ℝ) →
    SigmaTPhaseCouplingAt ρ → associatorPerturbNonNormalityWitnessAt ρ →
      associatorHolonomyDefectVanishesAt 3 (by decide) ρ

/--
**Sharper on-line target:** coupling + triplet geometry should force the weight identity
`z(1-ρ) = -z(ρ)` — the actual `(0,1)` content of defect vanishing.
-/
def OnLineZeroAssociatorWeightOppositeFromCoupling : Prop :=
  ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → ρ.re = (1 / 2 : ℝ) →
    SigmaTPhaseCouplingAt ρ → associatorPerturbNonNormalityWitnessAt ρ →
      cascadeAssociatorHolonomyWeight (1 - ρ) = -cascadeAssociatorHolonomyWeight ρ

/--
**Slot-budget route (on-line carrier):** the additive Goldbach slot budget on the line
should force the `(6,5)` spectral product to be minus its conjugate at zeros.
Requires `GoldbachSlotPhasePinBudgetAt`, hence already on-line by definition.
-/
def OnLineZeroSpectralProductOpposedFromSlotBudget : Prop :=
  ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → GoldbachSlotPhasePinBudgetAt ρ →
    associatorPerturbNonNormalityWitnessAt ρ →
      star (so4SpectralLine 6 ρ) * star (so4SpectralLine 5 ρ) =
        -(so4SpectralLine 6 ρ * so4SpectralLine 5 ρ)

theorem on_line_zero_defect_target_of_weight_opposite
    (hWeight : OnLineZeroAssociatorWeightOppositeFromCoupling) :
    OnLineZeroAssociatorDefectVanishesFromCoupling := by
  intro ρ hζ hs hCoupling hNon
  rw [on_line_associator_defect_vanishes_iff_weight_opposite hs]
  exact hWeight hζ hs hCoupling hNon

theorem on_line_zero_weight_opposite_of_spectral_product_target
    (hSpectral : OnLineZeroSpectralProductOpposedFromSlotBudget) {ρ : ℂ}
    (hζ : IsNontrivialZetaZero ρ) (hs : ρ.re = (1 / 2 : ℝ))
    (hBudget : GoldbachSlotPhasePinBudgetAt ρ) (hNon : associatorPerturbNonNormalityWitnessAt ρ)
    (hch : 0 < octAssociatorChannel 6 5 11 ρ) :
    cascadeAssociatorHolonomyWeight (1 - ρ) = -cascadeAssociatorHolonomyWeight ρ := by
  have hspec := hSpectral hζ hBudget hNon
  exact (on_line_weight_opposite_iff_spectral_product_opposed hs hch).mpr hspec

theorem on_line_zero_defect_from_slot_budget_at
    (hSpectral : OnLineZeroSpectralProductOpposedFromSlotBudget) {ρ : ℂ}
    (hζ : IsNontrivialZetaZero ρ) (hBudget : GoldbachSlotPhasePinBudgetAt ρ)
    (hNon : associatorPerturbNonNormalityWitnessAt ρ) :
    associatorHolonomyDefectVanishesAt 3 (by decide) ρ := by
  have hs := hBudget.hσ
  have hch := zero_cascade_associator_channel_pos hζ
  have hWeight :=
    on_line_zero_weight_opposite_of_spectral_product_target hSpectral hζ hs hBudget hNon hch
  exact (on_line_associator_defect_vanishes_iff_weight_opposite hs).mpr hWeight

theorem on_line_zero_defect_target_of_slot_budget_route
    (hSpectral : OnLineZeroSpectralProductOpposedFromSlotBudget) :
    ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → GoldbachSlotPhasePinBudgetAt ρ →
      associatorPerturbNonNormalityWitnessAt ρ →
        associatorHolonomyDefectVanishesAt 3 (by decide) ρ :=
  fun hζ hBudget hNon => on_line_zero_defect_from_slot_budget_at hSpectral hζ hBudget hNon

/-!
**Slot-budget carrier split (honest).**  The spectral-product target is not a consequence
of coupling alone; on the line it is exactly the height-phase lock
`exp(2 i t log 30) = -1` at `ρ = 1/2 + it`.  Closing
`OnLineZeroSpectralProductOpposedFromSlotBudget` therefore reduces to proving that
zeros with `GoldbachSlotPhasePinBudgetAt` sit on that discrete phase ladder — the
tail-band / triplet geometry route.
-/
def OnLineZeroHeightPhaseLockFromSlotBudget : Prop :=
  ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → GoldbachSlotPhasePinBudgetAt ρ →
    OnLineHeightPhaseLockAt ρ.im

theorem on_line_zero_spectral_product_opposed_of_slot_budget_carrier
    (hHeight : OnLineZeroHeightPhaseLockFromSlotBudget) {ρ : ℂ}
    (hζ : IsNontrivialZetaZero ρ) (hBudget : GoldbachSlotPhasePinBudgetAt ρ) :
    star (so4SpectralLine 6 ρ) * star (so4SpectralLine 5 ρ) =
      -(so4SpectralLine 6 ρ * so4SpectralLine 5 ρ) :=
  on_line_zero_spectral_product_opposed_of_height_phase hBudget.hσ (hHeight hζ hBudget)

theorem on_line_zero_spectral_product_opposed_from_slot_budget_of_height_carrier
    (hHeight : OnLineZeroHeightPhaseLockFromSlotBudget) :
    OnLineZeroSpectralProductOpposedFromSlotBudget := by
  intro ρ hζ hBudget _hNon
  exact on_line_zero_spectral_product_opposed_of_slot_budget_carrier hHeight hζ hBudget

theorem goldbach_parity_on_line_zero_defect_from_height_carrier
    (hG : GoldbachParity) (hHeight : OnLineZeroHeightPhaseLockFromSlotBudget) :
    OnLineZeroAssociatorDefectVanishesFromCoupling := by
  intro ρ hζ hs _hCoupling hNon
  exact on_line_zero_defect_from_slot_budget_at
    (on_line_zero_spectral_product_opposed_from_slot_budget_of_height_carrier hHeight)
    hζ (goldbach_slot_phase_pin_budget_at_of_parity hG hζ hs) hNon

theorem on_line_zero_perturbed_adjoint_from_slot_budget_of_height_carrier
    (hHeight : OnLineZeroHeightPhaseLockFromSlotBudget) {ρ : ℂ}
    (hζ : IsNontrivialZetaZero ρ) (hBudget : GoldbachSlotPhasePinBudgetAt ρ)
    (hNon : associatorPerturbNonNormalityWitnessAt ρ) :
    perturbedHolonomyFullAdjointAt 3 (by decide) ρ := by
  have hs := hBudget.hσ
  have hch := zero_cascade_associator_channel_pos hζ
  exact (perturbed_holonomy_on_line_defect_vanishes_iff_full_adjoint (by decide) hs).mpr
    (on_line_zero_defect_from_slot_budget_at
      (on_line_zero_spectral_product_opposed_from_slot_budget_of_height_carrier hHeight)
      hζ hBudget hNon)

theorem goldbach_parity_on_line_zero_perturbed_adjoint_from_height_carrier
    (hG : GoldbachParity) (hHeight : OnLineZeroHeightPhaseLockFromSlotBudget) {ρ : ℂ}
    (hζ : IsNontrivialZetaZero ρ) (hs : ρ.re = (1 / 2 : ℝ))
    (hNon : associatorPerturbNonNormalityWitnessAt ρ) :
    perturbedHolonomyFullAdjointAt 3 (by decide) ρ :=
  on_line_zero_perturbed_adjoint_from_slot_budget_of_height_carrier hHeight hζ
    (goldbach_slot_phase_pin_budget_at_of_parity hG hζ hs) hNon

/--
**Off-line sub-target:** no nontrivial zero off the line carries both σ–t coupling and the
non-normality witness.  Together with `off_line_excludes_perturbed_holonomy_full_adjoint`,
this is the contradiction route toward the adjoint target.
-/
def OffLineZeroExcludedByCouplingAndNonNormality : Prop :=
  ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → ρ.re ≠ (1 / 2 : ℝ) →
    SigmaTPhaseCouplingAt ρ → associatorPerturbNonNormalityWitnessAt ρ → False

theorem octAssociatorChannel_cascade_not_exact_off_line {ρ : ℂ}
    (hOff : ρ.re ≠ (1 / 2 : ℝ)) :
    octAssociatorChannel 6 5 11 ρ ≠ 2 / ((6 * 5 * 11 : ℕ) : ℝ) :=
  fun h => hOff ((octAssociatorChannel_eq_iff (by decide) (by decide) (by decide)).mp h)

/--
**Off-line asymmetry certificate:** the `(6,5,11)` channel misses the square-root locator
exactly when `Re ρ ≠ 1/2`.  This packages the channel side of the off-line exclusion route.
-/
theorem off_line_cascade_channel_asymmetry {ρ : ℂ} (hOff : ρ.re ≠ (1 / 2 : ℝ)) :
    octAssociatorChannel 6 5 11 ρ ≠
      octAssociatorChannel 6 5 11 (Complex.mk (1 / 2 : ℝ) ρ.im) := by
  intro h
  have hon :
      octAssociatorChannel 6 5 11 (Complex.mk (1 / 2 : ℝ) ρ.im) =
        2 / ((6 * 5 * 11 : ℕ) : ℝ) :=
    (octAssociatorChannel_eq_iff (by decide) (by decide) (by decide)).mpr (by simp)
  have hex : octAssociatorChannel 6 5 11 ρ = 2 / ((6 * 5 * 11 : ℕ) : ℝ) := (h.trans hon)
  exact octAssociatorChannel_cascade_not_exact_off_line hOff hex

theorem on_line_zero_perturbed_adjoint_of_defect_target
    (hDefect : OnLineZeroAssociatorDefectVanishesFromCoupling) {ρ : ℂ}
    (hζ : IsNontrivialZetaZero ρ) (hs : ρ.re = (1 / 2 : ℝ))
    (hCoupling : SigmaTPhaseCouplingAt ρ) (hNon : associatorPerturbNonNormalityWitnessAt ρ) :
    perturbedHolonomyFullAdjointAt 3 (by decide) ρ :=
  (perturbed_holonomy_on_line_defect_vanishes_iff_full_adjoint (by decide) hs).mpr
    (hDefect hζ hs hCoupling hNon)

theorem NontrivialZeroForcesPerturbedHolonomyAdjoint_of_subtargets
    (hOnLine : OnLineZeroAssociatorDefectVanishesFromCoupling)
    (hOffLine : OffLineZeroExcludedByCouplingAndNonNormality) :
    NontrivialZeroForcesPerturbedHolonomyAdjoint := by
  intro ρ hζ hCoupling hNon
  by_cases hs : ρ.re = (1 / 2 : ℝ)
  · exact on_line_zero_perturbed_adjoint_of_defect_target hOnLine hζ hs hCoupling hNon
  · exact absurd (hOffLine hζ hs hCoupling hNon) id

theorem RH_of_subtargets_and_non_normality_everywhere
    (hWitnessAll :
      ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → associatorPerturbNonNormalityWitnessAt ρ)
    (hOnLine : OnLineZeroAssociatorDefectVanishesFromCoupling)
    (hOffLine : OffLineZeroExcludedByCouplingAndNonNormality) :
    RiemannHypothesis :=
  RH_of_nontrivial_zero_forces_perturbed_holonomy_adjoint hWitnessAll
    (NontrivialZeroForcesPerturbedHolonomyAdjoint_of_subtargets hOnLine hOffLine)

theorem off_line_zero_with_full_adjoint_forces_line
    {ρ : ℂ} (hOff : ρ.re ≠ (1 / 2 : ℝ))
    (hAdj : perturbedHolonomyFullAdjointAt 3 (by decide) ρ) :
    False :=
  hOff (perturbed_holonomy_full_adjoint_forces_critical_line (by decide) hAdj)

end

end Hqiv.Story

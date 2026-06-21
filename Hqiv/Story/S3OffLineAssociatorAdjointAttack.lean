import Hqiv.Story.S3HarmonicHolonomyAssociatorAdjointAttack
import Hqiv.Story.S3GoldbachSlotPhaseOffLineHarmonicBridge
import Hqiv.Story.S3OnLineZeroHeightPhaseSlotBudgetAttack

/-!
# Off-line half — `OffLineZeroExcludedByCouplingAndNonNormality`

Parallel attack packaging for the off-line sub-target of
`NontrivialZeroForcesPerturbedHolonomyAdjoint`.

**Proved ingredients.**

* Off-line points cannot carry `GoldbachSlotPhasePinBudgetAt`.
* `(6,5,11)` associator channel misses the on-line square-root locator off the line.
* Full perturbed holonomy adjoint is excluded off the line
  (`off_line_excludes_perturbed_holonomy_full_adjoint`).
* σ–t coupling is **unconditional** at every nontrivial zero — so the off-line
  target is not “no coupling off the line”; it is the contradiction route through
  coupling + non-normality + channel asymmetry.

**Open pin.** `OffLineZeroExcludedByCouplingAndNonNormality` — discharge from the
proved asymmetry certificates to a contradiction at off-line zeros carrying both
coupling and the non-normality witness.
-/

namespace Hqiv.Story

open Complex Real Hqiv.Geometry

noncomputable section

/-! ## Proved off-line ingredients -/

structure OffLineAssociatorAdjointAttackData where
  slot_budget_excluded :
    OffLineCannotCarryGoldbachSlotBudget
  channel_asymmetry :
    ∀ {ρ : ℂ}, ρ.re ≠ (1 / 2 : ℝ) →
      octAssociatorChannel 6 5 11 ρ ≠
        octAssociatorChannel 6 5 11 (Complex.mk (1 / 2 : ℝ) ρ.im)
  full_adjoint_excluded :
    ∀ {ρ : ℂ}, ρ.re ≠ (1 / 2 : ℝ) →
      ¬ perturbedHolonomyFullAdjointAt 3 (by decide) ρ
  coupling_unconditional :
    ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → SigmaTPhaseCouplingAt ρ

def off_line_associator_adjoint_attack_data : OffLineAssociatorAdjointAttackData where
  slot_budget_excluded := off_line_cannot_carry_goldbach_slot_budget
  channel_asymmetry := fun hOff => off_line_cascade_channel_asymmetry hOff
  full_adjoint_excluded := fun {ρ} hOff =>
    off_line_excludes_perturbed_holonomy_full_adjoint (by decide) hOff
  coupling_unconditional := fun hζ => sigma_t_coupling_at_every_nontrivial_zero hζ

theorem off_line_zero_cannot_host_slot_budget
    {ρ : ℂ} (hOff : ρ.re ≠ (1 / 2 : ℝ)) :
    ¬ GoldbachSlotPhasePinBudgetAt ρ :=
  off_line_cannot_carry_goldbach_slot_budget ρ hOff

theorem off_line_nontrivial_zero_has_coupling_anyway
    {ρ : ℂ} (hζ : IsNontrivialZetaZero ρ) (_hOff : ρ.re ≠ (1 / 2 : ℝ)) :
    SigmaTPhaseCouplingAt ρ :=
  sigma_t_coupling_at_every_nontrivial_zero hζ

theorem off_line_cascade_channel_misses_square_root_locator
    {ρ : ℂ} (hOff : ρ.re ≠ (1 / 2 : ℝ)) :
    octAssociatorChannel 6 5 11 ρ ≠ 2 / ((6 * 5 * 11 : ℕ) : ℝ) :=
  octAssociatorChannel_cascade_not_exact_off_line hOff

/-! ## Open pin ⇒ off-line half (modulo carrier) -/

theorem off_line_zero_excluded_from_coupling_and_non_normal
    (hOff : OffLineZeroExcludedByCouplingAndNonNormality) {ρ : ℂ}
    (hζ : IsNontrivialZetaZero ρ) (hOffσ : ρ.re ≠ (1 / 2 : ℝ))
    (hCoupling : SigmaTPhaseCouplingAt ρ)
    (hNon : associatorPerturbNonNormalityWitnessAt ρ) :
    False :=
  hOff hζ hOffσ hCoupling hNon

/--
**Off-line half complete** once the exclusion pin closes.
-/
theorem off_line_half_complete
    (hOff : OffLineZeroExcludedByCouplingAndNonNormality) :
    OffLineZeroExcludedByCouplingAndNonNormality :=
  hOff

structure OffLineAssociatorAdjointAttackHalf where
  attack_data : OffLineAssociatorAdjointAttackData
  exclusion : OffLineZeroExcludedByCouplingAndNonNormality

def off_line_associator_adjoint_attack_half
    (hOff : OffLineZeroExcludedByCouplingAndNonNormality) :
    OffLineAssociatorAdjointAttackHalf where
  attack_data := off_line_associator_adjoint_attack_data
  exclusion := hOff

/-! ## Full attack closes when both halves close -/

structure AssociatorAdjointAttackComplete where
  on_line : OnLineAssociatorAdjointAttackHalf
  off_line : OffLineAssociatorAdjointAttackHalf
  millennium :
    NontrivialZeroForcesPerturbedHolonomyAdjoint

def associator_adjoint_attack_complete
    (hG : GoldbachParity)
    (hOnDischarge : OnLineZeroTripletTailBandDischargesLinePhaseThirty)
    (hOffExclusion : OffLineZeroExcludedByCouplingAndNonNormality) :
    AssociatorAdjointAttackComplete where
  on_line := on_line_associator_adjoint_attack_half hG hOnDischarge
  off_line := off_line_associator_adjoint_attack_half hOffExclusion
  millennium :=
    nontrivial_zero_forces_perturbed_adjoint_of_slot_budget_discharge_and_off_line
      hG hOnDischarge hOffExclusion

theorem RH_of_associator_adjoint_attack_complete
    (hWitnessAll :
      ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → associatorPerturbNonNormalityWitnessAt ρ)
    (C : AssociatorAdjointAttackComplete) :
    RiemannHypothesis :=
  RH_of_subtargets_and_non_normality_everywhere hWitnessAll
    C.on_line.on_line_defect C.off_line.exclusion

end

end Hqiv.Story

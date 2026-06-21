import Hqiv.Story.S3OnLineSpectralProductHeightPhaseLadder
import Hqiv.Story.S3LogPhaseZetaCouplingFrontier
import Hqiv.Story.S3GoldbachSlotPhaseCouplingBridge
import Hqiv.Story.S3HarmonicHolonomyCriticalLineFrontier
import Hqiv.Story.S3LogPhaseAssociatorCoupling

/-!
# On-line zero: σ–t coupling ⇒ height-phase lock (attack bridge)

**Main open pin (Option A).**  At a nontrivial zero on the critical line,
`SigmaTPhaseCouplingAt ρ` should force the `(6,5)` spectral-product height lock
`OnLineHeightPhaseLockAt ρ.im` — equivalently the discrete ladder
`2 t log 30 = π + 2 k π` (`on_line_spectral_product_opposed_iff_height_phase`).

Coupling alone is **unconditional** at every nontrivial zero; this target therefore
packages the **on-line geometric discharge** (tail-band reflection, Goldbach triplet
geometry at cascade slots `(6,5,11)`, slot-phase budget), not a tautology from
`sigma_t_coupling_at_every_nontrivial_zero`.

**Proved here.**

* Named main lemma applying the open carrier.
* Ladder reformulation at zero height.
* Tail-band reflection and cascade `(6,5,11)` channel positivity at zeros.
* Under `GoldbachParity`, the coupling route **reduces to**
  `OnLineZeroHeightPhaseLockFromSlotBudget`.
* Height lock ⇒ weight oppositeness ⇒ defect vanishing ⇒ perturbed adjoint on the line.
-/

namespace Hqiv.Story

open Complex Real Hqiv.Geometry

noncomputable section

/-! ## Main on-line target -/

/--
**On-line coupling ⇒ height-phase lock.**  The `(0,1)` sheet content behind
`OnLineZeroAssociatorWeightOppositeFromCoupling` at cascade slots `(6,5)`.
-/
def OnLineZeroHeightPhaseLockFromCoupling : Prop :=
  ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → ρ.re = (1 / 2 : ℝ) →
    SigmaTPhaseCouplingAt ρ → OnLineHeightPhaseLockAt ρ.im

/--
Named main lemma (applies the open carrier).
-/
theorem on_line_zero_height_phase_lock_from_coupling
    (hLock : OnLineZeroHeightPhaseLockFromCoupling) {ρ : ℂ}
    (hζ : IsNontrivialZetaZero ρ) (hs : ρ.re = (1 / 2 : ℝ))
    (hCoupling : SigmaTPhaseCouplingAt ρ) :
    OnLineHeightPhaseLockAt ρ.im :=
  hLock hζ hs hCoupling

theorem on_line_zero_height_phase_lock_from_coupling_iff_ladder
    (hLock : OnLineZeroHeightPhaseLockFromCoupling) {ρ : ℂ}
    (hζ : IsNontrivialZetaZero ρ) (hs : ρ.re = (1 / 2 : ℝ))
    (hCoupling : SigmaTPhaseCouplingAt ρ) :
    ∃ k : ℤ, (2 : ℝ) * ρ.im * Real.log 30 = Real.pi + (2 : ℝ) * (k : ℝ) * Real.pi := by
  exact (on_line_spectral_product_opposed_iff_height_phase ρ.im).mp
    (on_line_zero_height_phase_lock_from_coupling hLock hζ hs hCoupling)

/-! ## Proved attack ingredients -/

structure OnLineCouplingHeightPhaseAttackIngredients where
  ladder : OnLineSpectralProductOpposedIffHeightPhase
  tail_reflection : ∀ t : ℝ,
    star (tailBandCriticalLinePhase t) = tailBandCriticalLinePhase (-t)
  cascade_channel_pos :
    ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → 0 < octAssociatorChannel 6 5 11 ρ

theorem on_line_coupling_height_phase_attack_ingredients :
    OnLineCouplingHeightPhaseAttackIngredients where
  ladder := on_line_spectral_product_opposed_iff_height_phase
  tail_reflection := tailBandCriticalLinePhase_conj
  cascade_channel_pos := fun hζ => zero_cascade_associator_channel_pos hζ

theorem on_line_zero_tail_band_reflection {ρ : ℂ} (_hs : ρ.re = (1 / 2 : ℝ)) :
    star (tailBandCriticalLinePhase ρ.im) = tailBandCriticalLinePhase (-ρ.im) :=
  tailBandCriticalLinePhase_conj ρ.im

theorem on_line_zero_cascade_associator_channel_pos {ρ : ℂ} (hζ : IsNontrivialZetaZero ρ) :
    0 < octAssociatorChannel 6 5 11 ρ :=
  zero_cascade_associator_channel_pos hζ

theorem on_line_zero_goldbach_triplet_at_six
    (hG : GoldbachParity) {ρ : ℂ} (hζ : IsNontrivialZetaZero ρ)
    (hs : ρ.re = (1 / 2 : ℝ)) :
    Nonempty (GoldbachTripletLogAssociatorInvariant ρ 6) :=
  goldbach_triplet_invariant_under_parity_on_line hG hζ hs (by decide)

/-! ## Reduction to slot-budget carrier (under parity) -/

theorem on_line_zero_height_phase_lock_from_slot_budget_carrier
    (hSlot : OnLineZeroHeightPhaseLockFromSlotBudget) {ρ : ℂ}
    (hζ : IsNontrivialZetaZero ρ) (hBudget : GoldbachSlotPhasePinBudgetAt ρ) :
    OnLineHeightPhaseLockAt ρ.im :=
  hSlot hζ hBudget

theorem on_line_zero_height_phase_lock_from_coupling_of_parity
    (hG : GoldbachParity) (hSlot : OnLineZeroHeightPhaseLockFromSlotBudget) :
    OnLineZeroHeightPhaseLockFromCoupling := by
  intro ρ hζ hs _hCoupling
  exact hSlot hζ (goldbach_slot_phase_pin_budget_at_of_parity hG hζ hs)

theorem on_line_zero_height_phase_lock_from_coupling_iff_slot_budget_under_parity
    (hG : GoldbachParity) :
    OnLineZeroHeightPhaseLockFromCoupling ↔ OnLineZeroHeightPhaseLockFromSlotBudget := by
  constructor
  · intro hHeight ρ hζ hBudget
    exact on_line_zero_height_phase_lock_from_coupling hHeight hζ hBudget.hσ
      (goldbach_slot_phase_budget_implies_sigma_t_coupling hBudget)
  · exact on_line_zero_height_phase_lock_from_coupling_of_parity hG

/-! ## On-line half: height lock ⇒ associator defect (modulo open pin) -/

theorem on_line_zero_weight_opposite_from_height_coupling
    (hLock : OnLineZeroHeightPhaseLockFromCoupling) {ρ : ℂ}
    (hζ : IsNontrivialZetaZero ρ) (hs : ρ.re = (1 / 2 : ℝ))
    (hCoupling : SigmaTPhaseCouplingAt ρ) :
    cascadeAssociatorHolonomyWeight (1 - ρ) = -cascadeAssociatorHolonomyWeight ρ :=
  on_line_zero_weight_opposite_of_height_phase hs
    (zero_cascade_associator_channel_pos hζ)
    (on_line_zero_height_phase_lock_from_coupling hLock hζ hs hCoupling)

theorem on_line_zero_associator_weight_opposite_from_coupling
    (hLock : OnLineZeroHeightPhaseLockFromCoupling) :
    OnLineZeroAssociatorWeightOppositeFromCoupling := by
  intro ρ hζ hs hCoupling _hNon
  exact on_line_zero_weight_opposite_from_height_coupling hLock hζ hs hCoupling

theorem on_line_zero_defect_from_height_coupling
    (hLock : OnLineZeroHeightPhaseLockFromCoupling) :
    OnLineZeroAssociatorDefectVanishesFromCoupling :=
  on_line_zero_defect_target_of_weight_opposite
    (on_line_zero_associator_weight_opposite_from_coupling hLock)

theorem on_line_zero_perturbed_adjoint_from_height_coupling
    (hLock : OnLineZeroHeightPhaseLockFromCoupling) {ρ : ℂ}
    (hζ : IsNontrivialZetaZero ρ) (hs : ρ.re = (1 / 2 : ℝ))
    (hCoupling : SigmaTPhaseCouplingAt ρ) :
    perturbedHolonomyFullAdjointAt 3 (by decide) ρ :=
  on_line_zero_perturbed_adjoint_of_height_phase hs
    (on_line_zero_height_phase_lock_from_coupling hLock hζ hs hCoupling)

theorem goldbach_parity_on_line_zero_defect_from_height_coupling
    (hG : GoldbachParity) (hLock : OnLineZeroHeightPhaseLockFromCoupling) {ρ : ℂ}
    (hζ : IsNontrivialZetaZero ρ) (hs : ρ.re = (1 / 2 : ℝ))
    (hNon : associatorPerturbNonNormalityWitnessAt ρ) :
    associatorHolonomyDefectVanishesAt 3 (by decide) ρ :=
  on_line_zero_defect_from_height_coupling hLock hζ hs
    (goldbach_parity_slot_budget_sigma_t_coupling hG hζ hs) hNon

end

end Hqiv.Story

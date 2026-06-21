import Hqiv.Story.S3OnLineTripletSixGapSpectralAttack
import Hqiv.Story.S3LogPhaseInteriorAssemblyBridge
import Hqiv.Story.S3LogPhaseAssociatorCoupling
import Hqiv.Story.S3HarmonicMulModCubeLieTransportBridge
import Hqiv.Story.S3GoldbachAnnulusPhasePinning
import Hqiv.Story.S3ZeroHolonomyGoldbachChain
import Hqiv.Story.S3DeltaHarmonicDischargeBridge
import Hqiv.Geometry.AlphaGammaForcedByLattice

/-!
# Rolling identification → triplet `N = 6` gap spectral opposition (Step 1a-i route)

Wires the explicit-formula rolling readout at `criticalLinePointAtHeight ρ.im` to
the gap `(5,7)` spectral sub-pins from `S3OnLineTripletSixGapSpectralAttack`.

**Proved packaging.**

* `goldbach_triplet_six_uses_five_seven_arms` — every `N = 6` triplet uses `(5,7)`;
* matched rolling / residual readout at on-line zeros;
* `OnLineTripletSixRollingGapReadoutAt ρ` — triplet + gap = pair + polar + floor;
* `on_line_zero_triplet_six_associator_phase_identifies_gap_spectral` applies the
  rolling packaging hypothesis `OnLineZeroTripletSixGapSpectralFromRollingIdentification`.

**Open content (1a-i).**

* `OnLineZeroTripletSixRollingAssociatorIdentifiesGapSpectralPhase` — the zero-level
  rolling + associator phase link forcing gap spectral opposition.
* **Light decomposition:**
  * `OnLineZeroRollingResidualGivesGapSpectralBalance` — rolling residual + ζ-zero
    ⇒ gap `(5,7)` spectral readout balance;
  * `OnLineZeroGapSpectralBalanceAndAssociatorFloorGiveOpposition` — balance +
    triplet associator floor ⇒ gap spectral opposition.
-/

namespace Hqiv.Story

open Complex Real Hqiv.Geometry

noncomputable section

/-! ## Certified `(5,7)` arms at `N = 6` -/

theorem goldbach_midpoint_pair_six_eq_five_seven {p q : ℕ}
    (h : GoldbachMidpointPair 6 p q) : p = 5 ∧ q = 7 := by
  obtain ⟨hp, hq, hpN, _hqN, _hsum⟩ := h
  have h12 : p + q = 12 := by omega
  have hp6 : p ≤ 6 := hpN
  interval_cases p
  · norm_num [Nat.Prime] at hp
  · norm_num [Nat.Prime] at hp
  · have hq10 : q = 10 := by omega
    rw [hq10] at hq
    norm_num [Nat.Prime] at hq
  · have hq9 : q = 9 := by omega
    rw [hq9] at hq
    norm_num [Nat.Prime] at hq
  · norm_num [Nat.Prime] at hp
  · have hq7 : q = 7 := by omega
    exact ⟨rfl, by simp [hq7] at hq ⊢⟩
  · norm_num [Nat.Prime] at hp

theorem goldbach_triplet_six_uses_five_seven_arms
    {ρ : ℂ} (G : GoldbachTripletLogAssociatorInvariant ρ 6) :
    G.p = 5 ∧ G.q = 7 :=
  goldbach_midpoint_pair_six_eq_five_seven G.pair

theorem goldbach_triplet_six_gap_eq_pair_from_invariant
    {ρ : ℂ} (G : GoldbachTripletLogAssociatorInvariant ρ 6) :
    gapFiveSevenSpectralChannel ρ =
      so4SpectralLine 5 ρ * so4SpectralLine 7 ρ := by
  have hPQ := goldbach_triplet_six_uses_five_seven_arms G
  rw [goldbach_triplet_six_gap_eq_pair_at_five_seven G hPQ.1, hPQ.1, hPQ.2]

/-! ## Rolling readout at zero height -/

theorem on_line_zero_matched_rolling_at_height
    (hRoll : RollingZetaIdentificationAtCriticalLine) {ρ : ℂ} (hs : ρ.re = (1 / 2 : ℝ)) :
    MatchedRollingZeroAt ρ (rolledSampleAtHeight ρ.im) :=
  matched_rolling_of_on_line_and_identification hRoll hs

theorem on_line_zero_rolling_residual_at_height
    (hRoll : RollingZetaIdentificationAtCriticalLine) {ρ : ℂ} (hs : ρ.re = (1 / 2 : ℝ)) :
    ZetaEqualsS3ResidualAt ρ (rolledSampleAtHeight ρ.im) := by
  rcases on_line_zero_matched_rolling_at_height hRoll hs with ⟨_, hEq⟩
  exact hEq

/-! ## Rolling-route open pin -/

/--
**Finest rolling-route content.**  At a shared-slot zero, rolling identification
together with the `N = 6` triplet associator readout and gap = pair-line alignment
forces gap `(5,7)` spectral opposition.
-/
def OnLineZeroTripletSixRollingAssociatorIdentifiesGapSpectralPhase : Prop :=
  ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → ρ.re = (1 / 2 : ℝ) →
    OnLineCascadeTripletSharedSlotFive ρ →
    RollingZetaIdentificationAtCriticalLine →
    OnLineZeroGapFiveSevenSpectralOpposedAt ρ

/-! ## Light decomposition of `OnLineZeroTripletSixRollingAssociatorIdentifiesGapSpectralPhase` -/

/--
**Gap `(5,7)` spectral balance** at zero height — real part vanishes on the gap
readout (unit-circle sheet).  Full opposition `star gap = -gap` implies balance.
-/
def OnLineZeroGapFiveSevenSpectralBalancedAt (ρ : ℂ) : Prop :=
  (gapFiveSevenSpectralChannel ρ).re = 0

theorem gap_five_seven_spectral_opposed_implies_balanced
    {ρ : ℂ} (hOpp : OnLineZeroGapFiveSevenSpectralOpposedAt ρ) :
    OnLineZeroGapFiveSevenSpectralBalancedAt ρ := by
  dsimp [OnLineZeroGapFiveSevenSpectralBalancedAt, OnLineZeroGapFiveSevenSpectralOpposedAt] at hOpp ⊢
  simp only [starRingEnd_apply] at hOpp
  have hre := congrArg Complex.re hOpp
  simp [Complex.conj_re] at hre
  linarith

theorem gap_five_seven_spectral_balanced_implies_opposed
    {ρ : ℂ} (hBal : OnLineZeroGapFiveSevenSpectralBalancedAt ρ) :
    OnLineZeroGapFiveSevenSpectralOpposedAt ρ := by
  dsimp [OnLineZeroGapFiveSevenSpectralBalancedAt, OnLineZeroGapFiveSevenSpectralOpposedAt] at hBal ⊢
  simp only [starRingEnd_apply]
  apply Complex.ext <;> simp [Complex.conj_re, hBal]

theorem gap_five_seven_spectral_balanced_iff_opposed {ρ : ℂ} :
    OnLineZeroGapFiveSevenSpectralBalancedAt ρ ↔
      OnLineZeroGapFiveSevenSpectralOpposedAt ρ :=
  ⟨gap_five_seven_spectral_balanced_implies_opposed,
    gap_five_seven_spectral_opposed_implies_balanced⟩

/--
**Sub-lemma A (analytic / rolling).**  Rolling residual at `criticalLinePointAtHeight ρ.im`
together with ζ-zero forces gap `(5,7)` spectral balance.
-/
def OnLineZeroRollingResidualGivesGapSpectralBalance : Prop :=
  ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → ρ.re = (1 / 2 : ℝ) →
    OnLineCascadeTripletSharedSlotFive ρ →
    RollingZetaIdentificationAtCriticalLine →
    OnLineZeroGapFiveSevenSpectralBalancedAt ρ

/--
**Sub-lemma B (associator transfer).**  Gap spectral balance together with the
`N = 6` triplet associator floor on `octAssociatorChannel 5 7 12` and gap = pair
alignment forces full gap spectral opposition.
-/
def OnLineZeroGapSpectralBalanceAndAssociatorFloorGiveOpposition : Prop :=
  ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → ρ.re = (1 / 2 : ℝ) →
    OnLineCascadeTripletSharedSlotFive ρ →
    OnLineZeroGapFiveSevenSpectralBalancedAt ρ →
    GoldbachTripletLogAssociatorInvariant ρ 6 →
    OnLineZeroGapFiveSevenSpectralOpposedAt ρ

theorem on_line_zero_rolling_residual_gives_gap_spectral_balance
    (hBalance : OnLineZeroRollingResidualGivesGapSpectralBalance)
    (hRoll : RollingZetaIdentificationAtCriticalLine)
    {ρ : ℂ} (hζ : IsNontrivialZetaZero ρ) (hs : ρ.re = (1 / 2 : ℝ))
    (hShared : OnLineCascadeTripletSharedSlotFive ρ) :
    OnLineZeroGapFiveSevenSpectralBalancedAt ρ :=
  hBalance hζ hs hShared hRoll

theorem on_line_zero_gap_spectral_balance_and_floor_give_opposition
    (hTransfer : OnLineZeroGapSpectralBalanceAndAssociatorFloorGiveOpposition)
    {ρ : ℂ} (hζ : IsNontrivialZetaZero ρ) (hs : ρ.re = (1 / 2 : ℝ))
    (hShared : OnLineCascadeTripletSharedSlotFive ρ)
    (hBal : OnLineZeroGapFiveSevenSpectralBalancedAt ρ)
    (G : GoldbachTripletLogAssociatorInvariant ρ 6) :
    OnLineZeroGapFiveSevenSpectralOpposedAt ρ :=
  hTransfer hζ hs hShared hBal G

theorem on_line_zero_gap_spectral_balance_and_floor_give_opposition_unconditional :
    OnLineZeroGapSpectralBalanceAndAssociatorFloorGiveOpposition :=
  fun _hζ _hs _hShared hBal tripletInv => by
    -- The triplet evidence is retained here as the formal hook for the `(5,7,12)`
    -- associator readout, while the present complex-valued opposition surface
    -- reduces to pure-imaginary balance.
    have _hGapPair := goldbach_triplet_six_gap_eq_pair_from_invariant tripletInv
    have _hFloor := tripletInv.associator_floor
    exact gap_five_seven_spectral_balanced_implies_opposed hBal

theorem on_line_zero_triplet_six_rolling_associator_phase_of_balance_and_floor
    (hBalance : OnLineZeroRollingResidualGivesGapSpectralBalance)
    (hTransfer : OnLineZeroGapSpectralBalanceAndAssociatorFloorGiveOpposition) :
    OnLineZeroTripletSixRollingAssociatorIdentifiesGapSpectralPhase :=
  fun {ρ} hζ hs hShared hRoll => by
    obtain ⟨tripletInv⟩ := hShared.triplet_six
    exact hTransfer hζ hs hShared (hBalance hζ hs hShared hRoll) tripletInv

theorem on_line_zero_triplet_six_rolling_associator_phase_of_balance
    (hBalance : OnLineZeroRollingResidualGivesGapSpectralBalance) :
    OnLineZeroTripletSixRollingAssociatorIdentifiesGapSpectralPhase :=
  on_line_zero_triplet_six_rolling_associator_phase_of_balance_and_floor hBalance
    on_line_zero_gap_spectral_balance_and_floor_give_opposition_unconditional

theorem on_line_zero_rolling_balance_of_associator_phase
    (hMain : OnLineZeroTripletSixRollingAssociatorIdentifiesGapSpectralPhase) :
    OnLineZeroRollingResidualGivesGapSpectralBalance :=
  fun hζ hs hShared hRoll =>
    gap_five_seven_spectral_opposed_implies_balanced (hMain hζ hs hShared hRoll)

theorem on_line_zero_associator_transfer_of_associator_phase
    (hMain : OnLineZeroTripletSixRollingAssociatorIdentifiesGapSpectralPhase)
    (hRoll : RollingZetaIdentificationAtCriticalLine) :
    OnLineZeroGapSpectralBalanceAndAssociatorFloorGiveOpposition :=
  fun hζ hs hShared _hBal _tripletInv =>
    hMain hζ hs hShared hRoll

/-! ## Mul-mod / Fano de-diagonalized attack surface -/

/--
Finite de-diagonalization skeleton for the `(5,7)` gap product.  The structured
SO(4) promotion on shell `35` supplies the coprime mul-mod sweep, and the mod-7
cube chart supplies the Fano-fibre triangulation.  The only non-finite datum is
the eventual readout equation tying this skeleton to the rolling projection.
-/
structure MulModFanoGapDeDiagonalizationSkeletonAt (ρ : ℂ) where
  promotion : SO4StructuredCascadeLiePromotion 35 (by decide)
  fano_zero_fibre : ((35 : ℕ) : ZMod 7) = 0
  fano_triangulation :
    ∃ a b c : ZMod 7, a ^ 3 + b ^ 3 + c ^ 3 = ((35 : ℕ) : ZMod 7)
  slot_five_hit :
    ∃ x : ℕ, x < 35 ∧ so4LieTransportIndex 35 promotion.multiplier x = 5
  slot_seven_hit :
    ∃ x : ℕ, x < 35 ∧ so4LieTransportIndex 35 promotion.multiplier x = 7
  gap_eq_pair :
    gapFiveSevenSpectralChannel ρ =
      so4SpectralLine 5 ρ * so4SpectralLine 7 ρ
  associator_floor :
    1 / ((6 ^ 3 : ℕ) : ℝ) ≤
      octAssociatorChannel 5 7 12 (Complex.mk (1 / 2 : ℝ) ρ.im)

noncomputable def mulModFano_gap_deDiagonalizationSkeleton_at
    {ρ : ℂ} (hShared : OnLineCascadeTripletSharedSlotFive ρ) :
    MulModFanoGapDeDiagonalizationSkeletonAt ρ := by
  let P : SO4StructuredCascadeLiePromotion 35 (by decide) :=
    so4LiePromotion_structured 35 (by decide)
  let G : GoldbachTripletLogAssociatorInvariant ρ 6 :=
    Classical.choice hShared.triplet_six
  have hPQ := goldbach_triplet_six_uses_five_seven_arms G
  refine
    { promotion := P
      fano_zero_fibre := by native_decide
      fano_triangulation := ?_
      slot_five_hit := ?_
      slot_seven_hit := ?_
      gap_eq_pair := goldbach_triplet_six_gap_eq_pair_from_invariant G
      associator_floor := ?_ }
  · simpa using P.chart.triangulate (((35 : ℕ) : ZMod 7))
  · exact P.hits 5 (by decide) (by decide)
  · exact P.hits 7 (by decide) (by decide)
  · simpa [hPQ.1, hPQ.2] using G.associator_floor

/-! ## Goldbach-circle / Hopf-tower pair map -/

theorem goldbach_midpoint_pair_six_five_seven :
    GoldbachMidpointPair 6 5 7 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem midpoint_scan_slot_six_five : 5 ∈ midpointScanSlots 6 :=
  (mem_midpointScanSlots_iff (N := 6) (p := 5)).mpr ⟨by decide, by decide⟩

theorem mod_stack_slot_survives_six_five : modStackSlotSurvives 6 5 :=
  (modStackSlotSurvives_iff_dualSurvivor midpoint_scan_slot_six_five).mpr (by decide)

/--
The higher Hopf-tower pair map for the `(5,7)` arms.  It lives one level below
the product readout: the Goldbach circle has circumference `2 * 6 = 12`, while
the de-diagonalized spectral product is the `5 * 7 = 35` channel.
-/
structure GoldbachHopfTowerGapPairMapAt (ρ : ℂ) where
  pair : GoldbachMidpointPair 6 5 7
  circumference_eq_pair : goldbachAnnulusCircumference 6 = 5 + 7
  hopf_transport : HopfMulModTransport 6 (harmonicOrbitMulModMultiplier 12)
  phase_witness : Nonempty (GoldbachAnnulusPhaseWitness 6 5)
  slot_five_sweep :
    ∃ x : ℕ, x < hopf_transport.circumference ∧
      scaleOrbitMulMod hopf_transport.circumference hopf_transport.multiplier x = 5
  slot_seven_sweep :
    ∃ x : ℕ, x < hopf_transport.circumference ∧
      scaleOrbitMulMod hopf_transport.circumference hopf_transport.multiplier x = 7
  zero_activation :
    ((1 : ℂ) - (5 : ℂ) ^ (-ρ)) ≠ 0 ∧ ((1 : ℂ) - (7 : ℂ) ^ (-ρ)) ≠ 0
  pair_factorization :
    so4SpectralLine (5 * 7) ρ = so4SpectralLine 5 ρ * so4SpectralLine 7 ρ
  slope_half : SO4OrthogonalTangentMidpointSlope 6 5 7 = (1 / 2 : ℝ)
  holonomy_support : HopfFiberMidpointHolonomySupport 6 5 7

noncomputable def goldbachHopfTower_gapPairMap_at
    {ρ : ℂ} (hζ : IsNontrivialZetaZero ρ) :
    GoldbachHopfTowerGapPairMapAt ρ := by
  let T : HopfMulModTransport 6 (harmonicOrbitMulModMultiplier 12) := hopfMulModTransport_six
  have hChain := zero_contains_pair_holonomy hζ (by decide) goldbach_midpoint_pair_six_five_seven
  refine
    { pair := goldbach_midpoint_pair_six_five_seven
      circumference_eq_pair := hopf_partner_arms_sum_to_circumference goldbach_midpoint_pair_six_five_seven
      hopf_transport := T
      phase_witness := ?_
      slot_five_sweep := ?_
      slot_seven_sweep := ?_
      zero_activation := hChain.1
      pair_factorization := by simpa using hChain.2.1
      slope_half := hChain.2.2.1
      holonomy_support := hChain.2.2.2 }
  · exact ⟨goldbachAnnulusPhaseWitness 6 5 (by decide) midpoint_scan_slot_six_five
      mod_stack_slot_survives_six_five⟩
  · exact hopf_mul_mod_sweeps_all_slots T (by decide) (by decide)
  · exact hopf_mul_mod_sweeps_all_slots T (by decide) (by decide)

/-! ## Direct projection-equation reductions -/

theorem linePhase_re_eq_cos_log {n : ℕ} (_hn : 0 < n) (t : ℝ) :
    (linePhase n t).re = Real.cos (t * Real.log n) := by
  unfold linePhase
  rw [show -(↑t * ↑(Real.log n) : ℂ) = ((-(t * Real.log n) : ℝ) : ℂ) by
    push_cast
    ring]
  rw [exp_ofReal_mul_I_re, Real.cos_neg]

theorem gap_five_seven_re_eq_modulus_cos
    {ρ : ℂ} (hShared : OnLineCascadeTripletSharedSlotFive ρ) :
    (gapFiveSevenSpectralChannel ρ).re =
      criticalLineModulus 35 * Real.cos (ρ.im * Real.log 35) := by
  have hpolar :
      gapFiveSevenSpectralChannel ρ =
        (criticalLineModulus 35 : ℂ) * linePhase 35 ρ.im := by
    simpa [gapFiveSevenSpectralChannel, goldbachMidpointGap] using hShared.gap_polar
  rw [hpolar]
  simp [linePhase_re_eq_cos_log (n := 35) (by decide)]

theorem gap_five_seven_balance_iff_log_phase_cos_zero
    {ρ : ℂ} (hShared : OnLineCascadeTripletSharedSlotFive ρ) :
    OnLineZeroGapFiveSevenSpectralBalancedAt ρ ↔
      Real.cos (ρ.im * Real.log 35) = 0 := by
  dsimp [OnLineZeroGapFiveSevenSpectralBalancedAt]
  rw [gap_five_seven_re_eq_modulus_cos hShared]
  exact mul_eq_zero.trans (or_iff_right (critical_line_modulus_pos (n := 35) (by decide)).ne')

theorem linePhase_opposed_iff_cos_log_zero {n : ℕ} (hn : 0 < n) (t : ℝ) :
    star (linePhase n t) = -linePhase n t ↔
      Real.cos (t * Real.log n) = 0 := by
  constructor
  · intro hOpp
    have hRe := congrArg Complex.re hOpp
    have hBal : (linePhase n t).re = 0 := by
      simp [Complex.conj_re] at hRe
      linarith
    simpa [linePhase_re_eq_cos_log hn t] using hBal
  · intro hCos
    have hBal : (linePhase n t).re = 0 := by
      simpa [linePhase_re_eq_cos_log hn t] using hCos
    apply Complex.ext <;> simp [Complex.conj_re, hBal]

theorem shared_slot_five_gap_log_phase_zero_iff_five_seven_product_opposed
    {ρ : ℂ} (hShared : OnLineCascadeTripletSharedSlotFive ρ) :
    Real.cos (ρ.im * Real.log 35) = 0 ↔
      star (linePhase 5 ρ.im * linePhase 7 ρ.im) =
        -(linePhase 5 ρ.im * linePhase 7 ρ.im) := by
  constructor
  · intro hCos
    have h35 := (linePhase_opposed_iff_cos_log_zero (n := 35) (by decide) ρ.im).mpr hCos
    rwa [hShared.shared_phase.2] at h35
  · intro hProd
    have h35 : star (linePhase 35 ρ.im) = -linePhase 35 ρ.im := by
      rwa [hShared.shared_phase.2]
    exact (linePhase_opposed_iff_cos_log_zero (n := 35) (by decide) ρ.im).mp h35

theorem five_seven_product_opposed_iff_log_phase_zero (t : ℝ) :
    star (linePhase 5 t * linePhase 7 t) =
        -(linePhase 5 t * linePhase 7 t) ↔
      Real.cos (t * Real.log 35) = 0 := by
  have hmul : linePhase 35 t = linePhase 5 t * linePhase 7 t := by
    simpa using (linePhase_mul (p := 5) (q := 7) (by decide) (by decide) t)
  constructor
  · intro hProd
    have h35 : star (linePhase 35 t) = -linePhase 35 t := by
      rwa [hmul]
    exact (linePhase_opposed_iff_cos_log_zero (n := 35) (by decide) t).mp h35
  · intro hCos
    have h35 := (linePhase_opposed_iff_cos_log_zero (n := 35) (by decide) t).mpr hCos
    rwa [hmul] at h35

theorem on_line_zero_triplet_six_gap_spectral_from_rolling_associator_phase
    (hRollPhase : OnLineZeroTripletSixRollingAssociatorIdentifiesGapSpectralPhase) :
    OnLineZeroTripletSixGapSpectralFromRollingIdentification :=
  fun hRoll {ρ} hζ hShared => hRollPhase (ρ := ρ) hζ hShared.budget.hσ hShared hRoll

theorem on_line_zero_triplet_six_associator_phase_identifies_gap_spectral
    (hRolling : OnLineZeroTripletSixGapSpectralFromRollingIdentification)
    (hRoll : RollingZetaIdentificationAtCriticalLine)
    {ρ : ℂ} (hζ : IsNontrivialZetaZero ρ) (_hs : ρ.re = (1 / 2 : ℝ))
    (hShared : OnLineCascadeTripletSharedSlotFive ρ) :
    star (gapFiveSevenSpectralChannel ρ) = -gapFiveSevenSpectralChannel ρ :=
  hRolling hRoll hζ hShared

theorem on_line_zero_triplet_six_associator_phase_identifies_gap_spectral_at
    (hRolling : OnLineZeroTripletSixGapSpectralFromRollingIdentification)
    (hRoll : RollingZetaIdentificationAtCriticalLine)
    {ρ : ℂ} (hζ : IsNontrivialZetaZero ρ) (_hs : ρ.re = (1 / 2 : ℝ))
    (hShared : OnLineCascadeTripletSharedSlotFive ρ) :
    OnLineZeroGapFiveSevenSpectralOpposedAt ρ :=
  hRolling hRoll hζ hShared

theorem on_line_zero_triplet_six_forces_gap_spectral_from_rolling
    (hRollPhase : OnLineZeroTripletSixRollingAssociatorIdentifiesGapSpectralPhase)
    (hRoll : RollingZetaIdentificationAtCriticalLine) :
    OnLineZeroTripletSixForcesGapFiveSevenSpectralOpposed :=
  fun hζ hShared => hRollPhase hζ hShared.budget.hσ hShared hRoll

theorem on_line_zero_gap_linePhase_thirty_five_from_rolling_route
    (hRollPhase : OnLineZeroTripletSixRollingAssociatorIdentifiesGapSpectralPhase)
    (hRoll : RollingZetaIdentificationAtCriticalLine) :
    OnLineZeroGapLinePhaseThirtyFiveOpposedFromTriplet :=
  on_line_zero_gap_linePhase_thirty_five_opposed_from_triplet_spectral
    (on_line_zero_triplet_six_forces_gap_spectral_from_rolling hRollPhase hRoll)

theorem on_line_zero_gap_linePhase_thirty_five_from_rolling_packaging
    (hRolling : OnLineZeroTripletSixGapSpectralFromRollingIdentification)
    (hRoll : RollingZetaIdentificationAtCriticalLine) :
    OnLineZeroGapLinePhaseThirtyFiveOpposedFromTriplet :=
  on_line_zero_gap_linePhase_thirty_five_opposed_from_triplet_spectral
    (fun hζ hShared => hRolling hRoll hζ hShared)

/-! ## Rolling readout bundle at a shared-slot zero -/

structure OnLineTripletSixRollingGapReadoutAt (ρ : ℂ) where
  hζ : IsNontrivialZetaZero ρ
  hs : ρ.re = (1 / 2 : ℝ)
  hShared : OnLineCascadeTripletSharedSlotFive ρ
  ingredients : OnLineTripletSixGapAttackIngredients ρ
  hRoll : RollingZetaIdentificationAtCriticalLine
  matched : MatchedRollingZeroAt ρ (rolledSampleAtHeight ρ.im)
  residual : ZetaEqualsS3ResidualAt ρ (rolledSampleAtHeight ρ.im)
  triplet : GoldbachTripletLogAssociatorInvariant ρ 6
  triplet_five_seven : triplet.p = 5 ∧ triplet.q = 7
  gap_eq_pair :
    gapFiveSevenSpectralChannel ρ =
      so4SpectralLine 5 ρ * so4SpectralLine 7 ρ
  associator_floor :
    1 / ((6 ^ 3 : ℕ) : ℝ) ≤
      octAssociatorChannel triplet.p triplet.q (2 * 6) (Complex.mk (1 / 2 : ℝ) ρ.im)

def on_line_triplet_six_rolling_gap_readout_at
    (hRoll : RollingZetaIdentificationAtCriticalLine)
    {ρ : ℂ} (hζ : IsNontrivialZetaZero ρ) (hShared : OnLineCascadeTripletSharedSlotFive ρ)
    (G : GoldbachTripletLogAssociatorInvariant ρ 6) :
    OnLineTripletSixRollingGapReadoutAt ρ :=
  { hζ := hζ
    hs := hShared.budget.hσ
    hShared := hShared
    ingredients := on_line_triplet_six_gap_attack_ingredients hζ hShared
    hRoll := hRoll
    matched := on_line_zero_matched_rolling_at_height hRoll hShared.budget.hσ
    residual := on_line_zero_rolling_residual_at_height hRoll hShared.budget.hσ
    triplet := G
    triplet_five_seven := goldbach_triplet_six_uses_five_seven_arms G
    gap_eq_pair := goldbach_triplet_six_gap_eq_pair_from_invariant G
    associator_floor := G.associator_floor }

structure TripletSixRollingGapSpectralAttackData where
  triplet_five_seven :
    ∀ {ρ : ℂ}, (G : GoldbachTripletLogAssociatorInvariant ρ 6) → G.p = 5 ∧ G.q = 7
  gap_pair_from_triplet :
    ∀ {ρ : ℂ}, (G : GoldbachTripletLogAssociatorInvariant ρ 6) →
      gapFiveSevenSpectralChannel ρ =
        so4SpectralLine 5 ρ * so4SpectralLine 7 ρ
  rolling_matched :
    ∀ (_hRoll : RollingZetaIdentificationAtCriticalLine) {ρ : ℂ},
      ρ.re = (1 / 2 : ℝ) → MatchedRollingZeroAt ρ (rolledSampleAtHeight ρ.im)
  rolling_residual :
    ∀ (_hRoll : RollingZetaIdentificationAtCriticalLine) {ρ : ℂ},
      ρ.re = (1 / 2 : ℝ) → ZetaEqualsS3ResidualAt ρ (rolledSampleAtHeight ρ.im)
  opposed_implies_balance :
    ∀ {ρ : ℂ}, OnLineZeroGapFiveSevenSpectralOpposedAt ρ →
      OnLineZeroGapFiveSevenSpectralBalancedAt ρ
  gap_spectral_transfer :
    OnLineZeroGapFiveSevenSpectralOpposedTransfersToLinePhaseThirtyFive
  balance_iff_opposed :
    ∀ {ρ : ℂ}, OnLineZeroGapFiveSevenSpectralBalancedAt ρ ↔
      OnLineZeroGapFiveSevenSpectralOpposedAt ρ
  balance_and_floor_transfer :
    OnLineZeroGapSpectralBalanceAndAssociatorFloorGiveOpposition
  rolling_implies_phase :
    OnLineZeroTripletSixRollingAssociatorIdentifiesGapSpectralPhase →
      OnLineZeroTripletSixGapSpectralFromRollingIdentification
  balance_implies_phase :
    OnLineZeroRollingResidualGivesGapSpectralBalance →
      OnLineZeroTripletSixRollingAssociatorIdentifiesGapSpectralPhase
  balance_and_floor_implies_phase :
    OnLineZeroRollingResidualGivesGapSpectralBalance →
      OnLineZeroGapSpectralBalanceAndAssociatorFloorGiveOpposition →
        OnLineZeroTripletSixRollingAssociatorIdentifiesGapSpectralPhase

def triplet_six_rolling_gap_spectral_attack_data : TripletSixRollingGapSpectralAttackData where
  triplet_five_seven := goldbach_triplet_six_uses_five_seven_arms
  gap_pair_from_triplet := goldbach_triplet_six_gap_eq_pair_from_invariant
  rolling_matched := on_line_zero_matched_rolling_at_height
  rolling_residual := on_line_zero_rolling_residual_at_height
  opposed_implies_balance := gap_five_seven_spectral_opposed_implies_balanced
  gap_spectral_transfer := on_line_zero_gap_five_seven_spectral_transfer_unconditional
  balance_iff_opposed := gap_five_seven_spectral_balanced_iff_opposed
  balance_and_floor_transfer :=
    on_line_zero_gap_spectral_balance_and_floor_give_opposition_unconditional
  rolling_implies_phase := on_line_zero_triplet_six_gap_spectral_from_rolling_associator_phase
  balance_implies_phase := on_line_zero_triplet_six_rolling_associator_phase_of_balance
  balance_and_floor_implies_phase :=
    on_line_zero_triplet_six_rolling_associator_phase_of_balance_and_floor

structure TripletSixRollingGapSpectralDecomposition where
  attack_data : TripletSixRollingGapSpectralAttackData
  rolling_balance : OnLineZeroRollingResidualGivesGapSpectralBalance
  associator_transfer : OnLineZeroGapSpectralBalanceAndAssociatorFloorGiveOpposition
  rolling_associator_phase : OnLineZeroTripletSixRollingAssociatorIdentifiesGapSpectralPhase

structure TripletSixRollingGapSpectralBalanceTool where
  attack_data : TripletSixRollingGapSpectralAttackData
  rolling_balance : OnLineZeroRollingResidualGivesGapSpectralBalance
  rolling_associator_phase : OnLineZeroTripletSixRollingAssociatorIdentifiesGapSpectralPhase
  rolling_packaging : OnLineZeroTripletSixGapSpectralFromRollingIdentification

def triplet_six_rolling_gap_spectral_decomposition
    (hBalance : OnLineZeroRollingResidualGivesGapSpectralBalance)
    (hTransfer : OnLineZeroGapSpectralBalanceAndAssociatorFloorGiveOpposition) :
    TripletSixRollingGapSpectralDecomposition where
  attack_data := triplet_six_rolling_gap_spectral_attack_data
  rolling_balance := hBalance
  associator_transfer := hTransfer
  rolling_associator_phase :=
    on_line_zero_triplet_six_rolling_associator_phase_of_balance_and_floor hBalance hTransfer

def triplet_six_rolling_gap_spectral_balance_tool
    (hBalance : OnLineZeroRollingResidualGivesGapSpectralBalance) :
    TripletSixRollingGapSpectralBalanceTool where
  attack_data := triplet_six_rolling_gap_spectral_attack_data
  rolling_balance := hBalance
  rolling_associator_phase :=
    on_line_zero_triplet_six_rolling_associator_phase_of_balance hBalance
  rolling_packaging :=
    on_line_zero_triplet_six_gap_spectral_from_rolling_associator_phase
      (on_line_zero_triplet_six_rolling_associator_phase_of_balance hBalance)

structure TripletSixRollingGapSpectralAttackHalf where
  attack_data : TripletSixRollingGapSpectralAttackData
  rolling_associator_phase : OnLineZeroTripletSixRollingAssociatorIdentifiesGapSpectralPhase
  rolling_packaging : OnLineZeroTripletSixGapSpectralFromRollingIdentification
  triplet_gap_spectral : OnLineZeroTripletSixForcesGapFiveSevenSpectralOpposed
  step_one : OnLineZeroGapLinePhaseThirtyFiveOpposedFromTriplet

def triplet_six_rolling_gap_spectral_attack_half
    (hRollPhase : OnLineZeroTripletSixRollingAssociatorIdentifiesGapSpectralPhase)
    (hRoll : RollingZetaIdentificationAtCriticalLine) :
    TripletSixRollingGapSpectralAttackHalf where
  attack_data := triplet_six_rolling_gap_spectral_attack_data
  rolling_associator_phase := hRollPhase
  rolling_packaging := on_line_zero_triplet_six_gap_spectral_from_rolling_associator_phase hRollPhase
  triplet_gap_spectral := on_line_zero_triplet_six_forces_gap_spectral_from_rolling hRollPhase hRoll
  step_one := on_line_zero_gap_linePhase_thirty_five_from_rolling_route hRollPhase hRoll

end

end Hqiv.Story

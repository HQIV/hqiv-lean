import Hqiv.Story.S3GoldbachAnnulusPhasePinning
import Hqiv.Story.S3MidpointConstructiveSpectralSlope
import Hqiv.Story.S3MidpointEckmannHiltonSoe
import Hqiv.Story.ArityFTADecomposition
import Hqiv.Geometry.SoeModStackCombinatorics

/-!
# Annulus proof by contradiction: no fill ⇒ twiddle prime; composite ⇒ S₂…Sₙ prime pieces

## User proof shape

1. **Contrapositive.**  If no equidistant prime pair fills the annulus at axis `N`,
   then `N` is prime (`AnnulusNoFillImpliesTwiddlePrime`).
2. **Composite twiddle on the ring.**  If `N` is composite, a prime factor of `N`
   already lies in the finite stack `S₂…Sₙ = finiteSoeAngleStack N`.
3. **Composite reflected arm.**  If the left arm is prime and the partner composite,
   `minFac` lands in the same stack — a prime **piece** on the ring.
4. **Contradiction step (open globally).**  Assume composite `N` and no annulus fill;
   extinction + stack crossings + EH cardinality obstruction cannot coexist.

Items (1)–(3) are proved below.  (4) is packaged as `AnnulusContradictionDischarge N`,
   equivalent to the global Goldbach midpoint target once the EH obstruction is closed.
-/

namespace Hqiv.Story

open Hqiv.Geometry

/-! ## 1. Contrapositive: no annulus fill ⇒ twiddle axis is prime -/

def AnnulusNoFillImpliesTwiddlePrime (N : ℕ) : Prop :=
  MidpointNoSurvivorImpliesPrime N

def TwiddleCompositeForcesAnnulusFill (N : ℕ) : Prop :=
  GoldbachAnnulusCirclePhasePin N

theorem annulus_no_fill_iff_twiddle_composite_forces (N : ℕ) :
    AnnulusNoFillImpliesTwiddlePrime N ↔ TwiddleCompositeForcesAnnulusFill N := by
  dsimp [AnnulusNoFillImpliesTwiddlePrime, TwiddleCompositeForcesAnnulusFill]
  rw [midpoint_no_survivor_iff_composite_survivor, goldbach_annulus_circle_phase_pin_iff_composite]

theorem annulus_no_fill_contraposition (N : ℕ) :
    (¬ MidpointSieveSurvivorExists N → Nat.Prime N) ↔ CompositeMidpointHasSurvivor N :=
  midpoint_no_survivor_iff_composite_survivor N

theorem annulus_no_fill_implies_prime {N : ℕ}
    (h : AnnulusNoFillImpliesTwiddlePrime N) (hne : ¬ MidpointSieveSurvivorExists N) :
    Nat.Prime N :=
  h hne

theorem twiddle_composite_forces_fill {N : ℕ} (h : TwiddleCompositeForcesAnnulusFill N) :
    ModStackGoldbachMidpoint N :=
  (goldbach_annulus_circle_phase_pin_iff_fill N).mp h

/-! ## 2. Stack ring S₂…Sₙ = prime pieces on the annulus -/

abbrev soeStackPrimeRing (N : ℕ) : Finset ℕ :=
  finiteSoeAngleStack N

theorem mem_soe_stack_prime_ring_iff {N r : ℕ} :
    r ∈ soeStackPrimeRing N ↔ r ∈ finiteSoeAngleStack N := Iff.rfl

theorem soe_stack_prime_ring_members_prime {N r : ℕ} (hr : r ∈ soeStackPrimeRing N) :
    Nat.Prime r :=
  (mem_finiteSoeAngleStack_iff' (N := N)).mp hr |>.1

theorem soe_stack_prime_ring_fifteen :
    soeStackPrimeRing 15 = ({2, 3, 5} : Finset ℕ) :=
  finiteSoeAngleStack_fifteen

/-! ## 3. Composite twiddle deposits a prime piece on the ring -/

theorem composite_twiddle_minFac_in_stack {N : ℕ} (hN : 2 ≤ N) (hc : ¬ Nat.Prime N) :
    Nat.minFac N ∈ soeStackPrimeRing N :=
  composite_minFac_in_finite_stack hN hc

theorem composite_twiddle_has_stack_factor {N : ℕ} (hN : 2 ≤ N) (hc : ¬ Nat.Prime N) :
    ∃ r ∈ soeStackPrimeRing N, r ∣ N :=
  ⟨Nat.minFac N, composite_twiddle_minFac_in_stack hN hc, Nat.minFac_dvd N⟩

/-! ## 4. Composite reflected arm deposits minFac on the ring -/

theorem composite_reflected_minFac_in_stack {N p : ℕ} (hp : p ∈ midpointScanSlots N)
    (hpr : Nat.Prime p) (hc : ¬ Nat.Prime (2 * N - p)) (hq : 4 ≤ 2 * N - p) :
    Nat.minFac (2 * N - p) ∈ soeStackPrimeRing N :=
  composite_reflected_minFac_in_finite_stack hp hpr hc hq

/-! ## 5. Proof-by-contradiction packaging -/

structure AnnulusContradictionHypothesis (N : ℕ) where
  hc : ¬ Nat.Prime N
  hno : ¬ MidpointSieveSurvivorExists N

theorem annulus_contradiction_hypothesis_no_mod_stack {N : ℕ}
    (H : AnnulusContradictionHypothesis N) :
    ¬ ModStackGoldbachMidpoint N := by
  intro hFill
  obtain ⟨p, hStack, hp, _, hpLe⟩ := hFill H.hc
  have hpSlot : p ∈ midpointScanSlots N :=
    (mem_midpointScanSlots_iff (N := N) (p := p)).mpr ⟨Nat.Prime.two_le hp, hpLe⟩
  exact H.hno ⟨p, (modStackSlotSurvives_iff_dualSurvivor (N := N) (p := p) hpSlot).mp hStack⟩

theorem annulus_contradiction_implies_prime {N : ℕ}
    (h : AnnulusNoFillImpliesTwiddlePrime N) (H : AnnulusContradictionHypothesis N) :
    Nat.Prime N :=
  h H.hno

def AnnulusContradictionDischarge (N : ℕ) : Prop :=
  ¬ AnnulusContradictionHypothesis N

theorem annulus_contradiction_discharge_iff_composite (N : ℕ) :
    AnnulusContradictionDischarge N ↔ CompositeMidpointHasSurvivor N := by
  constructor
  · intro h hc
    by_contra hno
    exact h ⟨hc, hno⟩
  · intro hHas H
    rcases hHas H.hc with ⟨p, hSurv⟩
    exact H.hno ⟨p, hSurv⟩

theorem annulus_contradiction_discharge_iff_annulus_fill (N : ℕ) :
    AnnulusContradictionDischarge N ↔ TwiddleCompositeForcesAnnulusFill N := by
  rw [annulus_contradiction_discharge_iff_composite]
  exact (goldbach_annulus_circle_phase_pin_iff_composite N).symm

theorem annulus_contradiction_discharge_of_cardinality {N : ℕ} (hN : 4 ≤ N)
    (hOb : EckmannHiltonCardinalityObstruction N) :
    AnnulusContradictionDischarge N := by
  intro H
  have hSurv : CompositeMidpointHasSurvivor N :=
    (eckmann_hilton_forward_collapse_iff_composite N).mp
      (eckmann_hilton_forward_collapse_of_cardinality_obstruction hN hOb)
  have hMod : ModStackGoldbachMidpoint N :=
    (mod_stack_goldbach_iff_composite_survivor N).mpr hSurv
  exact (annulus_contradiction_hypothesis_no_mod_stack H) hMod

/-!
**Status.**  The annulus contradiction skeleton is wired: composite twiddle ⇒ prime
piece on `S₂…Sₙ`; composite reflected arm ⇒ `minFac` piece; no fill + composite ⇒
contradiction once `EckmannHiltonCardinalityObstruction` closes globally.
-/

end Hqiv.Story

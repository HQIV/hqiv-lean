import Hqiv.Geometry.GoldbachG2Parity
import Mathlib.Data.Nat.ModEq

/-!
# Mod-stack combinatorics for the Goldbach midpoint sieve

The forward/reflected SoE at midpoint `N` attaches a **finite residue profile** to
each scan slot `p`:

* coarse hex column `p mod 6` (prime labels only — **not** a partner constraint);
* fine stack phases `(p mod r, (2N - p) mod r)` for each `r` in `finiteSoeAngleStack N`.

**Mod-stack survival** is the meet (AND) of `dualModLineClear` over the finite
spectrum — the combinatorics of which profile tuples survive all stack moduli.

This file packages that layer and proves it is **definitionally equivalent** to the
existing `gapSurvivesFiniteAngleStack` / `CompositeMidpointHasSurvivor` pipeline.

## What is proved here

* hex column lemmas for primes `> 3`;
* CRT recombination for the `N = 15` stack `{2,3,5}` ↔ `mod 30`;
* profile definitions and equivalence with stack survival;
* `ModStackGoldbachMidpoint N` ↔ `CompositeMidpointHasSurvivor N`;
* `ModStackExtinctionImpossible N` ↔ `FiniteStackCannotExtinctAllGaps N`;
* worked instance `N = 15`: stack `{2,3,5}`, survivor slots `{7,11,13}`.

## What remains open ( = Goldbach midpoint )

`ModStackExtinctionImpossible N` for every composite `N`.  Proving that in full
generality is exactly the global extinction step — not a corollary of definitions.
-/

namespace Hqiv.Geometry

open Nat

/-! ## 1. Hex coarse spectrum (base-6 columns) -/

/-- Hex column label: `n mod 6`.  Only columns `1` and `5` host primes `> 3`. -/
def hexColumn (n : ℕ) : ℕ :=
  n % 6

def hexColumnPlusOne (n : ℕ) : Prop :=
  hexColumn n = 1

def hexColumnMinusOne (n : ℕ) : Prop :=
  hexColumn n = 5

def hexColumnPrimeSlot (n : ℕ) : Prop :=
  hexColumnPlusOne n ∨ hexColumnMinusOne n

theorem hexColumnPrimeSlot_iff (n : ℕ) :
    hexColumnPrimeSlot n ↔ hexColumn n = 1 ∨ hexColumn n = 5 := Iff.rfl

theorem prime_gt_three_hexColumn {p : ℕ} (hp : Nat.Prime p) (h3 : 3 < p) :
    hexColumnPrimeSlot p := by
  rw [hexColumnPrimeSlot_iff, hexColumn]
  rcases hp.eq_two_or_odd with h2 | hodd1
  · omega
  · have hnot3 : p % 3 ≠ 0 := by
      intro h
      have : 3 ∣ p := Nat.dvd_iff_mod_eq_zero.mpr h
      rcases (Nat.dvd_prime hp).1 this with h3eq | hp1
      · omega
      · omega
    omega

theorem hex_partner_sum_mod_six {N p : ℕ} (hpLe : p ≤ N) :
    (hexColumn p + hexColumn (2 * N - p)) % 6 = (2 * N) % 6 := by
  unfold hexColumn
  omega

/-!
Hex columns label scan slots on the base-6 grid only.  Partner geometry is
**equidistance from axis `N`** (`gapLeftArm` / `gapRightArm`); see
`S3GoldbachAnnulusCircle`.
-/

/-! ## 2. Mod-stack profile and survival -/

/--
**Mod-stack slot survival.**  Slot `p` clears every forward/reflected residue line
from the finite SoE spectrum at `2N`.
-/
def modStackSlotSurvives (N p : ℕ) : Prop :=
  ∀ r ∈ finiteSoeAngleStack N, dualModLineClear N r p

/--
The residue **phase pair** at modulus `r`: forward mark `p mod r`, reflect mark
`(2N - p) mod r`.
-/
def modStackPhase (N r p : ℕ) : ℕ × ℕ :=
  soeResiduePhasePair N r p

theorem modStackPhase_eq_soeResiduePhasePair (N r p : ℕ) :
    modStackPhase N r p = soeResiduePhasePair N r p := rfl

theorem modStackSlotSurvives_iff_phase_clear {N p : ℕ} :
    modStackSlotSurvives N p ↔
      ∀ r ∈ finiteSoeAngleStack N, modStackPhase N r p = (p % r, (2 * N - p) % r) ∧
        dualModLineClear N r p := by
  unfold modStackSlotSurvives modStackPhase
  constructor
  · intro h r hr
    exact ⟨rfl, h r hr⟩
  · intro h r hr
    exact (h r hr).2

theorem modStackSlotSurvives_iff_gapSurvives {N p : ℕ} (hpLe : p ≤ N) :
    modStackSlotSurvives N p ↔ gapSurvivesFiniteAngleStack N (midpointLeftGap N p) := by
  rw [gapSurvivesFiniteAngleStack_slot]
  unfold modStackSlotSurvives midpointLeftGap
  rw [Nat.sub_sub_self hpLe]

theorem modStackSlotSurvives_iff_symmetric {N p : ℕ} (hpLe : p ≤ N) (hp2 : 2 ≤ p) :
    modStackSlotSurvives N p ↔ symmetricPrimeReflectionAtGap N (midpointLeftGap N p) := by
  rw [modStackSlotSurvives_iff_gapSurvives hpLe]
  exact gap_survives_stack_iff_symmetric_prime (N := N) (g := midpointLeftGap N p)
    (by unfold midpointLeftGap; omega)
    (by unfold midpointLeftGap; exact Nat.sub_le _ _)

theorem modStackSlotSurvives_iff_dualSurvivor {N p : ℕ} (hp : p ∈ midpointScanSlots N) :
    modStackSlotSurvives N p ↔ dualMidpointSurvivor N p := by
  have hpLe : p ≤ N := (mem_midpointScanSlots_iff (N := N) (p := p)).mp hp |>.2
  have hp2 : 2 ≤ p := (mem_midpointScanSlots_iff (N := N) (p := p)).mp hp |>.1
  rw [modStackSlotSurvives_iff_symmetric hpLe hp2]
  exact (dualMidpointSurvivor_iff_symmetric_gap (N := N) (p := p) hpLe).symm

/-! ## 3. CRT for the `N = 15` stack (`2N = 30`) -/

theorem coprime_two_three : Nat.Coprime 2 3 := by decide

theorem coprime_six_five : Nat.Coprime 6 5 := by decide

/--
**CRT recombination.**  At `2N = 30` the stack moduli `{2,3,5}` merge to a single
class mod `30`.
-/
theorem modEq_six_iff {a b : ℕ} :
    a ≡ b [MOD 6] ↔ a ≡ b [MOD 2] ∧ a ≡ b [MOD 3] := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num]
  exact (Nat.modEq_and_modEq_iff_modEq_mul coprime_two_three).symm

theorem modEq_thirty_pair_iff {a b : ℕ} :
    a ≡ b [MOD 30] ↔ a ≡ b [MOD 6] ∧ a ≡ b [MOD 5] := by
  rw [show (30 : ℕ) = 6 * 5 by norm_num]
  exact (Nat.modEq_and_modEq_iff_modEq_mul coprime_six_five).symm

theorem modEq_thirty_iff {a b : ℕ} :
    a ≡ b [MOD 30] ↔ a ≡ b [MOD 2] ∧ a ≡ b [MOD 3] ∧ a ≡ b [MOD 5] := by
  rw [modEq_thirty_pair_iff, modEq_six_iff]
  tauto

theorem sqrt_thirty : Nat.sqrt 30 = 5 := by norm_num

theorem finiteSoeAngleStack_fifteen :
    finiteSoeAngleStack 15 = ({2, 3, 5} : Finset ℕ) := by
  ext r
  have hsqrt : Nat.sqrt (2 * 15) = 5 := by norm_num
  simp only [mem_finiteSoeAngleStack_iff', Finset.mem_insert, Finset.mem_singleton, hsqrt]
  constructor
  · intro ⟨hpr, hr2, hr⟩
    interval_cases r <;> simp_all (config := {decide := true})
  · intro hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨Nat.prime_two, by decide, by decide⟩
    · exact ⟨Nat.prime_three, by decide, by decide⟩
    · exact ⟨Nat.prime_five, by decide, by decide⟩

def modStackPeriodFifteen : ℕ :=
  30

theorem modStackPeriodFifteen_eq_lcm :
    modStackPeriodFifteen = Nat.lcm (Nat.lcm 2 3) 5 := by decide

/-! ## 4. Goldbach midpoint as mod-stack extinction -/

/--
**Mod-stack Goldbach at midpoint `N`.**  Some scan slot survives the finite profile
and both arms are prime — the combinatorial form of `p + q = 2N`.
-/
def ModStackGoldbachMidpoint (N : ℕ) : Prop :=
  ¬ Nat.Prime N →
    ∃ p, modStackSlotSurvives N p ∧ Nat.Prime p ∧ Nat.Prime (2 * N - p) ∧ p ≤ N

/--
**Mod-stack extinction impossible.**  One cannot kill every positive gap on the
slope orbit with the finite spectrum — the meet over moduli cannot be empty.
-/
def ModStackExtinctionImpossible (N : ℕ) : Prop :=
  FiniteStackCannotExtinctAllGaps N

theorem mod_stack_goldbach_iff_composite_survivor (N : ℕ) :
    ModStackGoldbachMidpoint N ↔ CompositeMidpointHasSurvivor N := by
  unfold ModStackGoldbachMidpoint CompositeMidpointHasSurvivor
  constructor
  · intro h hc
    obtain ⟨p, hStack, hp, hq, hpLe⟩ := h hc
    have hpSlot : p ∈ midpointScanSlots N :=
      (mem_midpointScanSlots_iff (N := N) (p := p)).mpr ⟨Nat.Prime.two_le hp, hpLe⟩
    exact ⟨p, (modStackSlotSurvives_iff_dualSurvivor (N := N) (p := p) hpSlot).mp hStack⟩
  · intro h hc
    obtain ⟨p, hSurv⟩ := h hc
    have hpLe : p ≤ N := hSurv.2.2.1
    have hpSlot : p ∈ midpointScanSlots N :=
      (mem_midpointScanSlots_iff (N := N) (p := p)).mpr ⟨Nat.Prime.two_le hSurv.1, hpLe⟩
    refine ⟨p, (modStackSlotSurvives_iff_dualSurvivor (N := N) (p := p) hpSlot).mpr hSurv,
      hSurv.1, hSurv.2.1, hpLe⟩

theorem mod_stack_extinction_impossible_iff (N : ℕ) :
    ModStackExtinctionImpossible N ↔ FiniteStackCannotExtinctAllGaps N := Iff.rfl

theorem mod_stack_extinction_iff_goldbach (N : ℕ) :
    ModStackExtinctionImpossible N ↔ ModStackGoldbachMidpoint N := by
  unfold ModStackExtinctionImpossible
  rw [finite_stack_extinction_iff_constructive, constructive_spectral_forces_iff_slope_hit,
    composite_slope_orbit_forces_iff_has_survivor, mod_stack_goldbach_iff_composite_survivor]

theorem mod_stack_extinction_iff_eh_forward (N : ℕ) :
    ModStackExtinctionImpossible N ↔ EckmannHiltonForwardCollapse N := by
  unfold ModStackExtinctionImpossible EckmannHiltonForwardCollapse
  rfl

/-! ## 5. Worked instance: `N = 15`, `2N = 30` -/

theorem mod_stack_slot_survives_fifteen_seven :
    modStackSlotSurvives 15 7 := by
  intro r hr
  rw [finiteSoeAngleStack_fifteen] at hr
  have hr' : r = 2 ∨ r = 3 ∨ r = 5 := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hr
  rcases hr' with rfl | rfl | rfl <;>
    unfold dualModLineClear forwardResidueCrossed reflectResidueCrossed <;> decide

theorem mod_stack_slot_survives_fifteen_eleven :
    modStackSlotSurvives 15 11 := by
  intro r hr
  rw [finiteSoeAngleStack_fifteen] at hr
  have hr' : r = 2 ∨ r = 3 ∨ r = 5 := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hr
  rcases hr' with rfl | rfl | rfl <;>
    unfold dualModLineClear forwardResidueCrossed reflectResidueCrossed <;> decide

theorem mod_stack_slot_survives_fifteen_thirteen :
    modStackSlotSurvives 15 13 := by
  intro r hr
  rw [finiteSoeAngleStack_fifteen] at hr
  have hr' : r = 2 ∨ r = 3 ∨ r = 5 := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hr
  rcases hr' with rfl | rfl | rfl <;>
    unfold dualModLineClear forwardResidueCrossed reflectResidueCrossed <;> decide

theorem mod_stack_survivor_iff_dual_fifteen {p : ℕ} (hp : p ∈ midpointScanSlots 15) :
    modStackSlotSurvives 15 p ↔ dualMidpointSurvivor 15 p :=
  modStackSlotSurvives_iff_dualSurvivor (N := 15) (p := p) hp

theorem mod_stack_survivor_slots_fifteen_eq :
    (midpointScanSlots 15).filter (fun p => dualMidpointSurvivor 15 p) =
      ({7, 11, 13} : Finset ℕ) := by
  native_decide

theorem mod_stack_survivor_slots_fifteen :
    (midpointScanSlots 15).filter (fun p => dualMidpointSurvivor 15 p) =
      dualMidpointLeftCandidates 15 := by
  rw [mod_stack_survivor_slots_fifteen_eq, dualMidpointLeftCandidates_fifteen]

theorem mod_stack_survivor_slots_fifteen_modstack {p : ℕ} (hp : p ∈ midpointScanSlots 15) :
    modStackSlotSurvives 15 p ↔ dualMidpointSurvivor 15 p :=
  mod_stack_survivor_iff_dual_fifteen hp

theorem mod_stack_goldbach_fifteen : ModStackGoldbachMidpoint 15 := by
  intro _
  refine ⟨7, mod_stack_slot_survives_fifteen_seven, nat_prime_seven, nat_prime_twentythree,
    by omega⟩

theorem mod_stack_extinction_impossible_fifteen : ModStackExtinctionImpossible 15 :=
  (mod_stack_extinction_iff_goldbach 15).mpr mod_stack_goldbach_fifteen

theorem mod_stack_goldbach_pair_fifteen :
    GoldbachMidpointPair 15 7 23 :=
  goldbach_midpoint_pair_fifteen_seven_twentythree

/-!
**Status.**  Mod-stack combinatorics is now a first-class layer, equivalent to the
existing EH / constructive-spectral targets.  The general theorem
`∀ N, ModStackExtinctionImpossible N` is the Goldbach midpoint problem stated in
profile language; only instances (e.g. `N = 15`) are closed here.
-/

end Hqiv.Geometry

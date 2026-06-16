import Hqiv.Story.S3GoldbachAnnulusCircle
import Hqiv.Story.S3ExplicitFormulaPrimePhaseCoincidence

/-!
# Goldbach annulus slots ↔ Euler prime phases on the filled Hopf circle

Mod-stack survivors on the midpoint scan become **prime phase pairs** on the
`2N`-slot Hopf circle.  Each arm carries a `PrimePhaseCoincidenceCell`; two
distinct partner primes **pin** any shared circle angle via the explicit-formula
coincidence bundle (`two_primes_pin`).

## Proved here

* annulus shell slots as `HarmonicShellSlot` at depth `m = 2N`;
* left/right arm phases = `linePhase` at annulus slot angles;
* `goldbachAnnulusPhaseWitness` packages coincidence cells + unit-circle phases;
* mod-stack survivor ⇒ phase witness (composite `N`);
* `GoldbachAnnulusCirclePhasePin N` ↔ `GoldbachAnnulusCircleFill N`;
* two partner primes pin `θ` unconditionally;
* worked instance `N = 15` (`7 + 23` on the `30`-slot circle).

## Open ( = global Goldbach midpoint )

`∀ composite N, GoldbachAnnulusCirclePhasePin N`.
-/

namespace Hqiv.Story

noncomputable section

open Complex Real Hqiv.Geometry
open scoped ComplexConjugate

/-! ## Annulus slots as harmonic-shell indices -/

theorem goldbach_scan_slot_lt_circumference {N p : ℕ} (hN : 0 < N)
    (hp : p ∈ midpointScanSlots N) : p < goldbachAnnulusCircumference N := by
  have ⟨_, hpLe⟩ := (mem_midpointScanSlots_iff (N := N) (p := p)).mp hp
  dsimp [goldbachAnnulusCircumference]
  omega

theorem goldbach_partner_lt_circumference {N p : ℕ} (hN : 0 < N)
    (hp : p ∈ midpointScanSlots N) : 2 * N - p < goldbachAnnulusCircumference N := by
  have ⟨_, hpLe⟩ := (mem_midpointScanSlots_iff (N := N) (p := p)).mp hp
  dsimp [goldbachAnnulusCircumference]
  omega

def goldbachLeftShellSlot (N p : ℕ) (hN : 0 < N) (hp : p ∈ midpointScanSlots N) :
    HarmonicShellSlot :=
  ⟨goldbachAnnulusCircumference N, ⟨p, goldbach_scan_slot_lt_circumference hN hp⟩⟩

def goldbachRightShellSlot (N p : ℕ) (hN : 0 < N) (hp : p ∈ midpointScanSlots N) :
    HarmonicShellSlot :=
  ⟨goldbachAnnulusCircumference N,
    ⟨2 * N - p, goldbach_partner_lt_circumference hN hp⟩⟩

theorem goldbach_left_shell_slot_angle {N p : ℕ} (hN : 0 < N) (hp : p ∈ midpointScanSlots N) :
    shellSweepAngle (goldbach_shell_depth_pos hN)
        (goldbachLeftShellSlot N p hN hp).2 =
      goldbachLeftArmAngle N p hN (goldbach_scan_slot_lt_circumference hN hp) := rfl

theorem goldbach_right_shell_slot_angle {N p : ℕ} (hN : 0 < N) (hp : p ∈ midpointScanSlots N) :
    shellSweepAngle (goldbach_shell_depth_pos hN)
        (goldbachRightShellSlot N p hN hp).2 =
      goldbachLeftArmAngle N (2 * N - p) hN
        (goldbach_partner_lt_circumference hN hp) := by
  rfl

/-! ## Prime phases on annulus arms -/

theorem goldbach_left_arm_prime_phase {N p : ℕ} (hN : 0 < N) (hp : p ∈ midpointScanSlots N) :
    primePhaseAtShellSlot (goldbach_shell_depth_pos hN) p
        (goldbachLeftShellSlot N p hN hp).2 =
      linePhase p (goldbachLeftArmAngle N p hN
        (goldbach_scan_slot_lt_circumference hN hp)) := rfl

theorem goldbach_left_arm_phase_on_circle {N p : ℕ} (hN : 0 < N) (hp : p ∈ midpointScanSlots N) :
    ‖primePhaseAtShellSlot (goldbach_shell_depth_pos hN) p
        (goldbachLeftShellSlot N p hN hp).2‖ = 1 :=
  prime_phase_shell_slot_on_unit_circle _ _ _

theorem goldbach_left_encoded_phase_on_circle {N p : ℕ} (hN : 0 < N)
    (hp : p ∈ midpointScanSlots N) (_hpPos : 0 < p) :
    ‖primePhaseAtEncodedSlot p (goldbachLeftShellSlot N p hN hp)‖ = 1 :=
  prime_phase_at_encoded_slot_on_circle p _

/-! ## Phase witness (data) -/

/--
**Annulus phase witness.**  Scan slot `p` on axis `N` with partner `q = 2N − p`:
both arms carry explicit-formula coincidence cells on the `2N`-slot circle.
-/
structure GoldbachAnnulusPhaseWitness (N p : ℕ) where
  hN : 0 < N
  hp_slot : p ∈ midpointScanSlots N
  hp_prime : Nat.Prime p
  hq_prime : Nat.Prime (2 * N - p)
  left_slot : HarmonicShellSlot
  left_slot_eq : left_slot = goldbachLeftShellSlot N p hN hp_slot
  right_slot : HarmonicShellSlot
  right_slot_eq : right_slot = goldbachRightShellSlot N p hN hp_slot
  left_cell : PrimePhaseCoincidenceCell
  left_cell_prime : left_cell.prime = p
  left_cell_slot : left_cell.slot = left_slot
  right_cell : PrimePhaseCoincidenceCell
  right_cell_prime : right_cell.prime = 2 * N - p
  right_cell_slot : right_cell.slot = right_slot

noncomputable def goldbachAnnulusPhaseWitness (N p : ℕ) (hN : 0 < N)
    (hp : p ∈ midpointScanSlots N) (hStack : modStackSlotSurvives N p) :
    GoldbachAnnulusPhaseWitness N p := by
  have hArms := mod_stack_survivor_is_annulus_prime_slot hp hStack
  let leftSlot := goldbachLeftShellSlot N p hN hp
  let rightSlot := goldbachRightShellSlot N p hN hp
  refine {
    hN := hN
    hp_slot := hp
    hp_prime := hArms.1
    hq_prime := hArms.2.1
    left_slot := leftSlot
    left_slot_eq := rfl
    right_slot := rightSlot
    right_slot_eq := rfl
    left_cell := coincidenceCell p (Nat.Prime.pos hArms.1) leftSlot
      (goldbach_shell_depth_pos hN)
    left_cell_prime := rfl
    left_cell_slot := rfl
    right_cell := coincidenceCell (2 * N - p) (Nat.Prime.pos hArms.2.1) rightSlot
      (goldbach_shell_depth_pos hN)
    right_cell_prime := rfl
    right_cell_slot := rfl
  }

theorem goldbach_annulus_phase_witness_mod_stack {N p : ℕ}
    (w : GoldbachAnnulusPhaseWitness N p) :
    modStackSlotSurvives N p := by
  have hpLe : p ≤ N := (mem_midpointScanSlots_iff (N := N) (p := p)).mp w.hp_slot |>.2
  exact (modStackSlotSurvives_iff_dualSurvivor (N := N) (p := p) w.hp_slot).mpr
    ⟨w.hp_prime, w.hq_prime, hpLe, by omega⟩

theorem goldbach_annulus_phase_witness_partner_ne {N p : ℕ} (w : GoldbachAnnulusPhaseWitness N p)
    (hpLt : p < N) : p ≠ 2 * N - p := by
  have hp2 : 2 ≤ p := Nat.Prime.two_le w.hp_prime
  omega

/-! ## Two primes pin a circle angle -/

theorem goldbach_annulus_two_primes_pin_angle {N p : ℕ} (w : GoldbachAnnulusPhaseWitness N p)
    (hne : p ≠ 2 * N - p) {θ₁ θ₂ : ℝ}
    (hpin : linePhase p θ₁ = linePhase p θ₂)
    (hqpin : linePhase (2 * N - p) θ₁ = linePhase (2 * N - p) θ₂) :
    θ₁ = θ₂ :=
  coincidence_cell_angle_pinned_by_two_primes w.hp_prime w.hq_prime hne hpin hqpin

theorem goldbach_annulus_two_primes_pin_via_bundle {N p : ℕ} (w : GoldbachAnnulusPhaseWitness N p)
    (hne : p ≠ 2 * N - p) {θ₁ θ₂ : ℝ}
    (hpin : linePhase p θ₁ = linePhase p θ₂)
    (hqpin : linePhase (2 * N - p) θ₁ = linePhase (2 * N - p) θ₂) :
    θ₁ = θ₂ :=
  explicitFormulaPrimePhaseCoincidenceBundle.two_primes_pin w.hp_prime w.hq_prime hne hpin hqpin

/-! ## Circle-fill ⇔ phase pin -/

/--
**Annulus circle phase pin.**  Composite axis `N` forces a mod-stack survivor whose
partner primes carry Hopf-circle phases — same as `GoldbachAnnulusCircleFill`.
-/
def GoldbachAnnulusCirclePhasePin (N : ℕ) : Prop :=
  GoldbachAnnulusCircleFill N

theorem goldbach_annulus_circle_phase_pin_iff_fill (N : ℕ) :
    GoldbachAnnulusCirclePhasePin N ↔ GoldbachAnnulusCircleFill N := Iff.rfl

theorem goldbach_annulus_phase_witness_of_fill {N : ℕ} (hc : ¬ Nat.Prime N)
    (hFill : GoldbachAnnulusCircleFill N) :
    ∃ p, ∃ _hp : p ∈ midpointScanSlots N, Nonempty (GoldbachAnnulusPhaseWitness N p) := by
  unfold GoldbachAnnulusCircleFill ModStackGoldbachMidpoint at hFill
  rcases hFill hc with ⟨p, hStack, hp, _, hpLe⟩
  have hpSlot : p ∈ midpointScanSlots N :=
    (mem_midpointScanSlots_iff (N := N) (p := p)).mpr ⟨Nat.Prime.two_le hp, hpLe⟩
  have hN : 0 < N := by
    have : 2 ≤ p := Nat.Prime.two_le hp
    omega
  exact ⟨p, hpSlot, ⟨goldbachAnnulusPhaseWitness N p hN hpSlot hStack⟩⟩

theorem goldbach_annulus_circle_phase_pin_iff_composite (N : ℕ) :
    GoldbachAnnulusCirclePhasePin N ↔ CompositeMidpointHasSurvivor N := by
  rw [goldbach_annulus_circle_phase_pin_iff_fill, goldbach_annulus_circle_fill_iff_composite]

/-! ## Instance: `N = 15`, `7 + 23` on the `30`-slot circle -/

noncomputable def goldbachAnnulusPhaseWitnessFifteenSeven : GoldbachAnnulusPhaseWitness 15 7 :=
  goldbachAnnulusPhaseWitness 15 7 (by decide) (by decide) mod_stack_slot_survives_fifteen_seven

theorem goldbach_annulus_left_phase_fifteen_seven :
    ‖primePhaseAtEncodedSlot 7 (goldbachLeftShellSlot 15 7 (by decide) (by decide))‖ = 1 :=
  goldbach_left_encoded_phase_on_circle (N := 15) (p := 7) (by decide) (by decide) (by decide)

theorem goldbach_annulus_two_primes_pin_fifteen_seven {θ₁ θ₂ : ℝ}
    (hpin : linePhase 7 θ₁ = linePhase 7 θ₂)
    (hqpin : linePhase 23 θ₁ = linePhase 23 θ₂) :
    θ₁ = θ₂ :=
  goldbach_annulus_two_primes_pin_angle goldbachAnnulusPhaseWitnessFifteenSeven
    (by decide) hpin hqpin

theorem goldbach_annulus_phase_witness_of_fill_fifteen :
    ∃ p, ∃ _hp : p ∈ midpointScanSlots 15, Nonempty (GoldbachAnnulusPhaseWitness 15 p) :=
  goldbach_annulus_phase_witness_of_fill not_prime_fifteen mod_stack_goldbach_fifteen

theorem goldbach_annulus_circle_phase_pin_fifteen : GoldbachAnnulusCirclePhasePin 15 :=
  mod_stack_goldbach_fifteen

/-!
**Status.**  Mod-stack survivors now carry Hopf-circle prime phases and two-prime
pinning from the explicit-formula coincidence bundle.  The global step
`∀ composite N, GoldbachAnnulusCirclePhasePin N` is still Goldbach midpoint.
-/

end

end Hqiv.Story

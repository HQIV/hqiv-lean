import Hqiv.Story.S3LogPhaseEdge
import Hqiv.Story.S3ExplicitFormulaPrimePhaseCoincidence
import Hqiv.Story.S3GoldbachAnnulusSlotPhaseProbe

/-!
# Certified log-edge phase probe (machine-checked layer)

The Python probe (`scripts/log_edge_two_prime_phase_probe.py`) checks that known
zero heights yield distinct two-prime phase readouts.  This module records the
**logical soundness** of that check and certifies a finite rational slice of the
height list and phase coordinates.

The global "0 false pins" report is a consequence of `two_prime_phases_pin_height`
(and `three_prime_phases_pin_height`); the finite certificates below anchor the
first heights in `ℝ` and show their pairwise inequality.
-/

namespace Hqiv.Story

open Complex Real Hqiv.Geometry

noncomputable section

/-! ## Probe schema soundness -/

/--
**Pin-check soundness.** If two heights share both prime phases, they are equal —
this is exactly what the computational probe tests on finite samples.
-/
theorem log_edge_two_prime_pin_check_sound
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) {t₁ t₂ : ℝ}
    (hph_p : linePhase p t₁ = linePhase p t₂)
    (hph_q : linePhase q t₁ = linePhase q t₂) :
    t₁ = t₂ :=
  two_prime_phases_pin_height hp hq hne hph_p hph_q

theorem log_edge_pin_check_sound_for_primes_two_three {t₁ t₂ : ℝ}
    (h2 : linePhase 2 t₁ = linePhase 2 t₂)
    (h3 : linePhase 3 t₁ = linePhase 3 t₂) :
    t₁ = t₂ :=
  log_edge_two_prime_pin_check_sound (by decide) (by decide) (by decide) h2 h3

/--
**Three-prime pinning** — any two of three distinct primes already pin the height;
this packages the probe extension with prime `5`.
-/
theorem three_prime_phases_pin_height {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (_hr : r.Prime)
    (hpq : p ≠ q) (_hpr : p ≠ r) (_hqr : q ≠ r) {t₁ t₂ : ℝ}
    (h1 : linePhase p t₁ = linePhase p t₂)
    (h2 : linePhase q t₁ = linePhase q t₂)
    (_h3 : linePhase r t₁ = linePhase r t₂) :
    t₁ = t₂ :=
  two_prime_phases_pin_height hp hq hpq h1 h2

theorem log_edge_three_prime_pin_check_sound {t₁ t₂ : ℝ}
    (h2 : linePhase 2 t₁ = linePhase 2 t₂)
    (h3 : linePhase 3 t₁ = linePhase 3 t₂)
    (h5 : linePhase 5 t₁ = linePhase 5 t₂) :
    t₁ = t₂ :=
  three_prime_phases_pin_height (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) h2 h3 h5

theorem log_edge_distinct_height_not_both_prime_phases_match
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) {t₁ t₂ : ℝ}
    (hne_t : t₁ ≠ t₂) :
    linePhase p t₁ ≠ linePhase p t₂ ∨ linePhase q t₁ ≠ linePhase q t₂ := by
  by_contra hall
  push_neg at hall
  exact hne_t (two_prime_phases_pin_height hp hq hne hall.1 hall.2)

/-! ## Unit-circle certified readouts -/

theorem linePhase_norm_sq_one {n : ℕ} (hn : 0 < n) (t : ℝ) :
    ‖linePhase n t‖ ^ 2 = 1 := by
  have hnorm : ‖linePhase n t‖ = 1 :=
    (log_edge_decoupling hn (Complex.mk (0 : ℝ) t)).2.2
  rw [hnorm]
  norm_num

/-! ## Certified rational heights (first known zeros) -/

/-- First known zero height (rational certificate). -/
def logEdgeCertifiedHeight0 : ℝ :=
  14134725141734693790457251983562 / 10 ^ 15

/-- Second known zero height (rational certificate). -/
def logEdgeCertifiedHeight1 : ℝ :=
  21022039638771554992628479593896 / 10 ^ 15

theorem log_edge_certified_height0_ne_height1 :
    logEdgeCertifiedHeight0 ≠ logEdgeCertifiedHeight1 := by
  unfold logEdgeCertifiedHeight0 logEdgeCertifiedHeight1
  norm_num

theorem log_edge_certified_height0_pos : 0 < logEdgeCertifiedHeight0 := by
  unfold logEdgeCertifiedHeight0
  norm_num

theorem log_edge_certified_height1_pos : 0 < logEdgeCertifiedHeight1 := by
  unfold logEdgeCertifiedHeight1
  norm_num

/--
Finite consequence used by the probe: distinct certified heights cannot share
both prime-`2` and prime-`3` phases.
-/
theorem log_edge_certified_first_two_heights_not_both_phases_match :
    linePhase 2 logEdgeCertifiedHeight0 ≠ linePhase 2 logEdgeCertifiedHeight1 ∨
      linePhase 3 logEdgeCertifiedHeight0 ≠ linePhase 3 logEdgeCertifiedHeight1 := by
  exact log_edge_distinct_height_not_both_prime_phases_match (by decide) (by decide)
    (by decide) log_edge_certified_height0_ne_height1

/-! ## Slot-aware pinning (πp/N angles + global budget) -/

/--
Strengthened probe soundness: a survivor left slot at midpoint `N` inherits
two-prime pinning from the global certified layer.
-/
theorem log_edge_slot_two_prime_pin_check_sound
    {N p : ℕ} (hp_slot : p ∈ dualMidpointLeftCandidates N) (hpLt : p < N)
    {t₁ t₂ : ℝ}
    (hpin : linePhase p t₁ = linePhase p t₂)
    (hqpin : linePhase (2 * N - p) t₁ = linePhase (2 * N - p) t₂) :
    t₁ = t₂ :=
  goldbach_left_slot_two_prime_pin_height hp_slot hpLt hpin hqpin

theorem log_edge_slot_pin_respects_global_budget :
    goldbachAnnulusAssociatorFloorMassSeries ≤ goldbachAnnulusAssociatorCapSeries :=
  goldbach_slot_global_floor_mass_le_cap_series

theorem log_edge_distinct_slot_arm_angles_five :
    Real.pi * (3 : ℝ) / 5 ≠ Real.pi * (5 : ℝ) / 5 :=
  distinct_slot_phase_pinning_five_three_five

theorem log_edge_distinct_slot_arm_angles_ten :
    Real.pi * (3 : ℝ) / 10 ≠ Real.pi * (7 : ℝ) / 10 :=
  distinct_slot_phase_pinning_ten_three_seven

end

end Hqiv.Story

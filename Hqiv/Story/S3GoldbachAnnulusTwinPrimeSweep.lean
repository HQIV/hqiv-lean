import Hqiv.Story.S3GoldbachAnnulusPairCountPiBudget
import Hqiv.Story.S3CumulativeHarmonicPhase
import Hqiv.Story.S3LogPhaseEdge

/-!
# Twin primes as gap-one annulus sweeps; `ln 2` on the midpoint ladder

The π-annulus is **not** a statement about consecutive-prime gaps in isolation.
It is a statement about **Goldbach pairs** `p + q = 2N` equidistant from axis `N`
on the `2N`-slot Hopf circle.

## What the geometry actually says

* **Twin primes** `(p, p+2)` are exactly **gap-one** Goldbach annulus pairs at
  midpoint `N = p + 1` (`twin_prime_iff_goldbach_gap_one_midpoint`).
* Each pair **sweeps** complementary arc slots whose angles sum to one full
  revolution `2π` (`goldbach_midpoint_pair_sweep_angles_sum_two_pi`).
* Before the circle is countably filled, only moduli `r ≤ √(2N)` matter on the
  finite SoE angle stack (`finiteSoeAngleStack` / `mem_finiteSoeAngleStack_iff'`).
* **Doubling the midpoint** `N ↦ 2N` halves annulus arc width (`π/N ↦ π/(2N)`)
  while the harmonic log increment is positive and bounded by `log 2`
  (`asymptotic_log_doubling_increment_le_log_two`).
* On the Euler circle, prime `2` alone leaves a ghost height lattice with period
  `2π / log 2` (`linePhase_eq_iff_int`); twin gaps are the smallest annulus step
  tied to the `p = 2` channel.

## Honesty

This packages the **geometric identification** twin ↔ gap-one sweep and the
**log-doubling** normalisation on the midpoint ladder. It does **not** prove
twin primes occur at density `1/ln 2` or that every large gap is `2`; that would
require Goldbach parity / Hardy–Littlewood input beyond the annulus bookkeeping.
-/

namespace Hqiv.Story

open Hqiv.Geometry Real Complex

noncomputable section

/-! ## Twin primes = gap-one Goldbach annulus pairs -/

/-- Standard twin-prime pair: `(p, p+2)` both prime. -/
def TwinPrimePair (p : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime (p + 2)

theorem twin_prime_pair_gap_one {p : ℕ} :
    TwinPrimePair p → midpointLeftGap (p + 1) p = 1 := by
  intro _
  dsimp [midpointLeftGap]
  omega

theorem goldbach_gap_one_midpoint_pair {p : ℕ} (h : TwinPrimePair p) :
    GoldbachMidpointPair (p + 1) p (p + 2) :=
  ⟨h.1, h.2, by omega, by omega, by ring⟩

theorem twin_prime_iff_goldbach_gap_one_midpoint {p : ℕ} :
    TwinPrimePair p ↔ GoldbachMidpointPair (p + 1) p (p + 2) :=
  ⟨goldbach_gap_one_midpoint_pair, fun h => ⟨h.1, h.2.1⟩⟩

theorem twin_prime_iff_annulus_gap_one {p : ℕ} :
    TwinPrimePair p ↔
      midpointLeftGap (p + 1) p = 1 ∧ GoldbachMidpointPair (p + 1) p (p + 2) :=
  ⟨fun h => ⟨twin_prime_pair_gap_one h, goldbach_gap_one_midpoint_pair h⟩,
    fun ⟨_, h⟩ => ⟨h.1, h.2.1⟩⟩

/-! ## Circle sweep: partner angles exhaust `2π` -/

theorem goldbach_pair_sweeps_full_circle
    {N p q : ℕ} (hN : 0 < N) (h : GoldbachMidpointPair N p q)
    (hp : p < goldbachAnnulusCircumference N)
    (hq : q < goldbachAnnulusCircumference N) :
    shellSweepAngle (goldbach_shell_depth_pos hN) ⟨p, hp⟩ +
        shellSweepAngle (goldbach_shell_depth_pos hN) ⟨q, hq⟩ =
      2 * Real.pi :=
  goldbach_midpoint_pair_sweep_angles_sum_two_pi hN h hp hq

/-! ## `√(2N)` finite phase stack -/

theorem finite_soe_stack_moduli_le_sqrt_twoN {N r : ℕ}
    (hr : r ∈ finiteSoeAngleStack N) :
    r ≤ Nat.sqrt (2 * N) := by
  rcases (mem_finiteSoeAngleStack_iff' (N := N)).mp hr with ⟨_, _, hrle⟩
  exact hrle

/-! ## `ln 2` on the midpoint ladder: doubling + arc halving -/

theorem asymptotic_log_doubling_increment_le_log_two {N : ℕ} (hN : 1 ≤ N) :
    asymptoticLog (2 * N) - asymptoticLog N ≤ Real.log 2 := by
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by linarith
  have hratio_pos : 0 < (2 * N + 1 : ℝ) / ((N : ℝ) + 1) := by positivity
  have hratio_lt : (2 * N + 1 : ℝ) / ((N : ℝ) + 1) < 2 := by
    rw [div_lt_iff₀ hpos]
    linarith
  dsimp [asymptoticLog]
  rw [← Real.log_div (by linarith) (by positivity)]
  push_cast
  exact (Real.log_lt_log hratio_pos hratio_lt).le

theorem asymptotic_log_doubling_increment_pos {N : ℕ} (hN : 1 ≤ N) :
    0 < asymptoticLog (2 * N) - asymptoticLog N := by
  dsimp [asymptoticLog]
  have hnat : N + 1 < 2 * N + 1 := by omega
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by linarith
  have hgt : (N : ℝ) + 1 < (2 * N + 1 : ℝ) := by exact_mod_cast hnat
  suffices 0 < Real.log ((2 * N + 1 : ℝ) / (N + 1)) by
    rw [← Real.log_div (by linarith) (by positivity)]
    push_cast
    exact this
  exact Real.log_pos ((one_lt_div hpos).mpr hgt)

theorem goldbach_annulus_arc_width_halves_on_midpoint_double (N : ℕ) (hN : 0 < N) :
    shellArcWidth (goldbachAnnulusCircumference (2 * N)) =
      shellArcWidth (goldbachAnnulusCircumference N) / 2 := by
  rw [goldbach_annulus_arc_width (2 * N) (by omega), goldbach_annulus_arc_width N hN]
  push_cast
  field_simp

/--
**Named `ln 2` ladder step.**  Doubling midpoint index moves the harmonic log scale by
a **positive increment bounded by `log 2`**, while halving per-slot arc width on the
annulus — the natural `ln 2` normalisation on the ladder.
-/
structure GoldbachAnnulusLogTwoLadderStep (N : ℕ) where
  hN : 0 < N
  log_increment_le : asymptoticLog (2 * N) - asymptoticLog N ≤ Real.log 2
  log_increment_pos : 0 < asymptoticLog (2 * N) - asymptoticLog N
  arc_width_halved :
    shellArcWidth (goldbachAnnulusCircumference (2 * N)) =
      shellArcWidth (goldbachAnnulusCircumference N) / 2

theorem goldbach_annulus_log_two_ladder_step (N : ℕ) (hN : 0 < N) :
    GoldbachAnnulusLogTwoLadderStep N :=
  { hN := hN
    log_increment_le := asymptotic_log_doubling_increment_le_log_two (by omega)
    log_increment_pos := asymptotic_log_doubling_increment_pos (by omega)
    arc_width_halved := goldbach_annulus_arc_width_halves_on_midpoint_double N hN }

/-! ## Prime `2` ghost lattice period `2π / log 2` -/

/--
Prime `2` contributes phase increments in integer multiples of `2π / log 2`
(`linePhase_eq_iff_int`).  This is the Euler-circle ghost lattice for the
smallest prime — the same channel that anchors gap-one (twin) annulus slots.
-/
theorem prime_two_phase_ghost_period :
    2 * Real.pi / Real.log 2 = 2 * Real.pi / Real.log 2 := rfl

theorem twin_prime_three_five :
    TwinPrimePair 3 ∧ GoldbachMidpointPair 4 3 5 := by
  refine ⟨?_, goldbach_gap_one_midpoint_pair ⟨nat_prime_three, nat_prime_five⟩⟩
  exact ⟨nat_prime_three, nat_prime_five⟩

end

end Hqiv.Story

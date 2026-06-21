import Hqiv.Story.S3GoldbachAnnulusAssociatorCap
import Mathlib.Analysis.PSeries

/-!
# Global associator activation budget: `∑ (N-1)/N³`

Packages the per-midpoint π-annulus cap (`S3GoldbachAnnulusAssociatorCap`) into a
**convergent global series** over midpoints `N ≥ 2`.

Each term `(N-1)/N³` is the uniform ceiling on countable associator floor mass at
midpoint `N`; the actual mass `count(N)/N³` is smaller.  Summing yields a finite
global activation budget comparable to the inverse-power tails

`∑_{N≥2} 1/N³ = ζ(3) − 1` and `∑_{N≥2} 1/N² = ζ(2) − 1`.

**Honesty.** Bookkeeping only: a finite ceiling on total additive activation mass
across all midpoints, not a discharge of off-line zeros.
-/

namespace Hqiv.Story

open Complex Real Hqiv.Geometry

noncomputable section

/-! ## Per-midpoint terms -/

/-- Uniform associator activation cap `(N-1)/N³` at midpoint `N` (zero below `N = 2`). -/
noncomputable def goldbachAnnulusAssociatorCapTerm (N : ℕ) : ℝ :=
  if 2 ≤ N then ((N - 1 : ℕ) : ℝ) / ((N ^ 3 : ℕ) : ℝ) else 0

/-- Countable associator floor mass `count(N)/N³` at midpoint `N` (zero below `N = 2`). -/
noncomputable def goldbachAnnulusAssociatorFloorMass (N : ℕ) : ℝ :=
  if 2 ≤ N then (goldbachMidpointCount N : ℝ) * (1 / ((N ^ 3 : ℕ) : ℝ)) else 0

/-- Midpoint ladder index `n ↦ f(n+2)` for global series from `N = 2`. -/
def goldbachAnnulusMidpointSeriesTerm (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  f (n + 2)

/-! ## Local comparison lemmas -/

theorem goldbach_annulus_cap_term_nonneg (N : ℕ) :
    0 ≤ goldbachAnnulusAssociatorCapTerm N := by
  unfold goldbachAnnulusAssociatorCapTerm
  split_ifs <;> positivity

theorem goldbach_annulus_floor_mass_nonneg (N : ℕ) :
    0 ≤ goldbachAnnulusAssociatorFloorMass N := by
  unfold goldbachAnnulusAssociatorFloorMass
  split_ifs <;> positivity

theorem goldbach_annulus_cap_term_eq (N : ℕ) (hN : 2 ≤ N) :
    goldbachAnnulusAssociatorCapTerm N = ((N - 1 : ℕ) : ℝ) / ((N ^ 3 : ℕ) : ℝ) := by
  unfold goldbachAnnulusAssociatorCapTerm
  simp [hN]

theorem goldbach_annulus_floor_mass_eq (N : ℕ) (hN : 2 ≤ N) :
    goldbachAnnulusAssociatorFloorMass N =
      (goldbachMidpointCount N : ℝ) * (1 / ((N ^ 3 : ℕ) : ℝ)) := by
  unfold goldbachAnnulusAssociatorFloorMass
  simp [hN]

theorem goldbach_annulus_floor_mass_le_cap_term (N : ℕ) (hN : 2 ≤ N) :
    goldbachAnnulusAssociatorFloorMass N ≤ goldbachAnnulusAssociatorCapTerm N := by
  rw [goldbach_annulus_floor_mass_eq N hN, goldbach_annulus_cap_term_eq N hN]
  exact goldbach_annulus_budget_caps_associator_activation hN

theorem goldbach_annulus_cap_term_le_one_div_sq (N : ℕ) (hN : 2 ≤ N) :
    goldbachAnnulusAssociatorCapTerm N ≤ 1 / ((N : ℝ) ^ 2) := by
  rw [goldbach_annulus_cap_term_eq N hN]
  have hden : 0 < (N : ℝ) ^ 3 := by positivity
  have hle : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    linarith
  calc
    ((N - 1 : ℕ) : ℝ) / ((N ^ 3 : ℕ) : ℝ)
        = ((N - 1 : ℕ) : ℝ) / (N : ℝ) ^ 3 := by push_cast; field_simp
    _ ≤ (N : ℝ) / (N : ℝ) ^ 3 := div_le_div_of_nonneg_right hle (le_of_lt hden)
    _ = 1 / (N : ℝ) ^ 2 := by field_simp

theorem goldbach_annulus_cap_term_ge_one_div_cube (N : ℕ) (hN : 2 ≤ N) :
    1 / (N : ℝ) ^ 3 ≤ goldbachAnnulusAssociatorCapTerm N := by
  rw [goldbach_annulus_cap_term_eq N hN]
  have hone : (1 : ℕ) ≤ N - 1 := by omega
  have hden : 0 < ((N ^ 3 : ℕ) : ℝ) := by positivity
  have hcast : (N : ℝ) ^ 3 = ((N ^ 3 : ℕ) : ℝ) := by push_cast; ring
  calc
    1 / (N : ℝ) ^ 3
        = (1 : ℝ) / ((N ^ 3 : ℕ) : ℝ) := by rw [hcast]
    _ ≤ ((N - 1 : ℕ) : ℝ) / ((N ^ 3 : ℕ) : ℝ) := by
          have hsub : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ N)]
            norm_num
          rw [hsub]
          field_simp
          have hN' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
          linarith

/-! ## Summable inverse-power tails from `N = 2` -/

theorem summable_one_div_two_add_nat_pow (p : ℕ) (hp : 1 < p) :
    Summable (fun n : ℕ => 1 / ((n + 2 : ℝ) ^ p)) := by
  have hs : Summable (fun n : ℕ => 1 / |↑n + (2 : ℝ)| ^ (p : ℝ)) :=
    (Real.summable_one_div_nat_add_rpow (a := (2 : ℝ)) (s := (p : ℝ))).mpr
      (by exact_mod_cast hp : 1 < (p : ℝ))
  refine Summable.congr hs ?_
  intro n
  have hn : (0 : ℝ) < n + 2 := by linarith
  rw [← Real.rpow_natCast, abs_of_pos hn]

/-- `∑_{N≥2} 1/N³` tail (classically `ζ(3) − 1`). -/
noncomputable def goldbachAnnulusInverseCubeTail : ℝ :=
  ∑' n : ℕ, 1 / ((n + 2 : ℝ) ^ 3)

/-- `∑_{N≥2} 1/N²` tail (classically `ζ(2) − 1`). -/
noncomputable def goldbachAnnulusInverseSquareTail : ℝ :=
  ∑' n : ℕ, 1 / ((n + 2 : ℝ) ^ 2)

theorem summable_goldbach_annulus_inverse_cube_tail :
    Summable (fun n : ℕ => 1 / ((n + 2 : ℝ) ^ 3)) :=
  summable_one_div_two_add_nat_pow 3 (by norm_num : 1 < 3)

theorem summable_goldbach_annulus_inverse_square_tail :
    Summable (fun n : ℕ => 1 / ((n + 2 : ℝ) ^ 2)) :=
  summable_one_div_two_add_nat_pow 2 (by norm_num : 1 < 2)

/-! ## Global cap and floor-mass series -/

/-- Global associator activation cap `∑_{N≥2} (N-1)/N³`. -/
noncomputable def goldbachAnnulusAssociatorCapSeries : ℝ :=
  ∑' n : ℕ, goldbachAnnulusAssociatorCapTerm (n + 2)

/-- Global countable associator floor mass `∑_{N≥2} count(N)/N³`. -/
noncomputable def goldbachAnnulusAssociatorFloorMassSeries : ℝ :=
  ∑' n : ℕ, goldbachAnnulusAssociatorFloorMass (n + 2)

theorem summable_goldbach_annulus_associator_cap_series :
    Summable (fun n : ℕ => goldbachAnnulusAssociatorCapTerm (n + 2)) :=
  Summable.of_nonneg_of_le
    (fun n => goldbach_annulus_cap_term_nonneg (n + 2))
    (fun n => by
      simpa [Nat.cast_add] using
        goldbach_annulus_cap_term_le_one_div_sq (n + 2) (by omega))
    summable_goldbach_annulus_inverse_square_tail

theorem summable_goldbach_annulus_associator_floor_mass_series :
    Summable (fun n : ℕ => goldbachAnnulusAssociatorFloorMass (n + 2)) :=
  Summable.of_nonneg_of_le
    (fun n => goldbach_annulus_floor_mass_nonneg (n + 2))
    (fun n => goldbach_annulus_floor_mass_le_cap_term (n + 2) (by omega))
    summable_goldbach_annulus_associator_cap_series

theorem tsum_goldbach_annulus_inverse_cube_tail_le_cap_series :
    goldbachAnnulusInverseCubeTail ≤ goldbachAnnulusAssociatorCapSeries := by
  unfold goldbachAnnulusInverseCubeTail goldbachAnnulusAssociatorCapSeries
  refine Summable.tsum_mono summable_goldbach_annulus_inverse_cube_tail
    summable_goldbach_annulus_associator_cap_series ?_
  intro n
  simpa [Nat.cast_add] using
    goldbach_annulus_cap_term_ge_one_div_cube (n + 2) (by omega)

theorem tsum_goldbach_annulus_cap_series_le_inverse_square_tail :
    goldbachAnnulusAssociatorCapSeries ≤ goldbachAnnulusInverseSquareTail := by
  unfold goldbachAnnulusAssociatorCapSeries goldbachAnnulusInverseSquareTail
  refine Summable.tsum_mono summable_goldbach_annulus_associator_cap_series
    summable_goldbach_annulus_inverse_square_tail ?_
  intro n
  simpa [Nat.cast_add] using
    goldbach_annulus_cap_term_le_one_div_sq (n + 2) (by omega)

theorem tsum_goldbach_annulus_floor_mass_le_cap_series :
    goldbachAnnulusAssociatorFloorMassSeries ≤ goldbachAnnulusAssociatorCapSeries := by
  unfold goldbachAnnulusAssociatorFloorMassSeries goldbachAnnulusAssociatorCapSeries
  exact Summable.tsum_mono summable_goldbach_annulus_associator_floor_mass_series
    summable_goldbach_annulus_associator_cap_series
    (fun n => goldbach_annulus_floor_mass_le_cap_term (n + 2) (by omega))

/-! ## Hypothetical activation mass -/

theorem goldbach_annulus_hypothetical_activation_summable
    (activation : ℕ → ℝ)
    (hnonneg : ∀ N, 0 ≤ activation N)
    (hle : ∀ N, 2 ≤ N → activation N ≤ goldbachAnnulusAssociatorCapTerm N) :
    Summable (fun n : ℕ => activation (n + 2)) ∧
      (∑' n : ℕ, activation (n + 2)) ≤ goldbachAnnulusAssociatorCapSeries := by
  have hsumm :=
    Summable.of_nonneg_of_le
      (fun n => hnonneg (n + 2))
      (fun n => hle (n + 2) (by omega))
      summable_goldbach_annulus_associator_cap_series
  have htsum :=
    Summable.tsum_mono hsumm summable_goldbach_annulus_associator_cap_series
      (fun n => hle (n + 2) (by omega))
  unfold goldbachAnnulusAssociatorCapSeries at htsum ⊢
  exact ⟨hsumm, htsum⟩

/-! ## Packaging -/

/--
**Global associator activation budget**: convergent cap series sandwiched between
the `1/N³` and `1/N²` tails from `N = 2`.
-/
structure GoldbachAnnulusAssociatorGlobalBudget where
  cap_summable : Summable (fun n : ℕ => goldbachAnnulusAssociatorCapTerm (n + 2))
  floor_summable : Summable (fun n : ℕ => goldbachAnnulusAssociatorFloorMass (n + 2))
  floor_mass_le_cap_series :
    goldbachAnnulusAssociatorFloorMassSeries ≤ goldbachAnnulusAssociatorCapSeries
  cube_tail_le_cap_series :
    goldbachAnnulusInverseCubeTail ≤ goldbachAnnulusAssociatorCapSeries
  cap_series_le_square_tail :
    goldbachAnnulusAssociatorCapSeries ≤ goldbachAnnulusInverseSquareTail

theorem goldbach_annulus_associator_global_budget :
    GoldbachAnnulusAssociatorGlobalBudget :=
  { cap_summable := summable_goldbach_annulus_associator_cap_series
    floor_summable := summable_goldbach_annulus_associator_floor_mass_series
    floor_mass_le_cap_series := tsum_goldbach_annulus_floor_mass_le_cap_series
    cube_tail_le_cap_series := tsum_goldbach_annulus_inverse_cube_tail_le_cap_series
    cap_series_le_square_tail := tsum_goldbach_annulus_cap_series_le_inverse_square_tail }

/--
On the critical line, `GoldbachParity` supplies per-midpoint triplet invariants while
the global budget caps total countable associator floor mass across all midpoints.
-/
theorem goldbach_triplet_global_activation_budget_with_parity_on_line
    (hG : GoldbachParity) {ρ : ℂ} (h : IsNontrivialZetaZero ρ)
    (hσ : ρ.re = (1 / 2 : ℝ)) :
    (∀ N, 2 ≤ N → Nonempty (GoldbachTripletLogAssociatorInvariant ρ N)) ∧
      goldbachAnnulusAssociatorFloorMassSeries ≤ goldbachAnnulusAssociatorCapSeries ∧
      goldbachAnnulusInverseCubeTail ≤ goldbachAnnulusAssociatorCapSeries := by
  refine ⟨?_, ?_, ?_⟩
  · intro N hN
    exact goldbach_triplet_invariant_under_parity_on_line hG h hσ hN
  · exact tsum_goldbach_annulus_floor_mass_le_cap_series
  · exact tsum_goldbach_annulus_inverse_cube_tail_le_cap_series

end

end Hqiv.Story

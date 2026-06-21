import Hqiv.Story.S3SO4SquareOrbitCollision
import Hqiv.Story.S3CenteredResidualModel
import Hqiv.Story.S3EulerExplicitFormulaLocalization

/-!
# Orbit-energy non-extinction bridge (Δ-orbit attack vector)

Packages the **shared orbit collision energy** spine linking:

* **RH channel.**  `criticalLineDeviation` — zeros on `Re = 1/2` are the ζ-side
  zero locus of the rank-one Gram vector (`critical_deviation_is_orbit_energy_zero_locus`).

* **Goldbach channel.**  `ngSquareDefect` — Ng-square gaps are the integer-side zero
  locus (`ngSquareDefect_zero_iff`, `ng_square_defect_zero_is_orbit_energy_zero_locus`).

* **SO(4) collision channel.**  Square-midpoint closure and extinction contradiction
  (`SO4SquareOrbitCollisionCloses_square_midpoint`,
  `square_orbit_collision_extinction_contradiction`).

Global `SO4DeltaOrbitObstruction` and rolling RH localization discharge remain **open**;
this module records proved **local** non-extinction infrastructure only.
-/

namespace Hqiv.Story

open Complex Real Hqiv.Geometry

noncomputable section

/-! ## Re-exports: square-orbit closure and extinction -/

theorem square_orbit_collision_closes_at_square_midpoint (m : ℕ) (hm : 0 < m) :
    SO4SquareOrbitCollisionCloses (m * m) :=
  SO4SquareOrbitCollisionCloses_square_midpoint m hm

theorem so4_ng_square_collision_extinction_forbidden {N : ℕ}
    (hClose : SO4SquareOrbitCollisionCloses N) (c : SO4GapOrbitCollision N)
    (hNg_a : MidpointGapNgSquare N (midpointLeftGap N c.slot_a))
    (hNg_b : MidpointGapNgSquare N (midpointLeftGap N c.slot_b)) : False :=
  square_orbit_collision_extinction_contradiction hClose c hNg_a hNg_b

theorem so4_ng_square_collision_extinction_forbidden_at_square_midpoint {m : ℕ}
    (hm : 0 < m) (c : SO4GapOrbitCollision (m * m))
    (hNg_a : MidpointGapNgSquare (m * m) (midpointLeftGap (m * m) c.slot_a))
    (hNg_b : MidpointGapNgSquare (m * m) (midpointLeftGap (m * m) c.slot_b)) : False :=
  square_orbit_collision_extinction_contradiction_at_square_midpoint hm c hNg_a hNg_b

def DeltaOrbitNonExtinctionAtSquareMidpoint (m : ℕ) : Prop :=
  SO4SquareOrbitCollisionCloses (m * m)

theorem delta_orbit_non_extinction_certified_square_midpoints :
    DeltaOrbitNonExtinctionAtSquareMidpoint 2 ∧
      DeltaOrbitNonExtinctionAtSquareMidpoint 3 ∧
      DeltaOrbitNonExtinctionAtSquareMidpoint 4 := by
  refine ⟨SO4SquareOrbitCollisionCloses_four, SO4SquareOrbitCollisionCloses_nine,
    SO4SquareOrbitCollisionCloses_sixteen⟩

/-! ## Shared orbit-energy zero loci -/

theorem rh_critical_line_is_orbit_energy_zero_locus (s : ℂ) :
    s.re = (1 / 2 : ℝ) ↔
      orbitCollisionEnergyVector (criticalLineDeviation s) (0 : ℝ) 0 = 0 := by
  rw [← criticalLineDeviation_eq_zero_iff, critical_deviation_is_orbit_energy_zero_locus]

theorem goldbach_ng_square_is_orbit_energy_zero_locus {N g s : ℕ} :
    N * g = s * s ↔
      orbitCollisionEnergyVector 0 ((ngSquareDefect N g s : ℝ)) 1 = 0 := by
  rw [← ngSquareDefect_zero_iff, ng_square_defect_zero_is_orbit_energy_zero_locus]

theorem orbit_energy_unifies_rh_and_goldbach_channels :
    (∀ {n : ℕ} (v : Fin n → ℝ), PSD (gramKernel v) ∧ 0 ≤ ∑ i, v i ^ 2) ∧
      (∀ s : ℂ, s.re = (1 / 2 : ℝ) ↔
        orbitCollisionEnergyVector (criticalLineDeviation s) (0 : ℝ) 0 = 0) ∧
      (∀ N g s : ℕ, N * g = s * s ↔
        orbitCollisionEnergyVector 0 ((ngSquareDefect N g s : ℝ)) 1 = 0) := by
  refine ⟨@orbit_energy_shares_weil_gram_backbone, ?_, ?_⟩
  · intro s; exact rh_critical_line_is_orbit_energy_zero_locus s
  · intro N g s; exact goldbach_ng_square_is_orbit_energy_zero_locus (N := N) (g := g) (s := s)

/-! ## Open global targets (documented) -/

/--
**Open.**  Global Δ-orbit non-extinction: every gap-orbit collision yields a stack
survivor.  Square-midpoint closure (`DeltaOrbitNonExtinctionAtSquareMidpoint`) is a
proved subcase only.
-/
def DeltaOrbitNonExtinctionObstruction (N : ℕ) : Prop :=
  SO4DeltaOrbitObstruction N

/--
**Open (RH route).**  Rolling zero localization + explicit-formula identification
forces critical-line deviation to vanish on nontrivial zeros — the analytic discharge
behind the ζ-side orbit-energy zero locus.
-/
def RollingExplicitFormulaOrbitEnergyDischarge : Prop :=
  RollingZetaIdentificationAtCriticalLine

theorem square_orbit_non_extinction_implies_no_ng_square_collision {N : ℕ}
    (hClose : SO4SquareOrbitCollisionCloses N) :
    ∀ (c : SO4GapOrbitCollision N),
      MidpointGapNgSquare N (midpointLeftGap N c.slot_a) →
        MidpointGapNgSquare N (midpointLeftGap N c.slot_b) →
          False := by
  intro c hNg_a hNg_b
  exact so4_ng_square_collision_extinction_forbidden hClose c hNg_a hNg_b

end

end Hqiv.Story

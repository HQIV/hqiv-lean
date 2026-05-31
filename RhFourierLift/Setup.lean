import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Order.Filter.AtTopBot.Tendsto

import Hqiv.Generators
import Hqiv.GeneratorsFromAxioms
import Hqiv.Algebra.G2Embedding
import Hqiv.Algebra.PhaseLiftDelta

-- SO(8) Lie closure certificate: `Hqiv.Algebra.G2_plus_Delta_closes_to_so8` in
-- `Hqiv.Algebra.SO8ClosureAbstract` (import `HQIVSO8Closure` / `lake build HQIVSO8Closure`).
-- Not imported here so `HQIVRhFourierLift` stays independent of the heavy
-- `GeneratorsLieClosureData*` matrix certificate chain.

/-!
# RH Fourier lift — Phase 0 setup

Discrete growth law, curvature channel `K(n)`, and abstract phase map used in later phases.
Paper/Python names map to Lean as follows:

* `OctonionHQIVAlgebra.g2_basis` → `Hqiv.Algebra.g2Generator`
* `OctonionHQIVAlgebra.Delta` / phase-lift Δ → `Hqiv.phaseLiftDelta` (see also `Hqiv.Algebra.phaseLiftDeltaMatrix`)
* SO(8) closure certificate → `Hqiv.Algebra.G2_plus_Delta_closes_to_so8` (`SO8ClosureAbstract.lean`, target `HQIVSO8Closure`)
-/

open scoped BigOperators
open Finset Filter

namespace RhFourierLift

/-!
## Paper counting and curvature density (Phase 0)
-/

/-- Shell occupation `N(m) = (m+2)(m+1)` from the discrete growth law. -/
def N (m : ℕ) : ℕ := (m + 2) * (m + 1)

/-- Area-scale factor `A(m) = 4 N(m)`. -/
def A (m : ℕ) : ℝ := 4 * (N m : ℝ)

/-- Curvature density sample `ρ(x) = (1 + α log x) / x` for `x > 0`. -/
noncomputable def rho (x : ℝ) (α : ℝ) : ℝ := (1 + α * Real.log x) / x

/-- Cumulative curvature channel: `K(n,α) = ∑_{m=0}^{n-1} ρ(m+1,α)`. -/
noncomputable def K (n : ℕ) (α : ℝ) : ℝ :=
  ∑ m ∈ range n, rho ((m + 1 : ℕ) : ℝ) α

/-- HQIV informational coupling (paper default `α = 3/5`). -/
noncomputable def alphaDefault : ℝ := (3 : ℝ) / 5

/-- Harmonic partial sum `H_n = ∑_{i=0}^{n-1} 1/(i+1)` (same indexing as `K`). -/
noncomputable def harmonic (n : ℕ) : ℝ :=
  ∑ i ∈ range n, (1 : ℝ) / (i + 1)

/-!
### Positivity and domination by the harmonic series
-/

lemma one_le_cast_succ (m : ℕ) : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
  have : (1 : ℕ) ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
  exact_mod_cast this

lemma log_nonneg_of_one_le {x : ℝ} (hx : 1 ≤ x) : 0 ≤ Real.log x :=
  Real.log_nonneg hx

theorem rho_pos_of_one_le {x : ℝ} (hx : 1 ≤ x) {α : ℝ} (hα : 0 ≤ α) : 0 < rho x α := by
  unfold rho
  have hnum : 0 < 1 + α * Real.log x := by
    have hlog : 0 ≤ Real.log x := log_nonneg_of_one_le hx
    have hαlog : 0 ≤ α * Real.log x := mul_nonneg hα hlog
    linarith
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  exact div_pos hnum hx0

theorem rho_ge_one_div_of_one_le {x : ℝ} (hx : 1 ≤ x) {α : ℝ} (hα : 0 ≤ α) :
    (1 : ℝ) / x ≤ rho x α := by
  unfold rho
  have hlog : 0 ≤ Real.log x := log_nonneg_of_one_le hx
  have hαlog : 0 ≤ α * Real.log x := mul_nonneg hα hlog
  have hle : (1 : ℝ) ≤ 1 + α * Real.log x := by linarith
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rwa [div_le_div_iff_of_pos_right hx0]

theorem K_pos {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 ≤ α) : 0 < K n α := by
  unfold K
  refine sum_pos (fun i _ => rho_pos_of_one_le (one_le_cast_succ i) hα) ?_
  exact nonempty_range_iff.mpr (Nat.pos_iff_ne_zero.mp hn)

theorem K_ge_harmonic (n : ℕ) {α : ℝ} (hα : 0 ≤ α) : harmonic n ≤ K n α := by
  unfold harmonic K
  refine sum_le_sum fun i hi => ?_
  simpa [rho] using rho_ge_one_div_of_one_le (one_le_cast_succ i) hα

theorem K_strict_mono {α : ℝ} (hα : 0 < α) : StrictMono (fun n => K n α) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  simp only [K, sum_range_succ]
  have hn : 1 ≤ ((n + 1 : ℕ) : ℝ) := one_le_cast_succ n
  linarith [rho_pos_of_one_le hn (le_of_lt hα)]

theorem K_tendsto_atTop {α : ℝ} (hα : 0 < α) : Tendsto (fun n => K n α) atTop atTop := by
  have hh := Real.tendsto_sum_range_one_div_nat_succ_atTop
  have hcmp : ∀ n, ∑ i ∈ range n, (1 : ℝ) / (i + 1) ≤ K n α :=
    fun n => K_ge_harmonic n (le_of_lt hα)
  exact tendsto_atTop_mono hcmp hh

/-- Curvature channel diverges (same data as `K_tendsto_atTop`: dominates the harmonic series). -/
theorem K_diverges {α : ℝ} (hα : 0 < α) : Tendsto (fun n => K n α) atTop atTop :=
  K_tendsto_atTop hα

/-!
### Abstract phase map (Phase 0 milestone; refined in `Rapidity.lean`)
-/

/-- Base harmonic readout used for normalization at `ω = 1`. -/
noncomputable def baseHarmonic (φ t : ℝ) : ℝ := φ * Real.cos t

/-- Phase map: curvature ratio `ω` lifts phase around the base harmonic. -/
structure PhaseMap where
  /-- Evaluation `R(φ,t,ω)`. -/
  eval : ℝ → ℝ → ℝ → ℝ
  /-- On the unit ratio, recover the base harmonic. -/
  norm_at_one : ∀ φ t, eval φ t 1 = baseHarmonic φ t

/-- Canonical example: rigid rotation of phase by `log ω` (multiplicative lift). -/
noncomputable def canonicalPhaseMap : PhaseMap where
  eval := fun φ t ω => φ * Real.cos (t + Real.log ω)
  norm_at_one := by
    intro φ t
    simp [baseHarmonic, Real.log_one]

/-- For every positive coupling `α`, the diverging curvature channel admits a phase lift
(modelled here by `canonicalPhaseMap`). This is the Phase 0 abstraction; later files
relate `ω` to `K n α / K m⋆ α`. -/
theorem curvature_forces_rapidity {α : ℝ} (_ : 0 < α) :
    ∃ R : PhaseMap, ∀ φ t, R.eval φ t 1 = baseHarmonic φ t :=
  ⟨canonicalPhaseMap, fun φ t => canonicalPhaseMap.norm_at_one φ t⟩

/-!
## Paper artifact anchors (compile-time `#check`)
-/

section PaperAnchors

#check Hqiv.Algebra.g2Generator
#check Hqiv.phaseLiftDelta
#check Hqiv.Algebra.phaseLiftDeltaMatrix

end PaperAnchors

end RhFourierLift

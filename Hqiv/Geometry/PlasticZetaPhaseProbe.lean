import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic

import Hqiv.Geometry.SpatialSliceRapidityScaffold

/-!
# Plastic zeta phase probe (hypothesis bundle)

This module introduces a Lean-facing experiment interface for the plastic/root-scale
zeta-zero probe:

- `snaps` stores arithmetic-native samples `(p, m, k)` from the plastic oracle,
- `polarAngleFromRapidity φ t m` is linked to a zeta-phase channel at `t_eff`,
- a near-zero witness records proximity to a known nontrivial zeta zero with a
  small observed `|ζ(1/2 + i t_eff)|`.

This is intentionally hypothesis-driven and compile-safe (no `axiom`, no `sorry`).
-/

namespace Hqiv.Geometry

abbrev PrimeSnap := ℕ × ℕ × ℕ

/-- Prime component of a snap `(p, m, k)`. -/
def snapPrime (s : PrimeSnap) : ℕ := s.1

/-- Shell-step component of a snap `(p, m, k)`. -/
def snapStep (s : PrimeSnap) : ℕ := s.2.1

/-- Arity component of a snap `(p, m, k)`. -/
def snapArity (s : PrimeSnap) : ℕ := s.2.2

/--
Hypothesis bundle for the plastic/root-scale zeta phase experiment.

`zetaPhaseAt` and `zetaAbsAtHalfLine` are explicit function slots so this module can
be instantiated by either numerical probes or future formalized channels.
-/
structure PlasticZetaPhaseProbe where
  φ : ℝ
  t : ℝ
  ε : ℝ
  δ : ℝ
  η : ℝ
  snaps : List PrimeSnap
  knownZeros : List ℝ
  tEff : ℕ → ℕ → ℕ → ℝ
  zetaPhaseAt : ℝ → ℝ
  zetaAbsAtHalfLine : ℝ → ℝ
  /-- Rapidity-to-zeta phase link on every snap in the sample list. -/
  hRapidityLink :
    ∀ p m k : ℕ, (p, m, k) ∈ snaps →
      |polarAngleFromRapidity φ t m - zetaPhaseAt (tEff p m k)| < ε
  /-- Near-zero witness: one sampled point lies near a listed zero and has small zeta amplitude. -/
  hNearZero :
    ∃ p m k : ℕ, (p, m, k) ∈ snaps ∧
      ∃ t0 : ℝ, t0 ∈ knownZeros ∧
        |tEff p m k - t0| < δ ∧
        zetaAbsAtHalfLine (tEff p m k) < η

/-- Repackage `hNearZero` as an explicit witness tuple for downstream use. -/
theorem PlasticZetaPhaseProbe.nearZeroWitness
    (P : PlasticZetaPhaseProbe) :
    ∃ s : PrimeSnap, s ∈ P.snaps ∧
      ∃ t0 : ℝ, t0 ∈ P.knownZeros ∧
        |P.tEff (snapPrime s) (snapStep s) (snapArity s) - t0| < P.δ ∧
        P.zetaAbsAtHalfLine (P.tEff (snapPrime s) (snapStep s) (snapArity s)) < P.η := by
  rcases P.hNearZero with ⟨p, m, k, hs, t0, hz, hdist, habs⟩
  refine ⟨(p, m, k), hs, t0, hz, ?_, ?_⟩
  · simpa [snapPrime, snapStep, snapArity] using hdist
  · simpa [snapPrime, snapStep, snapArity] using habs

/-- Convenience corollary: some sampled step `m` has rapidity/zeta phase agreement up to `ε`. -/
theorem PlasticZetaPhaseProbe.existsStepWithPhaseLink
    (P : PlasticZetaPhaseProbe) :
    ∃ p m k : ℕ, (p, m, k) ∈ P.snaps ∧
      |polarAngleFromRapidity P.φ P.t m - P.zetaPhaseAt (P.tEff p m k)| < P.ε := by
  rcases P.nearZeroWitness with ⟨s, hs, t0, hz, hdist, habs⟩
  refine ⟨snapPrime s, snapStep s, snapArity s, hs, ?_⟩
  exact P.hRapidityLink (snapPrime s) (snapStep s) (snapArity s) hs

end Hqiv.Geometry

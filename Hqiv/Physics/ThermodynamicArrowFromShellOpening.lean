import RhFourierLift.Setup

import Hqiv.Physics.ThermodynamicLawsFromLadder
import Hqiv.Topology.ParallelPoincareScaffold
import Hqiv.Topology.ShellOpeningEvolution

/-!
# Thermodynamic arrow from shell opening

Bundles the machine-checked **discrete arrow** (signed shell ledger + opening evolution) with the
ladder thermodynamic laws already in `ThermodynamicLawsFromLadder`.

**Layering (no proton/shell-4 conflation).**

* Curvature imprint (`δ_E`, `shell_shape`) stays positive — not driven by `shellOpeningStep`.
* `shellOpeningStep` closes **deficit-only** horizon states toward `S3NullReference` combinatorics.
* Strict lex descent is on `(totalEarlyNegativeBudget, totalNegativeBudget)`; with `linkDeficit ≡ 0`,
  the ℝ scaffold `lyapunovFunctional` is shell-0 mismatch and strictly drops only when shell `0` opens.
-/

namespace Hqiv.Physics

open Hqiv Hqiv.Topology RhFourierLift

/-- Packaged thermodynamic-arrow witness: laws 0–3 + opening convergence at horizon `n`. -/
structure ThermodynamicArrowFromShellOpening (n : ℕ) where
  href : 0 < K n (1 : ℝ)
  zeroth_law : ∀ m, thermalEquilibrium m m
  third_law : ∀ ε > 0, ∃ m, Hqiv.T m < ε
  opening_reaches_S3 :
    ∀ (M₀ : Discrete3Complex NullShellVertex) (hV : IsVertexOnly M₀),
      maxVertexShell M₀ = n → deficitOnlyOnHorizon M₀ n →
        ∃ k M',
          (shellOpeningEvolution (1 : ℝ) n href).iterate k M₀ = some M' ∧
            IsS3NullReference M' n

noncomputable def thermodynamicArrowFromShellOpening (n : ℕ) (href : 0 < K n (1 : ℝ)) :
    ThermodynamicArrowFromShellOpening n where
  href := href
  zeroth_law := fun m => zerothLaw_refl m
  third_law := thirdLaw_eventually_below
  opening_reaches_S3 := fun M₀ hV hmax hdef =>
    shellOpeningStep_reaches_S3NullReference (1 : ℝ) n href M₀ hV n hmax hdef

/-- Lex-encoded `RealLyapunovDescent` for opening (ℕ pair `(early, totalNegative)`). -/
noncomputable def shellOpeningRealLyapunovDescentAt (n : ℕ) (href : 0 < K n (1 : ℝ)) :
    RealLyapunovDescent (shellOpeningEvolution (1 : ℝ) n href) :=
  shellOpeningRealLyapunovDescent (1 : ℝ) n href

/-- Parallel-Poincaré hypothesis from `of_real_descent` at a converged opening equilibrium. -/
noncomputable def shell_opening_parallel_poincare_hypothesis (n : ℕ) (href : 0 < K n (1 : ℝ))
    (M : Discrete3Complex NullShellVertex) (hV : IsVertexOnly M) (hmax : maxVertexShell M = n)
    (hdef : deficitOnlyOnHorizon M n) (hq : QuadraticNullShellGrowthOnHorizon M n)
    (heq : (shellOpeningEvolution (1 : ℝ) n href).IsEquilibrium M) :
    DiscreteParallelPoincareHypothesis :=
  DiscreteParallelPoincareHypothesis.of_shell_opening_real_descent (1 : ℝ) n href (by norm_num) M hV hmax hdef hq heq

theorem shell_opening_discrete_parallel_poincare_at_horizon (n : ℕ) (href : 0 < K n (1 : ℝ))
    (M₀ : Discrete3Complex NullShellVertex) (hV : IsVertexOnly M₀)
    (hmax : maxVertexShell M₀ = n) (hdef : deficitOnlyOnHorizon M₀ n) :
    ∃ k M', (shellOpeningEvolution (1 : ℝ) n href).iterate k M₀ = some M' ∧
      IsS3NullReference M' n ∧
      ∃ H : DiscreteParallelPoincareHypothesis,
        H.evo = shellOpeningEvolution (1 : ℝ) n href ∧
          H.data.M = M' ∧ IsS3NullReference H.data.M n :=
  DiscreteParallelPoincareHypothesis.shell_opening_discrete_parallel_poincare_at_horizon
    (1 : ℝ) n href (by norm_num) M₀ hV hmax hdef

end Hqiv.Physics

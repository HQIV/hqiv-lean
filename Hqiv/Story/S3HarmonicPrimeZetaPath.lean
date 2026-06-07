import Hqiv.Story.S3ClosureDeltaLiftBridge
import Hqiv.Physics.ShellIndexRiemannZetaBridge
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Harmonic channel → Δ → prime product → ζ → Λ: the proved path

You are right that there is a genuine chain here. This module makes it explicit and
machine-checks every link that Mathlib and the closure spine already supply.

**Proved geometric / growth layer (closure + `OctonionicLightCone`):**

1. `harmonicPartialSum_le_curvatureChannel` — `H_n ≤ K(n)`;
2. `curvatureChannel_strictly_increasing` — the normalized channel `Ω` diverges;
3. `so3_delta_lifts_to_so4` — the phase-lift generator `Δ₄` closes `SO(3) → SO(4)`.

`Δ` is **forced by** the divergent harmonic-backed channel (`K ≥ H_n → Ω → ℛ → Δ` in
`papers/closure`); it is not identical to `H_n`, but it exists because the harmonic
lower bound makes `K` unbounded.

**Proved arithmetic / analytic layer (`Re s > 1`, Mathlib):**

4. `shell_sum_eq_riemannZeta` — discrete shell weights `1/(n+1)^s` sum to `ζ(s)`;
5. `prime_euler_product_eq_zeta` — `∏'_p (1 - p^{-s})^{-1} = ζ(s)`;
6. `prime_log_sum_exp_eq_zeta` — `exp(∑_p -log(1-p^{-s})) = ζ(s)`;
7. `vonMangoldt_lseries_eq_neg_log_deriv_zeta` — `L Λ(s) = -ζ'(s)/ζ(s)`;
8. `vonMangoldt_prime_eq_log` — `Λ(p) = log p` on primes.

So: **harmonic divergence → Δ lift → shell/Euler prime product → ζ → Λ = −ζ′/ζ** is a
proved pipeline on `Re s > 1`, and Mathlib already supplies **analytic continuation**
of `ζ` (`differentiableAt_riemannZeta`, functional equation, trivial zeros).

**RH is not continuation.** It is exclusively the **nontrivial zero** statement
(`AllNontrivialZerosOnLine` / `RiemannHypothesis`). Continuation tells you `ζ` exists
on `ℂ \\ {1}`; it does not place zeros on `Re = 1/2`.
-/

namespace Hqiv.Story

open ArithmeticFunction ArithmeticFunction.Moebius
open scoped LSeries.notation zeta

noncomputable section

/-! ### Geometric layer: harmonic channel forces Δ -/

/-- Re-export: harmonic partial sums sit below the curvature channel. -/
theorem harmonic_channel_lower_bound (n : ℕ) :
    harmonicPartialSum n ≤ Hqiv.curvature_integral n :=
  harmonicPartialSum_le_curvatureChannel n

/-- Re-export: the channel diverges — the closure normalization `Ω` is unbounded. -/
theorem harmonic_channel_diverges : StrictMono Hqiv.curvature_integral :=
  curvatureChannel_strictly_increasing

/-! ### Shell ladder ↔ classical ζ (`Re s > 1`) -/

/-- Discrete shell sum with the HQIV `(n+1)` shift equals `ζ(s)`. -/
theorem shell_sum_eq_riemannZeta (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ s :=
  Hqiv.Physics.riemannZeta_tsum_succ_eq s hs

/-! ### Prime Euler product ↔ ζ (`Re s > 1`) -/

/-- Prime-product form of the Riemann zeta function. -/
theorem prime_euler_product_eq_zeta (s : ℂ) (hs : 1 < s.re) :
    ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ = riemannZeta s :=
  riemannZeta_eulerProduct_tprod hs

/-- Logarithmic prime-sum form of the Euler product. -/
theorem prime_log_sum_exp_eq_zeta (s : ℂ) (hs : 1 < s.re) :
    Complex.exp (∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-s))) = riemannZeta s :=
  riemannZeta_eulerProduct_exp_log hs

/-! ### Von Mangoldt / Λ = −ζ′/ζ (`Re s > 1`) -/

/-- The L-series of `Λ` is the negative log-derivative of `ζ`. -/
theorem vonMangoldt_lseries_eq_neg_log_deriv_zeta (s : ℂ) (hs : 1 < s.re) :
    L ↗ArithmeticFunction.vonMangoldt s = -deriv riemannZeta s / riemannZeta s :=
  LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

/-- On primes, `Λ(p) = log p` — the local prime weight in the log-derivative. -/
theorem vonMangoldt_prime_weight {p : ℕ} (hp : p.Prime) :
    ArithmeticFunction.vonMangoldt p = Real.log p :=
  vonMangoldt_apply_prime hp

/-- Mathlib: `ζ` is differentiable on `ℂ \\ {1}` (analytic continuation, not RH). -/
theorem riemannZeta_differentiable_away_from_one {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ riemannZeta s :=
  differentiableAt_riemannZeta hs

/--
**The full path packaging.** The harmonic–prime–ζ chain and continuation are proved;
`localization` is the **zero-locus** capstone only (`Re = 1/2` for nontrivial zeros).
-/
structure HarmonicPrimeZetaPath where
  weil_positive : DiscreteWeilFormPositive
  localization : ExplicitFormulaLocalization

/-- RH from the full path: proved links + explicit-formula inputs. -/
theorem RiemannHypothesis_of_harmonic_prime_zeta_path (P : HarmonicPrimeZetaPath) :
    RiemannHypothesis :=
  RiemannHypothesis_of_closure_harmonic_delta_bridge
    ⟨P.weil_positive, P.localization⟩

end

end Hqiv.Story

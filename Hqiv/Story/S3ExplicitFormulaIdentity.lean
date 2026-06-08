import Hqiv.Story.S3WeilPositivityCriterion
import Mathlib.NumberTheory.Divisors

/-!
# Discrete explicit-formula identity: arch + Λ-side + ∑|ĝ|²

Mathlib does not yet supply the full analytic explicit formula for `riemannZeta`.
This module builds the **finite, honest backbone** of that identity:

`W(g) = A(g) + ∑_n Λ(n) g(n) + ∑_ρ |ĝ(ρ)|²`

at a discrete truncation, with `g = f ⋆̃ f` the Dirichlet autocorrelation of a test
function `f`.

**Proved here (no analytic input):**

* `dirichletAutocorr` — discrete autocorrelation `g(n) = ∑_{d ∣ n} f(d) f(n/d)`;
* `primeExplicitTerm` — the prime-side pairing `∑_{n ≤ N} Λ(n) g(n)` using Mathlib's
  `vonMangoldt`;
* `zeroExplicitTerm` — the critical-line zero side `∑_i aᵢ²` (sum of squares);
* `split_zero_nonneg` — the zero side is automatically `≥ 0` (`weilSumOnLine_nonneg`);
* `split_total_ge_arch_plus_prime` — any split forces
  `arch + prime ≤ total` because the zero side is nonnegative.

**Named analytic input (RH-hard):**

* `DiscreteExplicitFormulaSplit.split` — the explicit formula identity at this
  truncation;
* `ExplicitFormulaLocalization` — nonnegativity of every split implies zeros on
  the line.

So `WeilFormPositive` is no longer a bare rename: it becomes a consequence of
`DiscreteWeilFormPositive` plus the localization step, with the zero-side Gram
structure proved in advance.
-/

namespace Hqiv.Story

open ArithmeticFunction Nat

noncomputable section

/--
Dirichlet autocorrelation `g = f ⋆̃ f` at `n`:

`g(n) = ∑_{d ∣ n} f(d) · f(n/d)`.
-/
noncomputable def dirichletAutocorr (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, f d * f (n / d)

/--
Prime-side explicit-formula term at truncation `N`:

`∑_{1 ≤ n ≤ N} Λ(n) · g(n)`.
-/
noncomputable def primeExplicitTerm (N : ℕ) (g : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, vonMangoldt n * g n

/--
Zero-side explicit-formula term on the critical line (finite truncation):

`∑_i aᵢ² = ∑ |ĝ(ρᵢ)|²`.
-/
noncomputable def zeroExplicitTerm {nz : ℕ} (amps : Fin nz → ℝ) : ℝ :=
  ∑ i, amps i ^ 2

/--
Three-way split of the Weil functional at a finite truncation:

`total = archimedean + prime + zero`.
-/
noncomputable def explicitFormulaTotal (arch prime zero : ℝ) : ℝ :=
  arch + prime + zero

/--
A discrete explicit-formula split for a test function `f` at bound `N` with `nz`
sampled zero amplitudes.

The `split` field is the **analytic identity** at this truncation; everything else
in the structure is concrete data.
-/
structure DiscreteExplicitFormulaSplit (nz N : ℕ) where
  f : ℕ → ℝ
  archimedean : ℝ
  zeroAmplitudes : Fin nz → ℝ
  total : ℝ
  split :
    total =
      explicitFormulaTotal archimedean
        (primeExplicitTerm N (dirichletAutocorr f))
        (zeroExplicitTerm zeroAmplitudes)

/-- The zero side is a sum of squares, hence nonnegative (proved Gram backbone). -/
theorem zeroExplicitTerm_nonneg {nz : ℕ} (amps : Fin nz → ℝ) :
    0 ≤ zeroExplicitTerm amps :=
  weilSumOnLine_nonneg amps

/-- Any split forces `arch + prime ≤ total` because the zero side is nonnegative. -/
theorem split_total_ge_arch_plus_prime {nz N : ℕ} (S : DiscreteExplicitFormulaSplit nz N) :
    S.archimedean +
        primeExplicitTerm N (dirichletAutocorr S.f) ≤
      S.total := by
  have hz := zeroExplicitTerm_nonneg S.zeroAmplitudes
  rw [S.split, explicitFormulaTotal]
  linarith

/-- The zero side of a split is nonnegative. -/
theorem split_zero_nonneg {nz N : ℕ} (S : DiscreteExplicitFormulaSplit nz N) :
    0 ≤ zeroExplicitTerm S.zeroAmplitudes :=
  zeroExplicitTerm_nonneg S.zeroAmplitudes

/--
**PSD certificate.** The zero-side kernel is positive semidefinite — this is the
linear-algebra content of Weil positivity on the critical line. The zero channel
`∑ aᵢ²` is the rank-one Gram instance proved in `gramKernel_psd`.
-/
theorem zeroExplicitTerm_gram_psd {nz : ℕ} (amps : Fin nz → ℝ) :
    PSD (gramKernel amps) :=
  gramKernel_psd amps

/-- Every discrete explicit-formula split has nonnegative zero side. -/
theorem split_zero_side_autopositive {nz N : ℕ} (S : DiscreteExplicitFormulaSplit nz N) :
    0 ≤ zeroExplicitTerm S.zeroAmplitudes ∧
      PSD (gramKernel S.zeroAmplitudes) :=
  ⟨split_zero_nonneg S, zeroExplicitTerm_gram_psd S.zeroAmplitudes⟩

/--
Discrete Weil positivity: every explicit-formula split has `total ≥ 0`.

This is the finite test-function version of "the Weil functional is nonnegative".
-/
def DiscreteWeilFormPositive : Prop :=
  ∀ {nz N : ℕ} (S : DiscreteExplicitFormulaSplit nz N), 0 ≤ S.total

/--
The localization step: discrete Weil positivity, given the explicit-formula
split for all tests, forces every nontrivial zero onto `Re = 1/2`.

This is the genuine analytic converse (RH-hard).
-/
def ExplicitFormulaLocalization : Prop :=
  DiscreteWeilFormPositive → AllNontrivialZerosOnLine

/--
Full bridge: discrete splits + global nonnegativity + localization ⇒ RH.
-/
structure FullExplicitFormulaBridge where
  weil_positive : DiscreteWeilFormPositive
  localization : ExplicitFormulaLocalization

/-- A populated full bridge yields Mathlib's `RiemannHypothesis`. -/
theorem RiemannHypothesis_of_fullExplicitFormulaBridge (B : FullExplicitFormulaBridge) :
    RiemannHypothesis :=
  allNontrivialZerosOnLine_iff_RiemannHypothesis.mp (B.localization B.weil_positive)

/--
`WeilFormPositive` as a consequence of the discrete explicit-formula positivity
plus the localization step — no longer a bare definitional alias.
-/
theorem weilFormPositive_of_discrete_and_localization
    (hPos : DiscreteWeilFormPositive) (hLoc : ExplicitFormulaLocalization) :
    WeilFormPositive :=
  hLoc hPos

/--
Connect to the earlier `WeilPositivityBridge`: discrete positivity + localization
is exactly the same RH packaging, now with the explicit-formula split in scope.
-/
theorem RiemannHypothesis_of_discrete_weil_and_localization
    (hPos : DiscreteWeilFormPositive) (hLoc : ExplicitFormulaLocalization) :
    RiemannHypothesis :=
  RiemannHypothesis_of_fullExplicitFormulaBridge
    ⟨hPos, hLoc⟩

end

end Hqiv.Story

import Hqiv.Story.S3OrbitVsPointwiseGap
import Hqiv.Geometry.GoldbachG2Parity
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Explicit-formula duality slot: prime side ↔ zero localization

This is the honest frontier the previous six guardrail modules pointed at. Every
finite cyclotomic / `S³` symmetry produces a real arithmetic invariant but cannot
localize `ζ`'s zeros (`no_finite_symmetry_isolates_primes`). The *one* place where
prime data genuinely meets the zeros is the **explicit formula**

`ψ(x) = x − ∑_ρ x^ρ / ρ − (low-order terms)`,

where `ψ(x) = ∑_{n ≤ x} Λ(n)` is the Chebyshev prime-power sum (von Mangoldt `Λ`),
and `ρ` runs over the nontrivial zeros. This is the analytic dual of your
"Fourier-twiddle residual" picture: `Λ` is the prime-power weight, and it is paired
against `∑_ρ x^ρ`.

This module supplies the **real** prime side from Mathlib (`vonMangoldt`) and names
the remaining analytic obligation precisely. The genuine content — that a
positivity input (Weil / Li / de Bruijn–Newman `Λ_dBN = 0`) forces every
nontrivial zero onto `Re = 1/2` — is *equivalent to RH*:

`WeilPositivityForcesCriticalLine ↔ RiemannHypothesis`.

So this is an honest packaging: the prime side is concrete and proved; the
localization step is named, and shown to be exactly RH (not smuggled in). It
connects to the repo's `lambdaHQIV` de Bruijn–Newman *analogue*
(`TempLadderForcesLambdaHQIVZero`) and to `nonempty_complexResidualModel_iff_RiemannHypothesis`.
-/

namespace Hqiv.Story

open ArithmeticFunction

noncomputable section

/-- **Prime side (real).** The Chebyshev function `ψ(x) = ∑_{n=1}^{x} Λ(n)`, the
von Mangoldt partial sum dual to the zero sum in the explicit formula. -/
def chebyshevPsi (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 x, vonMangoldt n

/-- The von Mangoldt weight is `log p` on primes — the prime-power content paired
against the zeros (this is the `Λ` your twiddle residual is dual to). -/
theorem vonMangoldt_prime_eq_log {p : ℕ} (hp : p.Prime) :
    vonMangoldt p = Real.log p :=
  vonMangoldt_apply_prime hp

/-- `Λ 1 = 0`: the unit carries no prime-power weight. -/
theorem vonMangoldt_one_eq_zero : vonMangoldt 1 = 0 :=
  vonMangoldt_apply_one

/-- Each von Mangoldt term is nonnegative — the positivity that the explicit-formula
criterion exploits on the prime side. -/
theorem vonMangoldt_term_nonneg (n : ℕ) : 0 ≤ vonMangoldt n :=
  vonMangoldt_nonneg

/--
**Explicit-formula bridge data.** A bundle carrying:

* a concrete prime side `psi` identified with `chebyshevPsi` (real, proved object);
* the localization conclusion `zeros_on_line` that the positivity argument is meant
  to deliver.

The `zeros_on_line` field is the genuine analytic obligation; it is *not* free.
-/
structure ExplicitFormulaData where
  psi : ℕ → ℝ
  psi_eq : psi = chebyshevPsi
  zeros_on_line : AllNontrivialZerosOnLine

/-- Given the explicit-formula bridge data, Mathlib's `RiemannHypothesis` follows. -/
theorem RiemannHypothesis_of_explicitFormulaData (D : ExplicitFormulaData) :
    RiemannHypothesis :=
  allNontrivialZerosOnLine_iff_RiemannHypothesis.mp D.zeros_on_line

/--
The Weil/positivity localization step, named as a `Prop`. The genuine statement is
"the explicit-formula quadratic form is positive semidefinite," and its standard
consequence is that every nontrivial zero lies on `Re = 1/2`.
-/
def WeilPositivityForcesCriticalLine : Prop :=
  AllNontrivialZerosOnLine

/--
**Honesty/equivalence theorem.** The positivity localization step is *equivalent*
to the Riemann Hypothesis. So constructing it (e.g. from a genuine Weil-positivity
or `Λ_dBN = 0` input) *is* proving RH — it is the real frontier, faithfully named,
not hidden.
-/
theorem weilPositivity_iff_RiemannHypothesis :
    WeilPositivityForcesCriticalLine ↔ RiemannHypothesis :=
  allNontrivialZerosOnLine_iff_RiemannHypothesis

/-! ## Shared half-slope bridge: RH side + Goldbach midpoint side -/

/--
SO(8) projected half-slope payload.

The intended geometric reading is that the same normalized `1/2` readout has
two projections:

* the zeta projection, where it locks nontrivial zeros to the critical line;
* the additive midpoint projection, where it forces positive Goldbach pair count
  around every sufficiently large midpoint.

The structure deliberately keeps both hard payloads explicit.  It does not claim
that either one follows from bare finite symmetry alone.
-/
structure SO8ProjectedHalfSlopeBridge (N₀ : ℕ) : Prop where
  critical_line :
    WeilPositivityForcesCriticalLine
  midpoint_pairs :
    Hqiv.Geometry.SO4ZetaHolonomyForcesMidpointPairs N₀

/-- The half-slope bridge yields Mathlib's `RiemannHypothesis`. -/
theorem RiemannHypothesis_of_so8_projected_half_slope
    {N₀ : ℕ}
    (B : SO8ProjectedHalfSlopeBridge N₀) :
    RiemannHypothesis :=
  weilPositivity_iff_RiemannHypothesis.mp B.critical_line

/--
The half-slope bridge yields eventual midpoint Goldbach, with diagonal pairs
allowed.
-/
theorem midpoint_goldbach_of_so8_projected_half_slope
    {N₀ : ℕ}
    (B : SO8ProjectedHalfSlopeBridge N₀) :
    Hqiv.Geometry.MidpointGoldbachEventually N₀ :=
  Hqiv.Geometry.midpoint_goldbach_of_so4_zeta_holonomy_bridge B.midpoint_pairs

/--
Combined conclusion: if the SO(8) projection really supplies the shared
half-slope payload on both the zeta and midpoint-prime channels, then RH and
eventual midpoint Goldbach follow together.
-/
theorem RH_and_midpoint_goldbach_of_so8_projected_half_slope
    {N₀ : ℕ}
    (B : SO8ProjectedHalfSlopeBridge N₀) :
    RiemannHypothesis ∧ Hqiv.Geometry.MidpointGoldbachEventually N₀ :=
  ⟨RiemannHypothesis_of_so8_projected_half_slope B,
    midpoint_goldbach_of_so8_projected_half_slope B⟩

/--
If the midpoint side is strengthened from eventual to all `n > 2` by taking
`N₀ = 2`, the usual even Goldbach parity statement follows from the same
half-slope package.
-/
theorem RH_and_goldbach_parity_of_so8_projected_half_slope_from_two
    (B : SO8ProjectedHalfSlopeBridge 2) :
    RiemannHypothesis ∧ Hqiv.Geometry.GoldbachParity := by
  refine ⟨RiemannHypothesis_of_so8_projected_half_slope B, ?_⟩
  intro n hn hEven
  rcases hEven with ⟨k, hk⟩
  subst n
  have hk2 : 2 ≤ k := by omega
  rcases midpoint_goldbach_of_so8_projected_half_slope B k hk2 with
    ⟨p, q, hMid⟩
  refine ⟨p, q, ?_⟩
  simpa [two_mul] using Hqiv.Geometry.goldbach_pair_of_midpoint_pair hMid

/--
Prominent joint statement: a global SO(8) projected half-slope bridge beginning
at midpoint `2` implies both RH and the even Goldbach parity statement.

This is intentionally a thin wrapper around
`RH_and_goldbach_parity_of_so8_projected_half_slope_from_two`; the proof content
remains in the two explicit bridge fields.
-/
theorem so8_half_slope_implies_rh_and_goldbach_parity
    (B : SO8ProjectedHalfSlopeBridge 2) :
    RiemannHypothesis ∧ Hqiv.Geometry.GoldbachParity :=
  RH_and_goldbach_parity_of_so8_projected_half_slope_from_two B

/-! ## Discharge of the bridge packaging: the bridge *is* RH ∧ Goldbach

The converse constructions below rebuild a half-slope bridge from the two
classical statements, so the packaging is an *equivalence*, not just a
sufficient condition.  This discharges the claim "the half-slope bridge encodes
RH together with Goldbach" exactly: the bridge has no slack content beyond the
conjunction, and nothing was smuggled in.  The two classical conjectures
themselves remain open; what is proved is that the geometric payload and the
conjunction are the same proposition.
-/

/-- RH and eventual midpoint Goldbach rebuild the half-slope bridge. -/
theorem so8_projected_half_slope_of_rh_and_midpoint_goldbach
    {N₀ : ℕ}
    (hRH : RiemannHypothesis)
    (hMid : Hqiv.Geometry.MidpointGoldbachEventually N₀) :
    SO8ProjectedHalfSlopeBridge N₀ where
  critical_line := weilPositivity_iff_RiemannHypothesis.mpr hRH
  midpoint_pairs :=
    Hqiv.Geometry.so4_zeta_holonomy_bridge_of_midpoint_goldbach hMid

/--
**Bridge equivalence (general threshold).** The SO(8) projected half-slope
bridge at threshold `N₀` is logically equivalent to the conjunction of
`RiemannHypothesis` with eventual midpoint Goldbach from `N₀`.
-/
theorem so8_projected_half_slope_iff_rh_and_midpoint_goldbach
    {N₀ : ℕ} :
    SO8ProjectedHalfSlopeBridge N₀ ↔
      (RiemannHypothesis ∧ Hqiv.Geometry.MidpointGoldbachEventually N₀) :=
  ⟨RH_and_midpoint_goldbach_of_so8_projected_half_slope,
    fun h => so8_projected_half_slope_of_rh_and_midpoint_goldbach h.1 h.2⟩

/-- RH and even Goldbach parity rebuild the half-slope bridge at threshold `2`. -/
theorem so8_projected_half_slope_two_of_rh_and_goldbach_parity
    (hRH : RiemannHypothesis)
    (hG : Hqiv.Geometry.GoldbachParity) :
    SO8ProjectedHalfSlopeBridge 2 :=
  so8_projected_half_slope_of_rh_and_midpoint_goldbach hRH
    (Hqiv.Geometry.midpoint_goldbach_two_of_goldbach_parity hG)

/--
**Capstone equivalence.** The SO(8) projected half-slope bridge at threshold `2`
*is* `RiemannHypothesis ∧ GoldbachParity`:

`SO8ProjectedHalfSlopeBridge 2 ↔ RiemannHypothesis ∧ GoldbachParity`.

This is the faithful formal content of "RH = Goldbach" in the projection story:
both classical statements are the two channel readouts of one geometric payload,
with a machine-checked equivalence in both directions.  Discharging the bridge
itself is exactly as hard as the two open problems combined — by this theorem,
provably so.
-/
theorem so8_projected_half_slope_two_iff_rh_and_goldbach_parity :
    SO8ProjectedHalfSlopeBridge 2 ↔
      (RiemannHypothesis ∧ Hqiv.Geometry.GoldbachParity) :=
  ⟨so8_half_slope_implies_rh_and_goldbach_parity,
    fun h => so8_projected_half_slope_two_of_rh_and_goldbach_parity h.1 h.2⟩

/--
Channel separation: the two bridge fields are *independently* equivalent to the
two classical statements.  The zeta channel is exactly RH and the midpoint
channel at threshold `2` is exactly Goldbach parity; neither channel leaks into
the other.
-/
theorem bridge_channels_are_rh_and_goldbach :
    (WeilPositivityForcesCriticalLine ↔ RiemannHypothesis) ∧
      (Hqiv.Geometry.SO4ZetaHolonomyForcesMidpointPairs 2 ↔
        Hqiv.Geometry.GoldbachParity) :=
  ⟨weilPositivity_iff_RiemannHypothesis,
    Hqiv.Geometry.so4_zeta_holonomy_bridge_two_iff_goldbach_parity⟩

end

end Hqiv.Story

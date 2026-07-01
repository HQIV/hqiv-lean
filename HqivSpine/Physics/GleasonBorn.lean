import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.GleasonBorn` — the Born functional as a Gleason frame function

The **measurement-probability** layer on the complex finite Hilbert space `ℂⁿ`, sitting
between `Physics.VonNeumann` (observables, computational-basis Born, density matrices) and the
real-carrier `Physics.Measurement` (ratio uniqueness `bornProbN_unique_of_coherence`).

Gleason's theorem has two directions. The hard **converse** — *every* `σ`-additive probability
measure on the projection lattice of a `dim ≥ 3` Hilbert space is `P ↦ tr(ρP)` for some density
operator `ρ` — needs the analytic projection-lattice machinery and is *not* attempted here (and
is in fact **false** in `dim = 2`). What is genuinely the constructive content of Gleason, and is
proved here from Mathlib's `OrthonormalBasis` Parseval identity, is the **representable
direction** valid in every finite dimension:

* `bornFrame φ ψ = ‖⟪φ, ψ⟫‖²` is the Born overlap probability of measuring the ray `ψ` in state
  `φ`. It is symmetric (`bornFrame_comm`), nonnegative (`bornFrame_nonneg`), and bounded by
  Cauchy–Schwarz, so for unit vectors it is a genuine probability in `[0,1]`
  (`bornFrame_le_one`).
* **Gleason frame condition (Parseval additivity):** over *any* orthonormal measurement basis
  `b`, the outcome probabilities sum to the state energy, `∑ᵢ bornFrame φ (b i) = ‖φ‖²`
  (`frame_sum`); for a unit state they sum to `1` in *every* basis (`frame_sum_pure`).
* **Non-contextuality / basis independence:** the total is the same for any two orthonormal
  bases (`frame_basis_independent`) — the defining property of a Gleason frame function.
* **Mixed (density) states:** a finite convex mixture `∑ₖ wₖ bornFrame (φₖ) ·` is again a frame
  function, summing to `∑ₖ wₖ‖φₖ‖²` (`mixFrame_sum`); convex weights on unit states give a frame
  function normalised to `1` (`mixFrame_sum_pure`). These are exactly the trace-rule
  `P ↦ tr(ρP)` representatives, with `ρ = ∑ₖ wₖ |φₖ⟩⟨φₖ|`.

* **The dimension gap is real** (`gleason_fails_in_dim_two`): the `dim ≥ 3` hypothesis of
  Gleason's theorem is *necessary*, not cosmetic. On the real 2-sphere (the circle) the sextic
  `θ ↦ cos 6θ` is a frame function (`sextic_isFrameFun`) that is **not** the quadratic form of any
  operator (`sextic_not_qform`). In `dim = 2` an orthonormal basis is just an antipodal pair, so
  additivity only constrains `f θ + f(θ+π/2)`; every Fourier mode `cos kθ` with `k ≡ 2 (mod 4)`
  survives, while quadratic forms `xᵀMx` reach only `k ≤ 2`. The qutrit (`qutrit_frame_sum`,
  `frame_sum` at `n = 3`) keeps the representable direction in the physical three-dimensional
  setting where, by Gleason's theorem, it is the *only* one — the rigidity a qubit model discards.

Combined with `Measurement.bornProbN_unique_of_coherence` (the finite ratio-uniqueness
substitute for Gleason's converse), this pins down the Born weights as the unique consistent
probability assignment **and** verifies that the quadratic overlap law satisfies the additivity /
basis-independence Gleason demands. Honest scope: the analytic `dim ≥ 3` converse itself (every
frame function equals `tr(ρ·)`) is cited, not formalised; what *is* proved is both representable
directions (every density operator gives a frame function, any dimension) and the sharp `dim = 2`
counterexample showing why three dimensions are essential.

Mathlib-only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Physics.GleasonBorn

open scoped InnerProductSpace BigOperators ComplexConjugate
open Finset

/-- Finite complex Hilbert space `ℂⁿ` with the standard `L²` inner product
(matching `Physics.VonNeumann.HilbertFin`). -/
abbrev HilbertFin (n : ℕ) := EuclideanSpace ℂ (Fin n)

noncomputable section

variable {n : ℕ}

/-- **Born overlap probability** of measuring ray `ψ` when the system is in state `φ`:
`|⟪φ, ψ⟫|²`. For unit vectors this is the squared cosine of the angle between the rays. -/
def bornFrame (φ ψ : HilbertFin n) : ℝ := ‖(inner ℂ φ ψ : ℂ)‖ ^ 2

theorem bornFrame_nonneg (φ ψ : HilbertFin n) : 0 ≤ bornFrame φ ψ := by
  unfold bornFrame; positivity

/-- The Born overlap is symmetric in state and measured ray: `|⟪φ,ψ⟫|² = |⟪ψ,φ⟫|²`. -/
theorem bornFrame_comm (φ ψ : HilbertFin n) : bornFrame φ ψ = bornFrame ψ φ := by
  unfold bornFrame
  congr 1
  rw [← inner_conj_symm ψ φ, RCLike.norm_conj]

/-- **Cauchy–Schwarz (cosine law) bound:** `|⟪φ,ψ⟫|² ≤ ‖φ‖²‖ψ‖²`. -/
theorem bornFrame_le (φ ψ : HilbertFin n) : bornFrame φ ψ ≤ ‖φ‖ ^ 2 * ‖ψ‖ ^ 2 := by
  unfold bornFrame
  have hcs : ‖(inner ℂ φ ψ : ℂ)‖ ≤ ‖φ‖ * ‖ψ‖ := norm_inner_le_norm φ ψ
  nlinarith [hcs, norm_nonneg (inner ℂ φ ψ : ℂ), norm_nonneg φ, norm_nonneg ψ,
    mul_nonneg (norm_nonneg φ) (norm_nonneg ψ)]

/-- For unit state and unit measured ray, the Born overlap is a genuine probability `≤ 1`. -/
theorem bornFrame_le_one {φ ψ : HilbertFin n} (hφ : ‖φ‖ = 1) (hψ : ‖ψ‖ = 1) :
    bornFrame φ ψ ≤ 1 := by
  simpa [hφ, hψ] using bornFrame_le φ ψ

/-- **Gleason frame condition (Parseval additivity).** Over *any* orthonormal measurement basis
`b`, the Born outcome probabilities sum to the informational energy `‖φ‖²` of the state. This is
the additivity of a probability assignment over an orthogonal resolution of the identity — the
defining axiom of a Gleason frame function — here *derived* from Parseval's identity. -/
theorem frame_sum (b : OrthonormalBasis (Fin n) ℂ (HilbertFin n)) (φ : HilbertFin n) :
    (∑ i, bornFrame φ (b i)) = ‖φ‖ ^ 2 := by
  unfold bornFrame
  exact b.sum_sq_norm_inner_left φ

/-- **Born normalisation in every basis.** For a unit state the outcome probabilities of a
measurement sum to `1`, regardless of which orthonormal basis is measured. -/
theorem frame_sum_pure (b : OrthonormalBasis (Fin n) ℂ (HilbertFin n)) {φ : HilbertFin n}
    (hφ : ‖φ‖ = 1) : (∑ i, bornFrame φ (b i)) = 1 := by
  rw [frame_sum b φ, hφ, one_pow]

/-- **Non-contextuality / basis independence.** The total Born weight is the same for any two
orthonormal measurement bases — the frame value depends only on the state, not on the chosen
orthogonal resolution. -/
theorem frame_basis_independent (b c : OrthonormalBasis (Fin n) ℂ (HilbertFin n))
    (φ : HilbertFin n) : (∑ i, bornFrame φ (b i)) = ∑ i, bornFrame φ (c i) := by
  rw [frame_sum b φ, frame_sum c φ]

/-- **Qutrit (`dim = 3`) trace-form frame function.** The physically relevant `frame_sum` at
`n = 3`: the Born overlaps of a `ℂ³` state with any orthonormal measurement basis sum to `‖φ‖²`.
This is the *representable* direction in the dimension where Gleason's theorem makes it the **only**
possibility — unlike `dim = 2`, where `gleason_fails_in_dim_two` exhibits a non-representable frame
function. -/
theorem qutrit_frame_sum (b : OrthonormalBasis (Fin 3) ℂ (HilbertFin 3)) (φ : HilbertFin 3) :
    (∑ i, bornFrame φ (b i)) = ‖φ‖ ^ 2 :=
  frame_sum b φ

/-! ## Mixed (density-operator) frame functions

A density operator `ρ = ∑ₖ wₖ |φₖ⟩⟨φₖ|` (convex mixture of pure states) induces the
probability assignment `P ↦ tr(ρ P)`, which on rays reads `∑ₖ wₖ |⟪φₖ, ·⟫|²`. We show it is again
a Gleason frame function: additive over every orthonormal basis. -/

/-- Born frame function of a mixed state `ρ = ∑ₖ wₖ |φₖ⟩⟨φₖ|`. -/
def mixFrame {m : ℕ} (w : Fin m → ℝ) (φ : Fin m → HilbertFin n) (ψ : HilbertFin n) : ℝ :=
  ∑ k, w k * bornFrame (φ k) ψ

theorem mixFrame_nonneg {m : ℕ} {w : Fin m → ℝ} (hw : ∀ k, 0 ≤ w k)
    (φ : Fin m → HilbertFin n) (ψ : HilbertFin n) : 0 ≤ mixFrame w φ ψ :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (bornFrame_nonneg _ _)

/-- **Mixed-state frame condition.** The mixed Born functional is additive over every
orthonormal basis, summing to the weighted energy `∑ₖ wₖ‖φₖ‖²` — so any density operator yields a
Gleason frame function (the representable / trace-rule direction of Gleason). -/
theorem mixFrame_sum {m : ℕ} (b : OrthonormalBasis (Fin n) ℂ (HilbertFin n))
    (w : Fin m → ℝ) (φ : Fin m → HilbertFin n) :
    (∑ i, mixFrame w φ (b i)) = ∑ k, w k * ‖φ k‖ ^ 2 := by
  unfold mixFrame
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.mul_sum, frame_sum b (φ k)]

/-- Convex weights on unit pure states give a frame function normalised to `1` in every basis —
a bona-fide density operator (`tr ρ = 1`) reproducing the Born rule. -/
theorem mixFrame_sum_pure {m : ℕ} (b : OrthonormalBasis (Fin n) ℂ (HilbertFin n))
    {w : Fin m → ℝ} {φ : Fin m → HilbertFin n}
    (hφ : ∀ k, ‖φ k‖ = 1) (hw : (∑ k, w k) = 1) :
    (∑ i, mixFrame w φ (b i)) = 1 := by
  rw [mixFrame_sum b w φ]
  have : (∑ k, w k * ‖φ k‖ ^ 2) = ∑ k, w k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hφ k, one_pow, mul_one]
  rw [this, hw]

end

/-! ## The dimension gap: Gleason representability **fails** at `dim = 2`

The frame-function additivity above holds in every finite dimension, but it does *not*
characterise the trace rule at `dim = 2`. Gleason's theorem (every frame function is `tr(ρ·)`)
needs `dim ≥ 3`, and that hypothesis is genuinely necessary: on the real 2-dimensional sphere
(the circle) there is a frame function that is **not** the quadratic form of any operator. We
construct one explicitly — `θ ↦ cos 6θ` — and prove it is a frame function yet not representable.

Geometrically: in `dim = 2` an orthonormal basis is just an antipodal pair `{θ, θ+π/2}`, so the
only constraint is `f θ + f(θ+π/2) = const`. This is satisfied by every Fourier mode `cos kθ` with
`k ≡ 2 (mod 4)`, whereas quadratic forms `xᵀMx` only produce `k ≤ 2`. The extra modes (`k = 6,
10, …`) are the pathological frame functions that the richer overlapping bases of `dim ≥ 3`
eliminate. This is exactly the structure a qubit-only model silently discards. -/

section DimensionGap

open Real

/-- Unit vector on the real circle (`dim = 2` sphere) at angle `θ`. -/
noncomputable def uvec (θ : ℝ) : Fin 2 → ℝ := ![Real.cos θ, Real.sin θ]

/-- Quadratic / trace form `x ↦ xᵀ M x` of a real `2×2` matrix on the unit circle. These are
exactly the Born–Gleason **representable** frame functions (`M` ↔ a real density matrix). -/
noncomputable def qform (M : Matrix (Fin 2) (Fin 2) ℝ) (θ : ℝ) : ℝ :=
  ∑ i, ∑ j, M i j * uvec θ i * uvec θ j

/-- A frame function on the circle: additive over every orthonormal pair `{θ, θ+π/2}`, summing to
a constant total `W` (the `dim = 2` instance of the Gleason frame condition). -/
def IsFrameFun (f : ℝ → ℝ) : Prop := ∃ W : ℝ, ∀ θ : ℝ, f θ + f (θ + π / 2) = W

/-- Every quadratic/trace form is a frame function, with total `W = tr M`. -/
theorem qform_isFrameFun (M : Matrix (Fin 2) (Fin 2) ℝ) : IsFrameFun (qform M) := by
  refine ⟨M 0 0 + M 1 1, fun θ => ?_⟩
  have hc : Real.cos (θ + π / 2) = -Real.sin θ := by
    rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have hs : Real.sin (θ + π / 2) = Real.cos θ := by
    rw [Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  simp only [qform, Fin.sum_univ_two, uvec, Matrix.cons_val_zero, Matrix.cons_val_one, hc, hs]
  linear_combination (M 0 0 + M 1 1) * Real.sin_sq_add_cos_sq θ

/-- The pathological **sextic** frame function `θ ↦ cos 6θ`. -/
noncomputable def sextic (θ : ℝ) : ℝ := Real.cos (6 * θ)

/-- `cos 6θ` is a genuine frame function: each orthonormal pair sums to the constant `0`. -/
theorem sextic_isFrameFun : IsFrameFun sextic := by
  refine ⟨0, fun θ => ?_⟩
  have h' : 6 * (θ + π / 2) = 6 * θ + 2 * π + π := by ring
  simp only [sextic]
  rw [h', Real.cos_add_pi, Real.cos_add_two_pi]
  ring

/-- `cos 6θ` is **not** the quadratic form of any `2×2` matrix: evaluating at
`θ = 0, π/2, π/4, π/3` over-determines `M` into a contradiction (it would need both
`M₀₀ = 1, M₁₁ = -1, M₀₁+M₁₀ = 0` and `1 = ¼ - ¾`). -/
theorem sextic_not_qform :
    ¬ ∃ M : Matrix (Fin 2) (Fin 2) ℝ, ∀ θ, sextic θ = qform M θ := by
  rintro ⟨M, h⟩
  have c2 : Real.cos (6 * (π / 2)) = -1 := by
    rw [show 6 * (π / 2) = π + 2 * π by ring, Real.cos_add_two_pi, Real.cos_pi]
  have c4 : Real.cos (6 * (π / 4)) = 0 := by
    rw [show 6 * (π / 4) = π / 2 + π by ring, Real.cos_add_pi, Real.cos_pi_div_two, neg_zero]
  have c3 : Real.cos (6 * (π / 3)) = 1 := by
    rw [show 6 * (π / 3) = 2 * π by ring, Real.cos_two_pi]
  have hs2 : Real.sqrt 2 / 2 * (Real.sqrt 2 / 2) = 1 / 2 := by
    rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  have hs3 : Real.sqrt 3 / 2 * (Real.sqrt 3 / 2) = 3 / 4 := by
    rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3)]; norm_num
  have q0 : qform M 0 = M 0 0 := by
    simp [qform, Fin.sum_univ_two, uvec, Real.cos_zero, Real.sin_zero]
  have q2 : qform M (π / 2) = M 1 1 := by
    simp [qform, Fin.sum_univ_two, uvec, Real.cos_pi_div_two, Real.sin_pi_div_two]
  have q4 : qform M (π / 4) = (M 0 0 + M 0 1 + M 1 0 + M 1 1) / 2 := by
    simp only [qform, Fin.sum_univ_two, uvec, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.cos_pi_div_four, Real.sin_pi_div_four]
    linear_combination (M 0 0 + M 0 1 + M 1 0 + M 1 1) * hs2
  have q3 : qform M (π / 3)
      = M 0 0 / 4 + (M 0 1 + M 1 0) * (Real.sqrt 3 / 4) + M 1 1 * (3 / 4) := by
    simp only [qform, Fin.sum_univ_two, uvec, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.cos_pi_div_three, Real.sin_pi_div_three]
    linear_combination M 1 1 * hs3
  have s0 : sextic 0 = 1 := by simp [sextic]
  have s2 : sextic (π / 2) = -1 := c2
  have s4 : sextic (π / 4) = 0 := c4
  have s3 : sextic (π / 3) = 1 := c3
  have e0 := h 0; rw [s0, q0] at e0
  have e2 := h (π / 2); rw [s2, q2] at e2
  have e4 := h (π / 4); rw [s4, q4] at e4
  have e3 := h (π / 3); rw [s3, q3] at e3
  have hbc : M 0 1 + M 1 0 = 0 := by linarith
  rw [hbc, zero_mul] at e3
  linarith

/-- **Gleason's representation theorem fails in dimension 2.** There is a frame function on the
real 2-sphere — `θ ↦ cos 6θ` — that is *not* the quadratic form of any operator (density matrix).
So qubit probabilities are **not** forced to the Born/trace rule by additivity alone: the `dim ≥ 3`
hypothesis of Gleason's theorem is genuinely necessary. In three or more dimensions every frame
function is `tr(ρ·)` (Gleason, cited — its analytic proof is out of scope here), and that rigidity
is precisely what a two-dimensional model throws away. -/
theorem gleason_fails_in_dim_two :
    ∃ f : ℝ → ℝ, IsFrameFun f ∧ ¬ ∃ M : Matrix (Fin 2) (Fin 2) ℝ, ∀ θ, f θ = qform M θ :=
  ⟨sextic, sextic_isFrameFun, sextic_not_qform⟩

end DimensionGap

end HqivSpine.Physics.GleasonBorn

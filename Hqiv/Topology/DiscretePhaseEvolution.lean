import Mathlib.Data.Real.Basic
import Mathlib.Data.Option.Basic
import Mathlib.LinearAlgebra.Matrix.Defs

import Hqiv.Algebra.G2Embedding
import Hqiv.Algebra.PhaseLiftDelta
import Hqiv.Algebra.Triality
import Hqiv.SO8ClosureSymbolic
import Hqiv.Topology.DiscreteCurvatureChannel
import Hqiv.Topology.DiscreteNullLatticeComplex
import Hqiv.Topology.SignedShellBudget

/-!
# Discrete phase evolution + Δ-suture slot

One-step evolution for the **parallel Poincaré** programme: divergent `K` channel, normalized
phase readout, and the antisymmetric phase-lift \(\Delta\) on \(\mathrm{span}\{e_1,e_7\}\).

**Cluster A (dynamics):** `iterate` algebra + **proved** termination/strict-descent from a
`NatLyapunovDescent` / `RealLyapunovDescent` certificates until `linkDeficit` and `step` are
nontrivial; use the measure-based lemmas in this file.

**Cluster B (bridge):** `SO8AdmissibleHolonomy` + template certificates in
`ParallelPoincareScaffold` — consume dynamics via `ParallelPoincareTemplateCertificate`.
-/

namespace Hqiv.Topology

open Hqiv Hqiv.Algebra RhFourierLift Matrix

/-!
## Phase readout at shell index
-/

/-- Normalized cumulative phase readout \(\mathcal{R}(\phi,t,n)=\Omega(n)\) for constant base phase. -/
noncomputable def normalizedPhaseReadout (n mStar : ℕ) (α : ℝ) (href : 0 < K mStar α) : ℝ :=
  Omega n mStar α href

/-- Phase increment \(\theta(n)=\mathcal{R}(n)-\mathcal{R}(m_\ast)\) (reference subtracts to zero). -/
theorem phaseIncrement_zero_at_reference (mStar : ℕ) (α : ℝ) (href : 0 < K mStar α) :
    normalizedPhaseReadout mStar mStar α href - normalizedPhaseReadout mStar mStar α href = 0 := by
  simp [normalizedPhaseReadout, Omega_ref]

/-!
## Discrete evolution step
-/

/-- One step of the discrete curvature channel flow (`none` = extinction / pinch resolved). -/
structure DiscreteCurvatureEvolution where
  α : ℝ
  mStar : ℕ
  href : 0 < K mStar α
  /-- Single evolution step on a 3-complex. -/
  step : Discrete3Complex NullShellVertex → Option (Discrete3Complex NullShellVertex)
  /-- Lyapunov does not increase (strict drop unless at equilibrium). -/
  lyapunov_nonincreasing :
    ∀ M, match step M with
    | none => True
    | some M' => lyapunovFunctional M' ≤ lyapunovFunctional M

namespace DiscreteCurvatureEvolution

/-- Iterate `step` `n` times. -/
def iterate (evo : DiscreteCurvatureEvolution) : ℕ → Discrete3Complex NullShellVertex →
    Option (Discrete3Complex NullShellVertex)
  | 0, M => some M
  | n + 1, M =>
      match evo.step M with
      | none => none
      | some M' => iterate evo n M'

@[simp] theorem iterate_zero (evo : DiscreteCurvatureEvolution) (M) :
    evo.iterate 0 M = some M := rfl

theorem iterate_one (evo : DiscreteCurvatureEvolution) (M) :
    evo.iterate 1 M = evo.step M := by
  unfold iterate
  rcases evo.step M with ⟨M'⟩ | none <;> rfl

theorem iterate_succ_of_step (evo : DiscreteCurvatureEvolution) (n M M')
    (h : evo.step M = some M') :
    evo.iterate (n + 1) M = evo.iterate n M' := by
  simp only [iterate, h]

/-- At equilibrium when `step` fixes the complex. -/
def IsEquilibrium (evo : DiscreteCurvatureEvolution) (M : Discrete3Complex NullShellVertex) : Prop :=
  evo.step M = some M

theorem not_equilibrium_of_step_none (evo : DiscreteCurvatureEvolution) (M)
    (hnone : evo.step M = none) : ¬ evo.IsEquilibrium M := by
  intro heq
  unfold IsEquilibrium at heq
  rw [hnone] at heq
  cases heq

end DiscreteCurvatureEvolution

/-- Termination/equilibrium proposition for a fixed initial complex. -/
def FlowTerminatesAt (evo : DiscreteCurvatureEvolution) (M : Discrete3Complex NullShellVertex) : Prop :=
  ∃ n, evo.iterate n M = none ∨ ∃ M', evo.iterate n M = some M' ∧ evo.IsEquilibrium M'

theorem FlowTerminatesAt.exists_equilibrium_of_no_extinction
    (evo : DiscreteCurvatureEvolution) (M : Discrete3Complex NullShellVertex)
    (h : FlowTerminatesAt evo M) (hno : ∀ k, evo.iterate k M ≠ none) :
    ∃ n M', evo.iterate n M = some M' ∧ evo.IsEquilibrium M' := by
  rcases h with ⟨n, hn⟩
  rcases hn with hnone | ⟨M', hiter, heq⟩
  · exact absurd hnone (hno n)
  · exact ⟨n, M', hiter, heq⟩

/-- Strict Lyapunov descent away from equilibrium for a fixed initial complex. -/
def LyapunovStrictDescentOffEquilibrium
    (evo : DiscreteCurvatureEvolution) (M : Discrete3Complex NullShellVertex) : Prop :=
  ¬ evo.IsEquilibrium M →
    ∃ M', evo.step M = some M' ∧ lyapunovFunctional M' < lyapunovFunctional M

/-!
## Cluster A — Nat measure engine (proved)
-/

/-- Certificate that a **ℕ-valued** measure decreases off equilibrium (extinction allowed). -/
structure NatLyapunovDescent (evo : DiscreteCurvatureEvolution) where
  μ : Discrete3Complex NullShellVertex → ℕ
  strict_off_equilibrium :
    ∀ M, ¬ evo.IsEquilibrium M →
      evo.step M = none ∨ ∃ M', evo.step M = some M' ∧ μ M' < μ M

/-- Bridge from a ℕ measure to the ℝ scaffold functional `lyapunovFunctional`.

Requires a genuine `some` step off equilibrium (extinction `none` is handled only by the ℕ
termination certificate, not by strict ℝ descent). -/
structure RealLyapunovDescent (evo : DiscreteCurvatureEvolution) extends NatLyapunovDescent evo where
  strict_some_off_equilibrium :
    ∀ M, IsVertexOnly M → ¬ evo.IsEquilibrium M → ∃ M', evo.step M = some M' ∧ μ M' < μ M
  /-- With `linkDeficit ≡ 0`, `lyapunovFunctional` is shell-0 mismatch; opening on `m > 0` may leave it
  unchanged while the encoded ℕ measure still strictly decreases. -/
  functional_nonincreasing_on_mu_descent :
    ∀ M M', evo.step M = some M' →
      μ M' < μ M → lyapunovFunctional M' ≤ lyapunovFunctional M
  functional_strict_shell0 :
    ∀ M M', evo.step M = some M' → negativeBudget M 0 → lyapunovFunctional M' < lyapunovFunctional M

/-- Finite termination or equilibrium from a ℕ Lyapunov certificate. -/
theorem discrete_flow_terminates_of_nat_measure
    (evo : DiscreteCurvatureEvolution) (μ : Discrete3Complex NullShellVertex → ℕ)
    (hstrict :
      ∀ M, ¬ evo.IsEquilibrium M →
        evo.step M = none ∨ ∃ M', evo.step M = some M' ∧ μ M' < μ M) :
    ∀ M, FlowTerminatesAt evo M := by
  suffices ∀ k, ∀ M, μ M ≤ k → FlowTerminatesAt evo M from fun M => this (μ M) M le_rfl
  intro k
  induction k with
  | zero =>
      intro M hle
      have hμ : μ M = 0 := Nat.eq_zero_of_le_zero hle
      by_cases heq : evo.IsEquilibrium M
      · refine ⟨0, Or.inr ⟨M, DiscreteCurvatureEvolution.iterate_zero evo M, heq⟩⟩
      · rcases hstrict M heq with hnone | ⟨M', hstep, hlt⟩
        · refine ⟨1, Or.inl ?_⟩
          simpa [DiscreteCurvatureEvolution.iterate_one] using hnone
        · exfalso
          apply Nat.not_lt_zero (μ M')
          rwa [hμ] at hlt
  | succ k ih =>
      intro M hle
      rcases Nat.le_iff_lt_or_eq.mp hle with hlt | hμ
      · exact ih M (Nat.lt_succ_iff.mp hlt)
      · by_cases heq : evo.IsEquilibrium M
        · refine ⟨0, Or.inr ⟨M, DiscreteCurvatureEvolution.iterate_zero evo M, heq⟩⟩
        · rcases hstrict M heq with hnone | ⟨M', hstep, hlt'⟩
          · refine ⟨1, Or.inl ?_⟩
            simpa [DiscreteCurvatureEvolution.iterate_one] using hnone
          · rw [hμ] at hlt'
            have hμ' : μ M' ≤ k := Nat.lt_succ_iff.mp hlt'
            rcases ih M' hμ' with ⟨n, hn⟩
            rcases hn with hnone | ⟨M'', hiter, heq'⟩
            · refine ⟨n + 1, Or.inl ?_⟩
              rw [DiscreteCurvatureEvolution.iterate_succ_of_step evo n M M' hstep, hnone]
            · refine ⟨n + 1, Or.inr ⟨M'', ?_, heq'⟩⟩
              rw [DiscreteCurvatureEvolution.iterate_succ_of_step evo n M M' hstep, hiter]

theorem discrete_flow_terminates_of_descent (evo : DiscreteCurvatureEvolution)
    (h : NatLyapunovDescent evo) : ∀ M, FlowTerminatesAt evo M :=
  discrete_flow_terminates_of_nat_measure evo h.μ h.strict_off_equilibrium

theorem lyapunov_strict_descent_off_equilibrium_of_real_descent
    (evo : DiscreteCurvatureEvolution) (h : RealLyapunovDescent evo)
    (M : Discrete3Complex NullShellVertex) (hV : IsVertexOnly M) (hne : ¬ evo.IsEquilibrium M)
    (h0 : negativeBudget M 0) :
    ∃ M', evo.step M = some M' ∧ lyapunovFunctional M' < lyapunovFunctional M := by
  rcases h.strict_some_off_equilibrium M hV hne with ⟨M', hstep, _⟩
  exact ⟨M', hstep, h.functional_strict_shell0 M M' hstep h0⟩

theorem lyapunov_nonincreasing_on_mu_descent_of_real_descent
    (evo : DiscreteCurvatureEvolution) (h : RealLyapunovDescent evo)
    (M M' : Discrete3Complex NullShellVertex) (hstep : evo.step M = some M')
    (hμ : h.μ M' < h.μ M) :
    lyapunovFunctional M' ≤ lyapunovFunctional M :=
  h.functional_nonincreasing_on_mu_descent M M' hstep hμ

theorem lyapunov_strict_descent_off_equilibrium_at_shell0_of_real_descent
    (evo : DiscreteCurvatureEvolution) (h : RealLyapunovDescent evo)
    (M : Discrete3Complex NullShellVertex) (hV : IsVertexOnly M) (h0 : negativeBudget M 0) :
    LyapunovStrictDescentOffEquilibrium evo M :=
  fun hne => lyapunov_strict_descent_off_equilibrium_of_real_descent evo h M hV hne h0

/-- Termination at `M` from a `RealLyapunovDescent` certificate (ℕ layer inside `h`). -/
theorem flow_terminates_at_of_real_descent (evo : DiscreteCurvatureEvolution)
    (h : RealLyapunovDescent evo) (M : Discrete3Complex NullShellVertex) :
    FlowTerminatesAt evo M :=
  discrete_flow_terminates_of_descent evo h.toNatLyapunovDescent M

/-!
## Curvature channel bundle (evolution ↔ K / Ω / Δ)
-/

/-- Placeholder 3-complex for channel axioms that do not depend on a particular `M`. -/
def channelAxiomComplex : Discrete3Complex NullShellVertex where
  vertices := ∅
  edges := ∅
  triangles := ∅
  tetrahedra := ∅
  edge_closed := by simp

/-- The evolution is driven by the HQIV curvature channel: divergent `K`, normalized Ω readout at
`evo.mStar`, HQIV step \(6^7\sqrt3\), and antisymmetric \(\Delta\) suture. -/
structure UsesCurvatureChannel (evo : DiscreteCurvatureEvolution) where
  /-- Positive coupling so `K n evo.α` is the tier-0 divergent channel. -/
  positive_coupling : 0 < evo.α
  /-- HQIV combinatorial curvature step \(6^7\sqrt3\). -/
  hqiv_step : UsesCurvatureStep channelAxiomComplex curvature_step_6_pow_7_sqrt_3
  /-- Scaffold readout: cumulative phase matches `Omega` at the evolution reference shell. -/
  phase_readout_eq_omega :
    ∀ n, normalizedPhaseReadout n evo.mStar evo.α evo.href =
      Omega n evo.mStar evo.α evo.href
  /-- \(\Delta\) lies in \(\mathfrak{so}(8)\) and is the distinguished suture direction. -/
  delta_suture_antisymmetric : Hqiv.phaseLiftDelta + Hqiv.phaseLiftDeltaᵀ = 0

theorem uses_curvature_channel_phase_readout (evo : DiscreteCurvatureEvolution)
    (h : UsesCurvatureChannel evo) (n : ℕ) :
    normalizedPhaseReadout n evo.mStar evo.α evo.href =
      Omega n evo.mStar evo.α evo.href :=
  h.phase_readout_eq_omega n

/-!
## Scaffold honesty — constant `linkDeficit` layer
-/

/-- With `linkDeficit ≡ 0`, strict **ℝ** descent along `lyapunovFunctional` on a `some` step
requires the shell-0 budget term to drop; a step that preserves it cannot strictly descend. -/
theorem no_real_lyapunov_descent_of_step_preserves_shell0
    (evo : DiscreteCurvatureEvolution) (M M' : Discrete3Complex NullShellVertex)
    (hstep : evo.step M = some M')
    (hpres :
      shellBudgetMismatch M 0 = shellBudgetMismatch M' 0) :
    ¬ lyapunovFunctional M' < lyapunovFunctional M := by
  intro hlt
  have hle := evo.lyapunov_nonincreasing M
  simp only [hstep] at hle
  rw [lyapunovFunctional_eq_shell0_budget, lyapunovFunctional_eq_shell0_budget, hpres] at hlt hle
  exact not_lt_of_ge hle hlt

/-!
## SO(8) admissibility bridge (explicit hypotheses — not bare closure)
-/

/-- Hypotheses linking a 3-complex to the **G₂ + Δ** chart inside \(\mathfrak{so}(8)\).

**Algebraic picture:** \(\mathfrak{so}(8) = \mathrm{Lie}(G_2 \cup \{\Delta\})\) (proved as
`G2DeltaGeneratedLie.g2DeltaGeneratedLie_eq_so8LieSubalgebra`). G₂ is 14 commutators
`[L(e_i),L(e_j)]`; Δ is U(1) in \((e_1,e_7)\). The **six-pack** `g2SixPackMiddle` is
\([e_2,e_3]\ldots[e_3,e_4]\); `g2E1E4Pair` is `[e_1,e_4]` and `[e_2,e_4]`. -/
structure SO8AdmissibleHolonomy (M : Discrete3Complex NullShellVertex) where
  /-- Holonomy fields are linear combinations of `g2Generator` and `phaseLiftDelta`. -/
  fields_g2_delta_recoverable : Prop
  /-- Use the six middle commutators (`Hqiv.Algebra.g2SixPackMiddle`). -/
  uses_six_pack_middle_chart : Prop
  /-- Two \(e_1\)–\(e_4\) rotations (`Hqiv.Algebra.g2E1E4Pair`). -/
  two_e1_e4_rotations : Prop
  /-- Three Spin(8) 8-dim slots (triality). -/
  triality_three_slots : Prop
  /-- Diophantine-normalized phase readout (Ω channel). -/
  diophantine_phase_readout : Prop
  /-- Pinched links resolved along Δ in \((e_1,e_7)\). -/
  delta_resolves_pinched_links : Prop
  /-- Symbolic \(\mathfrak{so}(8)\) bracket closure. -/
  bracket_closure_symbolic :
    ∀ i j : Fin 28, ∃ f : Fin 28 → ℝ,
      Hqiv.lieBracket (Hqiv.so8Generator i) (Hqiv.so8Generator j) = ∑ k, f k • Hqiv.so8Generator k

theorem so8_triality_three_slots_default :
    Fintype.card Hqiv.Algebra.So8RepIndex = 3 :=
  Hqiv.Algebra.card_so8_eight_dim_irreps

/-- Δ is the preferred \((e_1,e_7)\) U(1) generator (matrix entries). -/
theorem preferred_delta_u1_plane :
    Hqiv.phaseLiftDelta 1 7 = -1 ∧
    Hqiv.phaseLiftDelta 7 1 = 1 :=
  ⟨Hqiv.phaseLiftDelta_17, Hqiv.phaseLiftDelta_71⟩

/-- Symbolic closure fact (interface axiom from `SO8ClosureSymbolic`). -/
theorem so8_bracket_closure_symbolic (i j : Fin 28) :
    ∃ f : Fin 28 → ℝ,
      Hqiv.lieBracket (Hqiv.so8Generator i) (Hqiv.so8Generator j) = ∑ k, f k • Hqiv.so8Generator k :=
  lieBracket_in_span_symbolic i j

/-- Delta is antisymmetric (lies in so(8)). -/
theorem delta_antisymmetric :
    Hqiv.phaseLiftDelta + Hqiv.phaseLiftDeltaᵀ = 0 :=
  Hqiv.Algebra.phaseLiftDelta_antisymm

end Hqiv.Topology

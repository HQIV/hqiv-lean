/-
Discrete Schrödinger evolution: time steps are finite products of `HQIVGate`s (combinatorial
automorphisms), so no PDE is solved in the digital layer. The continuum lapse-corrected Schrödinger
layer lives in `Hqiv.QuantumMechanics.Schrodinger` (import that module where you relate digital steps
to PDE predicates). Here `φ(m)` alignment uses `phiRat_coe_eq_phi_of_shell` from `DiscreteQuantumState`.
-/

import Mathlib.Data.Fintype.BigOperators
import Hqiv.QuantumComputing.DigitalGates

namespace Hqiv.QuantumComputing

open Hqiv
open Hqiv.Algebra

variable {L : ℕ}

/-- One digital time step is any `HQIVGate`. -/
abbrev DigitalTimeStep (L : ℕ) :=
  HQIVGate L

/-- Finite evolution: first gate in the list is applied first (innermost in function composition). -/
def digitalEvolution : List (DigitalTimeStep L) → DiscreteState L ≃ DiscreteState L
  | [] => Equiv.refl _
  | h :: t => h.toEquiv.trans (digitalEvolution t)

/-- Concatenating gate lists composes their digital evolutions (first list applied first). -/
theorem digitalEvolution_append (xs ys : List (DigitalTimeStep L)) :
    digitalEvolution (xs ++ ys) = (digitalEvolution xs).trans (digitalEvolution ys) := by
  induction xs with
  | nil =>
      simp [digitalEvolution]
  | cons a xs ih =>
      simp [digitalEvolution, ← ih, Equiv.trans_assoc]

theorem digitalEvolution_preserves_ip (steps : List (DigitalTimeStep L)) (f g : DiscreteState L) :
    discreteIp (digitalEvolution steps f) (digitalEvolution steps g) = discreteIp f g := by
  induction steps generalizing f g with
  | nil =>
      simp [digitalEvolution, discreteIp]
  | cons h t ih =>
      simp [digitalEvolution, Equiv.trans_apply]
      rw [ih]
      exact h.preserves_ip _ _

theorem digitalEvolution_preserves_normSq (steps : List (DigitalTimeStep L)) (f : DiscreteState L) :
    discreteNormSq (digitalEvolution steps f) = discreteNormSq f := by
  simpa [discreteNormSq] using digitalEvolution_preserves_ip steps f f

/-- **Energy proxy** on the digital ladder: same quadratic informational functional as `discreteNormSq`. -/
def discreteEnergyProxy {L : ℕ} (f : DiscreteState L) : ℝ :=
  discreteNormSq f

theorem discreteEnergyProxy_evolution_invariant (steps : List (DigitalTimeStep L)) (f : DiscreteState L) :
    discreteEnergyProxy (digitalEvolution steps f) = discreteEnergyProxy f :=
  digitalEvolution_preserves_normSq steps f

/-- **Angular-momentum proxy:** squared ℓ-weighted moment (combinatorial analogue of `L²` budget). -/
def discreteAngMomSq {L : ℕ} (f : DiscreteState L) : ℝ :=
  ∑ ij : HarmonicIndex L,
    (ij.fst.val : ℝ) * ((ij.fst.val + 1 : ℕ) : ℝ) * (phiRat ij.fst.val : ℝ) *
      octonionInner (f ij) (f ij)

theorem discreteAngMomSq_perm_invariant (σ : HarmonicIndex L ≃ HarmonicIndex L)
    (hσ : ∀ k : HarmonicIndex L, k.fst = (σ k).fst) (f : DiscreteState L) :
    discreteAngMomSq (fun k => f (σ k)) = discreteAngMomSq f := by
  classical
  simp [discreteAngMomSq]
  let w (k : HarmonicIndex L) : ℝ :=
    (k.fst.val : ℝ) * ((k.fst.val + 1 : ℕ) : ℝ) * (phiRat k.fst.val : ℝ)
  have hw : ∀ k : HarmonicIndex L, w k = w (σ k) := by
    intro k
    simp [w, hσ k]
  -- Replace `w k` by `w (σ k)` on the left-hand sum.
  have hL :
      (∑ k : HarmonicIndex L,
          w k * octonionInner (f (σ k)) (f (σ k))) =
        ∑ k : HarmonicIndex L,
          w (σ k) * octonionInner (f (σ k)) (f (σ k)) := by
    refine Finset.sum_congr rfl fun k _ => by
      simp [hw k]
  -- Re-index the final sum using `σ`.
  have hR :
      (∑ k : HarmonicIndex L,
          w (σ k) * octonionInner (f (σ k)) (f (σ k))) =
        ∑ k : HarmonicIndex L,
          w k * octonionInner (f k) (f k) := by
    simpa [w, mul_assoc, mul_left_comm, mul_comm] using
      Equiv.sum_comp σ (fun k => w k * octonionInner (f k) (f k))
  -- Unfold `w` so the final equality matches the goal's expanded scalar-weight form.
  simpa [discreteAngMomSq, w] using Eq.trans hL hR

/-- Monogamy/coherence proxies from `Hqiv.QM` are unchanged when scaling both sides of CKW by the same
nonnegative `etaModePhi` factor (already proved in `MonogamyTanglesPhiConditions`). -/
theorem discrete_coherence_proxy_monotone (m : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    Hqiv.QM.coherenceProxy (m + 1) τ ≤ Hqiv.QM.coherenceProxy m τ :=
  Hqiv.QM.coherenceProxy_step_nonincreasing_unconditional m hτ

/-- Bridge: rational `phiRat` casts to the ℝ field `phi_of_shell` used in lapse-corrected QM. -/
theorem digital_phi_aligns_with_lapse_field (m : ℕ) : (phiRat m : ℝ) = phi_of_shell m :=
  phiRat_coe_eq_phi_of_shell m

#print digitalEvolution
#print digitalEvolution_preserves_normSq
#print discreteEnergyProxy_evolution_invariant
#print digital_phi_aligns_with_lapse_field

#check digitalEvolution_preserves_ip
#check discreteAngMomSq_perm_invariant
#check discrete_coherence_proxy_monotone
#check digital_phi_aligns_with_lapse_field

end Hqiv.QuantumComputing

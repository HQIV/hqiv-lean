import HqivSpine.Physics.Measurement
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.Evolution` — discrete unitary evolution on the finite carrier

The **dynamics** layer for the measurement carrier `StateN n = Fin n → ℝ` of
`Physics.Measurement`. A digital time step is a `Gate` — a bijection of states that preserves
the real inner product `⟨f,g⟩ = ∑ fᵢ gᵢ` (a discrete *unitary*). Time evolution is a finite
list of gates composed in order; **no PDE is solved**, in keeping with the discrete null-lattice
programme.

Main results:

* `evolution_append` — concatenating gate lists composes their evolutions;
* `evolution_preserves_ip` / `evolution_preserves_normSq` — **unitarity**: evolution preserves
  the inner product, hence the informational energy `normSq` (a discrete Schrödinger
  conservation law);
* `evolution_preserves_energy` — the energy `normSq` is a conserved quantity of digital flow;
* `permGate` — relabelling outcomes by `σ : Fin n ≃ Fin n` is a gate, under which a Born weight
  is simply permuted (`bornWeight_permGate`) while the **total** Born probability is conserved
  (`sum_bornProbN_evolution`), so measurement statistics are stable under evolution.

Mathlib + `Physics.Measurement` only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`,
no `native_decide`.
-/

namespace HqivSpine.Physics.Evolution

open scoped BigOperators
open HqivSpine.Physics.Measurement

/-- Real inner product on the finite carrier. -/
def ip {n : ℕ} (f g : StateN n) : ℝ := ∑ i : Fin n, f i * g i

theorem ip_self_eq_normSq {n : ℕ} (f : StateN n) : ip f f = normSq f := by
  unfold ip normSq
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A discrete unitary gate: a bijection of states preserving the inner product. -/
structure Gate (n : ℕ) where
  toEquiv : StateN n ≃ StateN n
  preserves_ip : ∀ f g, ip (toEquiv f) (toEquiv g) = ip f g

namespace Gate

theorem preserves_normSq {n : ℕ} (G : Gate n) (f : StateN n) :
    normSq (G.toEquiv f) = normSq f := by
  rw [← ip_self_eq_normSq, ← ip_self_eq_normSq, G.preserves_ip]

end Gate

/-- Finite digital evolution: the first gate in the list is applied first. -/
def evolution {n : ℕ} : List (Gate n) → (StateN n ≃ StateN n)
  | [] => Equiv.refl _
  | g :: t => g.toEquiv.trans (evolution t)

@[simp] theorem evolution_nil {n : ℕ} : evolution ([] : List (Gate n)) = Equiv.refl _ := rfl

theorem evolution_cons {n : ℕ} (g : Gate n) (t : List (Gate n)) :
    evolution (g :: t) = g.toEquiv.trans (evolution t) := rfl

/-- Concatenating gate lists composes their evolutions (first list applied first). -/
theorem evolution_append {n : ℕ} (xs ys : List (Gate n)) :
    evolution (xs ++ ys) = (evolution xs).trans (evolution ys) := by
  induction xs with
  | nil => simp [evolution]
  | cons a xs ih => simp [evolution, ← ih, Equiv.trans_assoc]

/-- **Unitarity:** digital evolution preserves the inner product. -/
theorem evolution_preserves_ip {n : ℕ} (steps : List (Gate n)) (f g : StateN n) :
    ip (evolution steps f) (evolution steps g) = ip f g := by
  induction steps generalizing f g with
  | nil => simp [evolution]
  | cons h t ih =>
      rw [evolution_cons]
      simp only [Equiv.trans_apply]
      rw [ih]
      exact h.preserves_ip f g

/-- **Conservation of informational energy** (`normSq`) under digital evolution. -/
theorem evolution_preserves_normSq {n : ℕ} (steps : List (Gate n)) (f : StateN n) :
    normSq (evolution steps f) = normSq f := by
  rw [← ip_self_eq_normSq, ← ip_self_eq_normSq, evolution_preserves_ip]

/-- The informational energy is a conserved quantity of digital flow. -/
theorem evolution_preserves_energy {n : ℕ} (steps : List (Gate n)) (f : StateN n) :
    normSq (evolution steps f) = normSq f :=
  evolution_preserves_normSq steps f

theorem evolution_normSq_ne_zero {n : ℕ} (steps : List (Gate n)) {f : StateN n}
    (hf : normSq f ≠ 0) : normSq (evolution steps f) ≠ 0 := by
  rw [evolution_preserves_normSq]; exact hf

/-! ## Permutation gates and stability of Born statistics -/

/-- Relabelling outcomes by `σ : Fin n ≃ Fin n` as an equivalence of states. -/
def permEquiv {n : ℕ} (σ : Fin n ≃ Fin n) : StateN n ≃ StateN n where
  toFun f := fun i => f (σ.symm i)
  invFun f := fun i => f (σ i)
  left_inv f := by funext i; simp
  right_inv f := by funext i; simp

/-- An outcome relabelling is a unitary gate (reindexing preserves the inner product). -/
def permGate {n : ℕ} (σ : Fin n ≃ Fin n) : Gate n where
  toEquiv := permEquiv σ
  preserves_ip := fun f g => by
    show (∑ i : Fin n, f (σ.symm i) * g (σ.symm i)) = ∑ j : Fin n, f j * g j
    exact Equiv.sum_comp σ.symm (fun j => f j * g j)

/-- Under a relabelling gate a Born weight is simply permuted. -/
theorem bornWeight_permGate {n : ℕ} (σ : Fin n ≃ Fin n) (f : StateN n) (i : Fin n) :
    bornWeight ((permGate σ).toEquiv f) i = bornWeight f (σ.symm i) := rfl

/-- **Born statistics are stable under evolution:** on a state of nonzero energy the total
outcome probability stays `1` after any digital evolution. -/
theorem sum_bornProbN_evolution {n : ℕ} (steps : List (Gate n)) (f : StateN n)
    (hf : normSq f ≠ 0) :
    (∑ i : Fin n, bornProbN (evolution steps f) i) = 1 :=
  sum_bornProbN_eq_one _ (evolution_normSq_ne_zero steps hf)

end HqivSpine.Physics.Evolution

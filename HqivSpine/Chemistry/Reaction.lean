import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# `HqivSpine.Chemistry.Reaction` — stoichiometry, mass conservation, and Hess's law

Generic **element-vector** stoichiometry: `n` element types and `k` species slots, each species
carrying a fixed composition `Fin n → ℕ`. A `ReactionGate` specifies integer stoichiometric
coefficients `consume` / `produce` on `Fin k`; nothing else is posited.

Two structural laws fall out, with **no fitted chemistry and no empirical heat literal**:

* **Mass conservation** — an element-balanced gate preserves the total atom count of every element
  (`apply_preserves_totalElementAtoms`), proved relative to the composition matrix.
* **Hess's law** — reaction energy is the change in a *state function* `stateEnergy E s = ∑ sᵢ Eᵢ`
  (`reactionEnergy_eq_stateEnergy_diff`); along any applicable path the total energy telescopes to
  `stateEnergy(final) − stateEnergy(initial)` (`hess_path_energy`), hence is **path-independent**
  (`hess_path_independent`) and vanishes on a thermodynamic cycle (`hess_cycle_zero`).

The per-species energy `E` is the spine binding readout (a deeper composite well sits *below* the
separated-atom sum); the legacy `285.8 kJ/mol` water literal is dropped. The water instance's
exothermicity is therefore a **theorem conditioned on the binding ordering**
(`water_exothermic_of_binding`), not an injected number.

Mathlib-only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Chemistry.Reaction

open scoped BigOperators

/-- Molecular abundance register on `k` species slots. -/
abbrev Register (k : ℕ) := Fin k → ℕ

/-- Stoichiometric surplus (products minus reactants) per species, in `ℤ`. -/
def surplusZ {k : ℕ} (consume produce : Fin k → ℕ) (i : Fin k) : ℤ :=
  (produce i : ℤ) - (consume i : ℤ)

/-- Total atoms of element `e` contributed by register `s` (linear in counts). -/
def totalElementAtoms {n k : ℕ} (atomsPerSpecies : Fin k → Fin n → ℕ) (s : Register k)
    (e : Fin n) : ℕ :=
  ∑ i : Fin k, s i * atomsPerSpecies i e

/-- Same total, packaged in `ℤ` for stoichiometric algebra. -/
def totalElementAtomsZ {n k : ℕ} (atomsPerSpecies : Fin k → Fin n → ℕ) (s : Register k)
    (e : Fin n) : ℤ :=
  ∑ i : Fin k, (s i : ℤ) * (atomsPerSpecies i e : ℤ)

theorem totalElementAtoms_cast_eq_Z {n k : ℕ} (atomsPerSpecies : Fin k → Fin n → ℕ)
    (s : Register k) (e : Fin n) :
    (totalElementAtoms atomsPerSpecies s e : ℤ) = totalElementAtomsZ atomsPerSpecies s e := by
  simp [totalElementAtoms, totalElementAtomsZ, Nat.cast_sum, Nat.cast_mul]

/-- Per-element stoichiometric balance residual (zero ⟺ element-wise mass balance). -/
def elementResidual {n k : ℕ} (atomsPerSpecies : Fin k → Fin n → ℕ) (consume produce : Fin k → ℕ)
    (e : Fin n) : ℤ :=
  ∑ i : Fin k, surplusZ consume produce i * (atomsPerSpecies i e : ℤ)

/-- Generic reaction gate over `n` element types and `k` species. -/
structure ReactionGate (n k : ℕ) where
  atomsPerSpecies : Fin k → Fin n → ℕ
  consume : Fin k → ℕ
  produce : Fin k → ℕ

namespace ReactionGate

variable {n k : ℕ}

/-- The gate can fire from state `s` when every reactant is in stock. -/
def canApply (g : ReactionGate n k) (s : Register k) : Prop :=
  ∀ i : Fin k, g.consume i ≤ s i

/-- Fire the gate: subtract reactants, add products. -/
def apply (g : ReactionGate n k) (s : Register k) : Register k :=
  fun i => s i - g.consume i + g.produce i

def balanceResidual (g : ReactionGate n k) (e : Fin n) : ℤ :=
  elementResidual g.atomsPerSpecies g.consume g.produce e

/-- A gate is element-balanced when every element's residual vanishes. -/
def isElementBalanced (g : ReactionGate n k) : Prop :=
  ∀ e : Fin n, g.balanceResidual e = 0

theorem totalElementAtomsZ_apply_sub (g : ReactionGate n k) (s : Register k)
    (hcan : g.canApply s) (e : Fin n) :
    totalElementAtomsZ g.atomsPerSpecies (g.apply s) e - totalElementAtomsZ g.atomsPerSpecies s e =
      elementResidual g.atomsPerSpecies g.consume g.produce e := by
  unfold ReactionGate.apply totalElementAtomsZ elementResidual surplusZ
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hci : g.consume i ≤ s i := hcan i
  have hcast :
      ((s i - g.consume i + g.produce i : ℕ) : ℤ) =
        (s i : ℤ) - (g.consume i : ℤ) + (g.produce i : ℤ) := by
    have hsplits : s i - g.consume i + g.produce i = (s i - g.consume i) + g.produce i := rfl
    rw [hsplits, Nat.cast_add, Nat.cast_sub hci]
  rw [hcast, sub_mul]
  ring

/-- **Mass conservation.** An element-balanced gate preserves the total atom count of every element. -/
theorem apply_preserves_totalElementAtoms (g : ReactionGate n k) (s : Register k)
    (hcan : g.canApply s) (hbal : g.isElementBalanced) (e : Fin n) :
    totalElementAtoms g.atomsPerSpecies (g.apply s) e = totalElementAtoms g.atomsPerSpecies s e := by
  have hΔ := totalElementAtomsZ_apply_sub g s hcan e
  have hz : elementResidual g.atomsPerSpecies g.consume g.produce e = 0 := by
    simpa [ReactionGate.balanceResidual, ReactionGate.isElementBalanced] using hbal e
  have hEqZ : totalElementAtomsZ g.atomsPerSpecies (g.apply s) e
      = totalElementAtomsZ g.atomsPerSpecies s e := by
    rw [← sub_eq_zero, hΔ, hz]
  rw [← totalElementAtoms_cast_eq_Z, ← totalElementAtoms_cast_eq_Z] at hEqZ
  exact Nat.cast_inj.mp hEqZ

/-- Firing nudges each species count by its surplus (given enough reactants). -/
theorem apply_cast_sub (g : ReactionGate n k) (s : Register k) (hcan : g.canApply s) (i : Fin k) :
    ((g.apply s i : ℕ) : ℝ) - (s i : ℝ) = ((surplusZ g.consume g.produce i : ℤ) : ℝ) := by
  have hci : g.consume i ≤ s i := hcan i
  unfold ReactionGate.apply surplusZ
  have hsplits : s i - g.consume i + g.produce i = (s i - g.consume i) + g.produce i := rfl
  rw [hsplits, Nat.cast_add, Nat.cast_sub hci]
  push_cast
  ring

end ReactionGate

/-! ## Energetics and Hess's law -/

/-- **State function**: the total energy content of a register, `stateEnergy E s = ∑ sᵢ Eᵢ`, with
`E` the per-species energy (the spine binding readout). -/
def stateEnergy {k : ℕ} (E : Fin k → ℝ) (s : Register k) : ℝ :=
  ∑ i : Fin k, (s i : ℝ) * E i

/-- **Reaction energy** `ΔE = ∑ surplusᵢ Eᵢ = E(products) − E(reactants)` — a function of the
stoichiometry alone (independent of the ambient state), the standard `ΔH = ΣH_prod − ΣH_react`. -/
def reactionEnergy {k : ℕ} (E : Fin k → ℝ) (consume produce : Fin k → ℕ) : ℝ :=
  ∑ i : Fin k, ((surplusZ consume produce i : ℤ) : ℝ) * E i

/-- **Reaction energy is a state-function difference** — the heart of Hess's law. Firing an
applicable gate changes `stateEnergy` by exactly the reaction energy. -/
theorem reactionEnergy_eq_stateEnergy_diff {n k : ℕ} (E : Fin k → ℝ) (g : ReactionGate n k)
    (s : Register k) (hcan : g.canApply s) :
    reactionEnergy E g.consume g.produce = stateEnergy E (g.apply s) - stateEnergy E s := by
  unfold reactionEnergy stateEnergy
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← ReactionGate.apply_cast_sub g s hcan i]
  ring

/-- Apply a path (left-to-right list of gates) to a register. -/
def applyPath {n k : ℕ} : List (ReactionGate n k) → Register k → Register k
  | [], s => s
  | g :: gs, s => applyPath gs (g.apply s)

/-- Every gate along the path can fire from the running state it sees. -/
def CanApplyPath {n k : ℕ} : List (ReactionGate n k) → Register k → Prop
  | [], _ => True
  | g :: gs, s => g.canApply s ∧ CanApplyPath gs (g.apply s)

/-- Total energy released along a path = sum of step reaction energies. -/
def pathEnergy {n k : ℕ} (E : Fin k → ℝ) (gs : List (ReactionGate n k)) : ℝ :=
  (gs.map (fun g => reactionEnergy E g.consume g.produce)).sum

/-- **Hess's law (telescoping form).** Along any applicable path the accumulated reaction energy
equals the change in the state function `stateEnergy` between the final and initial registers. -/
theorem hess_path_energy {n k : ℕ} (E : Fin k → ℝ) :
    ∀ (gs : List (ReactionGate n k)) (s : Register k), CanApplyPath gs s →
      pathEnergy E gs = stateEnergy E (applyPath gs s) - stateEnergy E s := by
  intro gs
  induction gs with
  | nil => intro s _; simp [pathEnergy, applyPath]
  | cons g gs ih =>
    intro s hcan
    obtain ⟨hg, hrest⟩ := hcan
    have hstep := reactionEnergy_eq_stateEnergy_diff E g s hg
    have htail := ih (g.apply s) hrest
    simp only [pathEnergy, List.map_cons, List.sum_cons] at htail ⊢
    rw [hstep, htail]
    simp only [applyPath]
    ring

/-- **Path independence.** Two applicable paths from the same start that reach the same final
register release the same total energy — heat depends only on the endpoints, not the route. -/
theorem hess_path_independent {n k : ℕ} (E : Fin k → ℝ)
    (gs hs : List (ReactionGate n k)) (s : Register k)
    (hg : CanApplyPath gs s) (hh : CanApplyPath hs s)
    (hsame : applyPath gs s = applyPath hs s) :
    pathEnergy E gs = pathEnergy E hs := by
  rw [hess_path_energy E gs s hg, hess_path_energy E hs s hh, hsame]

/-- **Zero energy around a cycle.** A thermodynamic cycle (the path returns to its start register)
releases no net energy. -/
theorem hess_cycle_zero {n k : ℕ} (E : Fin k → ℝ)
    (gs : List (ReactionGate n k)) (s : Register k)
    (hcan : CanApplyPath gs s) (hcycle : applyPath gs s = s) :
    pathEnergy E gs = 0 := by
  rw [hess_path_energy E gs s hcan, hcycle, sub_self]

/-! ## Water synthesis: `n = 2` elements (H, O), `k = 3` species (H, O, H₂O) -/

/-- Composition matrix for the three-species water scaffold (H, O, H₂O). -/
def waterAtomsPerSpecies : Fin 3 → Fin 2 → ℕ
  | ⟨0, _⟩ => ![1, 0]
  | ⟨1, _⟩ => ![0, 1]
  | ⟨2, _⟩ => ![2, 1]
  | ⟨n + 3, h⟩ => absurd h (by omega)

/-- `2 H + O → H₂O`: consume two H and one O, produce one H₂O. -/
def waterSynthesisGate : ReactionGate 2 3 where
  atomsPerSpecies := waterAtomsPerSpecies
  consume := ![2, 1, 0]
  produce := ![0, 0, 1]

/-- The water gate conserves both H and O atoms. -/
theorem waterSynthesisGate_balanced : waterSynthesisGate.isElementBalanced := by
  unfold ReactionGate.isElementBalanced ReactionGate.balanceResidual elementResidual surplusZ
    waterSynthesisGate waterAtomsPerSpecies
  intro e
  fin_cases e <;> simp [Fin.sum_univ_three]

/-- The water reaction energy in closed form: `ΔE = E(H₂O) − 2 E(H) − E(O)`. -/
theorem waterSynthesisGate_reactionEnergy (E : Fin 3 → ℝ) :
    reactionEnergy E waterSynthesisGate.consume waterSynthesisGate.produce
      = E 2 - 2 * E 0 - E 1 := by
  unfold reactionEnergy surplusZ waterSynthesisGate
  rw [Fin.sum_univ_three]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **Exothermicity is sourced from binding, not a heat literal.** Whenever the composite well sits
below the separated-atom sum — `E(H₂O) < 2 E(H) + E(O)`, exactly what the spine binding network
delivers — water synthesis releases energy (`ΔE < 0`). No `kJ/mol` constant is injected. -/
theorem water_exothermic_of_binding (E : Fin 3 → ℝ) (hbind : E 2 < 2 * E 0 + E 1) :
    reactionEnergy E waterSynthesisGate.consume waterSynthesisGate.produce < 0 := by
  rw [waterSynthesisGate_reactionEnergy]; linarith

end HqivSpine.Chemistry.Reaction

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Molecular reaction gate scaffold

Generic **element-vector** stoichiometry: `n` element types and `k` species slots,
each species carrying a fixed composition `Fin n → ℕ`. A reaction gate specifies
integer stoichiometric coefficients `consume` / `produce` on `Fin k`, plus
geometry/temperature/heat metadata.

A concrete **water** instance (`2H + O → H₂O`) uses `n = 2` (H, O) and `k = 3`
(H, O, H₂O), with a legacy `Species` inductive for readable names.

This layer is a lightweight control scaffold for downstream wavefunction/energy
modules; balance and register evolution are proved relative to the composition
matrix (no fitted chemistry beyond the declared compositions and targets).
-/

namespace Hqiv.QuantumChemistry

open scoped BigOperators

/-- Molecular abundance register on `k` species slots. -/
abbrev MolecularRegister (k : ℕ) := Fin k → ℕ

/-- Stoichiometric surplus (products minus reactants) per species, in `ℤ`. -/
def stoichiometricSurplusZ {k : ℕ} (consume produce : Fin k → ℕ) (i : Fin k) : ℤ :=
  (produce i : ℤ) - (consume i : ℤ)

/-- Total atoms of element `e` contributed by register `s` (linear in counts). -/
def totalElementAtoms {n k : ℕ} (atomsPerSpecies : Fin k → Fin n → ℕ) (s : MolecularRegister k)
    (e : Fin n) : ℕ :=
  ∑ i : Fin k, s i * atomsPerSpecies i e

/-- Same total, packaged in `ℤ` for stoichiometric algebra. -/
def totalElementAtomsZ {n k : ℕ} (atomsPerSpecies : Fin k → Fin n → ℕ) (s : MolecularRegister k)
    (e : Fin n) : ℤ :=
  ∑ i : Fin k, (s i : ℤ) * (atomsPerSpecies i e : ℤ)

theorem totalElementAtoms_cast_eq_Z {n k : ℕ} (atomsPerSpecies : Fin k → Fin n → ℕ)
    (s : MolecularRegister k) (e : Fin n) :
    (totalElementAtoms atomsPerSpecies s e : ℤ) = totalElementAtomsZ atomsPerSpecies s e := by
  simp [totalElementAtoms, totalElementAtomsZ, Nat.cast_sum, Nat.cast_mul]

/-- Per-element stoichiometric balance residual (zero ⟺ element-wise mass balance). -/
def stoichiometricElementResidual {n k : ℕ} (atomsPerSpecies : Fin k → Fin n → ℕ) (consume produce : Fin k → ℕ)
    (e : Fin n) : ℤ :=
  ∑ i : Fin k, stoichiometricSurplusZ consume produce i * (atomsPerSpecies i e : ℤ)

/-- Generic reaction gate over `n` element types and `k` species. -/
structure ReactionGate (n k : ℕ) where
  atomsPerSpecies : Fin k → Fin n → ℕ
  consume : Fin k → ℕ
  produce : Fin k → ℕ
  targetBondAngleDeg : ℝ
  targetTemperatureK : ℝ
  heatReleased_kJmol : ℝ

namespace ReactionGate

variable {n k : ℕ}

def canApply (g : ReactionGate n k) (s : MolecularRegister k) : Prop :=
  ∀ i : Fin k, g.consume i ≤ s i

def apply (g : ReactionGate n k) (s : MolecularRegister k) : MolecularRegister k :=
  fun i => s i - g.consume i + g.produce i

def elementBalanceResidual (g : ReactionGate n k) (e : Fin n) : ℤ :=
  stoichiometricElementResidual g.atomsPerSpecies g.consume g.produce e

def isElementBalanced (g : ReactionGate n k) : Prop :=
  ∀ e : Fin n, g.elementBalanceResidual e = 0

theorem totalElementAtomsZ_apply_sub (g : ReactionGate n k) (s : MolecularRegister k)
    (hcan : g.canApply s) (e : Fin n) :
    totalElementAtomsZ g.atomsPerSpecies (g.apply s) e - totalElementAtomsZ g.atomsPerSpecies s e =
      stoichiometricElementResidual g.atomsPerSpecies g.consume g.produce e := by
  unfold ReactionGate.apply totalElementAtomsZ stoichiometricElementResidual stoichiometricSurplusZ
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

theorem apply_preserves_totalElementAtoms (g : ReactionGate n k) (s : MolecularRegister k)
    (hcan : g.canApply s) (hbal : g.isElementBalanced) (e : Fin n) :
    totalElementAtoms g.atomsPerSpecies (g.apply s) e = totalElementAtoms g.atomsPerSpecies s e := by
  have hΔ := totalElementAtomsZ_apply_sub g s hcan e
  have hz : stoichiometricElementResidual g.atomsPerSpecies g.consume g.produce e = 0 := by
    simpa [ReactionGate.elementBalanceResidual, ReactionGate.isElementBalanced] using hbal e
  have hEqZ : totalElementAtomsZ g.atomsPerSpecies (g.apply s) e = totalElementAtomsZ g.atomsPerSpecies s e := by
    rw [← sub_eq_zero, hΔ, hz]
  rw [← totalElementAtoms_cast_eq_Z, ← totalElementAtoms_cast_eq_Z] at hEqZ
  exact Nat.cast_inj.mp hEqZ

end ReactionGate

/-! ## Water chemistry: `n = 2` elements, `k = 3` species (H, O, H₂O) -/

/-- Composition matrix for the standard three-species water scaffold (H, O, H₂O). -/
def waterAtomsPerSpecies : Fin 3 → Fin 2 → ℕ
  | ⟨0, _⟩ => ![1, 0]
  | ⟨1, _⟩ => ![0, 1]
  | ⟨2, _⟩ => ![2, 1]
  | ⟨n + 3, h⟩ => False.elim (Nat.lt_asymm h (by omega))

/-- Readable species names (order matches `Fin 3` indexing: H, O, H₂O). -/
inductive Species where
  | H
  | O
  | H2O
deriving DecidableEq, Repr

def speciesToFin3 : Species → Fin 3
  | .H => ⟨0, by simp⟩
  | .O => ⟨1, by simp⟩
  | .H2O => ⟨2, by simp⟩

def fin3ToSpecies : Fin 3 → Species
  | ⟨0, _⟩ => .H
  | ⟨1, _⟩ => .O
  | ⟨2, _⟩ => .H2O
  | ⟨n + 3, h⟩ => False.elim (Nat.lt_asymm h (by omega))

theorem speciesToFin3_fin3ToSpecies (s : Species) : fin3ToSpecies (speciesToFin3 s) = s := by
  cases s <;> rfl

theorem fin3ToSpecies_speciesToFin3 (i : Fin 3) : speciesToFin3 (fin3ToSpecies i) = i := by
  fin_cases i <;> rfl

/-- Molecular count register (legacy `Species`-indexed dictionary). -/
abbrev MolecularState := Species → ℕ

def registerOfSpeciesState (s : MolecularState) : MolecularRegister 3 :=
  fun i => s (fin3ToSpecies i)

theorem registerOfSpeciesState_species (s : MolecularState) (sp : Species) :
    registerOfSpeciesState s (speciesToFin3 sp) = s sp := by
  simp [registerOfSpeciesState, speciesToFin3_fin3ToSpecies]

/-- Total H / O atoms using the explicit water scaffold composition. -/
def totalHAtoms (s : MolecularState) : ℕ :=
  s .H + 2 * s .H2O

def totalOAtoms (s : MolecularState) : ℕ :=
  s .O + s .H2O

theorem totalHAtoms_eq_element0 (s : MolecularState) :
    totalHAtoms s = totalElementAtoms waterAtomsPerSpecies (registerOfSpeciesState s) ⟨0, by simp⟩ := by
  simp [totalHAtoms, totalElementAtoms, registerOfSpeciesState, waterAtomsPerSpecies, fin3ToSpecies,
    Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Nat.mul_comm]

theorem totalOAtoms_eq_element1 (s : MolecularState) :
    totalOAtoms s = totalElementAtoms waterAtomsPerSpecies (registerOfSpeciesState s) ⟨1, by simp⟩ := by
  simp [totalOAtoms, totalElementAtoms, registerOfSpeciesState, waterAtomsPerSpecies, fin3ToSpecies,
    Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]

def waterSynthesisGate : ReactionGate 2 3 where
  atomsPerSpecies := waterAtomsPerSpecies
  consume := ![2, 1, 0]
  produce := ![0, 0, 1]
  targetBondAngleDeg := 104.5
  targetTemperatureK := 298.15
  heatReleased_kJmol := 285.8

theorem waterSynthesisGate_balanced : waterSynthesisGate.isElementBalanced := by
  unfold ReactionGate.isElementBalanced ReactionGate.elementBalanceResidual stoichiometricElementResidual
    stoichiometricSurplusZ waterSynthesisGate waterAtomsPerSpecies
  intro e
  fin_cases e <;> simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]

theorem waterSynthesisGate_geometry_target :
    waterSynthesisGate.targetBondAngleDeg = 104.5 := rfl

theorem waterSynthesisGate_temperature_target :
    waterSynthesisGate.targetTemperatureK = 298.15 := rfl

theorem waterSynthesisGate_exothermic :
    0 < waterSynthesisGate.heatReleased_kJmol := by
  norm_num [waterSynthesisGate]

def applyWaterGate (s : MolecularState) : MolecularState :=
  fun sp =>
    s sp - waterSynthesisGate.consume (speciesToFin3 sp) + waterSynthesisGate.produce (speciesToFin3 sp)

theorem registerOf_applyWaterGate (s : MolecularState) :
    registerOfSpeciesState (applyWaterGate s) = waterSynthesisGate.apply (registerOfSpeciesState s) := by
  funext i
  simp [registerOfSpeciesState, applyWaterGate, ReactionGate.apply, waterSynthesisGate]
  rw [fin3ToSpecies_speciesToFin3]

theorem waterSynthesisGate_canApply_species (s : MolecularState) :
    waterSynthesisGate.canApply (registerOfSpeciesState s) ↔
      (∀ sp : Species, waterSynthesisGate.consume (speciesToFin3 sp) ≤ s sp) := by
  constructor
  · intro h sp
    simpa [registerOfSpeciesState, speciesToFin3_fin3ToSpecies] using h (speciesToFin3 sp)
  · intro h i
    simpa [registerOfSpeciesState, fin3ToSpecies_speciesToFin3] using h (fin3ToSpecies i)

theorem waterSynthesisGate_apply_preserves_H (s : MolecularState)
    (hcan : waterSynthesisGate.canApply (registerOfSpeciesState s)) :
    totalHAtoms (applyWaterGate s) = totalHAtoms s := by
  have hp :=
    ReactionGate.apply_preserves_totalElementAtoms waterSynthesisGate (registerOfSpeciesState s) hcan
      waterSynthesisGate_balanced ⟨0, by simp⟩
  calc
    totalHAtoms (applyWaterGate s) =
        totalElementAtoms waterAtomsPerSpecies (registerOfSpeciesState (applyWaterGate s)) ⟨0, by simp⟩ :=
      totalHAtoms_eq_element0 _
    _ = totalElementAtoms waterAtomsPerSpecies (waterSynthesisGate.apply (registerOfSpeciesState s))
          ⟨0, by simp⟩ := by rw [registerOf_applyWaterGate]
    _ = totalElementAtoms waterAtomsPerSpecies (registerOfSpeciesState s) ⟨0, by simp⟩ := by
      simpa [waterSynthesisGate] using hp
    _ = totalHAtoms s := (totalHAtoms_eq_element0 s).symm

theorem waterSynthesisGate_apply_preserves_O (s : MolecularState)
    (hcan : waterSynthesisGate.canApply (registerOfSpeciesState s)) :
    totalOAtoms (applyWaterGate s) = totalOAtoms s := by
  have hp :=
    ReactionGate.apply_preserves_totalElementAtoms waterSynthesisGate (registerOfSpeciesState s) hcan
      waterSynthesisGate_balanced ⟨1, by simp⟩
  calc
    totalOAtoms (applyWaterGate s) =
        totalElementAtoms waterAtomsPerSpecies (registerOfSpeciesState (applyWaterGate s)) ⟨1, by simp⟩ :=
      totalOAtoms_eq_element1 _
    _ = totalElementAtoms waterAtomsPerSpecies (waterSynthesisGate.apply (registerOfSpeciesState s))
          ⟨1, by simp⟩ := by rw [registerOf_applyWaterGate]
    _ = totalElementAtoms waterAtomsPerSpecies (registerOfSpeciesState s) ⟨1, by simp⟩ := by
      simpa [waterSynthesisGate] using hp
    _ = totalOAtoms s := (totalOAtoms_eq_element1 s).symm

/-- Backwards-compatible name: same transition as `applyWaterGate`. -/
abbrev MolecularReactionGate := ReactionGate

end Hqiv.QuantumChemistry

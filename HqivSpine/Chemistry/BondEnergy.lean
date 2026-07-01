import HqivSpine.Chemistry.Reaction
import HqivSpine.Chemistry.ShellStructure
import Mathlib.Tactic

/-!
# `HqivSpine.Chemistry.BondEnergy` — reaction energy from spine bond orders

`Chemistry.Reaction` left the per-species energy `E` parametric and conditioned water exothermicity on
the binding ordering `E(H₂O) < 2E(H)+E(O)`. Here that ordering is **derived**, not assumed: the energy
of a species (relative to its separated atoms) is the **negative** of its total bond order times one
positive well-depth unit,

  `speciesEnergy depthUnit B i = − depthUnit · B i`,

with the bond order `B` read off the spine combiner `ShellStructure.geometricBondOrder` (the saturated
Cauchy–Schwarz coupling, capped at the triple ceiling). Substituting into `Reaction.reactionEnergy`
gives the **bond-energy balance**

  `ΔE = depthUnit · (Σ reactant bond orders − Σ product bond orders)`  (`reactionEnergy_bondEnergy`),

so a reaction is exothermic **iff it raises the total bond order** (`exothermic_of_bondOrder_increase`)
— the only premise being `depthUnit > 0`, a positivity, never a `kJ/mol` number. Because `E` is now a
genuine state function, *all* of `Reaction`'s Hess machinery applies unchanged.

As a corollary the legacy water hypothesis is discharged: a single σ-bond order is the homonuclear
`geometricBondOrder 1 1 = 1` (`singleBondOrder_eq_one`), H₂O carries two O–H bonds while the H and O
atoms carry none, so forming water strictly raises the bond order and `water_exothermic_of_binding`
fires from bonds alone (`water_exothermic_from_bondOrder`).

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Chemistry.BondEnergy

open HqivSpine.Chemistry.Reaction
open HqivSpine.Chemistry.ShellStructure (geometricBondOrder maxBondOrder)
open scoped BigOperators

noncomputable section

/-- **Species energy relative to separated atoms** = `−depthUnit · (total bond order)`. Bonds lower
the energy; a deeper composite well is more bond order. -/
def speciesEnergy {k : ℕ} (depthUnit : ℝ) (B : Fin k → ℝ) (i : Fin k) : ℝ :=
  - depthUnit * B i

/-- **Bond-energy balance (Hess + additivity).** Feeding the bond-order energy into the spine
`reactionEnergy` gives `ΔE = depthUnit · (reactant bond orders − product bond orders)`. -/
theorem reactionEnergy_bondEnergy {k : ℕ} (depthUnit : ℝ) (B : Fin k → ℝ)
    (consume produce : Fin k → ℕ) :
    reactionEnergy (speciesEnergy depthUnit B) consume produce
      = depthUnit * ((∑ i, (consume i : ℝ) * B i) - (∑ i, (produce i : ℝ) * B i)) := by
  unfold reactionEnergy speciesEnergy surplusZ
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

/-- **Exothermic ⟺ more product bonds.** With a positive well-depth unit, a reaction that raises the
total bond order releases energy (`ΔE < 0`). The premise is a positivity, not a number. -/
theorem exothermic_of_bondOrder_increase {k : ℕ} (depthUnit : ℝ) (B : Fin k → ℝ)
    (consume produce : Fin k → ℕ) (hpos : 0 < depthUnit)
    (hbonds : (∑ i, (consume i : ℝ) * B i) < (∑ i, (produce i : ℝ) * B i)) :
    reactionEnergy (speciesEnergy depthUnit B) consume produce < 0 := by
  rw [reactionEnergy_bondEnergy]
  exact mul_neg_of_pos_of_neg hpos (by linarith)

/-- **Endothermic ⟺ fewer product bonds.** Breaking net bond order costs energy (`ΔE > 0`). -/
theorem endothermic_of_bondOrder_decrease {k : ℕ} (depthUnit : ℝ) (B : Fin k → ℝ)
    (consume produce : Fin k → ℕ) (hpos : 0 < depthUnit)
    (hbonds : (∑ i, (produce i : ℝ) * B i) < (∑ i, (consume i : ℝ) * B i)) :
    0 < reactionEnergy (speciesEnergy depthUnit B) consume produce := by
  rw [reactionEnergy_bondEnergy]
  exact mul_pos hpos (by linarith)

/-- **Thermoneutral ⟺ bond order conserved.** An isomerization that preserves total bond order
releases no energy. -/
theorem thermoneutral_of_bondOrder_eq {k : ℕ} (depthUnit : ℝ) (B : Fin k → ℝ)
    (consume produce : Fin k → ℕ)
    (hbonds : (∑ i, (consume i : ℝ) * B i) = (∑ i, (produce i : ℝ) * B i)) :
    reactionEnergy (speciesEnergy depthUnit B) consume produce = 0 := by
  rw [reactionEnergy_bondEnergy, hbonds, sub_self, mul_zero]

/-! ## The single σ-bond order, and water from bonds -/

/-- A single σ-bond is the homonuclear spine bond order `geometricBondOrder 1 1` (both endpoints
offer one shared pair). -/
def singleBondOrder : ℝ := geometricBondOrder 1 1

/-- **A single bond has bond order one** — derived from the spine combiner, not posited. -/
theorem singleBondOrder_eq_one : singleBondOrder = 1 :=
  ShellStructure.geometricBondOrder_homonuclear 1 (by norm_num)
    (by rw [ShellStructure.maxBondOrder_eq_three]; norm_num)

/-- Bond-order content of the water species `(H, O, H₂O)`: the atoms carry none, H₂O carries two
O–H single bonds. -/
def waterBondOrderTotal : Fin 3 → ℝ := ![0, 0, 2 * singleBondOrder]

/-- **Water exothermicity, sourced from bonds.** Forming H₂O from atomic H and O strictly raises the
total bond order (`0 → 2`), so for any positive well-depth unit the spine `reactionEnergy` is
negative — discharging the hypothesis that `Reaction.water_exothermic_of_binding` had to assume. -/
theorem water_exothermic_from_bondOrder (depthUnit : ℝ) (hpos : 0 < depthUnit) :
    reactionEnergy (speciesEnergy depthUnit waterBondOrderTotal)
      waterSynthesisGate.consume waterSynthesisGate.produce < 0 := by
  apply Reaction.water_exothermic_of_binding
  unfold speciesEnergy waterBondOrderTotal
  simp [singleBondOrder_eq_one]
  linarith

end

end HqivSpine.Chemistry.BondEnergy

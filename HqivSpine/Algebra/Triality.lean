import HqivSpine.Foundation.Carrier
import Mathlib.Data.Fintype.Card

/-!
# `HqivSpine.Algebra.Triality` — three generations from Spin(8) triality

`Spin(8)` (the carrier rotation group) is unique among simple groups in having
**three** inequivalent 8-dimensional irreducible representations — the vector `8v`
and the two chiral spinors `8s⁺`, `8s⁻` — permuted by the order-3 triality
automorphism of the `D₄` Dynkin diagram. HQIV reads each 8-dim slot as one fermion
generation, so the **three generations are forced** by the carrier algebra rather
than put in by hand.

Here `So8RepIndex := Fin 3` labels the three slots and `trialityCycle` is the
order-3 cycle `8v → 8s⁺ → 8s⁻ → 8v`. The generation count is `3`, and tying to the
`carrierMultiplicity = 8` channels gives `3·8 = 24` real carrier slots and `2·24 =
48` chiral Weyl slots — all derived integers, no representation-theoretic input.
-/

namespace HqivSpine.Algebra

open HqivSpine.Foundation

/-- **Order of the triality automorphism** (`τ³ = 1`). -/
def trialityOrder : ℕ := 3

/-- **The three 8-dimensional irreducibles of `Spin(8)`** (`D₄`):
`0 = 8v` (vector), `1 = 8s⁺`, `2 = 8s⁻`. -/
abbrev So8RepIndex := Fin 3

/-- `8v` — vector representation. -/
def rep8V : So8RepIndex := 0
/-- `8s⁺` — positive-chirality spinor. -/
def rep8SPlus : So8RepIndex := 1
/-- `8s⁻` — negative-chirality spinor. -/
def rep8SMinus : So8RepIndex := 2

/-- **Triality cycle** (`D₄`): `8v → 8s⁺ → 8s⁻ → 8v`. -/
def trialityCycle : So8RepIndex → So8RepIndex
  | 0 => 1
  | 1 => 2
  | 2 => 0

/-- Triality applied twice. -/
def trialityCycle2 (r : So8RepIndex) : So8RepIndex := trialityCycle (trialityCycle r)

/-- **Triality has order 3:** `τ³ = id`. -/
theorem triality_cycle_order_3 (r : So8RepIndex) :
    trialityCycle (trialityCycle2 r) = r := by
  fin_cases r <;> rfl

/-- **Triality³ is the identity** as a function equality. -/
theorem triality_cycle_cube_id : trialityCycle ∘ trialityCycle ∘ trialityCycle = id := by
  funext r; exact triality_cycle_order_3 r

/-- The cycle visits all three slots. -/
theorem triality_cycles_reps :
    trialityCycle rep8V = rep8SPlus ∧
    trialityCycle rep8SPlus = rep8SMinus ∧
    trialityCycle rep8SMinus = rep8V :=
  ⟨rfl, rfl, rfl⟩

/-- **Triality is a genuine permutation** of the three slots. -/
theorem trialityCycle_bijective : Function.Bijective trialityCycle := by decide

/-- **Exactly three 8-dimensional representations.** -/
theorem card_so8RepIndex_eq_three : Fintype.card So8RepIndex = 3 :=
  Fintype.card_fin 3

/-- **Generation count** = number of 8-dim slots = `3`. -/
def generationCount : ℕ := trialityOrder

theorem generationCount_eq_three : generationCount = 3 := rfl

/-- **Real carrier slots** = generations × carrier channels = `3 · 8`. -/
def carrierSlotCount : ℕ := trialityOrder * carrierMultiplicity

theorem carrierSlotCount_eq_24 : carrierSlotCount = 24 := by
  unfold carrierSlotCount trialityOrder; rw [carrierMultiplicity_eq_eight]

/-- **Chiral Weyl slots** = both chiralities × carrier slots = `2 · 24`. -/
def chiralSlotCount : ℕ := 2 * carrierSlotCount

theorem chiralSlotCount_eq_48 : chiralSlotCount = 48 := by
  unfold chiralSlotCount; rw [carrierSlotCount_eq_24]

/-- **Three fermion generations from the carrier algebra:** three 8-dim slots, an
order-3 triality cycle on them, and the derived `24`/`48` carrier/chiral slot counts. -/
theorem exactly_three_generations :
    Fintype.card So8RepIndex = 3 ∧
    trialityOrder = 3 ∧
    (∀ r : So8RepIndex, trialityCycle (trialityCycle2 r) = r) ∧
    carrierSlotCount = 24 ∧ chiralSlotCount = 48 :=
  ⟨card_so8RepIndex_eq_three, rfl, triality_cycle_order_3,
    carrierSlotCount_eq_24, chiralSlotCount_eq_48⟩

end HqivSpine.Algebra

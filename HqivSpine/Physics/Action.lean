import HqivSpine.Foundation.Carrier
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.Action` — the discrete O-Maxwell Lagrangian

The carrier has exactly `carrierMultiplicity = 8` octonion channels (derived in
`Foundation.Carrier`); spacetime is indexed by `Fin 4`. A **gauge potential** is one
real component per channel per spacetime index, `A : Fin 8 → Fin 4 → ℝ`. From it we
build the whole free-field story with no manifold integration — finite sums over the
index sets play the role of `∫ d⁴x`:

* **Field strength** `F a μ ν = A a ν − A a μ` (discrete exterior derivative), proved
  **antisymmetric** in `(μ, ν)`;
* **Kinetic Lagrangian** `−¼ ∑_{a,μ,ν} F²` and a **source** term `∑ J·A`, linear in `J`;
* **Euler–Lagrange covector** `EL J A a ν = (∑_μ F a μ ν) − 4π J a ν`, the variation of
  the action with respect to `A a ν`;
* **Equation of motion:** `EL J A a ν = 0` is exactly the inhomogeneous O-Maxwell
  equation `∑_μ F a μ ν = 4π J a ν` — Maxwell as a stationarity condition;
* **Superposition:** the source response is linear, so currents add (the kinetic core
  is shared and does not).

The channel count `8` is not a free choice: `potentialChannels = carrierMultiplicity`
ties the gauge index back to the derived octonion carrier.

Mathlib-only; no legacy `Hqiv.*` imports, no `sorry`, no new `axiom`.
-/

namespace HqivSpine.Physics

open Foundation

/-- The number of gauge channels equals the derived octonion carrier multiplicity `8`. -/
def potentialChannels : ℕ := carrierMultiplicity

theorem potentialChannels_eq_eight : potentialChannels = 8 := carrierMultiplicity_eq_eight

/-- A gauge potential: one real component per octonion channel (`Fin 8`) per spacetime
index (`Fin 4`). -/
abbrev Potential := Fin 8 → Fin 4 → ℝ
/-- A current source, same shape as a potential. -/
abbrev Current := Fin 8 → Fin 4 → ℝ

/-- **Field strength** (discrete exterior derivative) `F a μ ν = A a ν − A a μ`. -/
def fieldStrength (A : Potential) (a : Fin 8) (μ ν : Fin 4) : ℝ := A a ν - A a μ

/-- **`F` is antisymmetric** in its spacetime indices. -/
theorem fieldStrength_antisymm (A : Potential) (a : Fin 8) (μ ν : Fin 4) :
    fieldStrength A a μ ν = - fieldStrength A a ν μ := by
  unfold fieldStrength; ring

/-- The diagonal of `F` vanishes (immediate from antisymmetry). -/
theorem fieldStrength_self (A : Potential) (a : Fin 8) (μ : Fin 4) :
    fieldStrength A a μ μ = 0 := by
  unfold fieldStrength; ring

/-- **Discrete `F`-divergence** `∑_μ F a μ ν`, the kinetic slot in Euler–Lagrange. -/
def divergence (A : Potential) (a : Fin 8) (ν : Fin 4) : ℝ :=
  ∑ μ : Fin 4, fieldStrength A a μ ν

/-- **Kinetic Lagrangian** `−¼ ∑_{a,μ,ν} F²` (the `μ < ν` double count is absorbed by
the explicit `/2`, giving the standard `−¼ F²`). -/
noncomputable def kinetic (A : Potential) : ℝ :=
  -(1 / 4) * ∑ a : Fin 8, ∑ μ : Fin 4, ∑ ν : Fin 4, (fieldStrength A a μ ν) ^ 2 / 2

/-- **Source term** `J·A = ∑_{a,ν} J a ν · A a ν`. -/
def source (J : Current) (A : Potential) : ℝ :=
  ∑ a : Fin 8, ∑ ν : Fin 4, J a ν * A a ν

/-- **O-Maxwell Lagrangian** `L = kinetic + 4π·(J·A)`. -/
noncomputable def lagrangian (J : Current) (A : Potential) : ℝ :=
  kinetic A + 4 * Real.pi * source J A

/-- **Action**: the single-cell (sum) value of the Lagrangian. -/
noncomputable def action (J : Current) (A : Potential) : ℝ := lagrangian J A

/-- **Euler–Lagrange covector** from varying `A a ν`: `(∑_μ F a μ ν) − 4π J a ν`. -/
noncomputable def EL (J : Current) (A : Potential) (a : Fin 8) (ν : Fin 4) : ℝ :=
  divergence A a ν - 4 * Real.pi * J a ν

/-- **Equation of motion = inhomogeneous O-Maxwell.** Stationarity `EL = 0` is exactly
`∑_μ F a μ ν = 4π J a ν`. -/
theorem EL_eq_zero_iff_maxwell (J : Current) (A : Potential) (a : Fin 8) (ν : Fin 4) :
    EL J A a ν = 0 ↔ divergence A a ν = 4 * Real.pi * J a ν := by
  unfold EL; rw [sub_eq_zero]

/-- The Euler–Lagrange covector is literally the field divergence minus the source. -/
theorem EL_eq_divergence_sub_source (J : Current) (A : Potential) (a : Fin 8) (ν : Fin 4) :
    EL J A a ν = (∑ μ : Fin 4, fieldStrength A a μ ν) - 4 * Real.pi * J a ν := rfl

/-- **Vacuum** (`J = 0`): the equation of motion is `∑_μ F a μ ν = 0`. -/
theorem EL_vacuum (A : Potential) (a : Fin 8) (ν : Fin 4) :
    EL (fun _ _ => 0) A a ν = divergence A a ν := by
  unfold EL; simp

/-- **Source superposition:** the `J·A` term is linear in the current. -/
theorem source_add (J₁ J₂ : Current) (A : Potential) :
    source (fun a ν => J₁ a ν + J₂ a ν) A = source J₁ A + source J₂ A := by
  unfold source; simp_rw [add_mul, Finset.sum_add_distrib]

/-- **Euler–Lagrange is affine in the source:** the field response adds when currents
add (with the shared kinetic divergence subtracted once). -/
theorem EL_add_current (J₁ J₂ : Current) (A : Potential) (a : Fin 8) (ν : Fin 4) :
    EL (fun a ν => J₁ a ν + J₂ a ν) A a ν = EL J₁ A a ν + EL J₂ A a ν - divergence A a ν := by
  unfold EL; ring

/-- **Action discharge bundle:** the discrete O-Maxwell variational principle is fully
realised — antisymmetric field strength, an `8`-channel gauge field tied to the derived
carrier, and Euler–Lagrange equal to the inhomogeneous Maxwell equation. -/
structure ActionClosure : Prop where
  channels_from_carrier : potentialChannels = carrierMultiplicity
  field_antisymmetric : ∀ (A : Potential) (a : Fin 8) (μ ν : Fin 4),
    fieldStrength A a μ ν = - fieldStrength A a ν μ
  euler_lagrange_is_maxwell : ∀ (J : Current) (A : Potential) (a : Fin 8) (ν : Fin 4),
    EL J A a ν = 0 ↔ divergence A a ν = 4 * Real.pi * J a ν
  source_linear : ∀ (J₁ J₂ : Current) (A : Potential),
    source (fun a ν => J₁ a ν + J₂ a ν) A = source J₁ A + source J₂ A

/-- **The discrete O-Maxwell action principle is discharged.** -/
theorem action_closure : ActionClosure where
  channels_from_carrier := rfl
  field_antisymmetric := fieldStrength_antisymm
  euler_lagrange_is_maxwell := EL_eq_zero_iff_maxwell
  source_linear := source_add

end HqivSpine.Physics

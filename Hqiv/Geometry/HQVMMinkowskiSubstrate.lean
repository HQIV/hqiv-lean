import Hqiv.Geometry.HQVMetric
import Hqiv.Geometry.AuxFieldRapidityNullBridge

/-!
# HQVM Minkowski limit alongside the flat 1+1 Lorentz substrate

`HQVMetric` packages the ADM lapse `N = 1 + Φ + φ t`, the time-time metric coefficient
`g_tt = -N²`, and the narrative link between φ (from `AuxiliaryField`) and **horizon phase**
via `timeAngle φ t = φ * t` (period `2π` in the formal lemmas there).

`AuxFieldRapidityNullBridge` packages **special-relativistic** 1+1 data: `minkowskiMetric11`,
`boostMatrix11 η`, and **invariance** of the pairing `minkowskiInner11` under boosts.

## What this file makes explicit

1. **Vanishing `(Φ, φ)` ⇒ `N = 1` and `g_tt = -1`:** the HQVM slice matches the usual Minkowski
   time-time normalization in that limit (`HQVM_lapse_Minkowski`, `HQVM_geometry_Minkowski` are
   already in `HQVMetric`; we restate convenient one-line corollaries).
2. **Conceptual separation:** `timeAngle` is a **cumulative slice phase** tied to φ and `t` in the
   HQVM story; **rapidity** `η` parametrizes **flat** boosts in `AuxFieldRapidityNullBridge`. We do
   **not** assert an identification `timeAngle ↔ η` (different groups / different kinematics).

## Formal gap spelled out (checklist)

### Three independent formal layers today

1. **Discrete null bookkeeping** (`Hqiv.Geometry.OctonionicLightCone` and bridges such as
   `SphericalHarmonicsBridge`): shell index `m`, `available_modes m`, `latticeSimplexCount m`, etc.
   This is **combinatorial** counting tied to the HQIV light-cone axiom. Lean does **not** yet
   equip that data with a subset of `ℝ²` or with an action of the rapidity group.

2. **HQVM lapse / auxiliary φ** (`HQVMetric`, `AuxiliaryField`): real parameters `Φ`, `φ`, time
   `t`, lapse `N = 1 + Φ + φ t`, and `timeAngle φ t = φ * t`. This fixes **how φ enters the
   time-time factor** in the chosen ADM slicing. There is **no** theorem connecting `φ` or
   `timeAngle` to `boostMatrix11` or to a Lorentz transformation on `Fin 2 → ℝ`.

3. **Flat 1+1 Lorentz geometry** (`AuxFieldRapidityNullBridge`): `minkowskiMetric11`,
   `boostMatrix11 η`, and proved **bilinear** invariance of `minkowskiInner11` under `Λ(η) *ᵥ ·`.
   Rapidity parametrizes **linear automorphisms of** `Fin 2 → ℝ`, not the shell ladder.

`OnFlatHQVMSubstrate` only yields `N = 1` and `g_tt = -1` when `Φ = φ = 0`. That aligns the
**normalization** of the time-time block with Minkowski time; it is **not** a chart or a boost law.

### What a “join frames via φ / null structure” theorem would require

**(A) Carrier and chart.** A type `S` (or a family over shells) and a map `χ : S → (Fin 2 → ℝ)`
interpreting discrete increments or phases as **tangent-like** vectors in 1+1 Minkowski space,
so that “null on the lattice” can mean `minkowskiSq11 (χ s) = 0` when that is the intended model.

**(B) Rapidity action on `S`.** A rule `β : ℝ → S → S` (rapidity acts on the discrete carrier)
such that the diagram with `χ` and `boostMatrix11` commutes, e.g.
`χ (β η s) = boostMatrix11 η *ᵥ χ s` for all `η` and `s` (or a stated weakening). Until `S`, `χ`,
and `β` are **defined**, equivariance under `boostMatrix11` is not a proposition about
`latticeSimplexCount` or `phi_of_shell`.

**(C) Transformation rule for φ.** In `HQVM_lapse`, `φ` is a **slice parameter**, not a field on
`Fin 2 → ℝ`. Any law `φ ↦ φ'_η` (scalar pullback, phase recoloring, etc.) is **extra packaging**.
Standard special relativity would use a **Lorentz scalar** law only after φ is **defined** as a
function (or section) on the spacetime modeled by the chart—not from `timeAngle φ t` alone.

**(D) Target statement (shape only).** A closure would tie (A)–(C) to a quantity built from HQIV
data (phase, weight, lapse expression) and assert invariance or equivariance under the chosen
`(χ, β, φ ↦ φ'_η)`.

Items (A)–(D) are discharged in `Hqiv.Geometry.RapidityLorentzClosure` (`rapidity_lorentz_closure_discharged`).
Spatial rotations on `Fin 3` and directional readouts (flyby `‖r×v‖²`, CMB sky rotation, fluid
gradient covariance) are discharged in `Hqiv.Geometry.SpatialRotationLorentzClosure`
(`spatial_rotation_lorentz_closure_discharged`; combined certificate `full_lorentz_closure_discharged`).
The placeholders below remain as the **named interface** that the closure modules instantiate.

**Continuum chart (flat `l²` on four indices):** `Hqiv.Geometry.ContinuumSpacetimeChart` equips
`Fin 4` with `EuclideanSpace ℝ (Fin 4)` and Mathlib `gradient` / coordinate divergence — the
Euclidean backbone for φ and vector fields before Lorentzian metric factors or discrete lattice
embeddings.

**1+1 into `Fin 4`:** `Hqiv.Geometry.SpacetimeMinkowski11Embed4` embeds 1+1 Minkowski coordinates into
`Fin 4 → ℝ`, proves agreement of the quadratic form with `minkowskiSq11` on the slice, and shows the
constant forward-null `(1,1)` direction maps to a null vector in the ambient `minkowskiSq4` signature.
-/

namespace Hqiv.Geometry

/-- HQVM lapse is unity when Newtonian and auxiliary potentials vanish (flat time-time factor). -/
theorem HQVM_lapse_one_of_vanishing (Φ φ t : ℝ) (hΦ : Φ = 0) (hφ : φ = 0) :
    HQVM_lapse Φ φ t = 1 := by
  rw [hΦ, hφ]
  exact HQVM_lapse_Minkowski t

/-- In the same slice, `g_tt = -1`. -/
theorem HQVM_g_tt_neg_one_of_vanishing (Φ φ t : ℝ) (hΦ : Φ = 0) (hφ : φ = 0) :
    HQVM_g_tt (HQVM_lapse Φ φ t) = -1 := by
  rw [HQVM_lapse_one_of_vanishing Φ φ t hΦ hφ]
  unfold HQVM_g_tt
  norm_num

/-- Predicate packaging the vanishing slice used above. -/
def OnFlatHQVMSubstrate (Φ φ : ℝ) : Prop :=
  Φ = 0 ∧ φ = 0

theorem OnFlatHQVMSubstrate_lapse_one (Φ φ t : ℝ) (h : OnFlatHQVMSubstrate Φ φ) :
    HQVM_lapse Φ φ t = 1 := by
  rcases h with ⟨hΦ, hφ⟩
  exact HQVM_lapse_one_of_vanishing Φ φ t hΦ hφ

/-!
## Signature alignment (informative)

Both `HQVM_g_tt` (with `N = 1`) and `minkowskiMetric11` use the **mostly-plus spatial** convention
for the spatial part in their respective contexts; the time-time block is **negative** in either
formalism when `N > 0` and `g_tt = -N²`. A full dimensional match (3+1 HQVM vs 1+1 SR) is not stated
as a theorem — only the **normalization** `g_tt = -1` on the vanishing slice.
-/

open scoped Matrix

/-- Embedding of a discrete (or abstract) carrier into Minkowski 1+1 coordinates (`Fin 2 → ℝ`). -/
structure Minkowski11Chart (S : Type*) where
  embed : S → Fin 2 → ℝ

/-- Pointwise nullness of chart values in the `minkowskiSq11` sense. -/
def Minkowski11Chart.Null (C : Minkowski11Chart S) : Prop :=
  ∀ s : S, minkowskiSq11 (C.embed s) = 0

/-- Candidate rapidity-induced map on the carrier (must be chosen / constructed per model). -/
abbrev DiscreteRapidityMap (S : Type*) :=
  ℝ → S → S

/-- Strong chart–boost compatibility: discrete rapidity acts by the same linear map as `Λ(η)` after embedding. -/
def Minkowski11Chart.RapidityEquivariant (C : Minkowski11Chart S) (β : DiscreteRapidityMap S) : Prop :=
  ∀ η : ℝ, ∀ s : S, C.embed (β η s) = boostMatrix11 η *ᵥ C.embed s

/-- How φ in one slicing relates to φ after rapidity η — not determined by `HQVM_lapse` alone. -/
abbrev AuxiliaryPhiBoostRule : Type :=
  ℝ → ℝ → ℝ

end Hqiv.Geometry

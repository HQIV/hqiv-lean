import Hqiv.Physics.QuarkColorCarrierGaugeScaffold
import Hqiv.Physics.FanoResonance
import Hqiv.Geometry.AuxiliaryField

/-!
# Strong color × Rindler / auxiliary “rapidity fiber” bridge (research scaffold)

`Hqiv.Physics.QuarkColorCarrierGaugeScaffold` carries the **electroweak-style** packaging on the
abstract color chart (`Fin 3 → ℂ`) and the shared complexified octonion carrier (`WeakComplexOctonionCarrier`).
This module pushes one step further: strong-sector **covariant bookkeeping** reuses, in typed form,
the **same two scalar readouts** the rest of HQIV already treats as shared **resolution** data
(lepton ladders, quark ratios, harmonic ladders, EW Gram / detuning documentation).

## The two fibers (one shell index `m : ℕ`, two horizon readouts)

1. **`strongColorRindlerFiber m`** — `rindlerDetuningShared (m : ℝ)` from `Hqiv.Physics.FanoResonance`
   (coefficient `c_rindler_shared = γ/2`). Same object that enters `detunedShellSurface` and the
   global detuning story (`Hqiv.Physics.GlobalDetuning`).

2. **`strongColorAuxPhiFiber m`** — `phi_of_shell m` from `Hqiv.Geometry.AuxiliaryField` (temperature
   ladder / homogeneous-limit φ). **Same** discrete shell index `m` as the Rindler factor.

Together, `strongColorRapidityAuxHorizonPair m` packages `(Rindler factor, φ)` as the explicit
“two horizons / one resolution” **hook** for the rapidity-fiber research line. This is **not** a
theorem that a boost matrix equals that pair; it is a **normalization bridge** so color sees the
same spine as other sectors.

## EW-style coupling dress

`colorStrongGaugeCouplingAtShell m g := g / strongColorRindlerFiber m`, then
`colorTripletCovariantTermAtShell m g G ψ` reuses `colorTripletCovariantTerm` from
`QuarkColorCarrierGaugeScaffold` with that dressed real coupling (parallel to outer-closure scale
entering couplings in the W-sector narrative).

## Certificates (proved here)

* `strongColorRindlerFiber_pos`, `strongColorAuxPhiFiber_pos` — denominators stay positive.
* `colorStrongGaugeCouplingAtShell_mul_rindler` — undo the dress (`field_simp`).
* `colorTripletCovariantTermAtShell_eq` — definitional transparency (`rfl`).

No new dynamics: definitions + small lemmas only.

## Natural follow-ons (not in this file)

1. Relate `boostMatrix11` / cumulative rapidity (`AuxFieldRapidityNullBridge`, `SpatialSliceRapidityScaffold`,
   `GlobalDetuning`) to these scalars on an explicit chart hypothesis.
2. Embed dressed color generators into `8 × 8` on `WeakComplexOctonionCarrier` (analogue of
   `weakPauliEmbed` in `WeakInComplexStructure`), using the triplet support on indices `2,3,4` from
   `QuarkColorCarrierGaugeScaffold`.
3. Connect `colorTripletCovariantTermAtShell` to resonance ratios in `QuarkMetaResonance` / lock-in
   shell `referenceM` once a parameterized coupling API is desired there.

**Integration:** import this module wherever the color covariant slot should see the shared fibers;
changes in `FanoResonance` or `AuxiliaryField` propagate automatically because these are thin aliases.
Listed in `HQIVLEAN` and `HQIVPhysics` globs in `lakefile.toml`. `QuarkColorCarrierGaugeScaffold`’s
module doc points here.
-/

namespace Hqiv.Physics

open scoped BigOperators
open Complex Finset
open Hqiv

noncomputable section

/-- Rindler detuning factor at shell `m`, reused verbatim from the Fano resonance ladder (`FanoResonance`). -/
noncomputable def strongColorRindlerFiber (m : ℕ) : ℝ :=
  rindlerDetuningShared (m : ℝ)

/-- Auxiliary field φ at the **same** shell index (`AuxiliaryField`). -/
noncomputable def strongColorAuxPhiFiber (m : ℕ) : ℝ :=
  phi_of_shell m

theorem strongColorRindlerFiber_pos (m : ℕ) : 0 < strongColorRindlerFiber m := by
  unfold strongColorRindlerFiber rindlerDetuningShared c_rindler_shared
  rw [gamma_eq_2_5]
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith

theorem strongColorAuxPhiFiber_pos (m : ℕ) : 0 < strongColorAuxPhiFiber m :=
  phi_of_shell_pos m

/-- Real coupling `g` dressed by the shared Rindler denominator at shell `m` (EW methodology: outer closure scale enters couplings). -/
noncomputable def colorStrongGaugeCouplingAtShell (m : ℕ) (g : ℝ) : ℝ :=
  g / strongColorRindlerFiber m

/-- Covariant color slot at shell `m`, using the Rindler-dressed coupling on the abstract `Fin 3` chart. -/
noncomputable def colorTripletCovariantTermAtShell (m : ℕ) (g : ℝ) (G : Fin 3 → ℂ) (ψ : Fin 3 → ℂ) :
    Fin 3 → ℂ :=
  colorTripletCovariantTerm (colorStrongGaugeCouplingAtShell m g) G ψ

theorem colorTripletCovariantTermAtShell_eq (m : ℕ) (g : ℝ) (G : Fin 3 → ℂ) (ψ : Fin 3 → ℂ) :
    colorTripletCovariantTermAtShell m g G ψ =
      colorTripletCovariantTerm (colorStrongGaugeCouplingAtShell m g) G ψ := rfl

theorem colorStrongGaugeCouplingAtShell_mul_rindler (m : ℕ) (g : ℝ) :
    colorStrongGaugeCouplingAtShell m g * strongColorRindlerFiber m = g := by
  unfold colorStrongGaugeCouplingAtShell strongColorRindlerFiber
  have hne : rindlerDetuningShared (m : ℝ) ≠ 0 := ne_of_gt (strongColorRindlerFiber_pos m)
  field_simp [hne]

/-- Scalar pair `(Rindler factor, φ)` at one resolution — explicit “two horizons / one shell” packaging hook. -/
noncomputable def strongColorRapidityAuxHorizonPair (m : ℕ) : ℝ × ℝ :=
  (strongColorRindlerFiber m, strongColorAuxPhiFiber m)

end -- noncomputable section

end Hqiv.Physics

import Hqiv.Geometry.HQVMetric
import Hqiv.Geometry.HQVMPerturbations
import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.FanoResonance
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Matrix.Basic

namespace Hqiv.Physics

open Hqiv

/-!
## M6 (roadmap): gravity readout is scalar-only at the formal HQVM interface

[`AGENTS/MASS_DERIVATION_ROADMAP.md`](../../AGENTS/MASS_DERIVATION_ROADMAP.md) — **M6 — No fundamental
graviton target**.

### Best narrative surface (fixed null lattice; time drives the clock)

**Fixed null-lattice chart:** combinatorial objects indexed by `m : ℕ` — `latticeSimplexCount`, `shellSurface`,
`detunedShellSurface`, … — are **definitions with no coordinate-time parameter**. That readout chart is
**not** rewritten as a function of `t` in Lean; observer evolution does not mutate the stars-and-bars
bookkeeping or the leading area law at fixed `m`.

**Time as the dynamical knob in this chart:** in synchronous-comoving HQVM (`HQVMetric`), the cumulative
horizon phase is `timeAngle φ t = φ * t`, and the lapse is `N = 1 + Φ + timeAngle φ t`. Along a worldline
with **fixed** `(Φ, φ)`, **all** lapse and `timeAngle` differences between coordinate times are **purely linear
in `Δt`** (`HQVM_lapse_diff_fixedPotentials`, `timeAngle_diff`). The timelike metric coefficient is
`g_tt = -N²`, so comoving proper-time normalization along the `t` coordinate line is **entirely carried by
`N(Φ, φ, t)`** — there is no separate “geodesic field” beyond this scalar clock once the potentials are
chosen (`HQVM_g_tt`, `HQVM_unit_normal_squared`).

This is **not** a full manifold geodesic theorem (no affine connection API here); it is the precise
**formal surface** matching “null lattice fixed; time responsible for the geodesic / clock normalization in
this gauge.”

---

This file does **not** prove a metaphysical “gravitons do not exist” theorem for full quantum gravity.
It packages what is **already enforced by the Lean definitions** in `HQVMetric` / `HQVMPerturbations`:

1. **No hidden parameters:** `HQVM_lapse` is exactly `Φ, φ, t ↦ 1 + Φ + φ * t`. First-order clock /
   lapse response uses only `δΦ`, `δφ`, `δt` via `linearizedHQVM_lapse`.
2. **Single scalar branch for `g_tt` at linear order:** `linearizedHQVM_g_tt_from_lapse` depends on one
   scalar increment `δN` (itself determined by the three partial derivatives of the lapse). There is **no**
   `Fin 2`-style polarization index in these definitions.
3. **Formal “tensor graviton” polarization slot:** we expose `HQIVFormalGravitonPolarizationIdx := Fin 0`,
   which is **uninhabited** (`Fin.elim0`). This matches the perturbation API: no spin-2 polarization
   bookkeeping is adjoined alongside the lapse pipeline.
4. **Disjoint from matrix gauge carriers (types, not Hilbert space):** SM / SO(8) bookkeeping in this
   repository uses finite-dimensional **matrices** (see `SMGaugeCarrierMat8` below). The gravity sector’s
   lapse **values** are real **scalars** `ℝ`. No Lean definition in the HQVM metric files identifies a lapse
   with a matrix carrier or adjoins a graviton polarization index to the Lie-algebra matrix package —
   only coefficient-level unification (`φ`, `α`) is shared downstream (`SM_GR_Unification`, `GRFromMaxwell`).

This module only isolates the **metric readout** interface.
-/

/-- Typical finite-dimensional carrier shape for octonionic / SO(8) generator bookkeeping (`8 × 8`). -/
abbrev SMGaugeCarrierMat8 := Matrix (Fin 8) (Fin 8) ℝ

/-- Tuple of the three real arguments that **exhaust** the `HQVM_lapse` API. -/
abbrev HQVMGravityLapseArgumentTuple := ℝ × ℝ × ℝ

theorem HQVM_lapse_eq_tuple (p : HQVMGravityLapseArgumentTuple) :
    HQVM_lapse p.1 p.2.1 p.2.2 = 1 + p.1 + p.2.1 * p.2.2 := rfl

/-- First-order lapse increment uses only the three declared differentials (no extra slot). -/
theorem linearizedHQVM_lapse_eq_components (φ t δΦ δφ δt : ℝ) :
    linearizedHQVM_lapse φ t δΦ δφ δt = δΦ + φ * δt + t * δφ := rfl

/-- Linearized `g_tt` response is determined by **one** scalar `δN` given background lapse `N`. -/
theorem linearizedHQVM_g_tt_depends_on_scalar_deltaN (N δN : ℝ) :
    linearizedHQVM_g_tt_from_lapse N δN = -2 * N * δN := rfl

/-- Would-be spin-2 polarization indices at the HQIV perturbation layer: **none** (`Fin 0`). -/
abbrev HQIVFormalGravitonPolarizationIdx := Fin 0

theorem HQIVFormalGravitonPolarizationIdx_elim (i : HQIVFormalGravitonPolarizationIdx) : False :=
  i.elim0

/-! ## Fixed null lattice vs flowing observer time -/

theorem latticeSimplexCount_constant_in_observerTime (m : ℕ) (t t' : ℝ) :
    (fun _ : ℝ => latticeSimplexCount m) t = (fun _ : ℝ => latticeSimplexCount m) t' := rfl

theorem shellSurface_constant_in_observerTime (m : ℕ) (t t' : ℝ) :
    (fun _ : ℝ => shellSurface m) t = (fun _ : ℝ => shellSurface m) t' := rfl

theorem detunedShellSurface_constant_in_observerTime (m : ℕ) (t t' : ℝ) :
    (fun _ : ℝ => detunedShellSurface m) t = (fun _ : ℝ => detunedShellSurface m) t' := rfl

/-! ## Time drives lapse / horizon phase when potentials are fixed (comoving-clock surface) -/

theorem timeAngle_diff (φ : ℝ) (t₀ t₁ : ℝ) :
    timeAngle φ t₁ - timeAngle φ t₀ = φ * (t₁ - t₀) := by
  unfold timeAngle
  ring

theorem HQVM_lapse_diff_fixedPotentials (Φ φ : ℝ) (t₀ t₁ : ℝ) :
    HQVM_lapse Φ φ t₁ - HQVM_lapse Φ φ t₀ = φ * (t₁ - t₀) := by
  unfold HQVM_lapse
  ring

theorem HQVM_lapse_affine_in_coordinateTime (Φ φ : ℝ) :
    (fun t => HQVM_lapse Φ φ t) = fun t => 1 + Φ + φ * t := rfl

/-- `g_tt` along the time coordinate is `-N²` with `N = HQVM_lapse …`; no extra timelike slot. -/
theorem HQVM_g_tt_eq_neg_sq_lapse (Φ φ t : ℝ) :
    HQVM_g_tt (HQVM_lapse Φ φ t) = -(HQVM_lapse Φ φ t) ^ 2 := rfl

end Hqiv.Physics

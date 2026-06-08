import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv

import Hqiv.Geometry.HQVMetric
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Physics.Forces

namespace Hqiv

/-!
# Observer-centric linear response (lapse sector) — not a replay of GR perturbation theory

**Agent roadmap:** [AGENTS/HQIV_PERTURBATION_THEORY_ROADMAP.md](../../AGENTS/HQIV_PERTURBATION_THEORY_ROADMAP.md) (honest scope, milestones P0–P5, shell-indexed bridge in `Hqiv.Physics.HQIVPerturbationScaffold`). For **M6** (scalar-only gravity readout / no formal spin-2 carrier slot at this API), see `Hqiv.Physics.HQIVGravityReadoutScalars` and [`AGENTS/MASS_DERIVATION_ROADMAP.md`](../../AGENTS/MASS_DERIVATION_ROADMAP.md).

The goal here is **not** to reconstruct the standard pipeline (Bardeen potentials, synchronous vs
Newtonian gauge, `Φ`/`Ψ`, matter transfer functions, etc.). HQIV is **observer-centric**: the
informational-energy route fixes the ADM lapse in comoving gauge (`HQVM_lapse` in `HQVMetric`), and
many steps that assume a global foliation or translation-invariant background are **deliberately
out of scope** until they are re-derived from the same axiom base.

Just as importantly, this file does **not** posit a physically fundamental **sub-Planck continuum**.
The discrete null lattice and shell ladder remain the UV bookkeeping substrate. The calculus here is an
IR / observer-side readout layer: derivatives and linearizations organize how finite shell data is seen
by relativistic observers, not a claim that geometry below the lattice cutoff is a primitive smooth
manifold in the HQIV ontology.

What we **do** formalize is the **foundational** first-order response of that lapse to small changes
in the arguments that already appear in the axioms: `Φ`, `φ`, coordinate time `t`, and — when φ is
identified with the temperature ladder — `Θ` via `phi_of_T`. That is “close” to textbook
perturbation language only in the narrow sense of **linearized lapse / clock rate**; it is **not**
claimed to match the full GR perturbation spectrum.

Concretely: from `N = 1 + Φ + φ t` and real analyticity (`analyticOnNhd_HQVM_lapseTuple` in
`HQVMetricAnalytic`) we get the unique first-order piece `δN = δΦ + φ δt + t δφ`, an explicit
quadratic remainder in `(δφ, δt)`, and exact increments for `phi_of_T` (`phi_of_shell_eq_phi_of_T`
bridges discrete shells to the continuous `Θ` picture).

Collective **plasma** bookkeeping (lapse × schematic current, uniform proxy coordinates, flat-φ link
to the O-Maxwell source) lives in `Hqiv.Physics.SchematicPlasmaCurrent` (`linearisedScalarPerturbation`,
`emergentMaxwell_plasma_uniform_t_flat_phi`).

**Uncertainty as driver (no extra axioms):** the same energy–time scale `τ = ħ/ΔE` used for resonance
width in `Hqiv.Physics.SpinStatistics` (`resonance_lifetime`, MeV units) is mirrored here in SI via
`hbar_SI` from `Forces` as `energyTimeResolutionScale`. That fixes a **minimal time resolution** at a
chosen energy increment `ΔE`. Separately, `ObserverChart` matches `Schrodinger.Position` so the spatial
**domain** of perturbations is the same ℝ³ chart the QM skeleton already uses; refinement to shells
or balls is then geometric, not axiomatic. Lapse response to ladder temperature drift is packaged in
`linearizedLapse_from_Theta` using `deriv phi_of_T` from the existing `phi_of_T` definition.

Axis-aligned **finite-difference** Laplacian scaffolding on this same chart (independent of the QM
Laplacian placeholder in `Schrodinger`) lives in `Hqiv.Geometry.HQVMDiscreteLaplacian`. Lebesgue
volume means on `observerBall` (global–local bookkeeping toward homogeneous backgrounds) are in
`Hqiv.Geometry.HQVMGlobalLocalDictionary`.
-/

section LapseLinearization

/-- First-order lapse perturbation: differential of `N = 1 + Φ + φ t` (no explicit dependence on the background `Φ` at linear order beyond `δΦ`). -/
noncomputable def linearizedHQVM_lapse (φ t δΦ δφ δt : ℝ) : ℝ :=
  δΦ + φ * δt + t * δφ

/-- Partial derivative of the lapse w.r.t. `Φ` is `1`. -/
theorem deriv_HQVM_lapse_wrt_Phi (φ t Φ₀ : ℝ) :
    deriv (fun Φ => HQVM_lapse Φ φ t) Φ₀ = 1 := by
  have hf : (fun Φ => HQVM_lapse Φ φ t) = fun Φ => Φ + (1 + φ * t) := by
    funext Φ
    simp [HQVM_lapse]; ring
  rw [hf, deriv_add_const]
  simp [deriv_id'']

/-- Partial derivative of the lapse w.r.t. `φ` is `t`. -/
theorem deriv_HQVM_lapse_wrt_phi (Φ t φ₀ : ℝ) :
    deriv (fun φ => HQVM_lapse Φ φ t) φ₀ = t := by
  have h : (fun φ => HQVM_lapse Φ φ t) = fun φ => (1 + Φ) + t * φ := by
    funext φ
    simp [HQVM_lapse]
    ring
  rw [h, deriv_const_add, deriv_const_mul_field]
  simp [deriv_id'']

/-- Partial derivative of the lapse w.r.t. `t` is `φ`. -/
theorem deriv_HQVM_lapse_wrt_t (Φ φ t₀ : ℝ) :
    deriv (fun t => HQVM_lapse Φ φ t) t₀ = φ := by
  have h : (fun t => HQVM_lapse Φ φ t) = fun t => (1 + Φ) + φ * t := by
    funext t; simp [HQVM_lapse]
  rw [h, deriv_const_add, deriv_const_mul_field]
  simp [deriv_id'']

/-- Exact finite increment; remainder beyond `linearizedHQVM_lapse` is the single bilinear `δφ δt`. -/
theorem HQVM_lapse_increment_eq (Φ φ t δΦ δφ δt : ℝ) :
    HQVM_lapse (Φ + δΦ) (φ + δφ) (t + δt) - HQVM_lapse Φ φ t =
      linearizedHQVM_lapse φ t δΦ δφ δt + δφ * δt := by
  unfold HQVM_lapse linearizedHQVM_lapse
  ring

/-!
### Homogeneous background vs lapse perturbations (CLASS-oriented bookkeeping)

Volume-averaged or patchwise codes typically hold a **background** `(Φ_bg, φ_bg, t)` and add small
increments `(δΦ, δφ, δt)`. For the HQVM homogeneous slice `Φ_bg = 0`, `φ_bg = H`,
`HQVM_lapse_homogeneous_limit` gives `N_bg = 1 + H t`. The **exact** nonlinear remainder in the lapse
increment is the single bilinear term `δφ * δt` already isolated in `HQVM_lapse_increment_eq`; the
first-order piece is `linearizedHQVM_lapse`. This does **not** assert equivalence with CLASS’s full
Boltzmann/gauge system — only the lapse algebra implied by `HQVM_lapse`.
-/

/-- Same increment identity as `HQVM_lapse_increment_eq`, specialized to `Φ = 0` (homogeneous Newtonian
potential) and background expansion rate `φ = H`, written with `δΦ` as the first argument so it
matches “perturbed Φ” notation directly. -/
theorem HQVM_lapse_increment_homogeneous (H t δΦ δφ δt : ℝ) :
    HQVM_lapse δΦ (H + δφ) (t + δt) - HQVM_lapse 0 H t =
      linearizedHQVM_lapse H t δΦ δφ δt + δφ * δt := by
  simpa [zero_add] using HQVM_lapse_increment_eq 0 H t δΦ δφ δt

end LapseLinearization

section MetricCoefficientLinearization

/-- First-order change in the timelike metric coefficient induced by a lapse increment `δN`.

Since `g_tt = -N^2`, the linearized part is `-2 N δN`. This is the narrow
observer-centric metric readout used here; it is not a full curvature tensor.
-/
noncomputable def linearizedHQVM_g_tt_from_lapse (N δN : ℝ) : ℝ :=
  -2 * N * δN

/-- Exact `g_tt` increment is linearized piece plus the quadratic remainder `-δN^2`. -/
theorem HQVM_g_tt_increment_eq_linearized_remainder (N δN : ℝ) :
    HQVM_g_tt (N + δN) - HQVM_g_tt N =
      linearizedHQVM_g_tt_from_lapse N δN - δN ^ 2 := by
  unfold HQVM_g_tt linearizedHQVM_g_tt_from_lapse
  ring

/-- Same metric-coefficient identity, written with an exact lapse increment `ΔN`. -/
theorem HQVM_g_tt_increment_eq_of_lapse_increment (N N' : ℝ) :
    HQVM_g_tt N' - HQVM_g_tt N =
      linearizedHQVM_g_tt_from_lapse N (N' - N) - (N' - N) ^ 2 := by
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    HQVM_g_tt_increment_eq_linearized_remainder N (N' - N)

end MetricCoefficientLinearization

section PhiOfTIncrement

/-- Exact increment of `phi_of_T` between two nonzero temperatures. -/
theorem phi_of_T_increment (Θ δΘ : ℝ) (hΘ : Θ ≠ 0) (hΘ' : Θ + δΘ ≠ 0) :
    phi_of_T (Θ + δΘ) - phi_of_T Θ =
      -phiTemperatureCoeff * δΘ / (Θ * (Θ + δΘ)) := by
  unfold phi_of_T
  field_simp [hΘ, hΘ']
  ring

/-- First-order coefficient in `δΘ` (formal derivative `∂phi_of_T/∂Θ = -2/Θ²` at `Θ ≠ 0`). -/
theorem deriv_phi_of_T (Θ : ℝ) (hΘ : Θ ≠ 0) :
    deriv phi_of_T Θ = -phiTemperatureCoeff / Θ ^ 2 := by
  unfold phi_of_T
  have hf : (fun t => phiTemperatureCoeff / t) = fun t => phiTemperatureCoeff * t⁻¹ := by
    funext t; rw [div_eq_mul_inv]
  rw [hf, deriv_const_mul_field phiTemperatureCoeff, deriv_inv]
  field_simp [pow_ne_zero 2 hΘ]

end PhiOfTIncrement

section UncertaintyDrivenScales

/-!
### Energy–time resolution and observer spatial chart

We do **not** posit a new Heisenberg inequality as an axiom. We **define** the usual
energy–time resolution scale `τ = ħ/ΔE` (SI joules for `ΔE`, seconds for `τ` up to the
convention baked into `hbar_SI`). Positivity is pure algebra once `ΔE > 0`.

The **spatial domain** is fixed to the same `Fin 3 → ℝ` chart already used for wavefunctions
(`Position` in `Hqiv.QuantumMechanics.Schrodinger`). Open balls in that chart are the natural sets on which to state
later PDE-localized perturbations when the Laplacian placeholder is upgraded.
-/

open Real

/-- SI energy–time resolution scale `τ = ħ/ΔE` (`hbar_SI` from `Forces`).

Same functional form as `Hqiv.Physics.SpinStatistics.resonance_lifetime` (MeV width there);
here `ΔE` is understood in the SI energy unit consistent with `hbar_SI`. -/
noncomputable def energyTimeResolutionScale (ΔE : ℝ) : ℝ :=
  hbar_SI / ΔE

theorem energyTimeResolutionScale_pos {ΔE : ℝ} (hΔ : 0 < ΔE) : 0 < energyTimeResolutionScale ΔE := by
  unfold energyTimeResolutionScale hbar_SI
  exact div_pos (by norm_num) hΔ

/-- A coordinate-time increment `δt` is **sub-resolution** for an energy scale `ΔE` if its magnitude
is smaller than `energyTimeResolutionScale ΔE`. -/
def timeIncrementSubResolution (δt ΔE : ℝ) : Prop :=
  |δt| < energyTimeResolutionScale ΔE

/-- Continuum spatial chart for an observer, aligned with `Hqiv.Position` from `Schrodinger`. -/
abbrev ObserverChart := Fin 3 → ℝ

noncomputable def observerDistSq (x y : ObserverChart) : ℝ :=
  (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2

/-- Open ball of squared-radius `R²` in the observer chart (avoids `sqrt` in the predicate). -/
def observerBall (center : ObserverChart) (R : ℝ) : Set ObserverChart :=
  { x | observerDistSq x center < R ^ 2 }

theorem observerBall_center_mem {center : ObserverChart} {R : ℝ} (hR : 0 < R) :
    center ∈ observerBall center R := by
  simp [observerBall, observerDistSq]
  nlinarith [sq_pos_of_pos hR]

theorem observerBall_mono_radius {center : ObserverChart} {R₁ R₂ : ℝ}
    (hR1 : 0 ≤ R₁) (hle : R₁ ≤ R₂) : observerBall center R₁ ⊆ observerBall center R₂ := by
  intro x hx
  simp [observerBall, observerDistSq] at hx ⊢
  have hsq : R₁ ^ 2 ≤ R₂ ^ 2 := by nlinarith [sq_nonneg R₁, sq_nonneg R₂, hR1, hle]
  linarith [hx, hsq]

end UncertaintyDrivenScales

section LapseFromThetaLinearization

/-- First-order lapse response to a temperature perturbation `δΘ` through the ladder only:
`N = 1 + Φ + φ t` with `φ` identified as `phi_of_T Θ` gives `δN ≈ t * δφ`, and
`δφ ≈ (∂_Θ phi_of_T)(Θ) · δΘ` in the linear regime. Background `Φ` does not enter at linear order.

This packaging is algebraically valid for any `Θ`, but the concrete derivative formula for
`phi_of_T` only holds on the nonzero-temperature domain recorded in `deriv_phi_of_T`. -/
noncomputable def linearizedLapse_from_Theta (Θ t δΘ : ℝ) : ℝ :=
  t * (deriv phi_of_T Θ * δΘ)

theorem linearizedLapse_from_Theta_eq (Θ t δΘ : ℝ) :
    linearizedLapse_from_Theta Θ t δΘ = t * (deriv phi_of_T Θ) * δΘ := by
  simp [linearizedLapse_from_Theta]
  rw [← mul_assoc t (deriv phi_of_T Θ) δΘ]

/-- Nonzero-domain form of `linearizedLapse_from_Theta_eq`, using the explicit derivative of `phi_of_T`. -/
theorem linearizedLapse_from_Theta_eq_onDomain (Θ t δΘ : ℝ) (hΘ : Θ ≠ 0) :
    linearizedLapse_from_Theta Θ t δΘ = t * (-phiTemperatureCoeff / Θ ^ 2) * δΘ := by
  rw [linearizedLapse_from_Theta_eq, deriv_phi_of_T Θ hΘ]

/-- Pure `φ`-channel piece of `linearizedHQVM_lapse` (no change in `Φ` or `t`). -/
theorem linearizedHQVM_lapse_phi_channel (φ t δφ : ℝ) :
    linearizedHQVM_lapse φ t 0 δφ 0 = t * δφ := by
  simp [linearizedHQVM_lapse]

/-- Linearized lapse from `Θ` matches the `φ`-channel formula when `δφ` is the derivative-weighted
    increment (formal product `deriv phi_of_T Θ * δΘ`). -/
theorem linearizedLapse_from_Theta_eq_phi_channel (Θ t δΘ : ℝ) :
    linearizedLapse_from_Theta Θ t δΘ =
      linearizedHQVM_lapse (phi_of_T Θ) t 0 (deriv phi_of_T Θ * δΘ) 0 := by
  rw [linearizedHQVM_lapse_phi_channel, linearizedLapse_from_Theta_eq Θ t δΘ]
  rw [mul_assoc t (deriv phi_of_T Θ) δΘ]

/-- Nonzero-domain `Θ`-channel identification with the explicit `phi_of_T` slope inserted. -/
theorem linearizedLapse_from_Theta_eq_phi_channel_onDomain (Θ t δΘ : ℝ) (hΘ : Θ ≠ 0) :
    linearizedLapse_from_Theta Θ t δΘ =
      linearizedHQVM_lapse (phi_of_T Θ) t 0 ((-phiTemperatureCoeff / Θ ^ 2) * δΘ) 0 := by
  rw [linearizedHQVM_lapse_phi_channel, linearizedLapse_from_Theta_eq_onDomain Θ t δΘ hΘ]
  ring

end LapseFromThetaLinearization

end Hqiv

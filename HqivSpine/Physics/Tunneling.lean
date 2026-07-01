import HqivSpine.Physics.Shell
import HqivSpine.Physics.Blackbody
import HqivSpine.Geometry.DiscreteLaplacian
import HqivSpine.Chemistry.Binding
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# `HqivSpine.Physics.Tunneling` — 3D quantum tunneling on the spine null-lattice stencil

A clean, Mathlib-only restatement of quantum tunneling, built directly on the spine's own
discrete Laplacian `HqivSpine.Geometry.HQVM_discreteLaplacian` (the axis-aligned 7-point stencil
on `ObserverChart = Fin 3 → ℝ`). **Spine-native units throughout**: `ħ ≡ 1` (Planck units), so it
never appears; reduced masses `μ` and energies are in Hartree exactly as
`Chemistry.LineSpectra` / `Chemistry.Binding` already use them; and the canonical lock-in step is
the proton-shell frequency tag `lockInCellStep = 1/(referenceM+1) = 1/5`. No `hbar`, no SI
constant, no PDG input, no continuum Laplacian; no legacy `Hqiv.*`, no `sorry`, no new `axiom`,
no `native_decide`.

## Physical picture (proper 3D, separable)

Inside a classically forbidden slab (constant potential `V₀ > E`), a stationary state of energy `E`
factorizes into *transverse propagating* plane waves along the two in-slab axes and a *longitudinal
evanescent* profile `cosh(κ x₀)` along the barrier-normal axis:

`ψ(x) = cosh(κ x₀) · cos(k₁ x₁) · cos(k₂ x₂)`  (`evanescentSlabMode`).

Because the discrete Laplacian is a **sum of one-axis second differences**, it acts on this product
additively, giving the discrete tunneling dispersion `Δ_h ψ = slabDispersion · ψ`. The discrete
Schrödinger equation `−(1/2μ) Δ_h ψ + V₀ ψ = E ψ` (ħ ≡ 1) fixes the longitudinal decay rate via
`longitudinalEigenFactor κ h = 2μ(V₀ − E) + transverseEigenCost k₁ k₂ h`.

## What is proved

* **Discrete dispersion** (`discreteLaplacian_evanescentSlabMode`, `slabDispersion_split`) and the
  **stationary-state construction** (`evanescentSlabMode_stationary_of_dispersion`).
* **Genuine evanescence**: in the forbidden region `cosh(κh) > 1` so `κ ≠ 0`
  (`evanescentSlabMode_genuinely_evanescent`).
* **The 3D coupling**: transverse momentum suppresses tunneling
  (`transverse_momentum_suppresses_transmission`), absent in 1D
  (`transverseEigenCost_zero`).
* **Bulk continuity**: exact lattice-sinc dispersion, continuity / translation / SO(2) rotation.
* **Textbook parity**: exact rectangular barrier, `T + R = 1`, energy/width monotonicity, Gamow
  half-life, and the `h → 0` continuum limit (`tendsto_longitudinalEigenFactor`).
* **Advanced**: WKB Gamow sum (additive/multiplicative), Breit–Wigner resonance, STM current,
  Fowler–Nordheim emission, Hartman traversal time.
* **Chemistry layer** (the point of the module): kinetic isotope effect / proton tunneling,
  double-well proton transfer & ammonia inversion, STM imaging of allotropes, field-emission
  ionization tied to `Chemistry.Binding`, and sub-barrier reaction crossing.

**Continuum status.** The continuum forms `Δ ψ = κ² ψ`, `ψ ∼ e^{−κ x}`, and the WKB suppression
`T ∼ exp(−2 ∫ κ dx)` are *approximations to* these discrete statements; the proved object is the
discrete stencil identity at the lock-in step.
-/

namespace HqivSpine.Physics

open Real Filter Topology
open HqivSpine.Geometry

/-! ## The lock-in cell step (the one derived discrete datum, spine-native, ħ ≡ 1)

In the HQIV ontology only the **shell / horizon index** is quantized, so the *single discrete datum*
of the whole tunneling layer is the lattice step `h`.  It is **derived, not posited**: it is the
proton-shell frequency tag `ω_{referenceM} = 1/(referenceM+1)` already living in `Physics.Blackbody`,
with `referenceM = 4` the lock-in shell.  Everything else (rate, barrier height, masses, widths, …)
is a continuous bulk input — see the provenance ledger at the end of the file. -/

/-- Canonical lock-in lattice step = the proton-shell frequency tag `ω_{referenceM} =
1/(referenceM+1)`. Spine-native; no SI step, no `hbar`. -/
noncomputable def lockInCellStep : ℝ := 1 / ((referenceM : ℝ) + 1)

/-- **The lock-in step is the spine's own proton-shell frequency tag** — it is `shellOmega
referenceM` from `Physics.Blackbody`, not a new constant.  This is the sense in which the single
discrete datum is *derived*. -/
theorem lockInCellStep_eq_shellOmega : lockInCellStep = shellOmega referenceM := rfl

theorem lockInCellStep_eq : lockInCellStep = 1 / 5 := by
  unfold lockInCellStep referenceM; norm_num

theorem lockInCellStep_pos : 0 < lockInCellStep := by
  rw [lockInCellStep_eq]; norm_num

/-! ## The 3D evanescent slab mode and its discrete dispersion -/

/-- Transverse-propagating × longitudinal-evanescent product mode on the observer chart:
`cosh(κ x₀)` (barrier-normal, evanescent) times `cos(k₁ x₁) cos(k₂ x₂)` (in-slab, propagating). -/
noncomputable def evanescentSlabMode (κ k₁ k₂ : ℝ) (x : ObserverChart) : ℝ :=
  Real.cosh (κ * x 0) * Real.cos (k₁ * x 1) * Real.cos (k₂ * x 2)

/-- Discrete tunneling dispersion symbol: the discrete-Laplacian eigenvalue of the slab mode. -/
noncomputable def slabDispersion (κ k₁ k₂ h : ℝ) : ℝ :=
  (2 * (Real.cosh (κ * h) - 1) + 2 * (Real.cos (k₁ * h) - 1)
    + 2 * (Real.cos (k₂ * h) - 1)) / h ^ 2

/-- Longitudinal (barrier-normal) evanescent eigenfactor `2(cosh κh − 1)/h²`. -/
noncomputable def longitudinalEigenFactor (κ h : ℝ) : ℝ :=
  2 * (Real.cosh (κ * h) - 1) / h ^ 2

/-- Transverse kinetic cost `[2(1 − cos k₁h) + 2(1 − cos k₂h)]/h²`. Always `≥ 0`. -/
noncomputable def transverseEigenCost (k₁ k₂ h : ℝ) : ℝ :=
  (2 * (1 - Real.cos (k₁ * h)) + 2 * (1 - Real.cos (k₂ * h))) / h ^ 2

theorem slabDispersion_split (κ k₁ k₂ h : ℝ) :
    slabDispersion κ k₁ k₂ h
      = longitudinalEigenFactor κ h - transverseEigenCost k₁ k₂ h := by
  unfold slabDispersion longitudinalEigenFactor transverseEigenCost
  ring

/-- Slab mode evaluated after a shift `s` along the barrier-normal axis `0`. -/
private theorem slab_shift0 (κ k₁ k₂ s : ℝ) (x : ObserverChart) :
    evanescentSlabMode κ k₁ k₂ (HQVM_axisShift x 0 s)
      = Real.cosh (κ * (x 0 + s)) * Real.cos (k₁ * x 1) * Real.cos (k₂ * x 2) := by
  unfold evanescentSlabMode
  rw [HQVM_axisShift_apply_same x 0 s,
      HQVM_axisShift_apply_of_ne (x := x) (i := (0 : Fin 3)) (i₀ := 1) s (by decide),
      HQVM_axisShift_apply_of_ne (x := x) (i := (0 : Fin 3)) (i₀ := 2) s (by decide)]

/-- Slab mode evaluated after a shift `s` along the transverse axis `1`. -/
private theorem slab_shift1 (κ k₁ k₂ s : ℝ) (x : ObserverChart) :
    evanescentSlabMode κ k₁ k₂ (HQVM_axisShift x 1 s)
      = Real.cosh (κ * x 0) * Real.cos (k₁ * (x 1 + s)) * Real.cos (k₂ * x 2) := by
  unfold evanescentSlabMode
  rw [HQVM_axisShift_apply_same x 1 s,
      HQVM_axisShift_apply_of_ne (x := x) (i := (1 : Fin 3)) (i₀ := 0) s (by decide),
      HQVM_axisShift_apply_of_ne (x := x) (i := (1 : Fin 3)) (i₀ := 2) s (by decide)]

/-- Slab mode evaluated after a shift `s` along the transverse axis `2`. -/
private theorem slab_shift2 (κ k₁ k₂ s : ℝ) (x : ObserverChart) :
    evanescentSlabMode κ k₁ k₂ (HQVM_axisShift x 2 s)
      = Real.cosh (κ * x 0) * Real.cos (k₁ * x 1) * Real.cos (k₂ * (x 2 + s)) := by
  unfold evanescentSlabMode
  rw [HQVM_axisShift_apply_same x 2 s,
      HQVM_axisShift_apply_of_ne (x := x) (i := (2 : Fin 3)) (i₀ := 0) s (by decide),
      HQVM_axisShift_apply_of_ne (x := x) (i := (2 : Fin 3)) (i₀ := 1) s (by decide)]

/-- The raw 7-point stencil sum on the slab mode factorizes as `(eigen-coefficient) · ψ(x)`. -/
private theorem slab_rawSum (κ k₁ k₂ h : ℝ) (x : ObserverChart) :
    HQVM_rawSecondDiff_sum h (evanescentSlabMode κ k₁ k₂) x
      = (2 * (Real.cosh (κ * h) - 1) + 2 * (Real.cos (k₁ * h) - 1)
          + 2 * (Real.cos (k₂ * h) - 1)) * evanescentSlabMode κ k₁ k₂ x := by
  unfold HQVM_rawSecondDiff_sum
  rw [Fin.sum_univ_three]
  unfold HQVM_rawSecondDiffAlong
  rw [slab_shift0 κ k₁ k₂ h x, slab_shift0 κ k₁ k₂ (-h) x,
      slab_shift1 κ k₁ k₂ h x, slab_shift1 κ k₁ k₂ (-h) x,
      slab_shift2 κ k₁ k₂ h x, slab_shift2 κ k₁ k₂ (-h) x]
  unfold evanescentSlabMode
  rw [show κ * (x 0 + h) = κ * x 0 + κ * h from by ring,
      show κ * (x 0 + -h) = κ * x 0 - κ * h from by ring,
      show k₁ * (x 1 + h) = k₁ * x 1 + k₁ * h from by ring,
      show k₁ * (x 1 + -h) = k₁ * x 1 - k₁ * h from by ring,
      show k₂ * (x 2 + h) = k₂ * x 2 + k₂ * h from by ring,
      show k₂ * (x 2 + -h) = k₂ * x 2 - k₂ * h from by ring]
  simp only [Real.cosh_add, Real.cosh_sub, Real.cos_add, Real.cos_sub]
  ring

/-- **Discrete 3D tunneling dispersion.**  The evanescent slab mode is an eigenfunction of the
patch discrete Laplacian, with eigenvalue `slabDispersion`. -/
theorem discreteLaplacian_evanescentSlabMode (κ k₁ k₂ h : ℝ) (x : ObserverChart) :
    HQVM_discreteLaplacian h (evanescentSlabMode κ k₁ k₂) x
      = slabDispersion κ k₁ k₂ h * evanescentSlabMode κ k₁ k₂ x := by
  unfold HQVM_discreteLaplacian slabDispersion
  rw [slab_rawSum]
  ring

/-! ## Forbidden-region decay rate -/

/-- Classical-turning decay rate `κ = √(2μ(V−E))` for the barrier interior (Planck units, ħ ≡ 1). -/
noncomputable def kappaForbidden (μ E V : ℝ) : ℝ :=
  Real.sqrt (2 * μ * (V - E))

theorem kappaForbidden_pos (μ E V : ℝ) (hμ : 0 < μ) (hb : E < V) :
    0 < kappaForbidden μ E V := by
  have hpos : 0 < 2 * μ * (V - E) := by nlinarith [sub_pos.mpr hb]
  exact Real.sqrt_pos.mpr hpos

theorem kappaForbidden_nonneg (μ E V : ℝ) : 0 ≤ kappaForbidden μ E V := Real.sqrt_nonneg _

/-! ## Discrete Schrödinger equation and stationary slab states -/

/-- Real discrete Schrödinger operator at lattice step `h` (Planck units, ħ ≡ 1):
`H f = −(1/2μ) Δ_h f + V·f`. -/
noncomputable def discreteSchrodingerReal (μ h : ℝ) (V : ObserverChart → ℝ)
    (f : ObserverChart → ℝ) (x : ObserverChart) : ℝ :=
  -(1 / (2 * μ)) * HQVM_discreteLaplacian h f x + V x * f x

/-- Stationary-state predicate `H f = E f`. -/
def IsStationaryReal (μ h : ℝ) (V : ObserverChart → ℝ) (f : ObserverChart → ℝ)
    (E : ℝ) : Prop :=
  ∀ x, discreteSchrodingerReal μ h V f x = E * f x

/-- **Construction theorem.**  Whenever the longitudinal rate `κ` and transverse momenta `k₁, k₂`
satisfy the discrete tunneling dispersion relation, the evanescent slab mode is a genuine
stationary state of energy `E` in the constant-potential slab. -/
theorem evanescentSlabMode_stationary_of_dispersion
    (μ h V₀ E κ k₁ k₂ : ℝ) (hμ : μ ≠ 0)
    (hdisp : longitudinalEigenFactor κ h
              = 2 * μ * (V₀ - E) + transverseEigenCost k₁ k₂ h) :
    IsStationaryReal μ h (fun _ => V₀) (evanescentSlabMode κ k₁ k₂) E := by
  intro x
  unfold discreteSchrodingerReal
  rw [discreteLaplacian_evanescentSlabMode, slabDispersion_split, hdisp]
  field_simp
  ring

/-! ## Genuine evanescence in the forbidden region -/

theorem transverseEigenCost_nonneg (k₁ k₂ h : ℝ) :
    0 ≤ transverseEigenCost k₁ k₂ h := by
  unfold transverseEigenCost
  have h1 : Real.cos (k₁ * h) ≤ 1 := Real.cos_le_one _
  have h2 : Real.cos (k₂ * h) ≤ 1 := Real.cos_le_one _
  apply div_nonneg
  · nlinarith
  · positivity

/-- Setting both transverse momenta to zero kills the transverse cost: the pure 1D barrier is the
`k_⊥ → 0` limit of the 3D treatment. -/
theorem transverseEigenCost_zero (h : ℝ) : transverseEigenCost 0 0 h = 0 := by
  unfold transverseEigenCost
  simp

/-- In the forbidden region the dispersion relation forces a strictly positive longitudinal
eigenfactor. -/
theorem longitudinalEigenFactor_pos_of_dispersion
    (μ h V₀ E κ k₁ k₂ : ℝ) (hμ : 0 < μ) (hb : E < V₀)
    (hdisp : longitudinalEigenFactor κ h
              = 2 * μ * (V₀ - E) + transverseEigenCost k₁ k₂ h) :
    0 < longitudinalEigenFactor κ h := by
  rw [hdisp]
  have ht := transverseEigenCost_nonneg k₁ k₂ h
  have hsrc : 0 < 2 * μ * (V₀ - E) := by nlinarith [sub_pos.mpr hb]
  linarith

/-- **Genuine evanescence.**  In a classically forbidden slab (`E < V₀`) any stationary slab mode
has a nonzero longitudinal rate: `cosh(κ·h) > 1`, hence `κ ≠ 0`.  No propagating longitudinal
solution exists — the lattice signature of tunneling. -/
theorem evanescentSlabMode_genuinely_evanescent
    (μ h V₀ E κ k₁ k₂ : ℝ) (hh : 0 < h) (hμ : 0 < μ) (hb : E < V₀)
    (hdisp : longitudinalEigenFactor κ h
              = 2 * μ * (V₀ - E) + transverseEigenCost k₁ k₂ h) :
    κ ≠ 0 := by
  have hpos := longitudinalEigenFactor_pos_of_dispersion μ h V₀ E κ k₁ k₂ hμ hb hdisp
  have hstep2 : 0 < h ^ 2 := pow_pos hh 2
  unfold longitudinalEigenFactor at hpos
  have hnum : 0 < 2 * (Real.cosh (κ * h) - 1) := by
    have hd := mul_pos hpos hstep2
    rwa [div_mul_cancel₀ _ (ne_of_gt hstep2)] at hd
  have hcosh : 1 < Real.cosh (κ * h) := by linarith
  have hne : κ * h ≠ 0 := one_lt_cosh.mp hcosh
  intro hk
  exact hne (by rw [hk]; ring)

/-- **Anchored stationary mode at the proton shell.**  At the *derived* lock-in step
`h = lockInCellStep = 1/5` (the proton-shell frequency tag, the only discrete datum), the slab mode
solving the dispersion relation is a genuine stationary state. -/
theorem lockIn_evanescentSlabMode_stationary
    (μ V₀ E κ k₁ k₂ : ℝ) (hμ : μ ≠ 0)
    (hdisp : longitudinalEigenFactor κ lockInCellStep
              = 2 * μ * (V₀ - E) + transverseEigenCost k₁ k₂ lockInCellStep) :
    IsStationaryReal μ lockInCellStep (fun _ => V₀) (evanescentSlabMode κ k₁ k₂) E :=
  evanescentSlabMode_stationary_of_dispersion μ lockInCellStep V₀ E κ k₁ k₂ hμ hdisp

/-- **Anchored evanescence at the proton shell.**  The forbidden-slab signature `κ ≠ 0` holds at the
derived lock-in step, using only `lockInCellStep_pos` for the step positivity — the discrete datum
is shell-fixed, everything else is bulk. -/
theorem lockIn_genuinely_evanescent
    (μ V₀ E κ k₁ k₂ : ℝ) (hμ : 0 < μ) (hb : E < V₀)
    (hdisp : longitudinalEigenFactor κ lockInCellStep
              = 2 * μ * (V₀ - E) + transverseEigenCost k₁ k₂ lockInCellStep) :
    κ ≠ 0 :=
  evanescentSlabMode_genuinely_evanescent μ lockInCellStep V₀ E κ k₁ k₂
    lockInCellStep_pos hμ hb hdisp

/-! ## Transmission coefficient (leading-order WKB observable) -/

/-- Leading-order transmission across a barrier of thickness `L` at longitudinal rate `κ`:
`T = exp(−2κL)`.  The continuum WKB form `exp(−2∫κ dx)` approximates this. -/
noncomputable def transmissionCoefficient (κ L : ℝ) : ℝ :=
  Real.exp (-(2 * κ * L))

theorem transmissionCoefficient_pos (κ L : ℝ) : 0 < transmissionCoefficient κ L :=
  Real.exp_pos _

theorem transmissionCoefficient_le_one (κ L : ℝ) (hκ : 0 ≤ κ) (hL : 0 ≤ L) :
    transmissionCoefficient κ L ≤ 1 := by
  unfold transmissionCoefficient
  rw [Real.exp_le_one_iff]
  nlinarith

theorem transmissionCoefficient_lt_one (κ L : ℝ) (hκ : 0 < κ) (hL : 0 < L) :
    transmissionCoefficient κ L < 1 := by
  unfold transmissionCoefficient
  rw [Real.exp_lt_one_iff]
  nlinarith

/-- Thicker barriers transmit less (for a fixed positive rate). -/
theorem transmissionCoefficient_antitone_L (κ : ℝ) (hκ : 0 < κ) {L L' : ℝ}
    (h : L ≤ L') : transmissionCoefficient κ L' ≤ transmissionCoefficient κ L := by
  unfold transmissionCoefficient
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Faster decay transmits less (for a fixed positive thickness). -/
theorem transmissionCoefficient_antitone_kappa (L : ℝ) (hL : 0 < L) {κ κ' : ℝ}
    (h : κ ≤ κ') : transmissionCoefficient κ' L ≤ transmissionCoefficient κ L := by
  unfold transmissionCoefficient
  apply Real.exp_le_exp.mpr
  nlinarith

/-! ## The 3D coupling: transverse momentum suppresses tunneling -/

/-- More transverse cost ⇒ larger longitudinal eigenfactor (both at fixed `μ, V₀, E`). -/
theorem transverse_raises_longitudinal
    (μ h V₀ E κ κ' k₁ k₂ k₁' k₂' : ℝ)
    (hdisp : longitudinalEigenFactor κ h
              = 2 * μ * (V₀ - E) + transverseEigenCost k₁ k₂ h)
    (hdisp' : longitudinalEigenFactor κ' h
              = 2 * μ * (V₀ - E) + transverseEigenCost k₁' k₂' h)
    (hcost : transverseEigenCost k₁ k₂ h ≤ transverseEigenCost k₁' k₂' h) :
    longitudinalEigenFactor κ h ≤ longitudinalEigenFactor κ' h := by
  rw [hdisp, hdisp']; linarith

/-- A larger longitudinal eigenfactor means a larger (nonnegative) decay rate. -/
theorem kappa_mono_of_factor_le {κ κ' h : ℝ} (hh : 0 < h) (hκ : 0 ≤ κ) (hκ' : 0 ≤ κ')
    (hle : longitudinalEigenFactor κ h ≤ longitudinalEigenFactor κ' h) : κ ≤ κ' := by
  have hstep2 : 0 < h ^ 2 := pow_pos hh 2
  unfold longitudinalEigenFactor at hle
  have hc : Real.cosh (κ * h) ≤ Real.cosh (κ' * h) := by
    have h2 := (div_le_div_iff_of_pos_right hstep2).mp hle
    linarith
  have habs : |κ * h| ≤ |κ' * h| := cosh_le_cosh.mp hc
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at habs
  exact le_of_mul_le_mul_right habs hh

/-- **Transverse momentum suppresses tunneling (a genuinely 3D statement).**  If a forbidden-region
state acquires more transverse cost, its longitudinal decay rate grows and the transmission across
any barrier of thickness `L > 0` drops. -/
theorem transverse_momentum_suppresses_transmission
    (μ h V₀ E κ κ' k₁ k₂ k₁' k₂' L : ℝ) (hh : 0 < h) (hL : 0 < L) (hκ : 0 ≤ κ) (hκ' : 0 ≤ κ')
    (hdisp : longitudinalEigenFactor κ h
              = 2 * μ * (V₀ - E) + transverseEigenCost k₁ k₂ h)
    (hdisp' : longitudinalEigenFactor κ' h
              = 2 * μ * (V₀ - E) + transverseEigenCost k₁' k₂' h)
    (hcost : transverseEigenCost k₁ k₂ h ≤ transverseEigenCost k₁' k₂' h) :
    transmissionCoefficient κ' L ≤ transmissionCoefficient κ L := by
  have hfac := transverse_raises_longitudinal μ h V₀ E κ κ' k₁ k₂ k₁' k₂' hdisp hdisp' hcost
  exact transmissionCoefficient_antitone_kappa L hL (kappa_mono_of_factor_le hh hκ hκ' hfac)

/-! ## Bulk continuity: the dispersion is a smooth function of the continuous parameters

Per the HQIV ontology, only the **shell / horizon index** is quantized — hence the lattice step
`h` is the sole discrete datum.  The *bulk* fields and kinematic parameters (rate `κ`, transverse
momenta `k₁, k₂`, base point `x`, translation `v`, rotation angle `θ`) are continuous. -/

private theorem cosh_sub_one_half (y : ℝ) :
    Real.cosh (2 * y) - 1 = 2 * Real.sinh y ^ 2 := by
  rw [Real.cosh_two_mul, Real.cosh_sq']; ring

private theorem one_sub_cos_half (y : ℝ) :
    1 - Real.cos (2 * y) = 2 * Real.sin y ^ 2 := by
  rw [Real.cos_two_mul, Real.sin_sq]; ring

/-- **Lattice-sinc form of the longitudinal eigenfactor.**  Exact (no limit): the discrete
evanescent eigenvalue is `(2 sinh(κh/2)/h)²`. -/
theorem longitudinalEigenFactor_eq_sinh_sq (κ h : ℝ) :
    longitudinalEigenFactor κ h = (2 * Real.sinh (κ * h / 2) / h) ^ 2 := by
  have hkey := cosh_sub_one_half (κ * h / 2)
  rw [show (2 : ℝ) * (κ * h / 2) = κ * h from by ring] at hkey
  unfold longitudinalEigenFactor
  rw [hkey]; ring

/-- **Lattice-sinc form of the transverse cost.** -/
theorem transverseEigenCost_eq_sin_sq (k₁ k₂ h : ℝ) :
    transverseEigenCost k₁ k₂ h
      = (2 * Real.sin (k₁ * h / 2) / h) ^ 2 + (2 * Real.sin (k₂ * h / 2) / h) ^ 2 := by
  have h1 := one_sub_cos_half (k₁ * h / 2)
  have h2 := one_sub_cos_half (k₂ * h / 2)
  rw [show (2 : ℝ) * (k₁ * h / 2) = k₁ * h from by ring] at h1
  rw [show (2 : ℝ) * (k₂ * h / 2) = k₂ * h from by ring] at h2
  unfold transverseEigenCost
  rw [h1, h2]; ring

/-- The full discrete tunneling dispersion as a difference of squared lattice-sincs. -/
theorem slabDispersion_eq_latticeSinc (κ k₁ k₂ h : ℝ) :
    slabDispersion κ k₁ k₂ h
      = (2 * Real.sinh (κ * h / 2) / h) ^ 2
        - (2 * Real.sin (k₁ * h / 2) / h) ^ 2
        - (2 * Real.sin (k₂ * h / 2) / h) ^ 2 := by
  rw [slabDispersion_split, longitudinalEigenFactor_eq_sinh_sq, transverseEigenCost_eq_sin_sq]
  ring

/-- The longitudinal eigenfactor is continuous in the continuous bulk rate `κ`. -/
theorem continuous_longitudinalEigenFactor (h : ℝ) :
    Continuous (fun κ : ℝ => longitudinalEigenFactor κ h) := by
  unfold longitudinalEigenFactor
  have hc : Continuous (fun κ : ℝ => Real.cosh (κ * h)) :=
    Real.continuous_cosh.comp (continuous_id.mul continuous_const)
  exact (continuous_const.mul (hc.sub continuous_const)).div_const _

/-- The discrete dispersion is continuous in the continuous bulk rate `κ`. -/
theorem continuous_slabDispersion_rate (k₁ k₂ h : ℝ) :
    Continuous (fun κ : ℝ => slabDispersion κ k₁ k₂ h) := by
  have hrw : (fun κ : ℝ => slabDispersion κ k₁ k₂ h)
      = (fun κ : ℝ => longitudinalEigenFactor κ h - transverseEigenCost k₁ k₂ h) := by
    funext κ; exact slabDispersion_split κ k₁ k₂ h
  rw [hrw]
  exact (continuous_longitudinalEigenFactor h).sub continuous_const

/-! ### Continuous translation symmetry of the bulk operator -/

/-- The raw stencil sum commutes with a continuous translation `v : ℝ³`. -/
theorem HQVM_rawSecondDiff_sum_translation (h : ℝ) (f : ObserverChart → ℝ)
    (v x : ObserverChart) :
    HQVM_rawSecondDiff_sum h (fun y => f (y + v)) x
      = HQVM_rawSecondDiff_sum h f (x + v) := by
  unfold HQVM_rawSecondDiff_sum HQVM_rawSecondDiffAlong HQVM_axisShift
  refine Finset.sum_congr rfl ?_
  intro i _
  dsimp only
  rw [add_right_comm x (Pi.single i h) v, add_right_comm x (Pi.single i (-h)) v]

/-- **Continuous translation symmetry.**  The patch discrete Laplacian commutes with any continuous
translation of the bulk.  Momentum is therefore a good continuous quantum number. -/
theorem HQVM_discreteLaplacian_translation (h : ℝ) (f : ObserverChart → ℝ)
    (v x : ObserverChart) :
    HQVM_discreteLaplacian h (fun y => f (y + v)) x
      = HQVM_discreteLaplacian h f (x + v) := by
  unfold HQVM_discreteLaplacian
  rw [HQVM_rawSecondDiff_sum_translation]

/-- A continuum (ℝ³) family of degenerate evanescent eigenstates. -/
theorem evanescentSlabMode_translate_eigen (κ k₁ k₂ h : ℝ) (v x : ObserverChart) :
    HQVM_discreteLaplacian h (fun y => evanescentSlabMode κ k₁ k₂ (y + v)) x
      = slabDispersion κ k₁ k₂ h * evanescentSlabMode κ k₁ k₂ (x + v) := by
  rw [HQVM_discreteLaplacian_translation, discreteLaplacian_evanescentSlabMode]

/-! ### Continuum envelope and continuous rotation symmetry -/

/-- Smooth bulk dispersion (the `h → 0` envelope of `slabDispersion`): `κ² − (k₁² + k₂²)`. -/
def slabDispersionContinuum (κ k₁ k₂ : ℝ) : ℝ :=
  κ ^ 2 - (k₁ ^ 2 + k₂ ^ 2)

/-- **Continuous SO(2) rotation symmetry** of the transverse plane. -/
theorem slabDispersionContinuum_rotInvariant (κ k₁ k₂ θ : ℝ) :
    slabDispersionContinuum κ (k₁ * Real.cos θ - k₂ * Real.sin θ)
        (k₁ * Real.sin θ + k₂ * Real.cos θ)
      = slabDispersionContinuum κ k₁ k₂ := by
  unfold slabDispersionContinuum
  have key : (k₁ * Real.cos θ - k₂ * Real.sin θ) ^ 2
              + (k₁ * Real.sin θ + k₂ * Real.cos θ) ^ 2
            = (k₁ ^ 2 + k₂ ^ 2) * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
  rw [key, Real.sin_sq_add_cos_sq, mul_one]

/-! ## Continuum evanescent spectrum and observable suppression -/

/-- Continuum 3D evanescence condition `κ² = k_⊥² + 2μ(V₀ − E)`. -/
def ContinuumEvanescenceCondition (μ V₀ E κ k₁ k₂ : ℝ) : Prop :=
  κ ^ 2 = (k₁ ^ 2 + k₂ ^ 2) + 2 * μ * (V₀ - E)

theorem continuumEvanescence_iff (μ V₀ E κ k₁ k₂ : ℝ) :
    ContinuumEvanescenceCondition μ V₀ E κ k₁ k₂ ↔
      slabDispersionContinuum κ k₁ k₂ = 2 * μ * (V₀ - E) := by
  unfold ContinuumEvanescenceCondition slabDispersionContinuum
  constructor <;> intro h <;> linarith

/-- The longitudinal rate induced by continuous transverse momentum and barrier height. -/
noncomputable def kappaOfTransverse (μ V₀ E k₁ k₂ : ℝ) : ℝ :=
  Real.sqrt ((k₁ ^ 2 + k₂ ^ 2) + 2 * μ * (V₀ - E))

theorem kappaOfTransverse_solves (μ V₀ E k₁ k₂ : ℝ)
    (hb : 0 ≤ (k₁ ^ 2 + k₂ ^ 2) + 2 * μ * (V₀ - E)) :
    ContinuumEvanescenceCondition μ V₀ E (kappaOfTransverse μ V₀ E k₁ k₂) k₁ k₂ := by
  unfold ContinuumEvanescenceCondition kappaOfTransverse
  rw [Real.sq_sqrt hb]

/-- The evanescent rate grows with transverse momentum. -/
theorem kappaOfTransverse_mono (μ V₀ E : ℝ) {k₁ k₂ k₁' k₂' : ℝ}
    (h : k₁ ^ 2 + k₂ ^ 2 ≤ k₁' ^ 2 + k₂' ^ 2) :
    kappaOfTransverse μ V₀ E k₁ k₂ ≤ kappaOfTransverse μ V₀ E k₁' k₂' := by
  unfold kappaOfTransverse
  exact Real.sqrt_le_sqrt (by linarith)

theorem continuous_kappaOfTransverse (μ V₀ E : ℝ) :
    Continuous (fun p : ℝ × ℝ => kappaOfTransverse μ V₀ E p.1 p.2) := by
  unfold kappaOfTransverse
  fun_prop

/-- **Observable hook (continuum form).**  Larger transverse momentum exponentially lowers the
transmission across any barrier of thickness `L > 0`. -/
theorem continuum_transverse_suppresses_transmission
    (μ V₀ E L : ℝ) (hL : 0 < L) {k₁ k₂ k₁' k₂' : ℝ}
    (h : k₁ ^ 2 + k₂ ^ 2 ≤ k₁' ^ 2 + k₂' ^ 2) :
    transmissionCoefficient (kappaOfTransverse μ V₀ E k₁' k₂') L
      ≤ transmissionCoefficient (kappaOfTransverse μ V₀ E k₁ k₂) L :=
  transmissionCoefficient_antitone_kappa L hL (kappaOfTransverse_mono μ V₀ E h)

/-! ## Textbook parity: exact barrier, reflection/conservation, energy dependence, decay -/

private theorem barrierExcess_nonneg (E V₀ κ L : ℝ) (hE : 0 < E) (hEV : E < V₀) :
    0 ≤ V₀ ^ 2 * Real.sinh (κ * L) ^ 2 / (4 * E * (V₀ - E)) := by
  apply div_nonneg
  · positivity
  · nlinarith [mul_pos hE (sub_pos.mpr hEV)]

/-- **Exact rectangular-barrier transmission** (textbook form, `0 < E < V₀`):
`T = [1 + V₀² sinh²(κL) / (4E(V₀−E))]⁻¹`. -/
noncomputable def transmissionExact (E V₀ κ L : ℝ) : ℝ :=
  (1 + V₀ ^ 2 * Real.sinh (κ * L) ^ 2 / (4 * E * (V₀ - E)))⁻¹

theorem transmissionExact_pos (E V₀ κ L : ℝ) (hE : 0 < E) (hEV : E < V₀) :
    0 < transmissionExact E V₀ κ L := by
  unfold transmissionExact
  have hb := barrierExcess_nonneg E V₀ κ L hE hEV
  exact inv_pos.mpr (by linarith)

theorem transmissionExact_le_one (E V₀ κ L : ℝ) (hE : 0 < E) (hEV : E < V₀) :
    transmissionExact E V₀ κ L ≤ 1 := by
  unfold transmissionExact
  have hb := barrierExcess_nonneg E V₀ κ L hE hEV
  rw [inv_le_one₀ (by linarith)]
  linarith

theorem transmissionExact_lt_one (E V₀ κ L : ℝ) (hE : 0 < E) (hEV : E < V₀)
    (hκL : κ * L ≠ 0) : transmissionExact E V₀ κ L < 1 := by
  unfold transmissionExact
  have hV0 : 0 < V₀ := by linarith
  have hsinh : Real.sinh (κ * L) ≠ 0 := Real.sinh_ne_zero.mpr hκL
  have hnum : 0 < V₀ ^ 2 * Real.sinh (κ * L) ^ 2 := by positivity
  have hden : 0 < 4 * E * (V₀ - E) := by nlinarith [mul_pos hE (sub_pos.mpr hEV)]
  have hB : 0 < V₀ ^ 2 * Real.sinh (κ * L) ^ 2 / (4 * E * (V₀ - E)) := div_pos hnum hden
  rw [inv_lt_one₀ (by linarith)]
  linarith

/-- A vanishing barrier is perfectly transmitting: `T(L = 0) = 1`. -/
theorem transmissionExact_zero_thickness (E V₀ κ : ℝ) :
    transmissionExact E V₀ κ 0 = 1 := by
  unfold transmissionExact
  simp

/-- Reflection coefficient `R = 1 − T`. -/
noncomputable def reflectionExact (E V₀ κ L : ℝ) : ℝ :=
  1 - transmissionExact E V₀ κ L

/-- **Probability conservation** for the exact barrier: `T + R = 1`. -/
theorem transmission_add_reflection_eq_one (E V₀ κ L : ℝ) :
    transmissionExact E V₀ κ L + reflectionExact E V₀ κ L = 1 := by
  unfold reflectionExact; ring

theorem reflectionExact_nonneg (E V₀ κ L : ℝ) (hE : 0 < E) (hEV : E < V₀) :
    0 ≤ reflectionExact E V₀ κ L := by
  unfold reflectionExact
  have := transmissionExact_le_one E V₀ κ L hE hEV; linarith

theorem reflectionExact_lt_one (E V₀ κ L : ℝ) (hE : 0 < E) (hEV : E < V₀) :
    reflectionExact E V₀ κ L < 1 := by
  unfold reflectionExact
  have := transmissionExact_pos E V₀ κ L hE hEV; linarith

/-! ### Energy and barrier-height dependence -/

/-- The decay rate falls as the energy approaches the barrier top: `κ` is antitone in `E`. -/
theorem kappaForbidden_antitone_E (μ V : ℝ) (hμ : 0 ≤ μ) {E E' : ℝ}
    (hE : E ≤ E') (_h' : E' < V) :
    kappaForbidden μ E' V ≤ kappaForbidden μ E V := by
  unfold kappaForbidden
  exact Real.sqrt_le_sqrt (by nlinarith [mul_nonneg hμ (sub_nonneg.mpr hE)])

/-- A taller barrier `V` gives a larger interior decay rate `κ`. -/
theorem kappaForbidden_monotone_V (μ E : ℝ) (hμ : 0 ≤ μ) {V V' : ℝ}
    (hV : V ≤ V') : kappaForbidden μ E V ≤ kappaForbidden μ E V' := by
  unfold kappaForbidden
  exact Real.sqrt_le_sqrt
    (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * μ) (sub_nonneg.mpr hV)])

/-- The decay rate grows with the tunneling mass `μ` (the kinetic-isotope lever). -/
theorem kappaForbidden_monotone_mass (E V : ℝ) (hEV : E ≤ V) {μ μ' : ℝ}
    (_hμ : 0 ≤ μ) (h : μ ≤ μ') : kappaForbidden μ E V ≤ kappaForbidden μ' E V := by
  unfold kappaForbidden
  exact Real.sqrt_le_sqrt
    (by nlinarith [mul_nonneg (sub_nonneg.mpr hEV) (sub_nonneg.mpr h)])

/-- **Higher energy tunnels more**: transmission is monotone in `E` (for `E < V`). -/
theorem transmissionCoefficient_monotone_E (μ V L : ℝ) (hμ : 0 ≤ μ) (hL : 0 < L)
    {E E' : ℝ} (hE : E ≤ E') (h' : E' < V) :
    transmissionCoefficient (kappaForbidden μ E V) L
      ≤ transmissionCoefficient (kappaForbidden μ E' V) L :=
  transmissionCoefficient_antitone_kappa L hL (kappaForbidden_antitone_E μ V hμ hE h')

/-! ### Gamow decay rate and half-life -/

/-- Decay rate `Γ = ν · T` (attempt frequency × transmission). -/
noncomputable def decayRate (attemptFreq κ L : ℝ) : ℝ :=
  attemptFreq * transmissionCoefficient κ L

theorem decayRate_pos (ν κ L : ℝ) (hν : 0 < ν) : 0 < decayRate ν κ L :=
  mul_pos hν (transmissionCoefficient_pos κ L)

/-- Wider barriers decay slower. -/
theorem decayRate_antitone_L (ν κ : ℝ) (hν : 0 ≤ ν) (hκ : 0 < κ) {L L' : ℝ} (h : L ≤ L') :
    decayRate ν κ L' ≤ decayRate ν κ L :=
  mul_le_mul_of_nonneg_left (transmissionCoefficient_antitone_L κ hκ h) hν

/-- Half-life `t₁/₂ = ln 2 / Γ`. -/
noncomputable def halfLife (attemptFreq κ L : ℝ) : ℝ :=
  Real.log 2 / decayRate attemptFreq κ L

theorem halfLife_pos (ν κ L : ℝ) (hν : 0 < ν) : 0 < halfLife ν κ L :=
  div_pos (Real.log_pos (by norm_num)) (decayRate_pos ν κ L hν)

/-- **Wider barriers live longer**: half-life is monotone in barrier thickness. -/
theorem halfLife_monotone_L (ν κ : ℝ) (hν : 0 < ν) (hκ : 0 < κ) {L L' : ℝ} (h : L ≤ L') :
    halfLife ν κ L ≤ halfLife ν κ L' :=
  div_le_div_of_nonneg_left (Real.log_nonneg one_le_two)
    (decayRate_pos ν κ L' hν) (decayRate_antitone_L ν κ hν.le hκ h)

/-- Larger decay rate κ means a slower (smaller) decay rate Γ. -/
theorem decayRate_antitone_kappa (ν L : ℝ) (hν : 0 ≤ ν) (hL : 0 < L) {κ κ' : ℝ}
    (h : κ ≤ κ') : decayRate ν κ' L ≤ decayRate ν κ L :=
  mul_le_mul_of_nonneg_left (transmissionCoefficient_antitone_kappa L hL h) hν

/-- **Taller barriers live longer**: half-life is monotone in the decay rate κ. -/
theorem halfLife_monotone_kappa (ν L : ℝ) (hν : 0 < ν) (hL : 0 < L) {κ κ' : ℝ}
    (h : κ ≤ κ') : halfLife ν κ L ≤ halfLife ν κ' L :=
  div_le_div_of_nonneg_left (Real.log_nonneg one_le_two)
    (decayRate_pos ν κ' L hν) (decayRate_antitone_kappa ν L hν.le hL h)

/-! ### Continuum limit (continuum approximates the discrete) -/

private theorem tendsto_sinh_div :
    Filter.Tendsto (fun t : ℝ => Real.sinh t / t) (𝓝[≠] 0) (𝓝 1) := by
  have h := hasDerivAt_iff_tendsto_slope.mp (Real.hasDerivAt_sinh 0)
  rw [Real.cosh_zero] at h
  exact Filter.Tendsto.congr (fun t => by rw [slope_def_field]; simp) h

/-- **Continuum limit.**  As the lattice step `h → 0`, the longitudinal eigenfactor converges to
the ordinary continuum dispersion `κ²`.  The discrete object is primary; the continuum is its
limit. -/
theorem tendsto_longitudinalEigenFactor (κ : ℝ) :
    Filter.Tendsto (fun h : ℝ => longitudinalEigenFactor κ h) (𝓝[≠] 0) (𝓝 (κ ^ 2)) := by
  by_cases hκ : κ = 0
  · subst hκ
    have hfun : (fun h : ℝ => longitudinalEigenFactor 0 h) = (fun _ => (0 : ℝ)) := by
      funext h; simp [longitudinalEigenFactor, Real.cosh_zero]
    rw [hfun, show ((0 : ℝ) ^ 2) = 0 from by norm_num]
    exact tendsto_const_nhds
  · have hφ : Filter.Tendsto (fun h : ℝ => κ * h / 2) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have hc : Continuous (fun h : ℝ => κ * h / 2) := by fun_prop
        have ht := hc.tendsto 0
        simp only [mul_zero, zero_div] at ht
        exact ht.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with h hh
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hh ⊢
        exact div_ne_zero (mul_ne_zero hκ hh) (by norm_num)
    have hs : Filter.Tendsto (fun h : ℝ => Real.sinh (κ * h / 2) / (κ * h / 2))
        (𝓝[≠] 0) (𝓝 1) := tendsto_sinh_div.comp hφ
    have hg : Filter.Tendsto (fun h : ℝ => 2 * Real.sinh (κ * h / 2) / h) (𝓝[≠] 0) (𝓝 κ) := by
      have hmul := (tendsto_const_nhds (x := κ) (f := 𝓝[≠] (0 : ℝ))).mul hs
      rw [mul_one] at hmul
      refine hmul.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with h hh
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hh
      field_simp
    have hsq := hg.mul hg
    have heq : (fun h : ℝ => longitudinalEigenFactor κ h)
        = (fun h : ℝ => 2 * Real.sinh (κ * h / 2) / h * (2 * Real.sinh (κ * h / 2) / h)) := by
      funext h; rw [longitudinalEigenFactor_eq_sinh_sq]; ring
    rw [heq, show κ ^ 2 = κ * κ from by ring]
    exact hsq

/-! ## WKB / Gamow factor for an arbitrary (piecewise) barrier -/

/-- Lattice Gamow exponent `G = Δx · Σ_{j<n} κⱼ` (discrete `∫₀ᴸ κ(x) dx`). -/
noncomputable def gamowExponent (κ : ℕ → ℝ) (Δx : ℝ) (n : ℕ) : ℝ :=
  Δx * ∑ j ∈ Finset.range n, κ j

/-- WKB transmission `T = exp(−2G)` through an arbitrary sampled barrier. -/
noncomputable def transmissionWKB (κ : ℕ → ℝ) (Δx : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(2 * gamowExponent κ Δx n))

theorem transmissionWKB_pos (κ : ℕ → ℝ) (Δx : ℝ) (n : ℕ) :
    0 < transmissionWKB κ Δx n := Real.exp_pos _

theorem gamowExponent_nonneg (κ : ℕ → ℝ) (Δx : ℝ) (n : ℕ)
    (hΔx : 0 ≤ Δx) (hκ : ∀ j ∈ Finset.range n, 0 ≤ κ j) :
    0 ≤ gamowExponent κ Δx n :=
  mul_nonneg hΔx (Finset.sum_nonneg hκ)

theorem transmissionWKB_le_one (κ : ℕ → ℝ) (Δx : ℝ) (n : ℕ)
    (hΔx : 0 ≤ Δx) (hκ : ∀ j ∈ Finset.range n, 0 ≤ κ j) :
    transmissionWKB κ Δx n ≤ 1 := by
  unfold transmissionWKB
  rw [Real.exp_le_one_iff]
  have := gamowExponent_nonneg κ Δx n hΔx hκ
  linarith

/-- **Gamow exponent is additive** over concatenated barrier segments. -/
theorem gamowExponent_add (κ : ℕ → ℝ) (Δx : ℝ) (n m : ℕ) :
    gamowExponent κ Δx (n + m)
      = gamowExponent κ Δx n + gamowExponent (fun j => κ (n + j)) Δx m := by
  unfold gamowExponent
  rw [Finset.sum_range_add, mul_add]

/-- **WKB transmissions multiply** across concatenated segments (`T = T₁ · T₂`). -/
theorem transmissionWKB_mul (κ : ℕ → ℝ) (Δx : ℝ) (n m : ℕ) :
    transmissionWKB κ Δx (n + m)
      = transmissionWKB κ Δx n * transmissionWKB (fun j => κ (n + j)) Δx m := by
  unfold transmissionWKB
  rw [gamowExponent_add, ← Real.exp_add]
  congr 1
  ring

/-- For a constant barrier the WKB transmission reduces to `exp(−2κ₀L)` with `L = Δx · n`. -/
theorem transmissionWKB_const (κ₀ Δx : ℝ) (n : ℕ) :
    transmissionWKB (fun _ => κ₀) Δx n = transmissionCoefficient κ₀ (Δx * n) := by
  unfold transmissionWKB transmissionCoefficient gamowExponent
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  congr 1
  ring

/-- A pointwise-taller barrier transmits less. -/
theorem transmissionWKB_antitone (κ κ' : ℕ → ℝ) (Δx : ℝ) (n : ℕ)
    (hΔx : 0 ≤ Δx) (h : ∀ j ∈ Finset.range n, κ j ≤ κ' j) :
    transmissionWKB κ' Δx n ≤ transmissionWKB κ Δx n := by
  unfold transmissionWKB
  apply Real.exp_le_exp.mpr
  have hsum : ∑ j ∈ Finset.range n, κ j ≤ ∑ j ∈ Finset.range n, κ' j :=
    Finset.sum_le_sum h
  unfold gamowExponent
  nlinarith [mul_le_mul_of_nonneg_left hsum hΔx]

/-! ## Resonant / double-barrier tunneling -/

/-- Breit–Wigner resonant transmission with half-width `γ`. -/
noncomputable def resonantTransmission (halfWidth E E_res : ℝ) : ℝ :=
  halfWidth ^ 2 / ((E - E_res) ^ 2 + halfWidth ^ 2)

/-- **Perfect transmission on resonance**: `T(E_res) = 1`. -/
theorem resonantTransmission_at_resonance (γ E_res : ℝ) (hγ : γ ≠ 0) :
    resonantTransmission γ E_res E_res = 1 := by
  unfold resonantTransmission
  rw [sub_self, show (0 : ℝ) ^ 2 + γ ^ 2 = γ ^ 2 from by ring]
  exact div_self (pow_ne_zero 2 hγ)

theorem resonantTransmission_pos (γ E E_res : ℝ) (hγ : γ ≠ 0) :
    0 < resonantTransmission γ E E_res := by
  unfold resonantTransmission
  apply div_pos (by positivity)
  positivity

theorem resonantTransmission_le_one (γ E E_res : ℝ) (hγ : γ ≠ 0) :
    resonantTransmission γ E E_res ≤ 1 := by
  unfold resonantTransmission
  rw [div_le_one (by positivity)]
  nlinarith [sq_nonneg (E - E_res)]

/-- Off resonance the transmission is strictly below unity. -/
theorem resonantTransmission_lt_one (γ E E_res : ℝ) (hγ : γ ≠ 0) (hE : E ≠ E_res) :
    resonantTransmission γ E E_res < 1 := by
  unfold resonantTransmission
  have hne : E - E_res ≠ 0 := sub_ne_zero.mpr hE
  rw [div_lt_one (by positivity)]
  have : 0 < (E - E_res) ^ 2 := by positivity
  nlinarith

/-- The resonance energy is the global transmission maximum. -/
theorem resonantTransmission_le_resonance (γ E E_res : ℝ) (hγ : γ ≠ 0) :
    resonantTransmission γ E E_res ≤ resonantTransmission γ E_res E_res := by
  rw [resonantTransmission_at_resonance γ E_res hγ]
  exact resonantTransmission_le_one γ E E_res hγ

/-! ## Scanning-tunneling-microscope current -/

/-- STM tunnel current `I = G · V · e^{−2κ d}`. -/
noncomputable def stmCurrent (conductance bias κ d : ℝ) : ℝ :=
  conductance * bias * transmissionCoefficient κ d

theorem stmCurrent_pos (G V κ d : ℝ) (hG : 0 < G) (hV : 0 < V) :
    0 < stmCurrent G V κ d :=
  mul_pos (mul_pos hG hV) (transmissionCoefficient_pos κ d)

/-- The current is Ohmic (linear) in the bias voltage. -/
theorem stmCurrent_linear_in_bias (G V₁ V₂ κ d : ℝ) :
    stmCurrent G (V₁ + V₂) κ d = stmCurrent G V₁ κ d + stmCurrent G V₂ κ d := by
  unfold stmCurrent; ring

/-- **Exponential gap sensitivity**: a larger tip–sample gap gives a smaller current. -/
theorem stmCurrent_antitone_gap (G V κ : ℝ) (hGV : 0 ≤ G * V) (hκ : 0 < κ) {d d' : ℝ}
    (h : d ≤ d') : stmCurrent G V κ d' ≤ stmCurrent G V κ d :=
  mul_le_mul_of_nonneg_left (transmissionCoefficient_antitone_L κ hκ h) hGV

/-! ## Fowler–Nordheim cold field emission -/

/-- Fowler–Nordheim emission current density `J(F) = a F² e^{−b/F}`. -/
noncomputable def fowlerNordheim (a b F : ℝ) : ℝ :=
  a * F ^ 2 * Real.exp (-(b / F))

theorem fowlerNordheim_pos (a b F : ℝ) (ha : 0 < a) (hF : 0 < F) :
    0 < fowlerNordheim a b F := by
  unfold fowlerNordheim; positivity

/-- **Stronger fields emit more**: the FN current grows monotonically with the applied field. -/
theorem fowlerNordheim_monotone_field (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    {F F' : ℝ} (hF : 0 < F) (h : F ≤ F') :
    fowlerNordheim a b F ≤ fowlerNordheim a b F' := by
  unfold fowlerNordheim
  have hF' : 0 < F' := lt_of_lt_of_le hF h
  have hsq : F ^ 2 ≤ F' ^ 2 := by nlinarith
  have hbF : b / F' ≤ b / F := by
    rw [div_le_div_iff₀ hF' hF]
    nlinarith [mul_le_mul_of_nonneg_left h hb]
  have hexp : Real.exp (-(b / F)) ≤ Real.exp (-(b / F')) :=
    Real.exp_le_exp.mpr (by linarith)
  have hnn : (0 : ℝ) ≤ Real.exp (-(b / F)) := (Real.exp_pos _).le
  calc a * F ^ 2 * Real.exp (-(b / F))
      ≤ a * F' ^ 2 * Real.exp (-(b / F)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq ha) hnn
    _ ≤ a * F' ^ 2 * Real.exp (-(b / F')) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)

/-- **Higher work function suppresses field emission**: at fixed field, a larger barrier parameter
`b` (∝ work function) lowers the FN current. -/
theorem fowlerNordheim_antitone_workfunction (a F : ℝ) (ha : 0 ≤ a) (hF : 0 < F)
    {b b' : ℝ} (h : b ≤ b') : fowlerNordheim a b' F ≤ fowlerNordheim a b F := by
  unfold fowlerNordheim
  have hbb : b / F ≤ b' / F := by gcongr
  have hexp : Real.exp (-(b' / F)) ≤ Real.exp (-(b / F)) :=
    Real.exp_le_exp.mpr (by linarith)
  exact mul_le_mul_of_nonneg_left hexp (by positivity)

/-! ## Tunneling traversal time and the Hartman effect -/

/-- Opaque-barrier phase traversal time `τ = 2 / (v κ)` (the saturated Hartman value). -/
noncomputable def traversalTimeOpaque (v κ : ℝ) (_L : ℝ) : ℝ := 2 / (v * κ)

theorem traversalTimeOpaque_pos (v κ L : ℝ) (hv : 0 < v) (hκ : 0 < κ) :
    0 < traversalTimeOpaque v κ L := by
  unfold traversalTimeOpaque; positivity

/-- **Hartman effect**: the opaque-barrier traversal time is independent of the barrier width. -/
theorem traversalTimeOpaque_width_independent (v κ L L' : ℝ) :
    traversalTimeOpaque v κ L = traversalTimeOpaque v κ L' := rfl

/-- Apparent traversal velocity `v_app = L / τ`. -/
noncomputable def apparentTraversalVelocity (v κ L : ℝ) : ℝ :=
  L / traversalTimeOpaque v κ L

theorem apparentTraversalVelocity_eq (v κ L : ℝ) :
    apparentTraversalVelocity v κ L = L * (v * κ) / 2 := by
  unfold apparentTraversalVelocity traversalTimeOpaque
  rw [div_div_eq_mul_div]

/-- **Apparent superluminality**: a wider opaque barrier yields a larger apparent velocity. -/
theorem apparentTraversalVelocity_monotone_width (v κ : ℝ) (hv : 0 < v) (hκ : 0 < κ)
    {L L' : ℝ} (h : L ≤ L') :
    apparentTraversalVelocity v κ L ≤ apparentTraversalVelocity v κ L' := by
  rw [apparentTraversalVelocity_eq, apparentTraversalVelocity_eq]
  have : L * (v * κ) ≤ L' * (v * κ) :=
    mul_le_mul_of_nonneg_right h (mul_pos hv hκ).le
  linarith

/-! ## Chemistry layer — what the tunneling spine unlocks

**Honest scope (see the provenance ledger below).**  Each statement is a *law* — a monotonicity,
positivity, or resonance fact — derived from the tunneling toolkit above.  The **laws** are the
results; the **inputs** are free bulk data, not derived:

* the reduced mass `μ` is an external/comparison quantity (isotope masses), so the kinetic isotope
  effect is proved only as a *μ-monotonicity* (`heavier_isotope_tunnels_less`), never as a numeral;
* the barrier height `V₀ − E` is an observer input (deriving it from `δ_E` is an open frontier);
* the only genuinely *derived* hook is the field-emission barrier `b`, taken as the spine's own
  `Chemistry.Binding.hydrogenicBindingHartree`.

No new constant, no PDG/CODATA numeral. -/

/-! ### (1) Kinetic isotope effect / proton tunneling -/

/-- **Heavier isotope tunnels less.**  At a fixed sub-barrier energy and width, a larger reduced
mass `μ` (e.g. deuterium vs protium) gives a strictly lower transmission — the primary kinetic
isotope effect, here a theorem about the tunneling rate `κ = √(2μ(V−E))`. -/
theorem heavier_isotope_tunnels_less (E V L : ℝ) (hL : 0 < L) (hEV : E ≤ V)
    {μ μ' : ℝ} (hμ : 0 ≤ μ) (h : μ ≤ μ') :
    transmissionCoefficient (kappaForbidden μ' E V) L
      ≤ transmissionCoefficient (kappaForbidden μ E V) L :=
  transmissionCoefficient_antitone_kappa L hL (kappaForbidden_monotone_mass E V hEV hμ h)

/-- **Kinetic isotope effect `≥ 1`.**  Writing the KIE as the protium/deuterium transmission ratio,
the lighter isotope always transmits at least as much, so `T_H ≥ T_D`. -/
theorem kineticIsotopeEffect_ge_one (E V L : ℝ) (hL : 0 < L) (hEV : E ≤ V)
    {μH μD : ℝ} (hμ : 0 ≤ μH) (h : μH ≤ μD) :
    transmissionCoefficient (kappaForbidden μD E V) L
      ≤ transmissionCoefficient (kappaForbidden μH E V) L :=
  heavier_isotope_tunnels_less E V L hL hEV hμ h

/-- **Heavier isotope decays slower**: a larger tunneling mass lengthens the Gamow half-life
(slower proton-transfer / heavier-isotope decay). -/
theorem heavier_isotope_longer_halfLife (ν E V L : ℝ) (hν : 0 < ν) (hL : 0 < L)
    (hEV : E < V) {μ μ' : ℝ} (hμ : 0 < μ) (h : μ ≤ μ') :
    halfLife ν (kappaForbidden μ E V) L ≤ halfLife ν (kappaForbidden μ' E V) L :=
  halfLife_monotone_kappa ν L hν hL (kappaForbidden_monotone_mass E V hEV.le hμ.le h)

/-! ### (2) Double-well proton transfer and ammonia inversion -/

/-- **Coherent double-well transfer.**  At a quasi-bound resonance energy a symmetric double well
(double barrier) transmits perfectly: `T(E_res) = 1`.  This is the resonance behind proton transfer
in symmetric hydrogen bonds and the ammonia-inversion doublet. -/
theorem resonant_double_well_perfect_transfer (γ E_res : ℝ) (hγ : γ ≠ 0) :
    resonantTransmission γ E_res E_res = 1 :=
  resonantTransmission_at_resonance γ E_res hγ

/-- Tunneling level splitting `Δ = A·e^{−κL}` (the symmetric/antisymmetric gap of a double well). -/
noncomputable def tunnelingSplitting (amplitude κ L : ℝ) : ℝ :=
  amplitude * Real.exp (-(κ * L))

theorem tunnelingSplitting_pos (A κ L : ℝ) (hA : 0 < A) : 0 < tunnelingSplitting A κ L :=
  mul_pos hA (Real.exp_pos _)

/-- **The inversion doublet is genuinely split** (positive gap) whenever the well couples
(`A > 0`): the ammonia/double-well ground state is nondegenerate. -/
theorem inversion_doublet_split (A κ L : ℝ) (hA : 0 < A) : 0 < tunnelingSplitting A κ L :=
  tunnelingSplitting_pos A κ L hA

/-- **Heavier inverting mass splits less** (ND₃ inverts more slowly than NH₃): the splitting is
antitone in the tunneling rate `κ`. -/
theorem tunnelingSplitting_antitone_kappa (A L : ℝ) (hA : 0 ≤ A) (hL : 0 < L) {κ κ' : ℝ}
    (h : κ ≤ κ') : tunnelingSplitting A κ' L ≤ tunnelingSplitting A κ L := by
  unfold tunnelingSplitting
  apply mul_le_mul_of_nonneg_left _ hA
  exact Real.exp_le_exp.mpr (by nlinarith)

/-! ### (3) STM imaging of allotropes -/

/-- **STM resolves atomic corrugation.**  Over a conductive allotrope surface (graphite, metallic
carbon) the tunnel current is positive, Ohmic in bias, and *exponentially* sensitive to the
tip–sample gap, so sub-ångström height differences produce order-of-magnitude current contrast. -/
theorem stm_images_atomic_corrugation (G V κ : ℝ) (hG : 0 < G) (hV : 0 < V) (hκ : 0 < κ) :
    0 < stmCurrent G V κ 0 ∧
      ∀ d d' : ℝ, d ≤ d' → stmCurrent G V κ d' ≤ stmCurrent G V κ d :=
  ⟨stmCurrent_pos G V κ 0 hG hV,
   fun _d _d' h => stmCurrent_antitone_gap G V κ (mul_pos hG hV).le hκ h⟩

/-! ### (4) Field-emission ionization, tied to `Chemistry.Binding` -/

/-- **Higher ionization energy suppresses cold field emission.**  Using the spine's hydrogenic
binding magnitude `μ Z_eff²/(2n²)` as the field-emission barrier parameter `b`, a more tightly
bound electron (larger effective charge, hence larger ionization energy) emits fewer electrons at
fixed applied field — the field-ionization analogue of the work-function trend. -/
theorem higher_ionization_suppresses_field_emission
    (a F μ n : ℝ) (ha : 0 ≤ a) (hF : 0 < F) (hμ : 0 ≤ μ) (hn : 0 < n)
    {zEff zEff' : ℝ} (hz : 0 ≤ zEff) (h : zEff ≤ zEff') :
    fowlerNordheim a (HqivSpine.Chemistry.Binding.hydrogenicBindingHartree μ zEff' n) F
      ≤ fowlerNordheim a (HqivSpine.Chemistry.Binding.hydrogenicBindingHartree μ zEff n) F := by
  apply fowlerNordheim_antitone_workfunction a F ha hF
  unfold HqivSpine.Chemistry.Binding.hydrogenicBindingHartree
  gcongr

/-! ### (5) Sub-barrier reaction crossing (Arrhenius vs tunneling) -/

/-- **Tunneling enables sub-barrier reactivity.**  Even for a state strictly below the activation
barrier (`E < V`), the transmission is strictly positive: a quantum reaction proceeds where the
classical Arrhenius picture forbids it. -/
theorem subBarrier_reactivity_positive (μ E V L : ℝ) :
    0 < transmissionCoefficient (kappaForbidden μ E V) L :=
  transmissionCoefficient_pos _ _

/-- **Taller activation barriers cross slower**: transmission is antitone in the barrier height. -/
theorem taller_barrier_slower_crossing (μ E L : ℝ) (hμ : 0 ≤ μ) (hL : 0 < L)
    {V V' : ℝ} (h : V ≤ V') :
    transmissionCoefficient (kappaForbidden μ E V') L
      ≤ transmissionCoefficient (kappaForbidden μ E V) L :=
  transmissionCoefficient_antitone_kappa L hL (kappaForbidden_monotone_V μ E hμ h)

/-- **Wider activation barriers cross slower**: transmission is antitone in the barrier width. -/
theorem wider_barrier_slower_crossing (μ E V : ℝ) (hμ : 0 < μ) (hEV : E < V) {L L' : ℝ}
    (h : L ≤ L') :
    transmissionCoefficient (kappaForbidden μ E V) L'
      ≤ transmissionCoefficient (kappaForbidden μ E V) L :=
  transmissionCoefficient_antitone_L _ (kappaForbidden_pos μ E V hμ hEV) h

/-! ## Provenance ledger — no smuggling

Held to the spine discipline (`Physics.Frontiers`, `AGENTS/ASSUMPTIONS.md` §7): every quantity is
either **derived from the foundation** or an **explicitly free bulk input** treated with care, and
no comparison numeral is smuggled.  The HQIV ontology quantizes only the **shell / horizon index**,
so the single *discrete* datum is the lock-in step `h`; the bulk-continuity section above *proves*
the dispersion is smooth in every other parameter (`continuous_slabDispersion_rate`,
`HQVM_discreteLaplacian_translation`, `slabDispersionContinuum_rotInvariant`).  The proved content is
therefore the **laws** relating these inputs, plus the one derived anchor — never their numeric
values. -/

/-- **Derived (foundation outputs), not posited.** -/
def tunnelingDerivedData : List String :=
  ["lockInCellStep = 1/(referenceM+1) = 1/5 = shellOmega referenceM (proton-shell frequency tag)",
   "discrete dispersion eigen-identity Δ_h ψ = slabDispersion · ψ on the 7-point stencil",
   "genuine evanescence cosh(κh) > 1 ⇒ κ ≠ 0 in a forbidden slab",
   "every monotonicity / conservation / continuum-limit law in the module",
   "field-emission barrier b = hydrogenicBindingHartree (tied to Chemistry.Binding)"]

/-- **Free bulk inputs (treated with care, NOT derived).**  Continuous observer / kinematic data;
the HQIV ontology makes these legitimately continuous (only the shell index `h` is quantized).  The
module proves *laws* about them and never fixes their values. -/
def tunnelingFreeBulkInputs : List String :=
  ["longitudinal rate κ (fixed by the evanescence condition from the inputs below)",
   "barrier height V₀ − E (observer-set; a derived-curvature barrier is a separate frontier)",
   "reduced mass μ (isotope masses are external comparison; only the μ-monotone KIE is proved)",
   "barrier width L", "transverse momenta k₁, k₂", "resonance half-width γ",
   "STM conductance G and bias V", "Fowler–Nordheim prefactor a", "attempt frequency ν",
   "group velocity v"]

/-- **Open frontier (not asserted as derived).**  A *fully* anchored tunneling rate would derive the
barrier height `V₀ − E` from the now-slice curvature imprint `δ_E` (`Physics.Curvature`) rather than
taking it as an observer input.  Until that closes, every `kappaForbidden μ E V` here carries a free
barrier — stated, not smuggled. -/
def derivedCurvatureBarrierFrontier : String :=
  "Derive the tunneling barrier height V₀ − E from the now-slice curvature imprint δ_E(m); " ++
  "currently V₀ − E is a free bulk input and the proved content is only the barrier-monotone laws."

/-- **No comparison numerals.**  The module introduces no decimal, PDG, CODATA, or fitted constant;
the only literal is the derived rational lock-in step `1/5`. -/
def tunnelingComparisonNumerals : List String := []

/-- **Closed (re-exported for contrast):** the lock-in step is the spine's derived proton-shell
frequency tag, the sole discrete datum — and it is genuinely used (anchored evanescence). -/
theorem lockInCellStep_derived_closed :
    lockInCellStep = shellOmega referenceM ∧ lockInCellStep = 1 / 5 :=
  ⟨lockInCellStep_eq_shellOmega, lockInCellStep_eq⟩

/-! ## Certificate bundles -/

/-- Bundles the load-bearing facts of the 3D patch-tunneling treatment. -/
structure PatchTunnelingCertified : Prop where
  dispersion :
    ∀ κ k₁ k₂ h x, HQVM_discreteLaplacian h (evanescentSlabMode κ k₁ k₂) x
      = slabDispersion κ k₁ k₂ h * evanescentSlabMode κ k₁ k₂ x
  split :
    ∀ κ k₁ k₂ h, slabDispersion κ k₁ k₂ h
      = longitudinalEigenFactor κ h - transverseEigenCost k₁ k₂ h
  transmission_pos : ∀ κ L, 0 < transmissionCoefficient κ L
  oneD_is_limit : ∀ h, transverseEigenCost 0 0 h = 0

theorem patchTunnelingCertified : PatchTunnelingCertified where
  dispersion := discreteLaplacian_evanescentSlabMode
  split := slabDispersion_split
  transmission_pos := transmissionCoefficient_pos
  oneD_is_limit := transverseEigenCost_zero

/-- Bundles the bulk-continuity layer. -/
structure BulkContinuityCertified : Prop where
  lattice_sinc :
    ∀ κ k₁ k₂ h, slabDispersion κ k₁ k₂ h
      = (2 * Real.sinh (κ * h / 2) / h) ^ 2
        - (2 * Real.sin (k₁ * h / 2) / h) ^ 2
        - (2 * Real.sin (k₂ * h / 2) / h) ^ 2
  rate_continuous :
    ∀ k₁ k₂ h, Continuous (fun κ : ℝ => slabDispersion κ k₁ k₂ h)
  translation_symmetry :
    ∀ h f v x, HQVM_discreteLaplacian h (fun y => f (y + v)) x
      = HQVM_discreteLaplacian h f (x + v)
  rotation_invariant :
    ∀ κ k₁ k₂ θ, slabDispersionContinuum κ (k₁ * Real.cos θ - k₂ * Real.sin θ)
        (k₁ * Real.sin θ + k₂ * Real.cos θ) = slabDispersionContinuum κ k₁ k₂

theorem bulkContinuityCertified : BulkContinuityCertified where
  lattice_sinc := slabDispersion_eq_latticeSinc
  rate_continuous := continuous_slabDispersion_rate
  translation_symmetry := HQVM_discreteLaplacian_translation
  rotation_invariant := slabDispersionContinuum_rotInvariant

/-- Bundles the textbook-parity toolkit. -/
structure TextbookParityCertified : Prop where
  exact_in_unit_interval :
    ∀ E V₀ κ L, 0 < E → E < V₀ →
      0 < transmissionExact E V₀ κ L ∧ transmissionExact E V₀ κ L ≤ 1
  conservation :
    ∀ E V₀ κ L, transmissionExact E V₀ κ L + reflectionExact E V₀ κ L = 1
  energy_monotone :
    ∀ μ V L, 0 ≤ μ → 0 < L → ∀ E E', E ≤ E' → E' < V →
      transmissionCoefficient (kappaForbidden μ E V) L
        ≤ transmissionCoefficient (kappaForbidden μ E' V) L
  half_life_monotone :
    ∀ ν κ, 0 < ν → 0 < κ → ∀ L L', L ≤ L' → halfLife ν κ L ≤ halfLife ν κ L'
  continuum_limit :
    ∀ κ, Filter.Tendsto (fun h : ℝ => longitudinalEigenFactor κ h) (𝓝[≠] 0) (𝓝 (κ ^ 2))

theorem textbookParityCertified : TextbookParityCertified where
  exact_in_unit_interval := fun E V₀ κ L hE hEV =>
    ⟨transmissionExact_pos E V₀ κ L hE hEV, transmissionExact_le_one E V₀ κ L hE hEV⟩
  conservation := transmission_add_reflection_eq_one
  energy_monotone := fun μ V L hμ hL _ _ hE h' =>
    transmissionCoefficient_monotone_E μ V L hμ hL hE h'
  half_life_monotone := fun ν κ hν hκ _ _ h => halfLife_monotone_L ν κ hν hκ h
  continuum_limit := tendsto_longitudinalEigenFactor

/-- Bundles the multi-cell / resonant toolkit. -/
structure AdvancedTunnelingCertified : Prop where
  wkb_in_unit_interval :
    ∀ κ Δx n, 0 ≤ Δx → (∀ j ∈ Finset.range n, 0 ≤ κ j) →
      0 < transmissionWKB κ Δx n ∧ transmissionWKB κ Δx n ≤ 1
  wkb_multiplicative :
    ∀ κ Δx n m, transmissionWKB κ Δx (n + m)
      = transmissionWKB κ Δx n * transmissionWKB (fun j => κ (n + j)) Δx m
  wkb_flat_reduces :
    ∀ κ₀ Δx n, transmissionWKB (fun _ => κ₀) Δx n = transmissionCoefficient κ₀ (Δx * n)
  resonance_is_unit_peak :
    ∀ γ E E_res, γ ≠ 0 →
      resonantTransmission γ E E_res ≤ resonantTransmission γ E_res E_res
      ∧ resonantTransmission γ E_res E_res = 1

theorem advancedTunnelingCertified : AdvancedTunnelingCertified where
  wkb_in_unit_interval := fun κ Δx n hΔx hκ =>
    ⟨transmissionWKB_pos κ Δx n, transmissionWKB_le_one κ Δx n hΔx hκ⟩
  wkb_multiplicative := transmissionWKB_mul
  wkb_flat_reduces := transmissionWKB_const
  resonance_is_unit_peak := fun γ E E_res hγ =>
    ⟨resonantTransmission_le_resonance γ E E_res hγ,
     resonantTransmission_at_resonance γ E_res hγ⟩

/-- Bundles the chemistry-layer consequences: kinetic isotope effect, double-well/inversion
splitting, STM corrugation, field-emission ionization trend, and sub-barrier reactivity. -/
structure ChemistryTunnelingCertified : Prop where
  kinetic_isotope_effect :
    ∀ E V L, 0 < L → E ≤ V → ∀ μH μD, 0 ≤ μH → μH ≤ μD →
      transmissionCoefficient (kappaForbidden μD E V) L
        ≤ transmissionCoefficient (kappaForbidden μH E V) L
  double_well_resonance : ∀ γ E_res, γ ≠ 0 → resonantTransmission γ E_res E_res = 1
  inversion_splits : ∀ A κ L, 0 < A → 0 < tunnelingSplitting A κ L
  stm_exponential_gap :
    ∀ G V κ, 0 < G → 0 < V → 0 < κ →
      0 < stmCurrent G V κ 0 ∧ ∀ d d', d ≤ d' → stmCurrent G V κ d' ≤ stmCurrent G V κ d
  subBarrier_reactivity : ∀ μ E V L, 0 < transmissionCoefficient (kappaForbidden μ E V) L

theorem chemistryTunnelingCertified : ChemistryTunnelingCertified where
  kinetic_isotope_effect := fun E V L hL hEV _ _ hμ h =>
    kineticIsotopeEffect_ge_one E V L hL hEV hμ h
  double_well_resonance := fun γ E_res hγ => resonant_double_well_perfect_transfer γ E_res hγ
  inversion_splits := fun A κ L hA => inversion_doublet_split A κ L hA
  stm_exponential_gap := fun G V κ hG hV hκ => stm_images_atomic_corrugation G V κ hG hV hκ
  subBarrier_reactivity := fun μ E V L => subBarrier_reactivity_positive μ E V L

end HqivSpine.Physics

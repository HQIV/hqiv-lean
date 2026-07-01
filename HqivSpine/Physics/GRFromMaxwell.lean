import HqivSpine.Physics.Gravity

/-!
# `HqivSpine.Physics.GRFromMaxwell` — linearized Einstein gravity is O-Maxwell

`Action` gave the gauge divergence operator `∑_μ F a μ ν = 4π·J`; `Gravity` gave the Friedmann
constraint and the lattice coupling `G_eff(φ) = φ^α`. This module shows the **gravitational sector
shares the gauge operator**: the weak-field (Newtonian) Einstein equation is *exactly* the discrete
O-Maxwell equation with the gauge current replaced by a mass current scaled by `G_eff(φ)`.

* **Newtonian limit = O-Maxwell.** The linearized Einstein equation `divergence Φ = 4π·G_eff(φ)·ρ`
  is the Euler–Lagrange stationarity `EL = 0` for the rescaled gravitational current `G_eff(φ)·ρ`
  (`linearizedEinstein_iff_EL`) — gravity is Maxwell with coupling `G_eff` and a mass source.
* **Friedmann ⇒ critical density.** At any positive curvature the constraint holds *iff* the total
  density is the critical density `ρ_c(φ) = (3−γ)φ²/(8π·G_eff φ)` (`friedmann_iff_critical`), which
  is strictly positive (`criticalDensity_pos`).
* **Hubble's law.** With `H(φ) = φ` the recession velocity `v = φ·d` is linear and strictly
  increasing in distance (`recessionVelocity_linear`, `recessionVelocity_strictMono`).

Everything is bundled in `GRClosure` / `gr_from_maxwell_closure`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.GRFromMaxwell

open HqivSpine.Physics HqivSpine.Foundation

/-- A mass current has the same shape as a gauge current. -/
abbrev MassCurrent := Current

/-! ## The Newtonian limit is the O-Maxwell equation -/

/-- **Gravitational source** = mass current scaled by the lattice coupling `G_eff(φ)`. -/
noncomputable def gravCurrent (φ : ℝ) (ρ : MassCurrent) : Current := fun a ν => gEff φ * ρ a ν

/-- **Linearized (weak-field) Einstein equation:** the discrete Poisson equation
`divergence Φ = 4π·G_eff(φ)·ρ`, the same operator as O-Maxwell. -/
def linearizedEinstein (φ : ℝ) (ρ : MassCurrent) (Φ : Potential) (a : Fin 8) (ν : Fin 4) : Prop :=
  divergence Φ a ν = 4 * Real.pi * gEff φ * ρ a ν

/-- **GR from Maxwell.** The linearized Einstein equation is precisely the O-Maxwell
Euler–Lagrange stationarity for the rescaled gravitational current. -/
theorem linearizedEinstein_iff_EL (φ : ℝ) (ρ : MassCurrent) (Φ : Potential) (a : Fin 8) (ν : Fin 4) :
    EL (gravCurrent φ ρ) Φ a ν = 0 ↔ linearizedEinstein φ ρ Φ a ν := by
  rw [EL_eq_zero_iff_maxwell]
  unfold linearizedEinstein gravCurrent
  constructor
  · intro h; rw [h]; ring
  · intro h; rw [h]; ring

/-! ## Friedmann ⇒ critical density -/

/-- **Critical density** `ρ_c(φ) = (3−γ)·φ² / (8π·G_eff φ)` solving the Friedmann constraint. -/
noncomputable def criticalDensity (φ : ℝ) : ℝ :=
  (3 - gammaHQIV) * φ ^ 2 / (8 * Real.pi * gEff φ)

theorem criticalDensity_pos {φ : ℝ} (hφ : 0 < φ) : 0 < criticalDensity φ := by
  unfold criticalDensity
  have h3 : (0 : ℝ) < 3 - gammaHQIV := by rw [three_minus_gammaHQIV]; norm_num
  have hG : 0 < gEff φ := gEff_pos hφ
  exact div_pos (mul_pos h3 (by positivity)) (by positivity)

/-- **Friedmann holds iff the total density is critical** (at any positive curvature). -/
theorem friedmann_iff_critical (φ : ℝ) (hφ : 0 < φ) (rhoM rhoR : ℝ) :
    friedmann φ rhoM rhoR ↔ rhoM + rhoR = criticalDensity φ := by
  have hG : 0 < gEff φ := gEff_pos hφ
  have hD : 0 < 8 * Real.pi * gEff φ := by positivity
  unfold friedmann criticalDensity hubble
  rw [eq_div_iff hD.ne']
  constructor
  · intro h; linear_combination -h
  · intro h; linear_combination -h

/-! ## Hubble's law -/

/-- **Recession velocity** `v = H(φ)·d = φ·d`. -/
def recessionVelocity (φ d : ℝ) : ℝ := hubble φ * d

theorem recessionVelocity_eq (φ d : ℝ) : recessionVelocity φ d = φ * d := rfl

/-- **Hubble's law is linear** in comoving distance. -/
theorem recessionVelocity_linear (φ d₁ d₂ : ℝ) :
    recessionVelocity φ (d₁ + d₂) = recessionVelocity φ d₁ + recessionVelocity φ d₂ := by
  unfold recessionVelocity hubble; ring

/-- More distant sources recede faster (for positive Hubble curvature). -/
theorem recessionVelocity_strictMono {φ : ℝ} (hφ : 0 < φ) {d₁ d₂ : ℝ} (h : d₁ < d₂) :
    recessionVelocity φ d₁ < recessionVelocity φ d₂ := by
  unfold recessionVelocity hubble; exact mul_lt_mul_of_pos_left h hφ

/-! ## Closure -/

/-- **GR-from-Maxwell discharge bundle.** -/
structure GRClosure : Prop where
  newtonian_is_maxwell : ∀ (φ : ℝ) (ρ : MassCurrent) (Φ : Potential) (a : Fin 8) (ν : Fin 4),
    EL (gravCurrent φ ρ) Φ a ν = 0 ↔ linearizedEinstein φ ρ Φ a ν
  friedmann_critical : ∀ (φ : ℝ), 0 < φ → ∀ (rhoM rhoR : ℝ),
    friedmann φ rhoM rhoR ↔ rhoM + rhoR = criticalDensity φ
  hubble_linear : ∀ (φ d₁ d₂ : ℝ),
    recessionVelocity φ (d₁ + d₂) = recessionVelocity φ d₁ + recessionVelocity φ d₂

/-- **The GR-from-Maxwell story is discharged:** linearized Einstein is the O-Maxwell operator,
the Friedmann constraint fixes the critical density, and `H(φ)=φ` gives a linear Hubble law. -/
theorem gr_from_maxwell_closure : GRClosure where
  newtonian_is_maxwell := linearizedEinstein_iff_EL
  friedmann_critical := friedmann_iff_critical
  hubble_linear := recessionVelocity_linear

end HqivSpine.Physics.GRFromMaxwell

import HqivSpine.Physics.DiscreteHeatCycle
import HqivSpine.Physics.Exclusion
import HqivSpine.Physics.Thermodynamics

/-!
# `HqivSpine.Physics.DiscreteDiffusion` — Brownian bookkeeping on a finite patch

Pure-HQIV diffusion/Brownian structure on the periodic mesh of `DiscreteHeatCycle`,
packaged from the shell temperature ladder and the monogamy mode budget of `Exclusion`.
This is the discrete, finite-patch analogue of Einstein's 1905 diffusion relations:

* **Density.** A nonnegative field `ρ` on `Cₙ` carries a total mass `∑ ρᵢ`; when positive,
  the normalised density is a finite probability mass (`totalMass`, `normalisedDensity`).
* **Fick flux.** Edge flux `jᵢ = −D (∇ρ)ᵢ` is the oriented jump driven by the discrete
  gradient (`fickFlux`).
* **Continuity / conservation.** The cycle Laplacian is divergence-form with zero net flux:
  `∑ (Δρ)ᵢ = 0` (`sum_lap_eq_zero`), so an explicit-Euler diffusion step preserves total mass
  (`eulerStep_totalMass_eq`, `eulerStep_totalMass_eq'`).  Under the same CFL bound as
  `DiscreteHeatCycle`, the quadratic density energy is nonincreasing
  (`eulerStep_energy_le_of_cfl`).
* **Dissipation.** Entropy production reuses the heat dissipation sign:
  `σ = −⟨ρ, Δρ⟩ ≥ 0` (`entropyProductionCycle`, `entropyProductionCycle_nonneg`).
* **Shell-scaled diffusion.** The dimensionless coefficient `D_m = ν·T_m` with `T_m = 1/(m+1)`
  increases on hotter inner shells (`shellDiffusionCoeff_pos`, `shellDiffusionCoeff_inner_larger`).
* **MSD bookkeeping.** A unit-variance symmetric walk on the cycle has
  `⟨(Δx)²⟩ = steps` in lattice units (`symmetricStepVariance`, `msdAfterSteps`).
  The Einstein readout `2 D t = MSD` is recorded as the structural identity
  `einsteinMsdReadout`.
* **Accessible count budget.** Monogamous occupation through shell `m` is capped by
  `cumulativeModes m = 4(m+1)(m+2)` — no Avogadro input on the spine path.

Honest scope: discrete dissipation, flux, and MSD *bookkeeping* on a 1-D periodic mesh —
**not** a continuum Brownian path measure, Stokes drag law, or fitted physical `D(η,T)`.
Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Physics.DiscreteDiffusion

open scoped BigOperators
open HqivSpine.Physics HqivSpine.Physics.DiscreteHeatCycle HqivSpine.Physics.Thermodynamics

variable {n : ℕ} [NeZero n]

/-! ## Density on the cycle -/

/-- **Total mass** (integrated density) on the cycle `Cₙ`. -/
def totalMass (ρ : ZMod n → ℝ) : ℝ := ∑ i, ρ i

theorem totalMass_nonneg (ρ : ZMod n → ℝ) (hρ : ∀ i, 0 ≤ ρ i) : 0 ≤ totalMass ρ :=
  Finset.sum_nonneg fun i _ => hρ i

/-- **Normalised density** when the total mass is positive. -/
noncomputable def normalisedDensity (ρ : ZMod n → ℝ) (_hρ : 0 < totalMass ρ) (i : ZMod n) : ℝ :=
  ρ i / totalMass ρ

theorem normalisedDensity_nonneg (ρ : ZMod n → ℝ) (hρ : 0 < totalMass ρ) (hρ' : ∀ i, 0 ≤ ρ i)
    (i : ZMod n) : 0 ≤ normalisedDensity ρ hρ i := by
  unfold normalisedDensity
  exact div_nonneg (hρ' i) (le_of_lt hρ)

theorem sum_normalisedDensity_eq_one (ρ : ZMod n → ℝ) (hρ : 0 < totalMass ρ) :
    (∑ i, normalisedDensity ρ hρ i) = 1 := by
  unfold normalisedDensity
  have hden : totalMass ρ ≠ 0 := ne_of_gt hρ
  rw [← Finset.sum_div]
  exact div_self hden

/-- **Discrete continuity:** the cycle Laplacian has zero net divergence. -/
theorem sum_lap_eq_zero (ρ : ZMod n → ℝ) : (∑ i, lap ρ i) = 0 := by
  simp only [lap, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_shift_add_one ρ, sum_shift_sub_one ρ]
  ring

/-! ## Fick flux and zero net divergence -/

/-- **Fick flux** on oriented edge `i`: `jᵢ = −D (∇ρ)ᵢ`. -/
def fickFlux (D : ℝ) (ρ : ZMod n → ℝ) (i : ZMod n) : ℝ := -D * fwdDiff ρ i

omit [NeZero n] in
/-- **Pointwise continuity form:** flux divergence is `−D Δρ` on each mesh site. -/
theorem fickFlux_divergence_eq_neg_D_mul_lap (D : ℝ) (ρ : ZMod n → ℝ) (i : ZMod n) :
    fickFlux D ρ i - fickFlux D ρ (i - 1) = -D * lap ρ i := by
  rw [lap_eq_fwdDiff_sub]
  unfold fickFlux
  ring

/-- **Fick flux net divergence vanishes** on the closed cycle. -/
theorem fickFlux_net_divergence_zero (D : ℝ) (ρ : ZMod n → ℝ) :
    (∑ i : ZMod n, (fickFlux D ρ i - fickFlux D ρ (i - 1))) = 0 := by
  have reindex : (∑ i, fwdDiff ρ (i - 1)) = ∑ i, fwdDiff ρ i := sum_shift_sub_one (fwdDiff ρ)
  simp only [fickFlux]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [reindex]
  ring

/-! ## Mass conservation under diffusion -/

/-- One explicit Euler diffusion step preserves **total mass**. -/
theorem eulerStep_totalMass_eq (ν dt : ℝ) (ρ : ZMod n → ℝ) :
    totalMass (eulerStep ν dt ρ) = totalMass ρ + dt * ν * (∑ i, lap ρ i) := by
  unfold totalMass eulerStep
  calc
    (∑ i, (ρ i + dt * ν * lap ρ i))
        = (∑ i, ρ i) + dt * ν * (∑ i, lap ρ i) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]

theorem eulerStep_totalMass_eq' (ν dt : ℝ) (ρ : ZMod n → ℝ) :
    totalMass (eulerStep ν dt ρ) = totalMass ρ := by
  rw [eulerStep_totalMass_eq, sum_lap_eq_zero, mul_zero, add_zero]

/-- Under the cycle CFL bound, the explicit diffusion step is a quadratic Lyapunov step. -/
theorem eulerStep_energy_le_of_cfl {ν dt : ℝ} (hν : 0 ≤ ν) (hdt : 0 ≤ dt)
    (hCFL : dt * ν * 4 ≤ 2) (ρ : ZMod n → ℝ) :
    energy (eulerStep ν dt ρ) ≤ energy ρ :=
  HqivSpine.Physics.DiscreteHeatCycle.eulerStep_energy_le_of_cfl hν hdt hCFL ρ

/-! ## Entropy production (second-law packaging) -/

/-- **Entropy-production proxy** on `Cₙ`: `σ = −⟨ρ, Δρ⟩`. -/
noncomputable def entropyProductionCycle (ρ : ZMod n → ℝ) : ℝ := -∑ i, ρ i * lap ρ i

theorem entropyProductionCycle_eq_jumpEnergy (ρ : ZMod n → ℝ) :
    entropyProductionCycle ρ = jumpEnergy ρ := by
  unfold entropyProductionCycle
  rw [sum_u_lap_eq_neg_jumpEnergy, neg_neg]

theorem entropyProductionCycle_nonneg (ρ : ZMod n → ℝ) : 0 ≤ entropyProductionCycle ρ := by
  rw [entropyProductionCycle_eq_jumpEnergy]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-! ## Shell-scaled diffusion coefficient -/

/-- **Dimensionless diffusion coefficient** at shell `m`: `D_m = ν·T_m`. -/
noncomputable def shellDiffusionCoeff (m : ℕ) (ν : ℝ) : ℝ := ν * shellTemp m

theorem shellDiffusionCoeff_eq (m : ℕ) (ν : ℝ) :
    shellDiffusionCoeff m ν = ν / ((m : ℝ) + 1) := by
  unfold shellDiffusionCoeff shellTemp
  unfold shellOmega
  ring

theorem shellDiffusionCoeff_pos (m : ℕ) {ν : ℝ} (hν : 0 < ν) : 0 < shellDiffusionCoeff m ν := by
  unfold shellDiffusionCoeff
  exact mul_pos hν (shellTemp_pos m)

/-- Hotter inner shells carry a **larger** diffusion coefficient at fixed `ν`. -/
theorem shellDiffusionCoeff_inner_larger {m : ℕ} {ν : ℝ} (hν : 0 < ν) :
    shellDiffusionCoeff (m + 1) ν < shellDiffusionCoeff m ν := by
  unfold shellDiffusionCoeff
  exact mul_lt_mul_of_pos_left (thirdLaw_hotter_inside m) hν

/-! ## Symmetric-walk MSD bookkeeping -/

/-- Unit lattice spacing for the cycle mesh. -/
def latticeSpacing : ℝ := 1

/-- **Per-step variance** of a symmetric nearest-neighbour walk on the cycle. -/
def symmetricStepVariance : ℝ := latticeSpacing ^ 2

theorem symmetricStepVariance_eq_one : symmetricStepVariance = 1 := by
  unfold symmetricStepVariance latticeSpacing
  ring

/-- **Mean-square displacement** after `steps` unit-variance symmetric steps (1-D readout). -/
def msdAfterSteps (steps : ℕ) : ℝ := (steps : ℝ) * symmetricStepVariance

theorem msdAfterSteps_zero : msdAfterSteps 0 = 0 := by
  unfold msdAfterSteps symmetricStepVariance latticeSpacing
  ring

theorem msdAfterSteps_succ (steps : ℕ) :
    msdAfterSteps (steps + 1) = msdAfterSteps steps + symmetricStepVariance := by
  unfold msdAfterSteps
  push_cast
  ring

theorem msdAfterSteps_nonneg (steps : ℕ) : 0 ≤ msdAfterSteps steps := by
  unfold msdAfterSteps symmetricStepVariance latticeSpacing
  positivity

/-- **Einstein MSD readout** in 1-D: `MSD = 2 D t`. -/
def einsteinMsdReadout (D t : ℝ) : ℝ := 2 * D * t

theorem einsteinMsdReadout_eq_msdAfterSteps (D : ℝ) (steps : ℕ) (dt : ℝ)
    (h : einsteinMsdReadout D (steps * dt) = msdAfterSteps steps) :
    einsteinMsdReadout D (steps * dt) = msdAfterSteps steps := h

/-- When `t = steps·dt`, the diffusion coefficient consistent with unit-step MSD is
`D = steps/(2·steps·dt) = 1/(2·dt)` in lattice units. -/
noncomputable def diffusionCoeffFromStep (dt : ℝ) : ℝ := 1 / (2 * dt)

theorem einsteinMsdReadout_from_step (steps : ℕ) {dt : ℝ} (hdt : 0 < dt) :
    einsteinMsdReadout (diffusionCoeffFromStep dt) (steps * dt) = msdAfterSteps steps := by
  unfold einsteinMsdReadout diffusionCoeffFromStep msdAfterSteps symmetricStepVariance latticeSpacing
  field_simp [ne_of_gt hdt]

/-! ## Accessible particle budget (monogamy, no Avogadro) -/

/-- **Accessible single-particle slots** through shell `m` — the monogamy occupation budget. -/
def accessibleParticleBudget (m : ℕ) : ℕ := cumulativeModes m

theorem accessibleParticleBudget_eq (m : ℕ) :
    accessibleParticleBudget m = 4 * (m + 1) * (m + 2) := cumulativeModes_eq m

theorem accessibleParticleBudget_zero : accessibleParticleBudget 0 = 8 := cumulativeModes_zero

theorem accessibleParticleBudget_strictMono : StrictMono accessibleParticleBudget :=
  cumulativeModes_strictMono

/-- A particle content of `N` quanta fits monogamously through shell `m`. -/
def particleContentFitsShell (N m : ℕ) : Prop := N ≤ accessibleParticleBudget m

theorem particleContentFitsShell_referenceM :
    particleContentFitsShell (accessibleParticleBudget referenceM) referenceM := le_rfl

/-! ## Closure bundle -/

/-- **Discrete Brownian / diffusion discharge bundle.** -/
structure DiscreteBrownianClosure (n : ℕ) [NeZero n] : Prop where
  mass_conserved :
    ∀ (ν dt : ℝ) (ρ : ZMod n → ℝ), totalMass (eulerStep ν dt ρ) = totalMass ρ
  energy_nonincreasing :
    ∀ {ν dt : ℝ}, 0 ≤ ν → 0 ≤ dt → dt * ν * 4 ≤ 2 →
      ∀ ρ : ZMod n → ℝ, energy (eulerStep ν dt ρ) ≤ energy ρ
  entropy_production_nonneg : ∀ ρ : ZMod n → ℝ, 0 ≤ entropyProductionCycle ρ
  fick_pointwise_continuity :
    ∀ (D : ℝ) (ρ : ZMod n → ℝ) (i : ZMod n),
      fickFlux D ρ i - fickFlux D ρ (i - 1) = -D * lap ρ i
  fick_zero_divergence :
    ∀ (D : ℝ) (ρ : ZMod n → ℝ),
      (∑ i : ZMod n, (fickFlux D ρ i - fickFlux D ρ (i - 1))) = 0
  shell_diffusion_positive : ∀ (m : ℕ) (ν : ℝ), 0 < ν → 0 < shellDiffusionCoeff m ν
  shell_diffusion_inner_larger :
    ∀ (m : ℕ) (ν : ℝ), 0 < ν → shellDiffusionCoeff (m + 1) ν < shellDiffusionCoeff m ν
  msd_linear : ∀ steps : ℕ, msdAfterSteps steps = (steps : ℝ) * symmetricStepVariance
  einstein_msd_readout :
    ∀ (steps : ℕ) (dt : ℝ), 0 < dt →
      einsteinMsdReadout (diffusionCoeffFromStep dt) (steps * dt) = msdAfterSteps steps
  accessible_budget_grows : StrictMono accessibleParticleBudget

/-- **Discrete Brownian bookkeeping is discharged** on every cycle length `n`. -/
theorem discrete_brownian_closure (n : ℕ) [NeZero n] : DiscreteBrownianClosure n where
  mass_conserved := @eulerStep_totalMass_eq' n _
  energy_nonincreasing := fun hν hdt hCFL ρ => eulerStep_energy_le_of_cfl hν hdt hCFL ρ
  entropy_production_nonneg := @entropyProductionCycle_nonneg n _
  fick_pointwise_continuity := fun D ρ i => fickFlux_divergence_eq_neg_D_mul_lap D ρ i
  fick_zero_divergence := fun D ρ => @fickFlux_net_divergence_zero n _ D ρ
  shell_diffusion_positive := fun m _ hν => shellDiffusionCoeff_pos (m := m) hν
  shell_diffusion_inner_larger := fun m _ hν => shellDiffusionCoeff_inner_larger (m := m) hν
  msd_linear := fun _ => rfl
  einstein_msd_readout := fun steps _ hdt => einsteinMsdReadout_from_step steps hdt
  accessible_budget_grows := accessibleParticleBudget_strictMono

end HqivSpine.Physics.DiscreteDiffusion

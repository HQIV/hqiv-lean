import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Order.MinMax
import Hqiv.Geometry.HQVMetric
import Hqiv.Geometry.ContinuumSpacetimeChart
import Hqiv.Physics.ModifiedMaxwell
import Hqiv.Physics.SchematicPlasmaCurrent

/-!
# HQIV effective fluid closure (scaffold)

**Purpose (F0):** shared vocabulary with `pyhqiv.fluid` and [AGENTS/FLUID_OMAXWELL_ROADMAP.md](../../AGENTS/FLUID_OMAXWELL_ROADMAP.md).

Defines the **modified inertia** factor `f`, the **vacuum momentum source** from `∇(φ δ̇θ′)`,
and **eddy viscosity** — the same formulas as the Python reference implementation.

**Not claimed:** Navier–Stokes PDEs, existence of solutions, global regularity, or derivation from
O-Maxwell / plasma. This module is definitions + a few algebraic consequences only.

**F3:** `PlasmaFluidClosureAssumptions`, `nuTotal_eq_nuMol_add_hqivEddy` — scalar stress split + HQIV eddy
viscosity as explicit **Props** (not from kinetics).

**F4:** `CoefficientsTowardClassicalNS`, `hqivVacuumMomentumSource3_toward_classical_of_grad_zero` — coefficient
step toward classical NS; **not** global PDE regularity.

**Plasma scale bridges (proved bookkeeping):** `hqivEddyViscosity_nonneg`, `hqivEddyViscosity_pos`,
`PlasmaFluidClosureAssumptions.mk_shell_debye` — identify `Θ_local` with shell temperature `T m`
(`AuxiliaryField`) and `ℓ_coh` with `lambdaDebye` (`SchematicPlasmaCurrent`). **Not** a kinetic derivation.

## F2 — O-Maxwell / plasma ↔ fluid inputs (hypothesis map; same table as roadmap §F2)

Candidate attachments — **no dynamical derivation** from Maxwell to fluid; the **F2 typed bundle**
below makes chart-level equalities explicit (`Prop` hypotheses, not a single global field theorem).

| Fluid input | Role | Lean anchors | Status / gap |
|:------------|:-----|:-------------|:-------------|
| **γ** | prefactor in `hqivVacuumMomentumSource3`, `hqivEddyViscosity` | `Hqiv.gamma_HQIV`, `gamma_eq_2_5` | matched (2/5) |
| **φ** | `hqivFluidInertiaFactor`; `hqivVacuumMomentumSource3` | `phi_of_T`, `phi_of_shell`; continuum `φF`, `coordsGradientComponents` in `ContinuumOmaxwellClosure`; φ-term in `emergentMaxwellInhomogeneous_O_general` | **Typed at a chart point:** `OMaxwellFluidChartHypothesis.phi_pointwise` (`phiFluid = φF c`) |
| **∇φ** (3-vector) | `hqivVacuumMomentumSource3` (`gradPhi`) | `grad_φ` placeholder in `ModifiedMaxwell`; real slot `coordsGradientComponents` / `contravariantGradientComponentsAt` in `ContinuumOmaxwellClosure` (spatial ν = 1,2,3) | **Typed:** `chartSpatialPhiGradient` + `OMaxwellFluidChartHypothesis.grad_phi_spatial` |
| **δ̇θ′** | `hqivVacuumMomentumSource3`, `hqivEddyViscosity` | `ModifiedMaxwell.delta_theta_prime E′` is **tipping from electric energy**, not ∂ₜ | **Typed bridge:** `OMaxwellFluidChartHypothesis.dotTheta_bridge` (`dotTheta = delta_theta_prime Eprime`). Still not ∂ₜ unless you add extra hypotheses. |
| **∇δ̇θ′** | `hqivVacuumMomentumSource3` (`gradDot`) | not defined in library yet | **Typed:** `chartSpatialDotGradient dotF` + `OMaxwellFluidChartHypothesis.grad_dot_spatial` — choose scalar `dotF` on the chart (proxy for δ̇θ′); not unique |
| **Θ_local** | `hqivEddyViscosity` | `AuxiliaryField`, `x_over_theta_from_horizons` (`OctonionicLightCone`), horizon/time-angle in `HQVMetric` | closure: pick horizon proxy |
| **ℓ_coh** | `hqivEddyViscosity` | `SchematicPlasmaCurrent.lambdaDebye`, `plasmaRadialProfile` | hypothesis: Debye vs integral scale |
| **Plasma J** | O–fluid bookkeeping | `J_src` in `emergentMaxwellInhomogeneous_O_general`; `J_O_plasma`, `schematicPlasmaScalar` | **EM leg:** `J_O_plasma_eq_schematic_on_em`, `abs_J_O_plasma_em`; **coherence:** `coherenceFromPlasmaAmp` + `PlasmaFluidClosureAssumptions.mk_shell_debye_plasmaAmp` (not stress tensor) |

**Read order:** `ModifiedMaxwell` → `ContinuumOmaxwellClosure` → `SchematicPlasmaCurrent` → this file.

**F2 (typed bundle):** `OMaxwellFluidChartHypothesis` below — explicit chart point `c`, continuum scalars
`φF` / `dotF`, spatial gradients via `coordsGradientComponents` on indices `ν = 1,2,3`, and
`dotTheta = delta_theta_prime Eprime`. **Not** a dynamical theorem: a **`Prop` bundle** agents can
cite to discharge the former “gap” rows in the table.
-/

namespace Hqiv.Physics

open Hqiv
open Hqiv.Geometry

noncomputable section

/-- Modified inertia factor `f(a_loc, φ) = a_loc / (a_loc + φ/6)` (paper; Python `f_inertia`).

Momentum form: `ρ f` multiplies the material derivative; equivalently acceleration picks up `1/f`.
Requires `a_loc + φ/6 ≠ 0` for the literal division. -/
noncomputable def hqivFluidInertiaFactor (aLoc phi : ℝ) : ℝ :=
  aLoc / (aLoc + phi / 6)

theorem hqivFluidInertiaFactor_eq_one_of_phi_zero {aLoc : ℝ} (ha : aLoc ≠ 0) :
    hqivFluidInertiaFactor aLoc 0 = 1 := by
  simp [hqivFluidInertiaFactor, ha]

theorem hqivFluidInertiaFactor_pos {aLoc phi : ℝ} (ha : 0 < aLoc) (hden : 0 < aLoc + phi / 6) :
    0 < hqivFluidInertiaFactor aLoc phi :=
  div_pos ha hden

theorem hqivFluidInertiaFactor_le_one_of_nonneg_phi {aLoc phi : ℝ} (_ha : 0 < aLoc) (hφ : 0 ≤ phi)
    (hden : 0 < aLoc + phi / 6) :
    hqivFluidInertiaFactor aLoc phi ≤ 1 := by
  unfold hqivFluidInertiaFactor
  rw [div_le_one hden]
  linarith [hφ]

theorem hqivFluidInertiaFactor_lt_one_of_pos_phi {aLoc phi : ℝ} (_ha : 0 < aLoc) (hφ : 0 < phi)
    (hden : 0 < aLoc + phi / 6) :
    hqivFluidInertiaFactor aLoc phi < 1 := by
  unfold hqivFluidInertiaFactor
  rw [div_lt_one hden]
  linarith [hφ]

/-- Vacuum momentum source `-γ/6 * ∇(φ δ̇θ′)` as spatial components on `Fin 3`.

Corresponds to `g_vac_vector` in `pyhqiv.fluid` with `term = φ * ∇δ̇θ′ + δ̇θ′ * ∇φ`. -/
noncomputable def hqivVacuumMomentumSource3 (gamma phi dot : ℝ) (gradPhi gradDot : Fin 3 → ℝ) :
    Fin 3 → ℝ := fun i =>
  (-gamma / 6) * (phi * gradDot i + dot * gradPhi i)

theorem hqivVacuumMomentumSource3_eq_zero_of_grad_zero (gamma phi dot : ℝ)
    (gradPhi gradDot : Fin 3 → ℝ) (hΦ : gradPhi = 0) (hD : gradDot = 0) :
    hqivVacuumMomentumSource3 gamma phi dot gradPhi gradDot = 0 := by
  funext i
  simp [hqivVacuumMomentumSource3, hΦ, hD]

theorem hqivVacuumMomentumSource3_smul_gamma (c γ phi dot : ℝ) (gradPhi gradDot : Fin 3 → ℝ) :
    hqivVacuumMomentumSource3 (c * γ) phi dot gradPhi gradDot =
      c • hqivVacuumMomentumSource3 γ phi dot gradPhi gradDot := by
  funext i
  simp [hqivVacuumMomentumSource3, Pi.smul_apply, smul_eq_mul]
  ring

/-- Affine in `gradPhi` (fixed `phi`, `dot`, `gradDot`): avoids double-counting the shared `phi * gradDot`
term when naively adding two full `hqivVacuumMomentumSource3` values. -/
theorem hqivVacuumMomentumSource3_add_gradPhi (γ phi dot : ℝ) (gΦ₁ gΦ₂ gradDot : Fin 3 → ℝ) :
    hqivVacuumMomentumSource3 γ phi dot (gΦ₁ + gΦ₂) gradDot =
      hqivVacuumMomentumSource3 γ phi dot gΦ₁ gradDot + hqivVacuumMomentumSource3 γ phi dot gΦ₂ gradDot -
        hqivVacuumMomentumSource3 γ phi dot 0 gradDot := by
  funext i
  simp [hqivVacuumMomentumSource3, Pi.add_apply]
  ring

/-- Affine in `gradDot` (fixed `phi`, `dot`, `gradPhi`). -/
theorem hqivVacuumMomentumSource3_add_gradDot (γ phi dot : ℝ) (gradPhi gD₁ gD₂ : Fin 3 → ℝ) :
    hqivVacuumMomentumSource3 γ phi dot gradPhi (gD₁ + gD₂) =
      hqivVacuumMomentumSource3 γ phi dot gradPhi gD₁ + hqivVacuumMomentumSource3 γ phi dot gradPhi gD₂ -
        hqivVacuumMomentumSource3 γ phi dot gradPhi 0 := by
  funext i
  simp [hqivVacuumMomentumSource3, Pi.add_apply]
  ring

theorem hqivVacuumMomentumSource3_add_phi (γ φ₁ φ₂ dot : ℝ) (gradPhi gradDot : Fin 3 → ℝ) :
    hqivVacuumMomentumSource3 γ (φ₁ + φ₂) dot gradPhi gradDot =
      hqivVacuumMomentumSource3 γ φ₁ dot gradPhi gradDot + hqivVacuumMomentumSource3 γ φ₂ dot gradPhi gradDot -
        hqivVacuumMomentumSource3 γ 0 dot gradPhi gradDot := by
  funext i
  simp [hqivVacuumMomentumSource3, Pi.add_apply]
  ring

theorem hqivVacuumMomentumSource3_add_dot (γ phi dot₁ dot₂ : ℝ) (gradPhi gradDot : Fin 3 → ℝ) :
    hqivVacuumMomentumSource3 γ phi (dot₁ + dot₂) gradPhi gradDot =
      hqivVacuumMomentumSource3 γ phi dot₁ gradPhi gradDot + hqivVacuumMomentumSource3 γ phi dot₂ gradPhi gradDot -
        hqivVacuumMomentumSource3 γ phi 0 gradPhi gradDot := by
  funext i
  simp [hqivVacuumMomentumSource3, Pi.add_apply]
  ring

/-!
## F2 — Typed O-Maxwell ↔ fluid chart hypothesis

Index convention on `Fin 4 → ℝ` charts: `0` = time, `1..3` = space (same as `ContinuumSpacetimeChart` /
`ContinuumOmaxwellClosure`). Spatial 3-vectors for the fluid use `Fin 3` embedded by `spatialFin4`.
-/

/-- Embed spatial index `i : Fin 3` as chart index `ν = i+1` (columns `1,2,3`). -/
def spatialFin4 (i : Fin 3) : Fin 4 :=
  ⟨i.val + 1, by fin_cases i <;> decide⟩

/-- Spatial part of `(∇φ)_ν` from a continuum scalar `φF` at chart point `c`. -/
noncomputable def chartSpatialPhiGradient (φF : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ) : Fin 3 → ℝ :=
  fun i => coordsGradientComponents φF c (spatialFin4 i)

/-- Spatial gradient of a second scalar `dotF` (proxy for a δ̇θ′-like field on the chart). -/
noncomputable def chartSpatialDotGradient (dotF : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ) : Fin 3 → ℝ :=
  fun i => coordsGradientComponents dotF c (spatialFin4 i)

/-- **F2 hypothesis bundle:** at chart point `c`, fluid inputs `(phiFluid, gradPhi3, dotTheta, gradDot3)`
are identified with continuum fields `(φF, dotF)` and the EM proxy `Eprime` for `Hqiv.delta_theta_prime`.

* `phi_pointwise`: single scalar equality — fluid `φ` equals `φF c` (same as O-Maxwell evaluation point).
* `grad_phi_spatial`: `gradPhi3` equals the spatial components of `coordsGradientComponents φF c`.
* `dotTheta_bridge`: fluid rate equals `delta_theta_prime Eprime` (tipping-from-`E′` channel — **not** an
  abstract time derivative unless you add further hypotheses).
* `grad_dot_spatial`: `gradDot3` equals spatial `∇(dotF)` — **choose** `dotF` to model δ̇θ′ or an
  auxiliary clock field; no uniqueness claim. -/
structure OMaxwellFluidChartHypothesis (φF dotF : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ)
    (phiFluid dotTheta : ℝ) (gradPhi3 gradDot3 : Fin 3 → ℝ) (Eprime : ℝ) : Prop where
  phi_pointwise : phiFluid = φF c
  grad_phi_spatial : gradPhi3 = chartSpatialPhiGradient φF c
  dotTheta_bridge : dotTheta = delta_theta_prime Eprime
  grad_dot_spatial : gradDot3 = chartSpatialDotGradient dotF c

/-- Under `OMaxwellFluidChartHypothesis`, `hqivVacuumMomentumSource3` depends only on `(φF, dotF, c, Eprime)`. -/
theorem hqivVacuumMomentumSource3_of_OMaxwellFluidChartHypothesis (γ : ℝ) (φF dotF : (Fin 4 → ℝ) → ℝ)
    (c : Fin 4 → ℝ) (phiFluid dotTheta : ℝ) (gradPhi3 gradDot3 : Fin 3 → ℝ) (Eprime : ℝ)
    (h : OMaxwellFluidChartHypothesis φF dotF c phiFluid dotTheta gradPhi3 gradDot3 Eprime) :
    hqivVacuumMomentumSource3 γ phiFluid dotTheta gradPhi3 gradDot3 =
      hqivVacuumMomentumSource3 γ (φF c) (delta_theta_prime Eprime) (chartSpatialPhiGradient φF c)
        (chartSpatialDotGradient dotF c) := by
  rcases h with ⟨hp, hg, hd, hdot⟩
  simp [hp, hg, hd, hdot]

/-- HQIV eddy viscosity `ν_eddy = γ Θ |δ̇θ′| ℓ_coh² C` (Python `eddy_viscosity`). -/
noncomputable def hqivEddyViscosity (gamma ThetaLocal dotTheta lCoh coherence : ℝ) : ℝ :=
  gamma * ThetaLocal * |dotTheta| * lCoh ^ 2 * coherence

/-- Same as `hqivEddyViscosity` with `γ = gamma_HQIV` (2/5). -/
noncomputable def hqivEddyViscosity_HQIV (ThetaLocal dotTheta lCoh coherence : ℝ) : ℝ :=
  hqivEddyViscosity gamma_HQIV ThetaLocal dotTheta lCoh coherence

theorem hqivEddyViscosity_HQIV_eq (ThetaLocal dotTheta lCoh coherence : ℝ) :
    hqivEddyViscosity_HQIV ThetaLocal dotTheta lCoh coherence =
      gamma_HQIV * ThetaLocal * |dotTheta| * lCoh ^ 2 * coherence := by
  simp [hqivEddyViscosity_HQIV, hqivEddyViscosity]

/-!
## F3 — Plasma-as-fluid closure (hypothesis bundle)

**Not derived** from kinetic theory or O-Maxwell here: the bundle records explicit **assumptions**
that (i) scalar shear viscosities add and (ii) the eddy piece matches `hqivEddyViscosity`, with
coherence in `[0,1]`.
-/

/-- **Hypothesis bundle (F3):** molecular + eddy scalar shear viscosities sum to the total; eddy part
matches `hqivEddyViscosity`; coherence `C` lies in `[0,1]`. No claim of derivation from plasma
kinetics or Maxwell. -/
structure PlasmaFluidClosureAssumptions (nuMol nuEddy nuTotal gamma Theta dot lCoh C : ℝ) : Prop where
  stress_scalar_split : nuTotal = nuMol + nuEddy
  eddy_viscosity_hqiv : nuEddy = hqivEddyViscosity gamma Theta dot lCoh C
  coherence_in_unit : 0 ≤ C ∧ C ≤ 1

theorem nuTotal_eq_nuMol_add_hqivEddy (nuMol nuEddy nuTotal gamma Theta dot lCoh C : ℝ)
    (h : PlasmaFluidClosureAssumptions nuMol nuEddy nuTotal gamma Theta dot lCoh C) :
    nuTotal = nuMol + hqivEddyViscosity gamma Theta dot lCoh C := by
  rw [h.stress_scalar_split, h.eddy_viscosity_hqiv]

/-!
## F4 — Coefficient-level limit toward classical NS (not global PDE)

Classical 3D incompressible Navier–Stokes **global regularity** is **not** proved in this repository
(see project narrative). This structure only records **algebraic** coefficient conditions: laminar
inertia (`f = 1`) and vanishing vacuum momentum source — a usual step before comparing to
classical NS *form*.
-/

/-- **Hypothesis bundle (F4):** modified inertia factor is `1` and vacuum source vanishes — coefficient
step toward classical NS; **not** a PDE theorem. -/
structure CoefficientsTowardClassicalNS (aLoc phi : ℝ) (gVac : Fin 3 → ℝ) : Prop where
  laminar_inertia : hqivFluidInertiaFactor aLoc phi = 1
  vacuum_source_zero : gVac = 0

theorem hqivVacuumMomentumSource3_toward_classical_of_grad_zero (gamma phi dot : ℝ)
    (gradPhi gradDot : Fin 3 → ℝ) (hΦ : gradPhi = 0) (hD : gradDot = 0) :
    CoefficientsTowardClassicalNS 1 0
        (hqivVacuumMomentumSource3 gamma phi dot gradPhi gradDot) := by
  refine ⟨?_, ?_⟩
  · -- aLoc = 1, phi = 0 ⇒ f = 1
    simp [hqivFluidInertiaFactor, one_ne_zero]
  · -- gVac = 0
    rw [hqivVacuumMomentumSource3_eq_zero_of_grad_zero gamma phi dot gradPhi gradDot hΦ hD]

/-- F2 chart + vanishing spatial gradients ⇒ F4 classical coefficient limit (`f=1`, `g_{\mathrm{vac}}=0`). -/
theorem coefficientsTowardClassicalNS_of_OMaxwell_flat_gradients
    (γ : ℝ) (φF dotF : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ) (phiFluid dotTheta : ℝ)
    (gradPhi3 gradDot3 : Fin 3 → ℝ) (Eprime : ℝ)
    (h : OMaxwellFluidChartHypothesis φF dotF c phiFluid dotTheta gradPhi3 gradDot3 Eprime)
    (hΦflat : chartSpatialPhiGradient φF c = 0) (hDflat : chartSpatialDotGradient dotF c = 0) :
    CoefficientsTowardClassicalNS (1 : ℝ) 0 (hqivVacuumMomentumSource3 γ phiFluid dotTheta gradPhi3 gradDot3) := by
  have hΦ : gradPhi3 = 0 := by rw [h.grad_phi_spatial, hΦflat]
  have hD : gradDot3 = 0 := by rw [h.grad_dot_spatial, hDflat]
  exact hqivVacuumMomentumSource3_toward_classical_of_grad_zero γ phiFluid dotTheta gradPhi3 gradDot3 hΦ hD

/-- **F2+F4 record:** chart identification packaged with the induced classical coefficients. -/
structure OMaxwellFluidChartClassicalCoefficients (φF dotF : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ)
    (phiFluid dotTheta : ℝ) (gradPhi3 gradDot3 : Fin 3 → ℝ) (Eprime γ : ℝ) : Prop where
  chart_hyp : OMaxwellFluidChartHypothesis φF dotF c phiFluid dotTheta gradPhi3 gradDot3 Eprime
  classical_coeff :
    CoefficientsTowardClassicalNS (1 : ℝ) 0 (hqivVacuumMomentumSource3 γ phiFluid dotTheta gradPhi3 gradDot3)

theorem OMaxwellFluidChartClassicalCoefficients.mk_flat_gradients
    (γ : ℝ) (φF dotF : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ) (phiFluid dotTheta : ℝ)
    (gradPhi3 gradDot3 : Fin 3 → ℝ) (Eprime : ℝ)
    (h : OMaxwellFluidChartHypothesis φF dotF c phiFluid dotTheta gradPhi3 gradDot3 Eprime)
    (hΦflat : chartSpatialPhiGradient φF c = 0) (hDflat : chartSpatialDotGradient dotF c = 0) :
    OMaxwellFluidChartClassicalCoefficients φF dotF c phiFluid dotTheta gradPhi3 gradDot3 Eprime γ :=
  { chart_hyp := h
    classical_coeff :=
      coefficientsTowardClassicalNS_of_OMaxwell_flat_gradients γ φF dotF c phiFluid dotTheta gradPhi3
        gradDot3 Eprime h hΦflat hDflat }

/-!
## Eddy viscosity — sign lemmas and shell / Debye specialization

`Θ_local = T m` matches the auxiliary-field doc (`phi_of_shell` uses temperature ladder).
`ℓ_coh = lambdaDebye` ties the eddy length to the same Debye placeholder used in
`SchematicPlasmaCurrent.plasmaRadialProfile`.
-/

theorem hqivEddyViscosity_nonneg (γ Θ dot ℓ C : ℝ) (hγ : 0 ≤ γ) (hΘ : 0 ≤ Θ) (hC : 0 ≤ C) :
    0 ≤ hqivEddyViscosity γ Θ dot ℓ C := by
  unfold hqivEddyViscosity
  have habs : 0 ≤ |dot| := abs_nonneg dot
  have hℓ2 : 0 ≤ ℓ ^ 2 := sq_nonneg ℓ
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hγ hΘ) habs) hℓ2) hC

theorem hqivEddyViscosity_pos (γ Θ dot ℓ C : ℝ) (hγ : 0 < γ) (hΘ : 0 < Θ) (hℓ : 0 < ℓ) (hC : 0 < C)
    (hdot : dot ≠ 0) : 0 < hqivEddyViscosity γ Θ dot ℓ C := by
  unfold hqivEddyViscosity
  have habs : 0 < |dot| := abs_pos.mpr hdot
  have hℓ2 : 0 < ℓ ^ 2 := sq_pos_of_pos hℓ
  exact mul_pos (mul_pos (mul_pos (mul_pos hγ hΘ) habs) hℓ2) hC

theorem hqivEddyViscosity_HQIV_nonneg (Θ dot ℓ C : ℝ) (hΘ : 0 ≤ Θ) (hC : 0 ≤ C) :
    0 ≤ hqivEddyViscosity_HQIV Θ dot ℓ C := by
  have hγ : 0 ≤ gamma_HQIV := by rw [gamma_eq_2_5]; norm_num
  simpa [hqivEddyViscosity_HQIV] using hqivEddyViscosity_nonneg gamma_HQIV Θ dot ℓ C hγ hΘ hC

theorem hqivEddyViscosity_HQIV_shell_debye_nonneg (m : ℕ) (dotTheta C : ℝ) (hC : 0 ≤ C) :
    0 ≤ hqivEddyViscosity_HQIV (T m) dotTheta lambdaDebye C := by
  refine hqivEddyViscosity_HQIV_nonneg (T m) dotTheta lambdaDebye C ?_ hC
  · exact le_of_lt (T_pos m)

/-- Eddy viscosity using shell temperature `T m` and schematic Debye length `lambdaDebye`. -/
noncomputable def hqivEddyViscosity_HQIV_shell_debye (m : ℕ) (dotTheta C : ℝ) : ℝ :=
  hqivEddyViscosity_HQIV (T m) dotTheta lambdaDebye C

theorem hqivEddyViscosity_HQIV_shell_debye_eq (m : ℕ) (dotTheta C : ℝ) :
    hqivEddyViscosity_HQIV_shell_debye m dotTheta C =
      gamma_HQIV * T m * |dotTheta| * lambdaDebye ^ 2 * C := by
  simp [hqivEddyViscosity_HQIV_shell_debye, hqivEddyViscosity_HQIV, hqivEddyViscosity]

theorem hqivEddyViscosity_HQIV_shell_debye_pos (m : ℕ) (dotTheta C : ℝ) (hC : 0 < C)
    (hdot : dotTheta ≠ 0) : 0 < hqivEddyViscosity_HQIV_shell_debye m dotTheta C := by
  unfold hqivEddyViscosity_HQIV_shell_debye hqivEddyViscosity_HQIV hqivEddyViscosity
  have hγ : 0 < gamma_HQIV := by rw [gamma_eq_2_5]; norm_num
  exact
    hqivEddyViscosity_pos gamma_HQIV (T m) dotTheta lambdaDebye C hγ (T_pos m) lambdaDebye_pos hC
      hdot

/-!
### F3 — constructor when `Θ = T m` and `ℓ_coh = lambdaDebye`
-/

/-- Build **F3** assuming the eddy piece matches `hqivEddyViscosity_HQIV` at shell temperature and
Debye length (schematic plasma scale). -/
theorem PlasmaFluidClosureAssumptions.mk_shell_debye (m : ℕ) (nuMol nuEddy nuTotal dotTheta C : ℝ)
    (hsplit : nuTotal = nuMol + nuEddy)
    (hnu : nuEddy = hqivEddyViscosity_HQIV (T m) dotTheta lambdaDebye C)
    (hC : 0 ≤ C ∧ C ≤ 1) :
    PlasmaFluidClosureAssumptions nuMol nuEddy nuTotal gamma_HQIV (T m) dotTheta lambdaDebye C :=
  { stress_scalar_split := hsplit
    eddy_viscosity_hqiv := hnu
    coherence_in_unit := hC }

theorem nuTotal_eq_nuMol_add_shell_debye (m : ℕ) (nuMol nuEddy nuTotal dotTheta C : ℝ)
    (h : PlasmaFluidClosureAssumptions nuMol nuEddy nuTotal gamma_HQIV (T m) dotTheta lambdaDebye C) :
    nuTotal = nuMol + hqivEddyViscosity_HQIV_shell_debye m dotTheta C := by
  simpa [hqivEddyViscosity_HQIV_shell_debye] using
    nuTotal_eq_nuMol_add_hqivEddy nuMol nuEddy nuTotal gamma_HQIV (T m) dotTheta lambdaDebye C h

/-!
### Coherence from plasma amplitude (closure choice)

`coherenceFromPlasmaAmp` maps the F3 factor `C ∈ [0,1]` to `min 1 (κ * |schematicPlasmaScalar|)` so the
**same** scalar amplitude as `J_O_plasma` on the EM leg (`SchematicPlasmaCurrent`) feeds eddy viscosity.
**Not** derived from kinetics—only definitional bookkeeping + `min` inequalities.
-/

noncomputable def coherenceFromPlasmaAmp (κ j₀ r : ℝ) : ℝ :=
  min 1 (κ * |schematicPlasmaScalar j₀ r|)

theorem coherenceFromPlasmaAmp_nonneg (κ j₀ r : ℝ) (hκ : 0 ≤ κ) : 0 ≤ coherenceFromPlasmaAmp κ j₀ r := by
  unfold coherenceFromPlasmaAmp
  have hx : 0 ≤ κ * |schematicPlasmaScalar j₀ r| :=
    mul_nonneg hκ (abs_nonneg _)
  cases le_total (κ * |schematicPlasmaScalar j₀ r|) 1 with
  | inl h1 => rw [min_eq_right h1]; exact hx
  | inr h1 => rw [min_eq_left h1]; exact zero_le_one

theorem coherenceFromPlasmaAmp_le_one (κ j₀ r : ℝ) : coherenceFromPlasmaAmp κ j₀ r ≤ 1 := by
  unfold coherenceFromPlasmaAmp
  exact min_le_left _ _

theorem coherenceFromPlasmaAmp_mem_unit (κ j₀ r : ℝ) (hκ : 0 ≤ κ) :
    0 ≤ coherenceFromPlasmaAmp κ j₀ r ∧ coherenceFromPlasmaAmp κ j₀ r ≤ 1 :=
  ⟨coherenceFromPlasmaAmp_nonneg κ j₀ r hκ, coherenceFromPlasmaAmp_le_one κ j₀ r⟩

theorem coherenceFromPlasmaAmp_mono_κ (κ₁ κ₂ j₀ r : ℝ) (horder : κ₁ ≤ κ₂) :
    coherenceFromPlasmaAmp κ₁ j₀ r ≤ coherenceFromPlasmaAmp κ₂ j₀ r := by
  unfold coherenceFromPlasmaAmp
  have hs : 0 ≤ |schematicPlasmaScalar j₀ r| := abs_nonneg _
  have hmul : κ₁ * |schematicPlasmaScalar j₀ r| ≤ κ₂ * |schematicPlasmaScalar j₀ r| :=
    mul_le_mul_of_nonneg_right horder hs
  exact min_le_min le_rfl hmul

theorem coherenceFromPlasmaAmp_mono_abs_j₀ (κ j₀₁ j₀₂ r : ℝ) (hκ : 0 ≤ κ)
    (habs : |j₀₁| ≤ |j₀₂|) :
    coherenceFromPlasmaAmp κ j₀₁ r ≤ coherenceFromPlasmaAmp κ j₀₂ r := by
  have hs :
      |schematicPlasmaScalar j₀₁ r| ≤ |schematicPlasmaScalar j₀₂ r| := by
    rw [abs_schematicPlasmaScalar, abs_schematicPlasmaScalar]
    have hp : 0 ≤ plasmaRadialProfile r := le_of_lt (plasmaRadialProfile_pos r)
    exact mul_le_mul_of_nonneg_right habs hp
  unfold coherenceFromPlasmaAmp
  exact min_le_min le_rfl (mul_le_mul_of_nonneg_left hs hκ)

theorem coherenceFromPlasmaAmp_eq_one_iff (κ j₀ r : ℝ) :
    coherenceFromPlasmaAmp κ j₀ r = 1 ↔ 1 ≤ κ * |schematicPlasmaScalar j₀ r| := by
  unfold coherenceFromPlasmaAmp
  rw [min_eq_left_iff]

theorem coherenceFromPlasmaAmp_eq_mul_iff (κ j₀ r : ℝ) :
    coherenceFromPlasmaAmp κ j₀ r = κ * |schematicPlasmaScalar j₀ r| ↔
      κ * |schematicPlasmaScalar j₀ r| ≤ 1 := by
  unfold coherenceFromPlasmaAmp
  rw [min_eq_right_iff]

/-- `hqivEddyViscosity_HQIV` at shell + Debye with `C = coherenceFromPlasmaAmp κ j₀ r`. -/
noncomputable def hqivEddyViscosity_HQIV_shell_debye_plasmaAmp (m : ℕ) (dotTheta κ j₀ r : ℝ) : ℝ :=
  hqivEddyViscosity_HQIV_shell_debye m dotTheta (coherenceFromPlasmaAmp κ j₀ r)

theorem PlasmaFluidClosureAssumptions.mk_shell_debye_plasmaAmp (m : ℕ)
    (nuMol nuEddy nuTotal dotTheta κ j₀ r : ℝ)
    (hsplit : nuTotal = nuMol + nuEddy)
    (hnu :
      nuEddy =
        hqivEddyViscosity_HQIV (T m) dotTheta lambdaDebye (coherenceFromPlasmaAmp κ j₀ r))
    (hκ : 0 ≤ κ) :
    PlasmaFluidClosureAssumptions nuMol nuEddy nuTotal gamma_HQIV (T m) dotTheta lambdaDebye
      (coherenceFromPlasmaAmp κ j₀ r) :=
  PlasmaFluidClosureAssumptions.mk_shell_debye m nuMol nuEddy nuTotal dotTheta (coherenceFromPlasmaAmp κ j₀ r)
    hsplit hnu (coherenceFromPlasmaAmp_mem_unit κ j₀ r hκ)

theorem nuTotal_eq_nuMol_add_shell_debye_plasmaAmp (m : ℕ) (nuMol nuEddy nuTotal dotTheta κ j₀ r : ℝ)
    (h :
      PlasmaFluidClosureAssumptions nuMol nuEddy nuTotal gamma_HQIV (T m) dotTheta lambdaDebye
        (coherenceFromPlasmaAmp κ j₀ r)) :
    nuTotal = nuMol + hqivEddyViscosity_HQIV_shell_debye_plasmaAmp m dotTheta κ j₀ r := by
  simpa [hqivEddyViscosity_HQIV_shell_debye_plasmaAmp] using
    nuTotal_eq_nuMol_add_shell_debye m nuMol nuEddy nuTotal dotTheta (coherenceFromPlasmaAmp κ j₀ r) h

end

end Hqiv.Physics

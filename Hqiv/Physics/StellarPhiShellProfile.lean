import Hqiv.Physics.ContinuousXiCoupling
import Hqiv.Physics.CoronalLongitudinalStress
import Hqiv.Physics.FluxTubeStressDivergenceBridge

/-!
# Stellar φ(s) profile from the HQIV shell ladder

**Purpose:** supply the footpoint-anchored axial φ chart used in coronal / flux-tube
programmes: linear interpolation in the continuous horizon coordinate ξ = m+1 between
photosphere and corona shell samples, with constant axial gradient and vanishing bulk
second derivative.

Companion: `papers/longitudinal_em_force_hqiv/hqiv_longitudinal_em_force.tex` §shell;
`Hqiv.Physics.ContinuousXiPath`, `Hqiv.Physics.FluxTubeStressDivergenceBridge`.

## Proof status (all definitional / algebraic, zero `sorry`)

* **§1.** Column geometry `(m_photo, m_corona, L)`.
* **§2.** Fractional coordinate `t ∈ [0,1]` and ξ(t) linear bridge.
* **§3.** φ(t) = `phiOfXi ξ(t)` and closed linear form in `Δφ`.
* **§4.** Axial gradients: `∂_s φ = Δφ/L`, `∂²_s φ = 0`.
* **§5.** Flux-tube / footpoint-only stress bundle hook.
* **§6.** Discharged honesty ledger.

**Not claimed:** unique solar `(m_photo, m_corona)` assignment; curved loop geometry;
nonlinear φ(s) from full MHD; automatic derivation of `L` from shells.
-/

namespace Hqiv.Physics

open Hqiv

noncomputable section

/-!
## §1. Column geometry
-/

/-- Stellar flux-tube column: shell-anchored footpoints and positive bulk length `L`. -/
structure StellarColumnGeometry where
  m_photo : ℕ
  m_corona : ℕ
  order : m_photo ≤ m_corona
  columnLength : ℝ
  length_pos : 0 < columnLength

/-- Alias to the coronal shell pair for boundary φ jumps. -/
def StellarColumnGeometry.toCoronalShells (geom : StellarColumnGeometry) : CoronalColumnShells :=
  ⟨geom.m_photo, geom.m_corona, geom.order⟩

theorem StellarColumnGeometry.phi_jump_eq
    (geom : StellarColumnGeometry) :
    coronalPhiJump geom.toCoronalShells =
      phi_of_shell geom.m_corona - phi_of_shell geom.m_photo := by
  unfold coronalPhiJump toCoronalShells
  ring

/-!
## §2. Fractional coordinate and ξ bridge
-/

/-- Normalised axial fraction `t` along the column (`0` = photosphere foot, `1` = corona foot). -/
def stellarColumnFraction (t : ℝ) : ℝ := t

/-- Continuous horizon coordinate along the column: linear in `t` between shell samples. -/
def stellarXiAtFraction (geom : StellarColumnGeometry) (t : ℝ) : ℝ :=
  xiOfShell geom.m_photo + t * (xiOfShell geom.m_corona - xiOfShell geom.m_photo)

theorem stellarXiAtFraction_photo (geom : StellarColumnGeometry) :
    stellarXiAtFraction geom 0 = xiOfShell geom.m_photo := by
  unfold stellarXiAtFraction xiOfShell
  ring

theorem stellarXiAtFraction_corona (geom : StellarColumnGeometry) :
    stellarXiAtFraction geom 1 = xiOfShell geom.m_corona := by
  unfold stellarXiAtFraction xiOfShell
  ring

theorem stellarXiAtFraction_linear (geom : StellarColumnGeometry) (t : ℝ) :
    stellarXiAtFraction geom t =
      (1 - t) * xiOfShell geom.m_photo + t * xiOfShell geom.m_corona := by
  unfold stellarXiAtFraction
  ring

/-!
## §3. φ profile along the column
-/

/-- Axial φ readout at fraction `t` using the continuous shell chart `phiOfXi`. -/
def stellarPhiAtFraction (geom : StellarColumnGeometry) (t : ℝ) : ℝ :=
  phiOfXi (stellarXiAtFraction geom t)

theorem stellarPhiAtFraction_photo (geom : StellarColumnGeometry) :
    stellarPhiAtFraction geom 0 = phi_of_shell geom.m_photo := by
  rw [stellarPhiAtFraction, stellarXiAtFraction_photo, phiOfXi_xiOfShell]

theorem stellarPhiAtFraction_corona (geom : StellarColumnGeometry) :
    stellarPhiAtFraction geom 1 = phi_of_shell geom.m_corona := by
  rw [stellarPhiAtFraction, stellarXiAtFraction_corona, phiOfXi_xiOfShell]

/-- Closed linear form: `φ(t) = φ_photo + t · Δφ`. -/
theorem stellarPhiAtFraction_linear_jump
    (geom : StellarColumnGeometry) (t : ℝ) :
    stellarPhiAtFraction geom t =
      phi_of_shell geom.m_photo + t * coronalPhiJump geom.toCoronalShells := by
  simp [stellarPhiAtFraction, stellarXiAtFraction, phiOfXi, xiOfShell,
    phiTemperatureCoeff_eq_two, coronalPhiJump_closed_form, phi_of_shell_closed_form,
    StellarColumnGeometry.toCoronalShells]
  ring

theorem stellarPhiAtFraction_endpoints_jump
    (geom : StellarColumnGeometry) :
    stellarPhiAtFraction geom 1 - stellarPhiAtFraction geom 0 =
      coronalPhiJump geom.toCoronalShells := by
  rw [stellarPhiAtFraction_photo, stellarPhiAtFraction_corona]
  unfold coronalPhiJump StellarColumnGeometry.toCoronalShells
  ring

/-!
## §4. Axial gradients (footpoint-linear chart)
-/

/-- Constant axial gradient `∂_s φ = Δφ / L` for the linear footpoint chart. -/
def stellarPhiGradAlong (geom : StellarColumnGeometry) : ℝ :=
  coronalPhiJump geom.toCoronalShells / geom.columnLength

/-- Bulk second derivative vanishes for the linear profile. -/
def stellarPhiSecondGrad : ℝ := 0

theorem stellarPhiGradAlong_eq_jump_over_length (geom : StellarColumnGeometry) :
    stellarPhiGradAlong geom = coronalPhiJump geom.toCoronalShells / geom.columnLength := rfl

theorem stellarPhiSecondGrad_zero : stellarPhiSecondGrad = 0 := rfl

theorem stellarPhiGradAlong_integrated_eq_jump
    (geom : StellarColumnGeometry) :
    stellarPhiGradAlong geom * geom.columnLength = coronalPhiJump geom.toCoronalShells := by
  unfold stellarPhiGradAlong
  field_simp [geom.length_pos.ne']

theorem stellarPhiGradAlong_ne_zero_of_jump_pos
    (geom : StellarColumnGeometry) (hΔ : 0 < coronalPhiJump geom.toCoronalShells) :
    stellarPhiGradAlong geom ≠ 0 := by
  unfold stellarPhiGradAlong
  intro h
  have hj0 : coronalPhiJump geom.toCoronalShells = 0 := by
    field_simp [geom.length_pos.ne'] at h
    simpa using h
  linarith [hΔ, hj0]

/-!
## §5. Flux-tube footpoint bundle
-/

/-- Footpoint φ jump slot (boundary / chart parameter). -/
def stellarPhiJump (geom : StellarColumnGeometry) : ℝ :=
  coronalPhiJump geom.toCoronalShells

/-- Footpoint-linear φ chart packaged for the 1-D stress divergence bridge. -/
structure StellarPhiFluxTubeProfileBundle
    (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ)
    (nq J sigma Estar couplingLog : ℝ) (geom : StellarColumnGeometry)
    (stress : FluxTube1DStressChart) (stressCoeff : LongitudinalStressCoefficientIdentification) : Prop where
  footpoint :
    FluxTubeFootpointOnlyStressBridge φ_val φF c nq J sigma Estar couplingLog
      (stellarPhiJump geom) stress stressCoeff
      (phi_of_shell geom.m_photo) (phi_of_shell geom.m_corona)
  grad_second :
    stress.gradPhiSecond = stellarPhiSecondGrad
  grad_along_eq_jump :
    stress.gradPhiAlong = stellarPhiJump geom

theorem StellarPhiFluxTubeProfileBundle.bulk_divergence_zero
    {φ_val : ℝ} {φF : (Fin 4 → ℝ) → ℝ} {c : Fin 4 → ℝ}
    {nq J sigma Estar couplingLog : ℝ} {geom : StellarColumnGeometry}
    {stress : FluxTube1DStressChart} {stressCoeff : LongitudinalStressCoefficientIdentification}
    (h : StellarPhiFluxTubeProfileBundle φ_val φF c nq J sigma Estar couplingLog geom stress
      stressCoeff) :
    fluxTubeAxialStressDivergence stress = 0 :=
  h.footpoint.bulk_divergence_zero

theorem StellarPhiFluxTubeProfileBundle.column_gradient_eq_jump_over_length
    {φ_val : ℝ} {φF : (Fin 4 → ℝ) → ℝ} {c : Fin 4 → ℝ}
    {nq J sigma Estar couplingLog : ℝ} {geom : StellarColumnGeometry}
    {stress : FluxTube1DStressChart} {stressCoeff : LongitudinalStressCoefficientIdentification}
    (_h : StellarPhiFluxTubeProfileBundle φ_val φF c nq J sigma Estar couplingLog geom stress
      stressCoeff) :
    stellarPhiGradAlong geom * geom.columnLength = stellarPhiJump geom := by
  unfold stellarPhiJump
  exact stellarPhiGradAlong_integrated_eq_jump geom

theorem StellarPhiFluxTubeProfileBundle.stress_gradAlong_eq_jump
    {φ_val : ℝ} {φF : (Fin 4 → ℝ) → ℝ} {c : Fin 4 → ℝ}
    {nq J sigma Estar couplingLog : ℝ} {geom : StellarColumnGeometry}
    {stress : FluxTube1DStressChart} {stressCoeff : LongitudinalStressCoefficientIdentification}
    (h : StellarPhiFluxTubeProfileBundle φ_val φF c nq J sigma Estar couplingLog geom stress
      stressCoeff) :
    stress.gradPhiAlong = stellarPhiJump geom :=
  h.grad_along_eq_jump

/-!
## §6. Honesty ledger
-/

structure StellarPhiShellProfileHonestyLedger : Prop where
  phi_linear :
    ∀ (geom : StellarColumnGeometry) (t : ℝ),
      stellarPhiAtFraction geom t =
        phi_of_shell geom.m_photo + t * coronalPhiJump geom.toCoronalShells
  grad_integrated :
    ∀ (geom : StellarColumnGeometry),
      stellarPhiGradAlong geom * geom.columnLength = coronalPhiJump geom.toCoronalShells
  footpoint_bulk_zero :
    ∀ {φ_val φF c nq J sigma Estar couplingLog geom stress stressCoeff}
      (h : StellarPhiFluxTubeProfileBundle φ_val φF c nq J sigma Estar couplingLog geom stress
        stressCoeff),
      fluxTubeAxialStressDivergence stress = 0

theorem stellarPhiShellProfileHonestyLedger_discharged : StellarPhiShellProfileHonestyLedger where
  phi_linear := stellarPhiAtFraction_linear_jump
  grad_integrated := stellarPhiGradAlong_integrated_eq_jump
  footpoint_bulk_zero := StellarPhiFluxTubeProfileBundle.bulk_divergence_zero

end

end Hqiv.Physics

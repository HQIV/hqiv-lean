import Hqiv.Physics.HQIVFluidClosureScaffold
import Hqiv.Physics.OrbitalFlybyScaffold
import Hqiv.Physics.NuclearOutsideTemperatureDynamics
import Hqiv.Physics.FanoResonance
import Hqiv.Physics.GlobalDetuning
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Compact-object rotating crust scaffold (variational torque + induction)

**Purpose:** name the thin-shell integral of `hqivLongitudinalStressTensor3` /
`hqivLongitudinalStressForce3` on a co-rotating neutron-star crust, and couple
induction resistivity `η` to the outside-temperature + gravity modulator stack.

Python: `scripts/hqiv_compact_object_mass.py` (`crust_misalign_torque_from_stress_div_si`,
`induction_resistivity_eta_from_environment`).

**Proved here:** algebra on shell factors, nonnegativity, and agreement of the
misaligning torque with the prior witness coupling `χ = a_LT a_∥ / a_grav²`.

**Not claimed:** full GR rotating-star metric, MHD induction PDE, crust elasticity
PDE, or variational derivation of the closed-form shell integral from a unique
continuum chart — the closed form is the **named thin-shell discharge** of the
longitudinal stress divergence slot, same honesty as `OrbitalFlybyScaffold` orbit
hypotheses.
-/

namespace Hqiv.Physics

open Hqiv

noncomputable section

/-- Lense–Thirring vector fraction ``λ = γ sin²θ ρ_pol`` (flyby repartition slot). -/
noncomputable def compactObjectLtVectorFraction (sinColatitude rhoPol : ℝ) : ℝ :=
  gamma_HQIV * sinColatitude ^ 2 * max rhoPol 0

theorem compactObjectLtVectorFraction_nonneg (sinColatitude rhoPol : ℝ) :
    0 ≤ compactObjectLtVectorFraction sinColatitude rhoPol := by
  unfold compactObjectLtVectorFraction
  rw [gamma_eq_2_5]
  positivity

/-- Shear coupling ``χ = a_LT a_∥ / a_grav²`` (ψ_shear channel). -/
noncomputable def compactObjectShearCoupling (aLt aParallel aGrav : ℝ) : ℝ :=
  if aGrav = 0 then 0 else aLt * aParallel / (aGrav * aGrav)

theorem compactObjectShearCoupling_zero_of_zero_grav (aLt aParallel : ℝ) :
    compactObjectShearCoupling aLt aParallel 0 = 0 := by
  unfold compactObjectShearCoupling
  simp

/-- Thin-shell geometric screen ``(h/R)²``. -/
noncomputable def compactObjectCrustShellThinFactor (hShell radius : ℝ) : ℝ :=
  if radius = 0 then 0 else (hShell / radius) ^ 2

/-- Crust vs nuclear density contrast ``ρ_crust / ρ_n``. -/
noncomputable def compactObjectCrustDensityContrast (rhoCrust rhoNuclear : ℝ) : ℝ :=
  if rhoNuclear = 0 then 0 else rhoCrust / rhoNuclear

/-- Rindler screen ``1 − c_rindler_shared = 1 − γ/2``. -/
noncomputable def compactObjectCrustRindlerScreen : ℝ := 1 - c_rindler_shared

theorem compactObjectCrustRindlerScreen_eq_four_fifths :
    compactObjectCrustRindlerScreen = 4 / 5 := by
  unfold compactObjectCrustRindlerScreen c_rindler_shared
  rw [gamma_eq_2_5]
  norm_num

/-- Integrated crust shell mass ``4π R² h ρ``. -/
noncomputable def compactObjectCrustShellMass (radius hShell rhoCrust : ℝ) : ℝ :=
  4 * Real.pi * radius ^ 2 * hShell * rhoCrust

/-- LT-weighted longitudinal stress magnitude ``κ_L ρ Λ (s·∇φ) λ_LT``.

Links the scalar stress driver to `hqivLongitudinalStressTensor3` with an explicit
L-T tangent weight on the directional slot. -/
noncomputable def compactObjectLtStressMagnitude
    (kappaL rho couplingLog gradPhiAlong ltFraction : ℝ) : ℝ :=
  kappaL * rho * couplingLog * gradPhiAlong * ltFraction

theorem compactObjectLtStressMagnitude_eq_zero_of_lt_zero
    (kappaL rho couplingLog gradPhiAlong : ℝ) :
    compactObjectLtStressMagnitude kappaL rho couplingLog gradPhiAlong 0 = 0 := by
  unfold compactObjectLtStressMagnitude
  ring

/-- Misaligning torque from thin-shell discharge of `hqivLongitudinalStressForce3`.

``τ_mis = M_shell R a_grav |χ| sin²θ (h/R)² (ρ_c/ρ_n) (1 − γ/2)`` with
``χ = compactObjectShearCoupling a_LT a_∥ a_grav``. -/
noncomputable def crustMisalignTorqueFromStressDivergence
    (radius aGrav shearCoupling sinColatitude hShell rhoCrust rhoNuclear : ℝ) : ℝ :=
  let massShell := compactObjectCrustShellMass radius hShell rhoCrust
  let geo := sinColatitude ^ 2 * compactObjectCrustShellThinFactor hShell radius
  let densityFrac := compactObjectCrustDensityContrast rhoCrust rhoNuclear
  massShell * radius * aGrav * abs shearCoupling * geo * densityFrac *
    compactObjectCrustRindlerScreen

theorem crustMisalignTorqueFromStressDivergence_zero_of_zero_coupling
    (radius aGrav sinColatitude hShell rhoCrust rhoNuclear : ℝ) :
    crustMisalignTorqueFromStressDivergence radius aGrav 0 sinColatitude hShell rhoCrust rhoNuclear = 0 := by
  unfold crustMisalignTorqueFromStressDivergence
  ring

/-- Witness discharge: torque from explicit LT / parallel accelerations. -/
noncomputable def crustMisalignTorqueFromAccelerations
    (radius aGrav aLt aParallel sinColatitude hShell rhoCrust rhoNuclear : ℝ) : ℝ :=
  crustMisalignTorqueFromStressDivergence radius aGrav
    (compactObjectShearCoupling aLt aParallel aGrav) sinColatitude hShell rhoCrust rhoNuclear

theorem crustMisalignTorqueFromAccelerations_eq_stressDivergence
    (radius aGrav aLt aParallel sinColatitude hShell rhoCrust rhoNuclear : ℝ) :
    crustMisalignTorqueFromAccelerations radius aGrav aLt aParallel sinColatitude hShell
      rhoCrust rhoNuclear =
      crustMisalignTorqueFromStressDivergence radius aGrav
        (compactObjectShearCoupling aLt aParallel aGrav) sinColatitude hShell rhoCrust
        rhoNuclear := rfl

/-!
## Induction resistivity η(ξ, ε) — outside environment stack
-/

/-- Lattice-aligned induction resistivity ``η = γ × release(ξ) × G_eff(ε)``. -/
noncomputable def inductionResistivityEta (xi phiEpsilon : ℝ) : ℝ :=
  gamma_HQIV * outsideCurvatureReleaseFactor xi *
    outsideGravityGeffModulator ⟨phiEpsilon⟩

theorem inductionResistivityEta_nonneg (xi phiEpsilon : ℝ) :
    0 ≤ inductionResistivityEta xi phiEpsilon := by
  unfold inductionResistivityEta outsideGravityGeffModulator
  have hrel := outsideCurvatureReleaseFactor_pos xi
  have hg : 0 ≤ gamma_HQIV := by rw [gamma_eq_2_5]; norm_num
  split_ifs with h
  · positivity
  · have hε : 0 < phiEpsilon := lt_of_not_ge h
    have hα : 0 < alpha := by rw [alpha_eq_3_5]; norm_num
    have hpow : 1 ≤ (1 + phiEpsilon) ^ alpha :=
      Real.one_le_rpow (le_of_lt (by linarith)) (le_of_lt hα)
    have hmod : 1 ≤ 1 + gamma_HQIV * ((1 + phiEpsilon) ^ alpha - 1) := by
      rw [gamma_eq_2_5]
      nlinarith
    positivity

theorem inductionResistivityEta_lockin_zero_gravity :
    inductionResistivityEta xiLockin 0 = gamma_HQIV := by
  unfold inductionResistivityEta outsideGravityGeffModulator outsideCurvatureReleaseFactor
    T_MeV_from_xi
  rw [bbnBindingReleaseFactor_at_xiLockin, gamma_eq_2_5]
  norm_num

/-- Schematic induction growth ``∂B/∂t ~ η a_LT / R``. -/
noncomputable def inductionGrowthRateFromLt (eta aLt radius : ℝ) : ℝ :=
  if radius = 0 then 0 else eta * abs aLt / radius

theorem inductionGrowthRateFromLt_zero_of_zero_radius (eta aLt : ℝ) :
    inductionGrowthRateFromLt eta aLt 0 = 0 := by
  unfold inductionGrowthRateFromLt
  simp

/-- Steady LT induction branch ``B_LT = η (a_LT / a_grav) B_surf``. -/
noncomputable def steadyInductionFieldLt (eta aLt aGrav bSurf : ℝ) : ℝ :=
  if aGrav = 0 then 0 else eta * (abs aLt / aGrav) * bSurf

theorem steadyInductionFieldLt_zero_of_zero_grav (eta aLt bSurf : ℝ) :
    steadyInductionFieldLt eta aLt 0 bSurf = 0 := by
  unfold steadyInductionFieldLt
  simp

/-- Relativistic Doppler temperature boost √(1+β)/(1−β) (witness cap below unity). -/
noncomputable def compactObjectDopplerTemperatureBoost (beta : ℝ) : ℝ :=
  if beta ≤ 0 then 1
  else Real.sqrt ((1 + min beta 0.9999) / (1 - min beta 0.9999))

/-- Effective outside temperature: max of spin-heated surface and boosted CMB channels. -/
noncomputable def compactObjectEffectiveOutsideTemperatureK
    (surfaceK betaSpin betaCombined cmbK : ℝ) : ℝ :=
  max (surfaceK * (1 + 2 * betaSpin))
    (cmbK * compactObjectDopplerTemperatureBoost betaCombined)

end

end Hqiv.Physics

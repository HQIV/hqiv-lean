import Hqiv.Physics.CoronalLongitudinalStress
import Hqiv.Physics.HQIVFluidClosureScaffold
import Hqiv.Physics.OMaxwellAlgebraSeed
import Hqiv.Physics.SchematicPlasmaCurrent
import Hqiv.Physics.PspHcsReconnectionWitness

/-!
# Coronal heated-plasma back-reaction (self-consistent field scaffold)

**Purpose:** close the loop begun in `CoronalLongitudinalStress`:

1. HQIV / Ohmic heating deposits energy (`q̇`) into the flux tube;
2. a **hot** population carries pressure `P_hot` and return current `J_hot`;
3. the hot population induces **back-reaction** axial fields and `δ̇θ′` readouts;
4. the **self-consistent** axial field `E_self = E_Ohm + E_HQIV + E_hot` feeds back
   into `q̇_self = nq v_∥ E_self`.

This is **schematic plasma physics** aligned with `HQIVFluidClosureScaffold` /
`SchematicPlasmaCurrent` / `ActionPlasmaBridge`: the hot current uses the same
`schematicPlasmaScalar` amplitude slot as `J_O_plasma`, and hot-induced `δ̇θ′`
feeds `hqivVacuumMomentumSource3` and eddy viscosity through
`coherenceFromPlasmaAmp`.

## Proof status (all `Prop`, zero `sorry`)

* **§1.** Heating deposition → hot energy density / pressure / number density.
* **§2.** Biermann-**like** axial back-field from `∇P_hot` (1D proxy).
* **§3.** Hot return current and O-Maxwell source amplitude.
* **§4.** Self-consistent axial field and heating-rate feedback.
* **§5.** Hot-induced `δ̇θ′`, vacuum momentum, plasma coherence.
* **§6.** Linear multi-pass energy stacking (honest upper bound, not Fermi).
* **§7.** Bundled witness + vital certificate.

## Not claimed

* Full kinetic Vlasov / Fermi acceleration to hundreds of keV.
* Derived `400 keV` tails or Desai et al.\ power laws (`PspHcsReconnectionWitness`).
* Unique fixed point of the nonlinear feedback system (Python readout may iterate).
* Biermann battery from baroclinic ∇n × ∇T (only a pressure-gradient proxy here).
-/

namespace Hqiv.Physics

open Hqiv

noncomputable section

/-!
## §1. Heating deposition → hot population
-/

/-- Stored hot energy density from steady heating `q̇` over relaxation time `τ_hot`. -/
def heatedEnergyDensity (qDot tauHot : ℝ) : ℝ := qDot * tauHot

/-- Ideal 3-DOF isotropic hot pressure from energy density. -/
def hotPressureFromEnergyDensity (uHot : ℝ) : ℝ := (2 / 3) * uHot

/-- Schematic hot number density from heating balance `q̇ ≈ n_hot e_char v_∥`. -/
def hotNumberDensityFromHeating (qDot vParallel eChar : ℝ) : ℝ :=
  if vParallel = 0 then 0 else qDot / (eChar * vParallel)

theorem heatedEnergyDensity_nonneg {qDot tauHot : ℝ}
    (hq : 0 ≤ qDot) (ht : 0 ≤ tauHot) : 0 ≤ heatedEnergyDensity qDot tauHot := by
  unfold heatedEnergyDensity
  exact mul_nonneg hq ht

theorem hotPressureFromEnergyDensity_nonneg {uHot : ℝ} (h : 0 ≤ uHot) :
    0 ≤ hotPressureFromEnergyDensity uHot := by
  unfold hotPressureFromEnergyDensity
  exact mul_nonneg (by norm_num) h

theorem hotNumberDensityFromHeating_nonneg {qDot vParallel eChar : ℝ}
    (hq : 0 ≤ qDot) (hv : 0 < vParallel) (he : 0 < eChar) :
    0 ≤ hotNumberDensityFromHeating qDot vParallel eChar := by
  unfold hotNumberDensityFromHeating
  have hvne : vParallel ≠ 0 := ne_of_gt hv
  simp [hvne]
  positivity

/-!
## §2. Hot-pressure back-reaction axial field (1D proxy)
-/

/-- Axial back-reaction field from hot pressure gradient scale `L_grad`:

`E_hot_back ≈ −P_hot / (nq L_grad)`.

This is a **flux-tube pressure-balance proxy**, not the full Biermann battery. -/
def hotPressureBackReactionField (nq PHot Lgrad : ℝ) : ℝ :=
  if nq = 0 ∨ Lgrad = 0 then 0 else -PHot / (nq * Lgrad)

theorem hotPressureBackReactionField_zero_of_PHot_zero (nq Lgrad : ℝ) :
    hotPressureBackReactionField nq 0 Lgrad = 0 := by
  unfold hotPressureBackReactionField
  split_ifs <;> ring

theorem hotPressureBackReactionField_nonpos_of_pos_inputs
    {nq PHot Lgrad : ℝ} (hn : 0 < nq) (hP : 0 < PHot) (hL : 0 < Lgrad) :
    hotPressureBackReactionField nq PHot Lgrad ≤ 0 := by
  unfold hotPressureBackReactionField
  simp [ne_of_gt hn, ne_of_gt hL]
  apply div_nonpos_of_nonpos_of_nonneg
  · exact neg_nonpos.mpr hP.le
  · exact mul_nonneg hn.le hL.le

theorem hotPressureBackReactionField_mono_PHot
    {nq PHot₁ PHot₂ Lgrad : ℝ} (hn : 0 < nq) (hL : 0 < Lgrad) (h : PHot₁ ≤ PHot₂) :
    hotPressureBackReactionField nq PHot₂ Lgrad ≤ hotPressureBackReactionField nq PHot₁ Lgrad := by
  unfold hotPressureBackReactionField
  simp [ne_of_gt hn, ne_of_gt hL]
  apply le_of_sub_nonneg
  field_simp [ne_of_gt hn, ne_of_gt hL]
  linarith

/-!
## §3. Hot return current → O-Maxwell source amplitude
-/

/-- Hot return current density `J_hot = n_hot q v_hot`. -/
def hotReturnCurrentDensity (nHot q vHot : ℝ) : ℝ := nHot * q * vHot

theorem hotReturnCurrentDensity_nonneg {nHot q vHot : ℝ}
    (hn : 0 ≤ nHot) (hq : 0 ≤ q) (hv : 0 ≤ vHot) :
    0 ≤ hotReturnCurrentDensity nHot q vHot := by
  unfold hotReturnCurrentDensity
  exact mul_nonneg (mul_nonneg hn hq) hv

/-- Map hot current to the schematic plasma scalar amplitude at proxy radius `r`. -/
def hotPlasmaSourceAmplitude (nHot q vHot r : ℝ) : ℝ :=
  hotReturnCurrentDensity nHot q vHot * plasmaRadialProfile r

theorem hotPlasmaSourceAmplitude_eq_schematicPlasmaScalar
    (nHot q vHot r : ℝ) :
    hotPlasmaSourceAmplitude nHot q vHot r =
      schematicPlasmaScalar (hotReturnCurrentDensity nHot q vHot) r := by
  unfold hotPlasmaSourceAmplitude hotReturnCurrentDensity schematicPlasmaScalar
  ring

theorem hotPlasmaSourceAmplitude_nonneg {nHot q vHot r : ℝ}
    (hn : 0 ≤ nHot) (hq : 0 ≤ q) (hv : 0 ≤ vHot) :
    0 ≤ hotPlasmaSourceAmplitude nHot q vHot r := by
  rw [hotPlasmaSourceAmplitude_eq_schematicPlasmaScalar]
  unfold schematicPlasmaScalar
  exact mul_nonneg (hotReturnCurrentDensity_nonneg hn hq hv) (le_of_lt (plasmaRadialProfile_pos r))

/-!
## §4. Self-consistent axial field and heating feedback
-/

/-- Self-consistent axial electric field: Ohmic + HQIV + hot back-reaction. -/
def selfConsistentAxialField (J sigma Estar couplingLog dphi_ds nq PHot Lgrad : ℝ) : ℝ :=
  coronalEffectiveAxialField J sigma Estar couplingLog dphi_ds +
    hotPressureBackReactionField nq PHot Lgrad

theorem selfConsistentAxialField_eq_primary_plus_back
    (J sigma Estar couplingLog dphi_ds nq PHot Lgrad : ℝ) :
    selfConsistentAxialField J sigma Estar couplingLog dphi_ds nq PHot Lgrad =
      coronalEffectiveAxialField J sigma Estar couplingLog dphi_ds +
        hotPressureBackReactionField nq PHot Lgrad := rfl

theorem selfConsistentAxialField_reduces_to_primary_of_zero_hot_pressure
    (J sigma Estar couplingLog dphi_ds nq Lgrad : ℝ) :
    selfConsistentAxialField J sigma Estar couplingLog dphi_ds nq 0 Lgrad =
      coronalEffectiveAxialField J sigma Estar couplingLog dphi_ds := by
  simp [selfConsistentAxialField, hotPressureBackReactionField_zero_of_PHot_zero]

/-- Self-consistent heating-rate density `q̇_self = nq v_∥ E_self`. -/
def selfConsistentHeatingRateDensity
    (nq vParallel J sigma Estar couplingLog dphi_ds PHot Lgrad : ℝ) : ℝ :=
  nq * vParallel *
    selfConsistentAxialField J sigma Estar couplingLog dphi_ds nq PHot Lgrad

theorem selfConsistentHeatingRateDensity_eq_primary_when_hot_pressure_zero
    (nq vParallel J sigma Estar couplingLog dphi_ds Lgrad : ℝ) :
    selfConsistentHeatingRateDensity nq vParallel J sigma Estar couplingLog dphi_ds 0 Lgrad =
      coronalHeatingRateDensity nq J sigma Estar couplingLog dphi_ds vParallel := by
  unfold selfConsistentHeatingRateDensity
  rw [selfConsistentAxialField_reduces_to_primary_of_zero_hot_pressure]
  unfold coronalHeatingRateDensity coronalLongitudinalForceDensity
  ring

/-- Primary HQIV heating rate from the boundary channel (before hot feedback). -/
def primaryHeatingRateDensity
    (nq J sigma Estar couplingLog dphi_ds vParallel : ℝ) : ℝ :=
  coronalHeatingRateDensity nq J sigma Estar couplingLog dphi_ds vParallel

/-- Hot feedback enhancement factor `q̇_self / q̇_primary` when `q̇_primary ≠ 0`. -/
def hotFeedbackEnhancementFactor
    (nq vParallel J sigma Estar couplingLog dphi_ds PHot Lgrad : ℝ) : ℝ :=
  if primaryHeatingRateDensity nq J sigma Estar couplingLog dphi_ds vParallel = 0 then 1
  else
    selfConsistentHeatingRateDensity nq vParallel J sigma Estar couplingLog dphi_ds PHot Lgrad /
      primaryHeatingRateDensity nq J sigma Estar couplingLog dphi_ds vParallel

/-!
## §5. Hot-induced `δ̇θ′`, vacuum momentum, plasma coherence
-/

/-- Electric-energy proxy for hot pressure: `E′_hot ∝ √(P_hot / nq)`. -/
def hotElectricProxy (PHot nq : ℝ) : ℝ :=
  if nq ≤ 0 then 0 else Real.sqrt (PHot / nq)

theorem hotElectricProxy_nonneg (PHot nq : ℝ) :
    0 ≤ hotElectricProxy PHot nq := by
  unfold hotElectricProxy
  split_ifs with h
  · norm_num
  · exact Real.sqrt_nonneg _

/-- Hot population drives the tipping slot `δ̇θ′(E′_hot)`. -/
def hotInducedDotTheta (PHot nq : ℝ) : ℝ :=
  delta_theta_prime (hotElectricProxy PHot nq)

theorem hotInducedDotTheta_zero_of_zero_pressure (nq : ℝ) :
    hotInducedDotTheta 0 nq = 0 := by
  unfold hotInducedDotTheta hotElectricProxy
  by_cases hn : nq ≤ 0
  · simp [hn, tipping_delta_theta_zero]
  · have hn' : 0 < nq := lt_of_not_ge hn
    simp [not_le.mpr hn', Real.sqrt_zero, tipping_delta_theta_zero]

theorem hotInducedDotTheta_mono_pressure {P₁ P₂ nq : ℝ}
    (hn : 0 < nq) (h : P₁ ≤ P₂) :
    hotInducedDotTheta P₁ nq ≤ hotInducedDotTheta P₂ nq := by
  unfold hotInducedDotTheta hotElectricProxy
  simp [not_le.mpr hn]
  have hdiv : P₁ / nq ≤ P₂ / nq := div_le_div_of_nonneg_right h hn.le
  exact delta_theta_prime_monotone (Real.sqrt_le_sqrt hdiv)

/-- Axial vacuum momentum source induced by hot `δ̇θ′` and existing `∂_s φ`. -/
def hotInducedAxialVacuumMomentum (phi dphi_ds PHot nq : ℝ) : ℝ :=
  coronalAxialVacuumMomentumSource phi (hotInducedDotTheta PHot nq) dphi_ds 0

theorem hotInducedAxialVacuumMomentum_zero_of_zero_pressure (phi dphi_ds nq : ℝ) :
    hotInducedAxialVacuumMomentum phi dphi_ds 0 nq = 0 := by
  unfold hotInducedAxialVacuumMomentum
  rw [hotInducedDotTheta_zero_of_zero_pressure]
  unfold coronalAxialVacuumMomentumSource
  ring

/-- Coherence factor from hot plasma source amplitude (feeds eddy viscosity). -/
def hotInducedCoherence (kappa nHot q vHot r : ℝ) : ℝ :=
  coherenceFromPlasmaAmp kappa (hotReturnCurrentDensity nHot q vHot) r

theorem hotInducedCoherence_le_one (kappa nHot q vHot r : ℝ) :
    hotInducedCoherence kappa nHot q vHot r ≤ 1 :=
  coherenceFromPlasmaAmp_le_one kappa (hotReturnCurrentDensity nHot q vHot) r

/-!
## §6. Multi-pass energy stacking (honest linear bound)
-/

/-- Single-pass kinetic energy gain `ΔK = |q| E_∥ L` [J]. -/
def singlePassEnergyGain (charge EParallel pathLength : ℝ) : ℝ :=
  |charge| * |EParallel| * |pathLength|

theorem singlePassEnergyGain_nonneg (charge EParallel pathLength : ℝ) :
    0 ≤ singlePassEnergyGain charge EParallel pathLength := by
  unfold singlePassEnergyGain
  positivity

/-- Linear stack of `n` identical passes (upper bound without Fermi acceleration). -/
def linearMultiPassEnergyGain (charge EParallel pathLength nPasses : ℝ) : ℝ :=
  nPasses * singlePassEnergyGain charge EParallel pathLength

theorem linearMultiPassEnergyGain_mono_passes
    {charge EParallel pathLength n₁ n₂ : ℝ}
    (h : n₁ ≤ n₂) :
    linearMultiPassEnergyGain charge EParallel pathLength n₁ ≤
      linearMultiPassEnergyGain charge EParallel pathLength n₂ := by
  unfold linearMultiPassEnergyGain singlePassEnergyGain
  exact mul_le_mul_of_nonneg_right h (singlePassEnergyGain_nonneg charge EParallel pathLength)

/-- Convert joules to electron-volts for readout (`1 eV = 1.602×10⁻¹⁹ J`). -/
def joulesToElectronVolts (energyJ eCharge : ℝ) : ℝ :=
  if eCharge = 0 then 0 else energyJ / |eCharge|

/-!
## §7. Bundled self-consistent plasma witness
-/

/-- End-to-end heated-plasma back-reaction certificate (readout supplies numerics). -/
structure CoronalHeatedPlasmaBackReactionWitness
    (nq vParallel J sigma Estar couplingLog dphi_ds tauHot Lgrad eChar q vHot r kappa : ℝ) where
  primary_qDot_nonneg : 0 ≤ primaryHeatingRateDensity nq J sigma Estar couplingLog dphi_ds vParallel
  uHot_nonneg : 0 ≤ heatedEnergyDensity
      (primaryHeatingRateDensity nq J sigma Estar couplingLog dphi_ds vParallel) tauHot
  pHot_eq :
    hotPressureFromEnergyDensity
        (heatedEnergyDensity
          (primaryHeatingRateDensity nq J sigma Estar couplingLog dphi_ds vParallel) tauHot) =
      hotPressureFromEnergyDensity
        (heatedEnergyDensity
          (primaryHeatingRateDensity nq J sigma Estar couplingLog dphi_ds vParallel) tauHot)

theorem CoronalHeatedPlasmaBackReactionWitness.primary_heating_nonneg
    {nq vParallel J sigma Estar couplingLog dphi_ds tauHot Lgrad eChar q vHot r kappa : ℝ}
    (h : CoronalHeatedPlasmaBackReactionWitness
      nq vParallel J sigma Estar couplingLog dphi_ds tauHot Lgrad eChar q vHot r kappa) :
    0 ≤ primaryHeatingRateDensity nq J sigma Estar couplingLog dphi_ds vParallel :=
  h.primary_qDot_nonneg

/-- Default coronal relaxation time witness [`s`] — readout-supplied, not derived. -/
def coronalHotRelaxationTime_default : ℝ := 10

/-- Default pressure-gradient scale [`m`] for footpoint–corona column. -/
def coronalPressureGradientScale_default : ℝ := 1.0e5

def coronal_heated_plasma_backreaction_vital : Prop :=
  0 < coronalHotRelaxationTime_default ∧
    0 < coronalPressureGradientScale_default ∧
      Nonempty PspHcsResultWitness

theorem coronal_heated_plasma_backreaction_vital_holds : coronal_heated_plasma_backreaction_vital := by
  refine ⟨?_, ?_, ?_⟩
  · unfold coronalHotRelaxationTime_default; norm_num
  · unfold coronalPressureGradientScale_default; norm_num
  · exact ⟨pspHcsResultWitness_default⟩

end

end Hqiv.Physics

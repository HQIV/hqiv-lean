import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.HQIVNuclei
import Hqiv.Physics.HomogeneousCurvatureSecondOrder
import Hqiv.Physics.NuclearOutsideTemperatureDynamics
import Hqiv.QuantumChemistry.OutsideContactLedger
import Hqiv.QuantumChemistry.SecondOrderEffects
import HqivSpine.Chemistry.Spectroscopy
import HqivSpine.Physics.GeneratorDependentCoupling

/-!
# Voltage-generation ledger (six classical EMF routes)

Classical open-circuit voltage generation is not a separate physics stack: each
route is a **stress × response** channel on the same outside/contact algebra used
by `OutsideContactLedger`.  The six textbook routes (schooling-terse list) are:

1. **chemo** — galvanic / chemical potential (ionic / μ asymmetry);
2. **thermo** — thermoelectric / Seebeck (ΔT / ξ contrast);
3. **photo** — photoelectric / photovoltaic (photon-phase excess);
4. **piezo** — piezoelectric (strain → polarization);
5. **tribo** — triboelectric (contact electrification asymmetry);
6. **faraday** — Faraday induction (phase-rate / flux proxy).

Each channel has the form

`1 + (4/8) · stress · response`

with `strongChannelFraction = 4/8`, and recovers exactly `1` when unstressed.
The product dress multiplies beside `outsideContactLedgerDress` into the promoted
n-body second-order factor — no fitted coefficient, no molecule-type case.

Absolute volts (SI) are a separate reference-potential pin
(`ionicBondSurplus` / contact eV scale); this ledger is the dimensionless EMF
dress, same contract as `outsideGeffSurplus`.
-/

namespace Hqiv.QuantumChemistry

open Hqiv
open Hqiv.Physics
open HqivSpine.Chemistry
open HqivSpine.Physics.GeneratorDependentCoupling

noncomputable section

/-- Generic voltage-generation channel: `1 + (4/8)·stress·response`. -/
def voltageChannel (stress response : ℝ) : ℝ :=
  1 + strongChannelFraction * stress * response

theorem voltageChannel_unstressed (response : ℝ) :
    voltageChannel 0 response = 1 := by
  unfold voltageChannel; ring

/-- Clamp a stress weight into `[0,1]`. -/
def clampUnitStress (x : ℝ) : ℝ := min 1 (max 0 x)

theorem clampUnitStress_zero : clampUnitStress 0 = 0 := by
  unfold clampUnitStress; norm_num

theorem clampUnitStress_one : clampUnitStress 1 = 1 := by
  unfold clampUnitStress; norm_num

/-! ## Six classical channels -/

/-- **Chemo / galvanic**: ionic-character (or μ) asymmetry across the cell.
`stress = |Δw|` with `w = bondIonicCharacter`; response = 1 (character already
squared).  Homonuclear / symmetric ⇒ stress 0 ⇒ channel 1. -/
def chemoVoltageChannel (ionicAsymmetry : ℝ) : ℝ :=
  voltageChannel (clampUnitStress ionicAsymmetry) 1

theorem chemoVoltageChannel_zero :
    chemoVoltageChannel 0 = 1 := by
  unfold chemoVoltageChannel
  rw [clampUnitStress_zero, voltageChannel_unstressed]

/-- **Thermo / Seebeck**: temperature / ξ contrast.
`stress = |release_hot/release_cold − 1|` (or equal-ξ → 0). -/
def thermoVoltageChannel (releaseContrast : ℝ) : ℝ :=
  voltageChannel (clampUnitStress releaseContrast) 1

theorem thermoVoltageChannel_zero :
    thermoVoltageChannel 0 = 1 := by
  unfold thermoVoltageChannel
  rw [clampUnitStress_zero, voltageChannel_unstressed]

/-- Joule / thermal-release contrast: ``clamp(carrier)·clamp(phononCage)·γ``. -/
noncomputable def jouleReleaseContrast (carrierFraction phononCageFraction : ℝ) : ℝ :=
  clampUnitStress carrierFraction * clampUnitStress phononCageFraction * gamma_HQIV

/-- Conductivity ↔ thermo dress; identity when carrier fraction is zero. -/
noncomputable def carrierThermoConductivityDress
    (carrierFraction phononCageFraction : ℝ) : ℝ :=
  thermoVoltageChannel (jouleReleaseContrast carrierFraction phononCageFraction)

theorem carrierThermoConductivityDress_no_carriers (phononCageFraction : ℝ) :
    carrierThermoConductivityDress 0 phononCageFraction = 1 := by
  unfold carrierThermoConductivityDress jouleReleaseContrast
  simp [clampUnitStress_zero, thermoVoltageChannel_zero]

/-- **Photo / photovoltaic**: photon-phase excess × dielectric concentration.
`stress = η_ph`, `response = curvatureConcentrationWeight n`. -/
def photoVoltageChannel (photonPhaseExcess nDielectric : ℝ) : ℝ :=
  voltageChannel (clampUnitStress photonPhaseExcess)
    (Spectroscopy.curvatureConcentrationWeight nDielectric)

theorem photoVoltageChannel_zero (nDielectric : ℝ) :
    photoVoltageChannel 0 nDielectric = 1 := by
  unfold photoVoltageChannel
  rw [clampUnitStress_zero, voltageChannel_unstressed]

/-- H-bond donor excess ``clamp01((n_σ − n_lp)/n_lp)`` — structural optical weight. -/
noncomputable def hbondDonorExcessWeight (nBonds nLonePairs : ℕ) : ℝ :=
  if nLonePairs = 0 ∨ nBonds = 0 then 0
  else min 1 (max 0 (((nBonds : ℝ) - (nLonePairs : ℝ)) / (nLonePairs : ℝ)))

/-- H-bond acceptor excess ``clamp01((n_lp − n_σ)/n_σ)`` — dual of donor excess. -/
noncomputable def hbondAcceptorExcessWeight (nBonds nLonePairs : ℕ) : ℝ :=
  if nLonePairs = 0 ∨ nBonds = 0 then 0
  else min 1 (max 0 (((nLonePairs : ℝ) - (nBonds : ℝ)) / (nBonds : ℝ)))

/-- Acceptor polarizability softener ``1 / (1 + γ·α · w_acc)`` (EM-weighted monogamy). -/
noncomputable def acceptorPolarizabilitySoftener (nBonds nLonePairs : ℕ) : ℝ :=
  1 / (1 + gamma_HQIV * alpha * hbondAcceptorExcessWeight nBonds nLonePairs)

/-- Apolar packing flag: true lone-pair vacuum ``1[n_lp = 0]``. -/
noncomputable def apolarPackingWeight (nLonePairs : ℕ) : ℝ :=
  if nLonePairs = 0 then 1 else 0

/-- Steric packing density fine-tune
``1 + (4/8)·γ/8 · (w_donor − w_apolar)``.  Raises donor-rich solids, softens
true apolars; identity when both weights vanish (H₂O / HF class). -/
noncomputable def stericPackingDensityDress (nBonds nLonePairs : ℕ) : ℝ :=
  1 + strongChannelFraction * gamma_HQIV / 8 *
    (hbondDonorExcessWeight nBonds nLonePairs - apolarPackingWeight nLonePairs)

/-- Density scale from piezo strain + optional apolar open + steric fine-tune.
``f = (1+(4/8)·ε) · (1+(4/8)·(γ/2))_apolar / steric``.  Lattice density uses
``ρ → ρ/f``; optical CM keeps the undressed electronic density (split bulk). -/
noncomputable def densityScaleFromPiezoStrain
    (strain : ℝ) (apolarOpen : Bool) (nBonds nLonePairs : ℕ) : ℝ :=
  let f := (1 + strongChannelFraction * strain) *
    (if apolarOpen then 1 + strongChannelFraction * (gamma_HQIV / 2) else 1)
  f / max (stericPackingDensityDress nBonds nLonePairs) 1e-12

/-- Ionic optical-gap softener ``1 / (1 + (4/8)·γ·δ²)``. -/
noncomputable def ionicOpticalGapSoftener (ionicCharacter : ℝ) : ℝ :=
  1 / (1 + strongChannelFraction * gamma_HQIV * ionicCharacter)

/-- Piezo-modulated ionic optical softener ``1 / (1 + (4/8)·ε·δ²)``. -/
noncomputable def ionicOpticalGapPiezoSoftener
    (ionicCharacter strain : ℝ) : ℝ :=
  1 / (1 + strongChannelFraction * strain * ionicCharacter)

/-- Combined ionic optical softener: character × piezo. -/
noncomputable def ionicOpticalGapSoftenerWithPiezo
    (ionicCharacter strain : ℝ) : ℝ :=
  ionicOpticalGapSoftener ionicCharacter *
    ionicOpticalGapPiezoSoftener ionicCharacter strain

/-- Period channel weight ``min(1, (2/P)^cap)`` (period-2 → 1; period-1 capped). -/
noncomputable def ionicPeriodChannelWeight (period : ℕ) : ℝ :=
  min 1 ((2 / (max period 1 : ℝ)) ^ (constructiveValleyCap : ℝ))

/-- Fluoride mixed-period melt residual: ``1 + (4/8)·(γ/8)·w_a·excess``. -/
noncomputable def ionicFluoridePeriodMeltResidual
    (periodCation periodAnion : ℕ) : ℝ :=
  let wA := ionicPeriodChannelWeight periodAnion
  let excess := max 0 ((periodCation : ℝ) / (max periodAnion 1 : ℝ) - 1)
  1 + strongChannelFraction * (gamma_HQIV / 8) * wA * excess

/--
Mixed-period ionic melt dress: ``1 + (4/8)·γ·w_a·(1−w_c)``,
softened by ``1 / (1 + (4/8)·(γ/8)·excess·(1−w_a))``,
times fluoride residual ``ionicFluoridePeriodMeltResidual``.

Period-2 anions with deeper cations raise melt cohesive; deep-cation fade
keeps KCl from over-binding; fluoride residual raises NaF.  Python:
``ionic_anion_period_melt_dress``.
-/
noncomputable def ionicAnionPeriodMeltDress (periodCation periodAnion : ℕ) : ℝ :=
  let wA := ionicPeriodChannelWeight periodAnion
  let wC := ionicPeriodChannelWeight periodCation
  let boost := 1 + strongChannelFraction * gamma_HQIV * wA * (1 - wC)
  let excess := max 0 ((periodCation : ℝ) / (max periodAnion 1 : ℝ) - 1)
  let soft := 1 / (1 + strongChannelFraction * (gamma_HQIV / 8) * excess * (1 - wA))
  boost * soft * ionicFluoridePeriodMeltResidual periodCation periodAnion

/-- Period-2 anion polarizability softener: ``1 / (1 + (4/8)·γ·w_a)``. -/
noncomputable def ionicAnionPeriodPolarizabilitySoftener (periodAnion : ℕ) : ℝ :=
  1 / (1 + strongChannelFraction * gamma_HQIV * ionicPeriodChannelWeight periodAnion)

/--
Cation-period optical softener: ``1 / (1 + (4/8)·γ·max(0, P_c/P_a − 1))``.

Deeper cations than the anion suppress CM polarizability; same-or-shallower
cations stay at identity.  Python: ``ionic_cation_period_polarizability_softener``.
-/
noncomputable def ionicCationPeriodPolarizabilitySoftener
    (periodCation periodAnion : ℕ) : ℝ :=
  let excess := max 0 ((periodCation : ℝ) / (max periodAnion 1 : ℝ) - 1)
  1 / (1 + strongChannelFraction * gamma_HQIV * excess)

/-- Period-channel optical softener: ``1 / (1 + (4/8)·α·γ·w_a·w_c)``. -/
noncomputable def ionicPeriodChannelOpticalSoftener
    (periodCation periodAnion : ℕ) : ℝ :=
  let wA := ionicPeriodChannelWeight periodAnion
  let wC := ionicPeriodChannelWeight periodCation
  1 / (1 + strongChannelFraction * alpha * gamma_HQIV * wA * wC)

/-- Combined anion × cation × channel period optical softener. -/
noncomputable def ionicPeriodPolarizabilitySoftener
    (periodCation periodAnion : ℕ) : ℝ :=
  ionicAnionPeriodPolarizabilitySoftener periodAnion *
    ionicCationPeriodPolarizabilitySoftener periodCation periodAnion *
    ionicPeriodChannelOpticalSoftener periodCation periodAnion

theorem ionicAnionPeriodMeltDress_same_period_two :
    ionicAnionPeriodMeltDress 2 2 = 1 := by
  unfold ionicAnionPeriodMeltDress ionicFluoridePeriodMeltResidual ionicPeriodChannelWeight
  rw [constructiveValleyCap_eq_six]
  norm_num

theorem ionicAnionPeriodPolarizabilitySoftener_period_two :
    ionicAnionPeriodPolarizabilitySoftener 2 =
      1 / (1 + strongChannelFraction * gamma_HQIV) := by
  unfold ionicAnionPeriodPolarizabilitySoftener ionicPeriodChannelWeight
  rw [constructiveValleyCap_eq_six]
  norm_num

theorem ionicPeriodChannelWeight_period_one_capped :
    ionicPeriodChannelWeight 1 = 1 := by
  unfold ionicPeriodChannelWeight
  rw [constructiveValleyCap_eq_six]
  norm_num

theorem ionicCationPeriodPolarizabilitySoftener_same_period :
    ionicCationPeriodPolarizabilitySoftener 3 3 = 1 := by
  unfold ionicCationPeriodPolarizabilitySoftener
  simp

/-- Thermal concentration dress on optical CM: ``1 + (4/8)·ε·(γ/2)``. -/
noncomputable def thermalConcentrationDress (strain : ℝ) : ℝ :=
  1 + strongChannelFraction * strain * (gamma_HQIV / 2)

/-- Brownian local-defect channel ``1 + γ·(4/8)·ε``. -/
noncomputable def brownianLocalDefectChannel (strain : ℝ) : ℝ :=
  outsideLocalDefectChannel (max strain 0)

/-- Optical voltage dress: interpolate chemo×photo by donor-excess weight (no motif case). -/
noncomputable def opticalVoltageDress
    (rhoCurv nDielectric : ℝ) (nBonds nLonePairs : ℕ) : ℝ :=
  let chemo := chemoVoltageChannel (gamma_HQIV / 2)
  let photo := photoVoltageChannel (max 0 (1 - rhoCurv) * gamma_HQIV) nDielectric
  let w := hbondDonorExcessWeight nBonds nLonePairs
  1 + (chemo * photo - 1) * w

theorem apolarPackingWeight_zero_lp :
    apolarPackingWeight 0 = 1 := by
  unfold apolarPackingWeight; rfl

theorem apolarPackingWeight_positive_lp (n : ℕ) (h : 0 < n) :
    apolarPackingWeight n = 0 := by
  unfold apolarPackingWeight
  split_ifs with h0
  · omega
  · rfl

theorem stericPackingDensityDress_balanced :
    stericPackingDensityDress 2 2 = 1 := by
  unfold stericPackingDensityDress hbondDonorExcessWeight apolarPackingWeight
  norm_num

theorem ionicOpticalGapSoftener_zero :
    ionicOpticalGapSoftener 0 = 1 := by
  unfold ionicOpticalGapSoftener; ring

theorem ionicOpticalGapPiezoSoftener_zero_strain (ionicCharacter : ℝ) :
    ionicOpticalGapPiezoSoftener ionicCharacter 0 = 1 := by
  unfold ionicOpticalGapPiezoSoftener; ring

theorem thermalConcentrationDress_zero :
    thermalConcentrationDress 0 = 1 := by
  unfold thermalConcentrationDress; ring

theorem brownianLocalDefectChannel_zero :
    brownianLocalDefectChannel 0 = 1 := by
  unfold brownianLocalDefectChannel
  simp [outsideLocalDefectChannel_zero]

/-- **Piezo**: strain × dielectric concentration.
`stress = |Δr|/r` (or angular strain fraction); `response = s(n)`. -/
def piezoVoltageChannel (strainFraction nDielectric : ℝ) : ℝ :=
  voltageChannel (clampUnitStress strainFraction)
    (Spectroscopy.curvatureConcentrationWeight nDielectric)

theorem piezoVoltageChannel_zero (nDielectric : ℝ) :
    piezoVoltageChannel 0 nDielectric = 1 := by
  unfold piezoVoltageChannel
  rw [clampUnitStress_zero, voltageChannel_unstressed]

/-! ## Thermal / Brownian (Lindemann) piezo stress

Condensed packing and voltage piezo share one continuous strain:

`ε(T) = clamp01( amp · √(T / T_melt) · (1 + phononCage) )`

with lattice amplitude `amp = γ/2` (or `γ/4` on linear-chain motifs).  At `T → 0`
the stress vanishes (channel identity); at melt it is O(γ/2).  This is the
Brownian / equipartition loader that splits piezo from photo in the condensed
constraint system — not a fitted coefficient.
-/

/-- Lindemann amplitude from monogamy γ (default condensed slot). -/
def lindemannPiezoAmplitude : ℝ := gamma_HQIV / 2

/-- Milder amplitude for linear-chain / zigzag solids (HF-class). -/
def lindemannPiezoAmplitudeLinearChain : ℝ := gamma_HQIV / 4

/-- Continuous thermal strain; `phononCage ≥ 0` softens the contact spring. -/
noncomputable def lindemannThermalStrain
    (temperatureK meltK amplitude phononCage : ℝ) : ℝ :=
  if meltK ≤ 0 ∨ temperatureK ≤ 0 then 0
  else
    clampUnitStress
      (amplitude * Real.sqrt (temperatureK / meltK) * (1 + max phononCage 0))

theorem lindemannThermalStrain_zero_temp (meltK amplitude phononCage : ℝ) :
    lindemannThermalStrain 0 meltK amplitude phononCage = 0 := by
  unfold lindemannThermalStrain
  split_ifs <;> first | rfl | simp_all

/-- Piezo channel from Lindemann thermal strain. -/
noncomputable def piezoVoltageChannelLindemann
    (temperatureK meltK amplitude phononCage nDielectric : ℝ) : ℝ :=
  piezoVoltageChannel
    (lindemannThermalStrain temperatureK meltK amplitude phononCage) nDielectric

theorem piezoVoltageChannelLindemann_zero_temp
    (meltK amplitude phononCage nDielectric : ℝ) :
    piezoVoltageChannelLindemann 0 meltK amplitude phononCage nDielectric = 1 := by
  unfold piezoVoltageChannelLindemann
  rw [lindemannThermalStrain_zero_temp, piezoVoltageChannel_zero]

/-- **Tribo**: preferred-axis spectral gap × local defect.
At `g = 0` and `δ = 0` this is exactly `1`. -/
def triboVoltageChannel (axisGap coordinationExcess : ℝ) : ℝ :=
  voltageChannel (clampUnitStress axisGap) 1 *
    outsideLocalDefectChannel coordinationExcess

theorem triboVoltageChannel_zero :
    triboVoltageChannel 0 0 = 1 := by
  unfold triboVoltageChannel
  rw [clampUnitStress_zero, voltageChannel_unstressed,
    outsideLocalDefectChannel_zero]
  ring

/-- **Faraday**: phase-rate / flux proxy.
`stress = |dη/dt| / (η + η_ref)` normalised; static phase ⇒ 0 ⇒ channel 1. -/
def faradayVoltageChannel (phaseRateFraction : ℝ) : ℝ :=
  voltageChannel (clampUnitStress phaseRateFraction) 1

theorem faradayVoltageChannel_zero :
    faradayVoltageChannel 0 = 1 := by
  unfold faradayVoltageChannel
  rw [clampUnitStress_zero, voltageChannel_unstressed]

/-! ## Ledger -/

/-- Six-channel voltage-generation ledger. -/
structure VoltageGenerationLedger where
  chemo : ℝ := 1
  thermo : ℝ := 1
  photo : ℝ := 1
  piezo : ℝ := 1
  tribo : ℝ := 1
  faraday : ℝ := 1

/-- Product dress from the voltage ledger. -/
def voltageGenerationLedgerDress (V : VoltageGenerationLedger) : ℝ :=
  V.chemo * V.thermo * V.photo * V.piezo * V.tribo * V.faraday

/-- Unstressed ledger: every channel at identity. -/
def unstressedVoltageGenerationLedger : VoltageGenerationLedger where
  chemo := chemoVoltageChannel 0
  thermo := thermoVoltageChannel 0
  photo := photoVoltageChannel 0 1
  piezo := piezoVoltageChannel 0 1
  tribo := triboVoltageChannel 0 0
  faraday := faradayVoltageChannel 0

theorem unstressedVoltageGenerationLedger_dress :
    voltageGenerationLedgerDress unstressedVoltageGenerationLedger = 1 := by
  unfold voltageGenerationLedgerDress unstressedVoltageGenerationLedger
  rw [chemoVoltageChannel_zero, thermoVoltageChannel_zero,
    photoVoltageChannel_zero, piezoVoltageChannel_zero,
    triboVoltageChannel_zero, faradayVoltageChannel_zero]
  ring

/-- Build from explicit stresses (n-body / condensed / interface ready). -/
def voltageGenerationLedgerFromStresses
    (ionicAsymmetry releaseContrast photonPhaseExcess nDielectric
      strainFraction axisGap coordinationExcess phaseRateFraction : ℝ) :
    VoltageGenerationLedger where
  chemo := chemoVoltageChannel ionicAsymmetry
  thermo := thermoVoltageChannel releaseContrast
  photo := photoVoltageChannel photonPhaseExcess nDielectric
  piezo := piezoVoltageChannel strainFraction nDielectric
  tribo := triboVoltageChannel axisGap coordinationExcess
  faraday := faradayVoltageChannel phaseRateFraction

/-- Combined outside-contact × voltage-generation dress. -/
def electroContactDress (L : OutsideContactLedger) (V : VoltageGenerationLedger) : ℝ :=
  outsideContactLedgerDress L * voltageGenerationLedgerDress V

/-- Dilute-gas + unstressed voltage: recovers legacy contact surplus alone. -/
theorem electroContactDress_dilute_unstressed
    (geffSum surplus : ℝ) :
    electroContactDress
        (diluteGasOutsideContactLedger geffSum surplus)
        unstressedVoltageGenerationLedger =
      outsideGeffSurplus geffSum surplus := by
  unfold electroContactDress
  rw [unstressedVoltageGenerationLedger_dress, diluteGasOutsideContactLedger_dress]
  ring

/-- Promoted n-body factor with outside ledger × voltage ledger × preferred-axis. -/
def nBodyPromotedElectroContactFactor
    (L : OutsideContactLedger) (V : VoltageGenerationLedger) (eta g : ℝ) : ℝ :=
  electroContactDress L V * preferredAxisPlaneLocalDress eta g

/-- Dilute + unstressed recovers `outsideGeff × preferredAxis`. -/
theorem nBodyPromotedElectroContactFactor_dilute_unstressed
    (geffSum surplus eta g : ℝ) :
    nBodyPromotedElectroContactFactor
        (diluteGasOutsideContactLedger geffSum surplus)
        unstressedVoltageGenerationLedger eta g =
      outsideGeffSurplus geffSum surplus * preferredAxisPlaneLocalDress eta g := by
  unfold nBodyPromotedElectroContactFactor
  rw [electroContactDress_dilute_unstressed]

end

end Hqiv.QuantumChemistry

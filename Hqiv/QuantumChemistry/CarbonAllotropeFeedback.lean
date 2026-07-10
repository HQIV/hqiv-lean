import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.BaryogenesisDynamicBulk
import Hqiv.Physics.HomogeneousCurvatureSecondOrder
import Hqiv.Physics.HQIVNuclei
import Hqiv.Physics.NuclearOutsideTemperatureDynamics
import Hqiv.QuantumChemistry.AllotropeNetwork
import Hqiv.QuantumChemistry.OutsideContactLedger
import Hqiv.QuantumChemistry.SecondOrderEffects
import Hqiv.QuantumChemistry.VoltageGenerationLedger
import HqivSpine.Chemistry.Spectroscopy
import HqivSpine.Physics.ContinuousHorizon
import HqivSpine.Physics.GeneratorDependentCoupling

/-!
# Carbon allotrope feedback dynamics

The mass-pin assay freezes every outside / voltage channel at dilute / unstressed
identity.  This module derives the **reopened** feedback terms for the carbon
fork (graphene \(k=3\) vs diamond \(k=4\)) so they can be applied correctly:

* **Exact slots** — bond orders \(4/3\) and \(1\), preferred-axis gap \(0\) on
  C–C, chemo identity, bulk identity at the Casimir lock-in shell.
* **Shared feedback** — electric channel from a common C–C dielectric \(n\);
  mild EMF stresses lift both motifs equally.
* **Fork feedback** — local defect relative to the diamond reference
  \(\delta = |k - 4|/4\) splits graphene from diamond; tribo inherits that split
  when the axis gap vanishes.

No fitted coefficients.  Absolute SI densities / volts remain readout pins;
this module is the dimensionless coupling algebra.

Python mirrors:
  `scripts/hqiv_carbon_feedback_tease.py`,
  `scripts/hqiv_graphene_mass_pin.py`.
-/

namespace Hqiv.QuantumChemistry

open Hqiv
open Hqiv.Physics
open Hqiv.QuantumChemistry.AllotropeNetwork
open HqivSpine.Chemistry
open HqivSpine.Physics.GeneratorDependentCoupling

noncomputable section

/-! ## Carbon network primitives -/

/-- Carbon octet shared-pair capacity: valence 4 ⇒ `cap = 4`. -/
def carbonOctetCapacity : ℝ := octetSharedPairCapacity 4

theorem carbonOctetCapacity_eq : carbonOctetCapacity = 4 := by
  unfold carbonOctetCapacity octetSharedPairCapacity; norm_num

/-- Graphene / graphite coordination. -/
def grapheneCoordination : ℝ := 3

/-- Diamond coordination (reference network for local-defect excess). -/
def diamondCoordination : ℝ := 4

/-- Graphene bond order `cap/k = 4/3`. -/
def grapheneBondOrder : ℝ :=
  networkBondOrder carbonOctetCapacity grapheneCoordination

/-- Diamond bond order `cap/k = 1`. -/
def diamondBondOrder : ℝ :=
  networkBondOrder carbonOctetCapacity diamondCoordination

theorem grapheneBondOrder_eq : grapheneBondOrder = 4 / 3 := by
  unfold grapheneBondOrder networkBondOrder carbonOctetCapacity grapheneCoordination
    octetSharedPairCapacity
  norm_num

theorem diamondBondOrder_eq : diamondBondOrder = 1 := by
  unfold diamondBondOrder networkBondOrder carbonOctetCapacity diamondCoordination
    octetSharedPairCapacity
  norm_num

theorem graphene_partition :
    grapheneBondOrder * grapheneCoordination = carbonOctetCapacity := by
  unfold grapheneBondOrder grapheneCoordination
  exact bondOrder_partition carbonOctetCapacity 3 (by norm_num)

theorem diamond_partition :
    diamondBondOrder * diamondCoordination = carbonOctetCapacity := by
  unfold diamondBondOrder diamondCoordination
  exact bondOrder_partition carbonOctetCapacity 4 (by norm_num)

/-! ## Coordination excess (fork stress) -/

/-- Local-defect stress relative to a reference coordination:
`δ = |k − k_ref| / max(k_ref, 1)`. -/
def coordinationExcessVsReference (k kRef : ℝ) : ℝ :=
  |k - kRef| / max kRef 1

def grapheneCoordinationExcess : ℝ :=
  coordinationExcessVsReference grapheneCoordination diamondCoordination

def diamondCoordinationExcess : ℝ :=
  coordinationExcessVsReference diamondCoordination diamondCoordination

theorem grapheneCoordinationExcess_eq : grapheneCoordinationExcess = 1 / 4 := by
  unfold grapheneCoordinationExcess coordinationExcessVsReference
    grapheneCoordination diamondCoordination
  norm_num

theorem diamondCoordinationExcess_eq : diamondCoordinationExcess = 0 := by
  unfold diamondCoordinationExcess coordinationExcessVsReference diamondCoordination
  norm_num

/-! ## Local-defect channel dynamics -/

theorem diamond_localDefect_identity :
    outsideLocalDefectChannel diamondCoordinationExcess = 1 := by
  rw [diamondCoordinationExcess_eq, outsideLocalDefectChannel_zero]

/-- Graphene local-defect lift:
`1 + γ·(4/8)·(1/4) = 1 + (2/5)·(1/2)·(1/4) = 21/20`. -/
theorem graphene_localDefect_eq :
    outsideLocalDefectChannel grapheneCoordinationExcess = 21 / 20 := by
  rw [grapheneCoordinationExcess_eq]
  unfold outsideLocalDefectChannel localCurvatureDefectExcess
  rw [gamma_eq_2_5, strongChannelFraction_eq_four_eighths]
  norm_num

theorem graphene_over_diamond_localDefect :
    outsideLocalDefectChannel grapheneCoordinationExcess /
      outsideLocalDefectChannel diamondCoordinationExcess = 21 / 20 := by
  rw [graphene_localDefect_eq, diamond_localDefect_identity]
  norm_num

/-- Graphene defect formation energy vs diamond reference:
`E_bind · γ · (4/8) · (1/4) = E_bind / 20`. -/
theorem graphene_defectFormationEnergyEv (bindingEv : ℝ) :
    defectFormationEnergyEv bindingEv grapheneCoordinationExcess =
      bindingEv / 20 := by
  unfold defectFormationEnergyEv localCurvatureDefectExcess
  rw [grapheneCoordinationExcess_eq, gamma_eq_2_5, strongChannelFraction_eq_four_eighths]
  have hmax : (max (1 / 4 : ℝ) 0) = 1 / 4 := by norm_num
  rw [hmax]
  ring

theorem diamond_defectFormationEnergyEv_zero (bindingEv : ℝ) :
    defectFormationEnergyEv bindingEv diamondCoordinationExcess = 0 := by
  rw [diamondCoordinationExcess_eq, defectFormationEnergyEv_zero_excess]

/-! ## Preferred-axis / chemo identities on C–C -/

/-- Bond polarity `|Zᵢ − Zⱼ| / (Zᵢ + Zⱼ)`. -/
def bondPolarity (zI zJ : ℝ) : ℝ := |zI - zJ| / max (zI + zJ) 1

theorem bondPolarity_homonuclear (z : ℝ) : bondPolarity z z = 0 := by
  unfold bondPolarity
  simp [abs_zero]

theorem carbon_carbon_polarity_zero : bondPolarity 6 6 = 0 :=
  bondPolarity_homonuclear 6

theorem preferredAxisSpectralGap_singleton_zero :
    preferredAxisSpectralGap [0] = 0 := by
  unfold preferredAxisSpectralGap polarityMass polaritySupport polarityMax
    polaritySecondMax
  simp

theorem carbon_carbon_preferredAxis_identity (eta : ℝ) :
    preferredAxisPlaneLocalDress eta
      (preferredAxisSpectralGap [bondPolarity 6 6]) = 1 := by
  rw [carbon_carbon_polarity_zero, preferredAxisSpectralGap_singleton_zero,
    preferredAxisPlaneLocalDress_zero_axis]

theorem carbon_carbon_chemo_identity : chemoVoltageChannel 0 = 1 :=
  chemoVoltageChannel_zero

/-! ## Bulk channel at the carbon / lock-in shell -/

/-- Carbon covalent-network contact ξ equals the lock-in shell (`xiLockin = 5`). -/
def carbonContactXi : ℝ := xiLockin

theorem carbonContactXi_eq_five : carbonContactXi = 5 := by
  unfold carbonContactXi; exact xiLockin_eq_five

/-- Casimir local/global budget at carbon contact is exactly 1. -/
theorem carbon_casimir_budget_lockin :
    curvatureBudgetLocalGlobalAtXi carbonContactXi = 1 := by
  unfold carbonContactXi
  exact curvatureBudgetLocalGlobalAtXi_lockin

def carbonBulkTarget : ℝ := curvatureBudgetLocalGlobalAtXi carbonContactXi

theorem carbonBulkTarget_eq_one : carbonBulkTarget = 1 :=
  carbon_casimir_budget_lockin

/-- Medium-density bulk channel is identity for any ρ when the target is 1. -/
theorem outsideBulkChannel_of_unit_target (ρ : ℝ) :
    outsideBulkChannel 1 ρ = 1 := by
  unfold outsideBulkChannel scaleOutsideCouplingForMediumDensity clampMediumDensity
  ring

theorem carbon_bulk_identity (ρ : ℝ) :
    outsideBulkChannel carbonBulkTarget ρ = 1 := by
  rw [carbonBulkTarget_eq_one, outsideBulkChannel_of_unit_target]

/-! ## Gravity channel at non-positive lapse -/

theorem outsideGravityGeffModulator_nonpos (φ : ℝ) (h : φ ≤ 0) :
    outsideGravityGeffModulator ⟨φ⟩ = 1 := by
  unfold outsideGravityGeffModulator
  simp [h]

theorem carbon_grav_identity_zero :
    outsideGravityGeffModulator ⟨0⟩ = 1 :=
  outsideGravityGeffModulator_nonpos 0 (le_refl 0)

/-! ## Electric channel (shared on C–C) -/

theorem carbon_em_unit : outsideEmChannel 1 = 1 := outsideEmChannel_unit

/-! ## Tribo inherits the local-defect fork when g = 0 -/

theorem triboVoltageChannel_zero_gap (δ : ℝ) :
    triboVoltageChannel 0 δ = outsideLocalDefectChannel δ := by
  unfold triboVoltageChannel
  rw [clampUnitStress_zero, voltageChannel_unstressed]
  ring

theorem graphene_tribo_eq_localDefect :
    triboVoltageChannel 0 grapheneCoordinationExcess =
      outsideLocalDefectChannel grapheneCoordinationExcess :=
  triboVoltageChannel_zero_gap _

theorem diamond_tribo_identity :
    triboVoltageChannel 0 diamondCoordinationExcess = 1 := by
  rw [triboVoltageChannel_zero_gap, diamond_localDefect_identity]

/-! ## Mass-pin freeze vs reopened ledgers -/

def carbonMassPinOutsideLedger : OutsideContactLedger :=
  diluteGasOutsideContactLedger 0 1

def carbonMassPinVoltageLedger : VoltageGenerationLedger :=
  unstressedVoltageGenerationLedger

theorem carbon_mass_pin_electro_identity :
    electroContactDress carbonMassPinOutsideLedger carbonMassPinVoltageLedger = 1 := by
  unfold carbonMassPinOutsideLedger carbonMassPinVoltageLedger
  rw [electroContactDress_dilute_unstressed, outsideGeffSurplus_base]

/-- Reopened local-defect-only ledger. -/
def carbonLocalDefectLedger (δ : ℝ) : OutsideContactLedger where
  grav := 1
  em := 1
  bulk := 1
  localDefect := outsideLocalDefectChannel δ
  contact := 1

theorem carbonLocalDefectLedger_dress (δ : ℝ) :
    outsideContactLedgerDress (carbonLocalDefectLedger δ) =
      outsideLocalDefectChannel δ := by
  unfold outsideContactLedgerDress carbonLocalDefectLedger
  ring

/-- Reopened electric-only ledger (shared). -/
def carbonEmLedger (n : ℝ) : OutsideContactLedger where
  grav := 1
  em := outsideEmChannel n
  bulk := 1
  localDefect := 1
  contact := 1

theorem carbonEmLedger_dress (n : ℝ) :
    outsideContactLedgerDress (carbonEmLedger n) = outsideEmChannel n := by
  unfold outsideContactLedgerDress carbonEmLedger
  ring

/-- Combined condensed carbon ledger: em + localDefect (+ optional bulk/grav).
Bulk stays identity at the carbon Casimir shell. -/
def carbonCondensedLedger (n φ δ ρ : ℝ) : OutsideContactLedger where
  grav := outsideGravityGeffModulator ⟨φ⟩
  em := outsideEmChannel n
  bulk := outsideBulkChannel carbonBulkTarget ρ
  localDefect := outsideLocalDefectChannel δ
  contact := 1

theorem carbonCondensedLedger_bulk_drops (n φ δ ρ : ℝ) :
    (carbonCondensedLedger n φ δ ρ).bulk = 1 := by
  unfold carbonCondensedLedger
  exact carbon_bulk_identity ρ

theorem electroContactDress_localDefect_factor (δ : ℝ) :
    electroContactDress (carbonLocalDefectLedger δ) unstressedVoltageGenerationLedger =
      outsideLocalDefectChannel δ := by
  unfold electroContactDress
  rw [unstressedVoltageGenerationLedger_dress, carbonLocalDefectLedger_dress]
  ring

theorem electroContactDress_em_factor (n : ℝ) :
    electroContactDress (carbonEmLedger n) unstressedVoltageGenerationLedger =
      outsideEmChannel n := by
  unfold electroContactDress
  rw [unstressedVoltageGenerationLedger_dress, carbonEmLedger_dress]
  ring

theorem graphene_localDefect_electro_dress :
    electroContactDress
        (carbonLocalDefectLedger grapheneCoordinationExcess)
        unstressedVoltageGenerationLedger =
      21 / 20 := by
  rw [electroContactDress_localDefect_factor, graphene_localDefect_eq]

theorem diamond_localDefect_electro_dress :
    electroContactDress
        (carbonLocalDefectLedger diamondCoordinationExcess)
        unstressedVoltageGenerationLedger =
      1 := by
  rw [electroContactDress_localDefect_factor, diamond_localDefect_identity]

/-- Condensed carbon dress at φ = 0 factors as em × localDefect. -/
theorem carbonCondensed_unstressed_dress_phi0 (n δ ρ : ℝ) :
    electroContactDress
        (carbonCondensedLedger n 0 δ ρ)
        unstressedVoltageGenerationLedger =
      outsideEmChannel n * outsideLocalDefectChannel δ := by
  unfold electroContactDress carbonCondensedLedger outsideContactLedgerDress
  rw [unstressedVoltageGenerationLedger_dress, carbon_bulk_identity,
    carbon_grav_identity_zero]
  ring

/-- Graphene / diamond condensed ratio at equal dielectric equals `21/20`. -/
theorem graphene_over_diamond_condensed_unstressed (n ρ : ℝ)
    (hne : outsideEmChannel n ≠ 0) :
    electroContactDress
        (carbonCondensedLedger n 0 grapheneCoordinationExcess ρ)
        unstressedVoltageGenerationLedger /
      electroContactDress
        (carbonCondensedLedger n 0 diamondCoordinationExcess ρ)
        unstressedVoltageGenerationLedger =
      21 / 20 := by
  rw [carbonCondensed_unstressed_dress_phi0, carbonCondensed_unstressed_dress_phi0,
    diamond_localDefect_identity, graphene_localDefect_eq]
  field_simp [hne]

/-- Mild piezo recovers identity when unstressed. -/
theorem carbon_piezo_unstressed (n : ℝ) : piezoVoltageChannel 0 n = 1 :=
  piezoVoltageChannel_zero n

end

end Hqiv.QuantumChemistry

import Mathlib.Data.Fin.Basic
import Hqiv.QuantumChemistry.AtomElectronicBinding
import Hqiv.QuantumChemistry.AtomElectronicDischarge
import Hqiv.QuantumChemistry.AtomNucleusCurvatureShell
import Hqiv.QuantumChemistry.AtomOutsideCurvatureFight
import Hqiv.QuantumChemistry.DynamicBindingChart
import Hqiv.QuantumChemistry.FiniteSiteQuantumChemistry

/-!
# Atom readout from nuclear charge (prediction path)

Assembles **nucleus + electronic discharge + Slater binding + outside fight** from HQIV math.

**Scale witness:** `proton_lockin` / `derivedProtonMass` at `referenceM` pins MeV.
**Comparison layer:** NIST/CODATA atomic masses live in Python `AtomComparisonLayer` only.

Python mirror: `scripts/hqiv_atom_construction.py`.
-/

namespace Hqiv.QuantumChemistry

open Hqiv.Physics
open scoped BigOperators

/-- Number of electron sites booked on the finite-site chart. -/
def atomElectronSiteCount (Z : ℕ) : ℕ := Z

/-- Diagonal site-energy trace for a neutral atom (core + valence on discharge slots). -/
noncomputable def atomSiteEnergyTrace (Z : ℕ) : ℝ :=
  if Z = 0 then 0
  else if Z = 1 then Hqiv.ProteinResearch.latticeFullModeEnergy electronicComptonHydrogenS
  else if Z = 2 then
    2 * Hqiv.ProteinResearch.latticeFullModeEnergy electronicComptonHydrogenS
  else
    let slots := atomComptonSlotsFromCharge Z
    let core := 2 * Hqiv.ProteinResearch.latticeFullModeEnergy electronicComptonHydrogenS
    let nVal := Z - 2
    let nS := min nVal (2 : ℕ)
    let nP := nVal - nS
    core +
      (nS : ℝ) * Hqiv.ProteinResearch.latticeFullModeEnergy slots.mCentreS +
        (nP : ℝ) * Hqiv.ProteinResearch.latticeFullModeEnergy slots.mCentreP

/-- Closed atomic mass [MeV]: nucleus + electrons − Slater binding + outside fight. -/
noncomputable def atomClosedMassMeV (Z : ℕ) (c : ℝ := 1) : ℝ :=
  if Z = 0 then 0
  else
    atomNuclearClusterMassMeV Z c + (Z : ℝ) * atomElectronMassMeV
      - atomElectronicBindingMeV Z c
      + atomElectronicOutsideCurvatureFightMeV Z c

/-- CODATA MeV/amu bridge for reporting only (not a chemistry fit). -/
def mevPerAmuBridge : ℝ := 931.49410242

/-- Nuclear cluster mass only [amu] (diagnostic tier). -/
noncomputable def atomNuclearOnlyMassAmu (Z : ℕ) (c : ℝ := 1) : ℝ :=
  atomNuclearClusterMassMeV Z c / mevPerAmuBridge

/-- Primary derived atomic mass [amu]: full closed readout. -/
noncomputable def atomDerivedAtomicMassAmu (Z : ℕ) (c : ℝ := 1) : ℝ :=
  atomClosedMassMeV Z c / mevPerAmuBridge

/-- Full atom readout bundle (prediction objects only). -/
structure AtomReadout where
  nuclearCharge : ℕ
  massNumber : ℕ
  discharge : AtomElectronicDischargeObs
  compton : AtomComptonSlots
  triplet : DynamicComptonTriplet
  nuclearMassMeV : ℝ
  electronMassTotalMeV : ℝ
  electronicBindingMeV : ℝ
  electronicOutsideCurvatureFightMeV : ℝ
  closedMassMeV : ℝ
  nuclearOnlyMassAmu : ℝ
  derivedAtomicMassAmu : ℝ
  siteEnergyTrace : ℝ
  hydrogenicBinding : ℝ
  firstIonizationEv : ℝ

/-- Construct atom readout from `Z` under `proton_lockin` mass chart. -/
noncomputable def atomReadoutFromCharge (Z : ℕ) (c : ℝ := 1) : AtomReadout :=
  { nuclearCharge := Z
    massNumber := stableMassNumberForCharge Z
    discharge := atomElectronicDischargeObs Z
    compton := atomComptonSlotsFromCharge Z
    triplet := atomComptonTripletFromCharge Z
    nuclearMassMeV := atomNuclearClusterMassMeV Z c
    electronMassTotalMeV := (Z : ℝ) * atomElectronMassMeV
    electronicBindingMeV := atomElectronicBindingMeV Z c
    electronicOutsideCurvatureFightMeV := atomElectronicOutsideCurvatureFightMeV Z c
    closedMassMeV := atomClosedMassMeV Z c
    nuclearOnlyMassAmu := atomNuclearOnlyMassAmu Z c
    derivedAtomicMassAmu := atomDerivedAtomicMassAmu Z c
    siteEnergyTrace := atomSiteEnergyTrace Z
    hydrogenicBinding := atomHydrogenicBindingMagnitude Z 1 c
    firstIonizationEv := atomFirstIonizationEv Z c }

theorem atomReadoutFromCharge_discharge (Z : ℕ) (c : ℝ) :
    (atomReadoutFromCharge Z c).discharge = atomElectronicDischargeObs Z := rfl

theorem atomReadoutFromCharge_compton (Z : ℕ) (c : ℝ) :
    (atomReadoutFromCharge Z c).compton = atomComptonSlotsFromCharge Z := rfl

theorem atomReadoutFromCharge_fight (Z : ℕ) (c : ℝ) :
    (atomReadoutFromCharge Z c).electronicOutsideCurvatureFightMeV =
      atomElectronicOutsideCurvatureFightMeV Z c := rfl

theorem atomReadoutFromCharge_binding (Z : ℕ) (c : ℝ) :
    (atomReadoutFromCharge Z c).electronicBindingMeV = atomElectronicBindingMeV Z c := rfl

/-- Finite-site chemistry spec: one shell label per electron site. -/
def atomFiniteSiteShell (Z : ℕ) (i : Fin Z) : ℕ :=
  atomElectronShellForIndex Z i.val

/-- Packaging as `FiniteSiteChemistrySpec` (requires `Z > 0`). -/
def atomFiniteSiteSpec (Z : ℕ) (_h : 0 < Z) : FiniteSiteChemistrySpec Z :=
  ⟨fun i => atomFiniteSiteShell Z i⟩

theorem atomReadoutFromCharge_hydrogen_triplet (c : ℝ) :
    (atomReadoutFromCharge 1 c).triplet = dynamicComptonTripletH2 := by
  simp [atomReadoutFromCharge, atomComptonTripletFromCharge, dynamicComptonTripletH2]

theorem atomReadoutFromCharge_hydrogen_fight_zero (c : ℝ) :
    (atomReadoutFromCharge 1 c).electronicOutsideCurvatureFightMeV = 0 :=
  atomElectronicOutsideCurvatureFightMeV_hydrogen c

end Hqiv.QuantumChemistry

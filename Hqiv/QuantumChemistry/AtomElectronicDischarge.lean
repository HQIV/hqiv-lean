import Hqiv.QuantumChemistry.DynamicBindingChart
import Hqiv.QuantumChemistry.ElectronicValenceFromTuftChart

/-!
# Atom electronic discharge registry (heavy-decay template)

**Prediction path:** nuclear charge `Z` alone fixes discharge observables; Compton shell
slots follow from a **fixed registry** (TUFT chart rows + period block logic).

**Comparison layer:** NIST/PDG atomic data never enter these definitions.

Mirrors `Hqiv.Physics.SpineDischargeUniqueness` factorization uniqueness on a slot table.
Python mirror: `scripts/hqiv_atom_electronic_discharge.py`.
-/

namespace Hqiv.QuantumChemistry

open Hqiv.Physics

/-! ## Block-period observables from `Z` alone -/

/-- Principal chemical period from nuclear charge (noble-gas block boundaries). -/
def chemicalPeriod (Z : ℕ) : ℕ :=
  if Z ≤ 2 then 1
  else if Z ≤ 10 then 2
  else if Z ≤ 18 then 3
  else if Z ≤ 36 then 4
  else if Z ≤ 54 then 5
  else 6 + (Z - 54 - 1) / 18

/-- Valence electrons outside the previous noble-gas core. -/
def valenceElectronCount (Z : ℕ) : ℕ :=
  if Z ≤ 2 then Z
  else if Z ≤ 10 then Z - 2
  else if Z ≤ 18 then Z - 10
  else if Z ≤ 36 then Z - 18
  else if Z ≤ 54 then Z - 36
  else Z - 54

theorem chemicalPeriod_one (Z : ℕ) (h : Z ≤ 2) : chemicalPeriod Z = 1 := by
  unfold chemicalPeriod
  split_ifs <;> omega

theorem chemicalPeriod_two (Z : ℕ) (h : 3 ≤ Z ∧ Z ≤ 10) : chemicalPeriod Z = 2 := by
  unfold chemicalPeriod
  split_ifs <;> omega

theorem valenceElectronCount_hydrogen : valenceElectronCount 1 = 1 := rfl

theorem valenceElectronCount_helium : valenceElectronCount 2 = 2 := rfl

theorem valenceElectronCount_carbon : valenceElectronCount 6 = 4 := by decide

theorem valenceElectronCount_oxygen : valenceElectronCount 8 = 6 := by decide

/-! ## Stable main-isotope mass numbers `A(Z)` (nuclear chart bookkeeping). -/

/-- Main-isotope mass number chart (not NIST mass input). -/
def stableMassNumberForCharge (Z : ℕ) : ℕ :=
  match Z with
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | 3 => 7
  | 4 => 9
  | 5 => 11
  | 6 => 12
  | 7 => 14
  | 8 => 16
  | 9 => 19
  | 11 => 23
  | 17 => 35
  | 26 => 56
  | n => if n ≤ 2 then n else if n % 2 = 0 then n else n + 1

theorem stableMassNumberForCharge_hydrogen : stableMassNumberForCharge 1 = 1 := rfl

theorem stableMassNumberForCharge_helium : stableMassNumberForCharge 2 = 4 := rfl

theorem stableMassNumberForCharge_carbon : stableMassNumberForCharge 6 = 12 := rfl

/-- Discharge observables extracted from `(Z)` (analogue of `DischargeObservables`). -/
structure AtomElectronicDischargeObs where
  nuclearCharge : ℕ
  chemicalPeriod : ℕ
  valenceCount : ℕ
  periodOffset : ℕ
  pShellActive : Bool
  deriving Repr

/-- Registry extraction: observables are a pure function of `Z`. -/
def atomElectronicDischargeObs (Z : ℕ) : AtomElectronicDischargeObs :=
  { nuclearCharge := Z
    chemicalPeriod := chemicalPeriod Z
    valenceCount := valenceElectronCount Z
    periodOffset := electronicComptonPeriodOffset (chemicalPeriod Z)
    pShellActive := 2 ≤ chemicalPeriod Z ∧ 1 < Z }

theorem atomElectronicDischargeObs_nuclearCharge (Z : ℕ) :
    (atomElectronicDischargeObs Z).nuclearCharge = Z := rfl

theorem atomElectronicDischargeObs_periodOffset (Z : ℕ) :
    (atomElectronicDischargeObs Z).periodOffset =
      electronicComptonPeriodOffset (chemicalPeriod Z) := rfl

/-! ## Canonical Compton slot assignment -/

/-- Compton ladder indices for chemistry (not nuclear `m_nuc`). -/
structure AtomComptonSlots where
  mH1s : ℕ
  mCentreS : ℕ
  mCentreP : ℕ
  pDegeneracy : ℕ
  deriving Repr

/-- S² orbital degeneracy `2ℓ+1` for ℓ=1 (p shell). -/
def pShellOrbitalDegeneracy : ℕ := 3

/-- s-shell degeneracy (ℓ=0). -/
def sShellOrbitalDegeneracy : ℕ := 1

/-- Canonical slot assignment from discharge observables. -/
def atomComptonSlotsCanonical (o : AtomElectronicDischargeObs) : AtomComptonSlots :=
  { mH1s := electronicComptonHydrogenS
    mCentreS := electronicComptonCentreSAtPeriod o.chemicalPeriod
    mCentreP := electronicComptonCentrePAtPeriod o.chemicalPeriod
    pDegeneracy := if o.pShellActive then pShellOrbitalDegeneracy else sShellOrbitalDegeneracy }

/-- Primary export: Compton slots from nuclear charge. -/
def atomComptonSlotsFromCharge (Z : ℕ) : AtomComptonSlots :=
  atomComptonSlotsCanonical (atomElectronicDischargeObs Z)

theorem atomComptonSlotsCanonical_h1s (o : AtomElectronicDischargeObs) :
    (atomComptonSlotsCanonical o).mH1s = 1 := rfl

theorem atomComptonSlotsCanonical_centreS (o : AtomElectronicDischargeObs) :
    (atomComptonSlotsCanonical o).mCentreS =
      electronicComptonCentreSAtPeriod o.chemicalPeriod := rfl

theorem atomComptonSlotsFromCharge_hydrogen :
    (atomComptonSlotsFromCharge 1).mH1s = 1 ∧
      (atomComptonSlotsFromCharge 1).mCentreS = tuftHeavyChartShell ∧
        (atomComptonSlotsFromCharge 1).pDegeneracy = sShellOrbitalDegeneracy := by
  unfold atomComptonSlotsFromCharge atomComptonSlotsCanonical atomElectronicDischargeObs
  decide

/-- Dynamic binding triplet `(m_s, m_p, m_H)` for heavy-hydride-style readouts. -/
def atomComptonTripletFromCharge (Z : ℕ) : DynamicComptonTriplet :=
  if Z ≤ 1 then
    dynamicComptonTripletH2
  else
    let s := atomComptonSlotsFromCharge Z
    { m0 := s.mCentreS, m1 := s.mCentreP, m2 := s.mH1s }

theorem atomComptonTripletFromCharge_hydrogen :
    atomComptonTripletFromCharge 1 = dynamicComptonTripletH2 := by
  simp [atomComptonTripletFromCharge, dynamicComptonTripletH2]

theorem atomComptonTripletFromCharge_lithium :
    atomComptonTripletFromCharge 3 = dynamicComptonTripletHeavyHydride := by
  simp [atomComptonTripletFromCharge, dynamicComptonTripletHeavyHydride, atomComptonSlotsFromCharge,
    atomComptonSlotsCanonical, atomElectronicDischargeObs, chemicalPeriod, valenceElectronCount,
    electronicComptonPeriodOffset, electronicComptonCentreSAtPeriod, electronicComptonCentrePAtPeriod,
    tuftHeavyChartShell_eq_four, tuftStrongChartShell_eq_three, electronicComptonHydrogenS,
    pShellOrbitalDegeneracy, DynamicComptonTriplet]

/-! ## Slot registry + factorization uniqueness (decay template) -/

inductive AtomElectronicSlot where
  | h1s
  | centreS
  | centreP
  | pDegeneracy
  deriving DecidableEq, Repr, Inhabited

def allAtomElectronicSlots : List AtomElectronicSlot :=
  [.h1s, .centreS, .centreP, .pDegeneracy]

def atomElectronicSlotValue (s : AtomElectronicSlot) (o : AtomElectronicDischargeObs) : ℕ :=
  match s with
  | .h1s => electronicComptonHydrogenS
  | .centreS => electronicComptonCentreSAtPeriod o.chemicalPeriod
  | .centreP => electronicComptonCentrePAtPeriod o.chemicalPeriod
  | .pDegeneracy => if o.pShellActive then pShellOrbitalDegeneracy else sShellOrbitalDegeneracy

theorem atomElectronicSlotValue_h1s (o : AtomElectronicDischargeObs) :
    atomElectronicSlotValue .h1s o = 1 := rfl

def atomComptonSlotsFromSlotValues (o : AtomElectronicDischargeObs) : AtomComptonSlots :=
  { mH1s := atomElectronicSlotValue .h1s o
    mCentreS := atomElectronicSlotValue .centreS o
    mCentreP := atomElectronicSlotValue .centreP o
    pDegeneracy := atomElectronicSlotValue .pDegeneracy o }

theorem atomComptonSlotsCanonical_eq_slot_values (o : AtomElectronicDischargeObs) :
    atomComptonSlotsCanonical o = atomComptonSlotsFromSlotValues o := by
  unfold atomComptonSlotsCanonical atomComptonSlotsFromSlotValues atomElectronicSlotValue
  simp [electronicComptonHydrogenS, pShellOrbitalDegeneracy, sShellOrbitalDegeneracy]

/--
A competitor assignment satisfies **electronic discharge factorization** when it equals the
canonical slot table on every observable pattern.
-/
def SatisfiesAtomElectronicFactorization (assign : AtomElectronicDischargeObs → AtomComptonSlots) :
    Prop :=
  ∀ o, assign o = atomComptonSlotsFromSlotValues o

theorem atomComptonSlotsCanonical_satisfies_factorization :
    SatisfiesAtomElectronicFactorization atomComptonSlotsCanonical := by
  intro o
  rw [atomComptonSlotsCanonical_eq_slot_values o]

theorem atomComptonSlots_unique_factorization {assign : AtomElectronicDischargeObs → AtomComptonSlots}
    (h : SatisfiesAtomElectronicFactorization assign) (o : AtomElectronicDischargeObs) :
    assign o = atomComptonSlotsCanonical o := by
  rw [h o, atomComptonSlotsCanonical_eq_slot_values o]

theorem atomComptonSlots_unique_factorization_fn {assign : AtomElectronicDischargeObs → AtomComptonSlots}
    (h : SatisfiesAtomElectronicFactorization assign) :
    assign = atomComptonSlotsCanonical := by
  funext o
  exact atomComptonSlots_unique_factorization h o

theorem atomComptonSlotsFromCharge_eq_canonical (Z : ℕ) :
    atomComptonSlotsFromCharge Z = atomComptonSlotsCanonical (atomElectronicDischargeObs Z) := rfl

end Hqiv.QuantumChemistry

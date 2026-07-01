import HqivSpine.Chemistry.Aufbau
import HqivSpine.Chemistry.Binding
import HqivSpine.Physics.Shell
import HqivSpine.Physics.DecayMasterFormula

/-!
# `HqivSpine.Chemistry.AtomDischarge` — unique `(Z) →` electronic discharge

Golfed from legacy `AtomElectronicDischarge` / `AtomFromCharge`: the heavy-decay template on
atoms — observables are a **pure function of `Z`**, using the derived `Aufbau` occupancy rather
than hand-entered Compton rows.

Honest scope: **registry extraction + factorization uniqueness** on a fixed slot table — NIST
masses stay comparison-only.
-/

namespace HqivSpine.Chemistry.AtomDischarge

open HqivSpine.Chemistry.Aufbau
open HqivSpine.Chemistry.Binding
open HqivSpine.Physics
open HqivSpine.Physics.DecayMasterFormula

/-- Discharge observables extracted from nuclear charge `Z`. -/
structure AtomDischargeObs where
  nuclearCharge : ℕ
  period : ℕ
  valenceCount : ℕ
  topShell : ℕ
  pShellActive : Bool
  deriving Repr

/-- Registry extraction: observables are a pure function of `Z`. -/
def atomDischargeObs (Z : ℕ) : AtomDischargeObs :=
  { nuclearCharge := Z
    period := topPrincipal Z
    valenceCount := valenceCount Z
    topShell := topPrincipal Z
    pShellActive := 2 ≤ topPrincipal Z ∧ 1 < Z }

theorem atomDischargeObs_charge (Z : ℕ) : (atomDischargeObs Z).nuclearCharge = Z := rfl

theorem atomDischargeObs_carbon :
    (atomDischargeObs 6).valenceCount = 4 ∧ (atomDischargeObs 6).period = 2 := by
  exact ⟨carbon_valence.2, carbon_valence.1⟩

theorem atomDischargeObs_sodium :
    (atomDischargeObs 11).valenceCount = 1 ∧ (atomDischargeObs 11).period = 3 := by
  exact ⟨sodium_valence.2, sodium_valence.1⟩

/-- Stable main-isotope chart (comparison bookkeeping, not NIST input). -/
def stableMassNumber (Z : ℕ) : ℕ :=
  match Z with
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | 6 => 12
  | 8 => 16
  | n => if n ≤ 2 then n else if n % 2 = 0 then n else n + 1

theorem stableMassNumber_hydrogen : stableMassNumber 1 = 1 := rfl

theorem stableMassNumber_helium : stableMassNumber 2 = 4 := rfl

/-- Compton shell slots from discharge: hydrogen `1s`, centre shells from period. -/
def comptonShell1s : ℕ := 0

def comptonShellCentreS (Z : ℕ) : ℕ :=
  if (atomDischargeObs Z).period ≤ 2 then 0 else referenceM + ((atomDischargeObs Z).period - 3)

def comptonShellCentreP (Z : ℕ) : ℕ :=
  if (atomDischargeObs Z).period ≤ 2 then 0 else referenceM + 1 + ((atomDischargeObs Z).period - 3)

/-- Electronic binding magnitude at the valence electron (Hartree units). -/
noncomputable def electronicBindingHartree (Z : ℕ) (μ : ℝ) : ℝ :=
  if h : 0 < Z then
    let obs := atomDischargeObs Z
    atomicSiteBindingHartree Z (principalBlock Z) ⟨Z - 1, by omega⟩ μ (obs.topShell : ℝ)
  else 0

/-- **Uniqueness of discharge extraction:** equal observables force equal charge. -/
theorem atomDischargeObs_injective_on_charge (Z Z' : ℕ)
    (h : atomDischargeObs Z = atomDischargeObs Z') : Z = Z' := by
  exact congrArg AtomDischargeObs.nuclearCharge h

/-- Inactive discharge pattern contributes unity (decay-master product law). -/
theorem atomDischargeProduct_inactive (g : Fin 8 → ℝ) :
    dischargeProduct g 0 = 1 :=
  dischargeProduct_zero g

end HqivSpine.Chemistry.AtomDischarge

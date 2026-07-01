import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Hqiv.Physics.NuclearCausticBinding
import Hqiv.Physics.NuclearOutsideTemperatureDynamics
import Hqiv.QuantumChemistry.AtomElectronicDischarge
import Hqiv.QuantumChemistry.AtomNucleusCurvatureShell
import Hqiv.QuantumChemistry.CurvatureBondContact

/-!
# Electronic outside-curvature fight (Z > H)

Nucleons **deepen** the cluster well via outside caustics (`nuclearOutsideCausticBinding`).
Bound electrons **fight** that outside load; mass adds as

`Σ_e (B_out/A) · (4/8) · G_eff(θ_e) · (α_eff/α_lock)² · max(0, mod_bonded(ξ_e) − 1) · (Z/A)`.

Hydrogen (`A = 1`, no outside caustic stack) carries zero fight.

Python mirror: `scripts/hqiv_atom_construction.py` (`atom_electronic_outside_curvature_fight_mev`).

S vs p valence slots use distinct discharge Compton rows (`mCentreS`, `mCentreP`).
-/

namespace Hqiv.QuantumChemistry

open Hqiv.Physics
open scoped BigOperators

noncomputable section

/-! ## Discharge shell vector with s / p valence rows -/

/-- Valence s electrons on the TUFT centre-s row (max two per period block). -/
def atomValenceSCount (Z : ℕ) : ℕ :=
  if Z ≤ 2 then 0 else min (Z - 2) 2

/-- Valence p electrons on the TUFT centre-p row. -/
def atomValencePCount (Z : ℕ) : ℕ :=
  if Z ≤ 2 then 0 else Z - 2 - atomValenceSCount Z

theorem atomValencePCount_oxygen : atomValencePCount 8 = 4 := by decide

/-- Orbital class for electron site `i` (core 1s vs valence s vs valence p). -/
inductive AtomElectronOrbitalSlot
  | coreS
  | valenceS
  | valenceP
  deriving DecidableEq, Repr

def atomElectronOrbitalSlotForIndex (Z i : ℕ) : AtomElectronOrbitalSlot :=
  if Z ≤ 2 then .coreS
  else if i ≤ 1 then .coreS
  else if i < 2 + atomValenceSCount Z then .valenceS
  else .valenceP

theorem atomElectronOrbitalSlotForIndex_core (Z : ℕ) (h : 2 < Z) :
    atomElectronOrbitalSlotForIndex Z 0 = .coreS ∧
      atomElectronOrbitalSlotForIndex Z 1 = .coreS := by
  unfold atomElectronOrbitalSlotForIndex
  simp [h]

theorem atomElectronOrbitalSlotForIndex_oxygen_p (i : ℕ) (h : 4 ≤ i ∧ i ≤ 7) :
    atomElectronOrbitalSlotForIndex 8 i = .valenceP := by
  unfold atomElectronOrbitalSlotForIndex atomValenceSCount
  have hZ : 2 < 8 := by decide
  have hn : atomValenceSCount 8 = 2 := by decide
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp_all [hn, hZ]

/-- Compton discharge shell index for electron site `i`. -/
def atomElectronShellForIndex (Z i : ℕ) : ℕ :=
  let slots := atomComptonSlotsFromCharge Z
  match atomElectronOrbitalSlotForIndex Z i with
  | .coreS => electronicComptonHydrogenS
  | .valenceS => slots.mCentreS
  | .valenceP => slots.mCentreP

theorem atomElectronShellForIndex_hydrogen :
    atomElectronShellForIndex 1 0 = electronicComptonHydrogenS := by
  unfold atomElectronShellForIndex atomElectronOrbitalSlotForIndex
  decide

theorem atomElectronShellForIndex_helium_both_1s :
    atomElectronShellForIndex 2 0 = 1 ∧ atomElectronShellForIndex 2 1 = 1 := by
  unfold atomElectronShellForIndex atomElectronOrbitalSlotForIndex
  decide

theorem atomElectronShellForIndex_oxygen_2p :
    atomElectronShellForIndex 8 4 = tuftStrongChartShell ∧
      atomElectronShellForIndex 8 5 = tuftStrongChartShell := by
  unfold atomElectronShellForIndex atomElectronOrbitalSlotForIndex atomComptonSlotsFromCharge
    atomComptonSlotsCanonical atomElectronicDischargeObs chemicalPeriod valenceElectronCount
    electronicComptonPeriodOffset electronicComptonCentrePAtPeriod
  decide

/-! ## Outside fight per discharge shell -/

/-- Caustic contact phase scaffold from shell triplet (Python compton-window mean). -/
noncomputable def atomNuclearCausticContactPhase (m mCluster mThird : ℕ) : ℝ :=
  min phaseTheta
    (phaseTheta *
      ((mThird : ℝ) / (max (max m mCluster) mThird + 1 : ℝ)))

/-- Outside caustic binding per nucleon at the cluster drum. -/
noncomputable def atomOutsideNuclearBindingPerNucleon (mNuc A : ℕ) (c : ℝ := 1) : ℝ :=
  if A ≤ 1 then 0
  else
    let θ := atomNuclearCausticContactPhase mNuc mNuc referenceM
    nuclearOutsideCausticBinding mNuc A θ c / (A : ℝ)

/-- Bonded outside modulator excess above lock-in unity (fight load). -/
noncomputable def outsideCurvatureFightLoadAtXi (ξ : ℝ) : ℝ :=
  max 0 (outsideCurvatureBindingModulatorBonded ξ - 1)

/-- Single-electron outside-curvature fight increment [MeV]. -/
noncomputable def atomElectronicOutsideFightPerShell
    (mNuc mShell : ℕ) (A Z : ℕ) (c : ℝ := 1) : ℝ :=
  let ξ := xiOfShell mShell
  let bOutPerN := atomOutsideNuclearBindingPerNucleon mNuc A c
  let θ := atomNuclearCausticContactPhase mNuc mShell referenceM
  let geff := outsideContactCoupling θ
  let load := outsideCurvatureFightLoadAtXi ξ
  let ae := alphaEffAtShell mShell c
  let aeLock := alphaEffAtShell referenceM c
  strongChannelFraction * bOutPerN * load * geff * (ae / aeLock) ^ 2 * ((Z : ℝ) / (A : ℝ))

/-- Total electronic outside fight for neutral atom (zero for H). -/
noncomputable def atomElectronicOutsideCurvatureFightMeV (Z : ℕ) (c : ℝ := 1) : ℝ :=
  if Z ≤ 1 then 0
  else
    let A := stableMassNumberForCharge Z
    let mNuc := nucleusCurvatureShell A
    (Finset.univ : Finset (Fin Z)).sum fun i =>
      atomElectronicOutsideFightPerShell mNuc (atomElectronShellForIndex Z i.val) A Z c

theorem atomElectronicOutsideCurvatureFightMeV_hydrogen (c : ℝ) :
    atomElectronicOutsideCurvatureFightMeV 1 c = 0 := by
  unfold atomElectronicOutsideCurvatureFightMeV
  simp

end

end Hqiv.QuantumChemistry

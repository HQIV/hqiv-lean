import Hqiv.Physics.TuftShellChart
import Hqiv.Physics.TrappedCasimirBindingBridge
import Hqiv.Physics.ContinuousXiPath
import Hqiv.QuantumChemistry.FiniteSiteQuantumChemistry
import Hqiv.QuantumChemistry.LiH
import Hqiv.QuantumChemistry.DynamicBindingChart

/-!
# Electronic valence shells from the TUFT chart (post-T12/T13)

Chemistry Compton slots are **not** nuclear drum indices `m_nuc(A)`.
They are the weak/strong/heavy Beltrami chart rows plus the proton-anchor
hydrogen rung `m = 1`.

No fitted constants; shells are named definitions from `TuftShellChart` and
`referenceM`.
-/

namespace Hqiv.QuantumChemistry

open Hqiv
open Hqiv.Physics
open scoped BigOperators

/-- Chemist-facing electronic slot tags. -/
inductive ElectronicSlot where
  | h1s
  | centre2s
  | centre2p
deriving DecidableEq, Repr

/-- Proton-anchor hydrogen `1s` Compton rung (below `tuftWeakChartShell`). -/
def electronicComptonHydrogenS : ℕ := 1

/-- Period-2 centre `2s` row = heavy TUFT chart shell. -/
def electronicComptonCentreS : ℕ := tuftHeavyChartShell

/-- Period-2 centre `2p` row = strong TUFT chart shell. -/
def electronicComptonCentreP : ℕ := tuftStrongChartShell

theorem electronicComptonCentreS_eq_tuftHeavy :
    electronicComptonCentreS = tuftHeavyChartShell := rfl

theorem electronicComptonCentreP_eq_tuftStrong :
    electronicComptonCentreP = tuftStrongChartShell := rfl

theorem electronicComptonCentreS_eq_four : electronicComptonCentreS = 4 := by
  rw [electronicComptonCentreS_eq_tuftHeavy, tuftHeavyChartShell_eq_four]

theorem electronicComptonCentreP_eq_three : electronicComptonCentreP = 3 := by
  rw [electronicComptonCentreP_eq_tuftStrong, tuftStrongChartShell_eq_three]

/-- Map electronic slot to Compton shell index `m`. -/
def electronicComptonShell (slot : ElectronicSlot) : ℕ :=
  match slot with
  | .h1s => electronicComptonHydrogenS
  | .centre2s => electronicComptonCentreS
  | .centre2p => electronicComptonCentreP

theorem electronicComptonShell_h1s : electronicComptonShell .h1s = 1 := rfl

theorem electronicComptonShell_centre2s : electronicComptonShell .centre2s = 4 := by
  simp [electronicComptonShell, electronicComptonCentreS_eq_four]

theorem electronicComptonShell_centre2p : electronicComptonShell .centre2p = 3 := by
  simp [electronicComptonShell, electronicComptonCentreP_eq_three]

theorem dynamicComptonTripletHeavyHydride_eq_electronic_slots :
    dynamicComptonTripletHeavyHydride.m0 = electronicComptonCentreS ∧
      dynamicComptonTripletHeavyHydride.m1 = electronicComptonCentreP ∧
        dynamicComptonTripletHeavyHydride.m2 = electronicComptonHydrogenS := by
  simp [dynamicComptonTripletHeavyHydride, electronicComptonCentreS, electronicComptonCentreP,
    electronicComptonHydrogenS]

theorem dynamicComptonTripletHeavyHydride_eq_chart :
    dynamicComptonTripletHeavyHydride.m0 = tuftHeavyChartShell ∧
      dynamicComptonTripletHeavyHydride.m1 = tuftStrongChartShell ∧
        dynamicComptonTripletHeavyHydride.m2 = 1 := by
  simpa [electronicComptonCentreS_eq_tuftHeavy, electronicComptonCentreP_eq_tuftStrong]
    using dynamicComptonTripletHeavyHydride_eq_electronic_slots

theorem lihComptonLiSShell_eq_electronicCentreS : lihComptonLiSShell = electronicComptonCentreS := rfl

theorem lihComptonLiPShell_eq_electronicCentreP : lihComptonLiPShell = electronicComptonCentreP := rfl

theorem lihComptonHSShell_eq_electronicHydrogenS : lihComptonHSShell = electronicComptonHydrogenS := rfl

/-- Site energy on shell `m` equals the trapped Casimir zero-point budget. -/
theorem latticeFullModeEnergy_eq_trappedCasimirEnergyAtShell (m : ℕ) :
    Hqiv.ProteinResearch.latticeFullModeEnergy m = trappedCasimirEnergyAtShell m := by
  unfold Hqiv.ProteinResearch.latticeFullModeEnergy trappedCasimirEnergyAtShell
  rw [casimirPerModeZeroPoint_eq_phi_half]

/-- ξ-chart lift of per-shell site energy (dynamic ladder). -/
theorem latticeFullModeEnergy_eq_xi_chart (m : ℕ) :
    Hqiv.ProteinResearch.latticeFullModeEnergy m =
      ContinuousXiPath.latticeFullModeEnergy_xi (xiOfShell m) :=
  (ContinuousXiPath.latticeFullModeEnergy_xi_chart m).symm

/-- Orbital-weighted site trace for O(2s,2p) + H(1s) pattern. -/
noncomputable def h2oOrbitalSiteEnergyTrace (mO mH : ℕ) : ℝ :=
  Hqiv.ProteinResearch.latticeFullModeEnergy mO +
    3 * Hqiv.ProteinResearch.latticeFullModeEnergy (electronicComptonCentreP) +
    2 * Hqiv.ProteinResearch.latticeFullModeEnergy mH

theorem h2oOrbitalSiteEnergyTrace_tuft_default :
    h2oOrbitalSiteEnergyTrace electronicComptonCentreS electronicComptonHydrogenS =
      Hqiv.ProteinResearch.latticeFullModeEnergy electronicComptonCentreS +
        3 * Hqiv.ProteinResearch.latticeFullModeEnergy electronicComptonCentreP +
        2 * Hqiv.ProteinResearch.latticeFullModeEnergy electronicComptonHydrogenS := rfl

theorem h2oOrbitalSiteEnergyTrace_tuft_default_nonneg :
    0 ≤ h2oOrbitalSiteEnergyTrace electronicComptonCentreS electronicComptonHydrogenS := by
  unfold h2oOrbitalSiteEnergyTrace
  nlinarith [latticeFullModeEnergy_nonneg electronicComptonCentreS,
    latticeFullModeEnergy_nonneg electronicComptonCentreP,
    latticeFullModeEnergy_nonneg electronicComptonHydrogenS]

end Hqiv.QuantumChemistry

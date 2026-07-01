import Mathlib.Data.Fin.Basic
import Hqiv.Physics.BoundStates
import Hqiv.Physics.FanoSectorSpectralMassEmergence
import Hqiv.QuantumChemistry.AtomElectronicDischarge
import Hqiv.QuantumChemistry.AtomNucleusCurvatureShell
import Hqiv.QuantumChemistry.AtomOutsideCurvatureFight

/-!
# Multi-electron Slater binding on discharge shells

Python mirror: `scripts/hqiv_atom_construction.py`
(`atom_electronic_binding_mev`, `config_effective_charge`, `bind_energy_ev_for_n`).

Uses physical Coulomb `−μ Z_eff²/(2n²)` in Hartree a.u. with principal `n` from the discharge
block.  HQIV `α_eff(m)` is tracked separately in the continuous-ξ panel.

Scope note: the definitions below infer the principal block from the Compton shell index `m`,
which is correct for period ≤ 2 (the lemmas `principalQuantumFromComptonShell_{h1s,2s,2p}`
remain valid).  The Python prediction path now resolves the principal quantum number from the
true Madelung **aufbau configuration** (`electron_configuration`, `config_effective_charge`,
`valence_electron_pull`) so that period 3+ valence electrons (e.g. Na 3s at `n = 3`) and the
electronegativity ordering `F > Cl > O > N > C > H > Na > Li` come out correctly; mirroring that
aufbau into Lean for period 3+ is future work.
-/

namespace Hqiv.QuantumChemistry

open Hqiv.Physics
open scoped BigOperators

noncomputable section

/-- CODATA proton/electron mass ratio — comparison guardrail only (no longer fed
into the electron mass). -/
def protonToElectronMassRatio : ℝ := codataProtonToElectronMassRatio

/-- Electron mass is now the DERIVED HQIV readout (TUFT vev→T8 winding `n=1`),
not `derivedProtonMass / 1836.15`.  See `Hqiv.Physics.derivedProtonToElectronMassRatio`. -/
noncomputable def atomElectronMassMeV : ℝ := derivedElectronMass_MeV

/-- Hartree → eV unit bridge (reporting only). -/
def hartreeToEvBridge : ℝ := 27.211386245988

/-- Map discharge Compton shell to principal block (Slater bookkeeping). -/
def principalQuantumFromComptonShell (m : ℕ) : ℕ :=
  if m ≤ 1 then 1 else if m ≤ 4 then 2 else 3 + (m - 4) / 2

theorem principalQuantumFromComptonShell_h1s :
    principalQuantumFromComptonShell electronicComptonHydrogenS = 1 := by
  unfold principalQuantumFromComptonShell electronicComptonHydrogenS
  decide

theorem principalQuantumFromComptonShell_2s :
    principalQuantumFromComptonShell tuftHeavyChartShell = 2 := by
  rw [tuftHeavyChartShell_eq_four]
  unfold principalQuantumFromComptonShell
  decide

theorem principalQuantumFromComptonShell_2p :
    principalQuantumFromComptonShell tuftStrongChartShell = 2 := by
  rw [tuftStrongChartShell_eq_three]
  unfold principalQuantumFromComptonShell
  decide

/-- Reduced mass μ = M/(M+1) with M = m_nucleus/m_e. -/
noncomputable def atomReducedMassAu (Z : ℕ) (c : ℝ := 1) : ℝ :=
  if Z = 0 then 1
  else
    let mOver := atomNuclearClusterMassMeV Z c / atomElectronMassMeV
    mOver / (mOver + 1)

/-! ## Screening derived from the carrier (no empirical Slater table)

The screening increments `0.35 / 0.85 / 1.00` are not fitted: a deeper electron screens a whole
unit by Gauss enclosure (`1`); a co-radial same-shell electron is only half enclosed on average
(the monogamy half `1/2`); and the valence carrier penetrates an adjacent shell by the lapse over
the proton-anchor shell, `leak = α / referenceM = (3/5)/4 = 0.15`.  Hence same-shell `1/2 − α/4 =
0.35` and adjacent `1 − α/4 = 0.85`, reproducing Slater exactly.  (`α = 3/5` is the lattice-forced
`OctonionicLightCone.alpha`; `referenceM = 4`.) -/

/-- Lattice-forced lapse `α = 3/5` (`OctonionicLightCone.alpha_eq_3_5`). -/
def screenLatticeAlpha : ℝ := 3 / 5

/-- Adjacent-shell penetration leak `α / referenceM = (3/5)/4`. -/
def screenPenetrationLeak : ℝ := screenLatticeAlpha / 4

/-- Same-shell increment = monogamy half − leak. -/
def slaterSameShell : ℝ := 1 / 2 - screenPenetrationLeak

/-- Adjacent (n−1) increment = full Gauss enclosure − leak. -/
def slaterAdjacentShell : ℝ := 1 - screenPenetrationLeak

/-- Deep-shell increment = full Gauss enclosure. -/
def slaterDeepShell : ℝ := 1

/-- The derived same-shell increment is exactly Slater's `0.35`. -/
theorem slaterSameShell_eq : slaterSameShell = 0.35 := by
  unfold slaterSameShell screenPenetrationLeak screenLatticeAlpha; norm_num

/-- The derived adjacent increment is exactly Slater's `0.85`. -/
theorem slaterAdjacentShell_eq : slaterAdjacentShell = 0.85 := by
  unfold slaterAdjacentShell screenPenetrationLeak screenLatticeAlpha; norm_num

/-- The same-shell and adjacent increments differ by exactly the monogamy half `1/2`. -/
theorem slater_same_adjacent_gap : slaterAdjacentShell - slaterSameShell = 1 / 2 := by
  unfold slaterAdjacentShell slaterSameShell; ring

/-- Slater screening increment from one other electron site (now from derived constants). -/
def slaterShieldingIncrement (nTarget nOther : ℕ) : ℝ :=
  if nTarget = nOther then slaterSameShell else slaterAdjacentShell

/-- Standard Slater effective charge at discharge site `target`. -/
noncomputable def slaterEffectiveCharge (Z : ℕ) (target : Fin Z) : ℝ :=
  let nTarget := principalQuantumFromComptonShell (atomElectronShellForIndex Z target.val)
  let shield :=
    (Finset.univ : Finset (Fin Z)).sum fun j =>
      if j = target then 0
      else
        slaterShieldingIncrement nTarget
          (principalQuantumFromComptonShell (atomElectronShellForIndex Z j.val))
  max 1 ((Z : ℝ) - shield)

/-- Hydrogenic binding magnitude [eV] at discharge shell `m`. -/
noncomputable def slaterBindEnergyEv (m : ℕ) (zEff μ : ℝ) : ℝ :=
  let n := (principalQuantumFromComptonShell m : ℝ)
  μ * zEff * zEff / (2 * n * n) * hartreeToEvBridge

/-- Total electronic binding [MeV] from Slater sum over discharge occupancy. -/
noncomputable def atomElectronicBindingMeV (Z : ℕ) (c : ℝ := 1) : ℝ :=
  if Z = 0 then 0
  else
    let μ := atomReducedMassAu Z c
    (1e-6 : ℝ) *
      (Finset.univ : Finset (Fin Z)).sum fun i =>
        slaterBindEnergyEv (atomElectronShellForIndex Z i.val)
          (slaterEffectiveCharge Z i) μ

/-- Legacy 1s hydrogenic magnitude (diagnostic). -/
noncomputable def atomHydrogenicBindingMagnitude (Z : ℕ) (μ : ℝ := 1) (c : ℝ := 1) : ℝ :=
  if Z = 0 then 0 else E_bind_atomic_shell_magnitude electronicComptonHydrogenS Z μ c

/-- Outermost discharge electron binding [eV] (ionization witness). -/
noncomputable def atomFirstIonizationEv (Z : ℕ) (c : ℝ := 1) : ℝ :=
  if hZ : Z = 0 then 0
  else
    have hpos : 0 < Z := by omega
    let last : Fin Z := ⟨Z - 1, Nat.sub_lt hpos Nat.one_pos⟩
    slaterBindEnergyEv (atomElectronShellForIndex Z last.val)
      (slaterEffectiveCharge Z last) (atomReducedMassAu Z c)

end

end Hqiv.QuantumChemistry

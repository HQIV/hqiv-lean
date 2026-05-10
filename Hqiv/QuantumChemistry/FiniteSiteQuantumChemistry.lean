import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

import Hqiv.Physics.LightConeMaxwellQFTBridge
import Hqiv.ProteinResearch.AtomEnergyOSHoracleBridge

/-!
# Finite-site quantum chemistry bridge (traditional organization)

This module organizes the finite-site chemistry proofs under a dedicated
`Hqiv.QuantumChemistry` namespace while reusing the same HQIV shell ladder.

Core objects:

* diagonal site energies from `latticeFullModeEnergy`,
* finite-patch QFT mode budgets from `LightConeMaxwellQFTBridge`,
* trace/nonnegativity facts suitable for external numerical pipelines.

No new `axiom`, no `sorry`.
-/

namespace Hqiv.QuantumChemistry

open scoped BigOperators
open Matrix Finset
open Hqiv

variable {n : ℕ}

/-- Per-shell lattice zero-point site energy is nonnegative (modes ≥ 0, φ > 0). -/
theorem latticeFullModeEnergy_nonneg (m : ℕ) : 0 ≤ Hqiv.ProteinResearch.latticeFullModeEnergy m := by
  unfold Hqiv.ProteinResearch.latticeFullModeEnergy
  have hν : 0 ≤ Hqiv.available_modes m := by
    rw [Hqiv.available_modes_eq]
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith [hm]
  have hφ : 0 < phi_of_shell m := phi_of_shell_pos m
  have hhalf : 0 ≤ phi_of_shell m / 2 := by linarith
  exact mul_nonneg hν hhalf

/-- First-principles closed form: no fitted coefficient in the per-shell site budget. -/
theorem latticeFullModeEnergy_closed_form (m : ℕ) :
    Hqiv.ProteinResearch.latticeFullModeEnergy m = 4 * (m + 2 : ℝ) * (m + 1 : ℝ) ^ 2 := by
  unfold Hqiv.ProteinResearch.latticeFullModeEnergy
  rw [Hqiv.available_modes_eq, phi_of_shell_closed_form]
  rw [phiTemperatureCoeff_eq_two]
  ring

/-- List-aligned site sum is nonnegative. -/
theorem listLatticeEnergySum_nonneg (shells : List ℕ) :
    0 ≤ Hqiv.ProteinResearch.listLatticeEnergySum shells := by
  unfold Hqiv.ProteinResearch.listLatticeEnergySum
  let R := List.range shells.length
  have hsum : 0 ≤ (R.map (fun i => Hqiv.ProteinResearch.latticeFullModeEnergy (shells.getD i 0))).sum := by
    induction R with
    | nil => simp
    | cons _ as ih =>
        simp [List.map_cons, List.sum_cons]
        exact add_nonneg (latticeFullModeEnergy_nonneg _) ih
  exact hsum

/-- Diagonal atomic site trace is nonnegative. -/
theorem atomSiteEnergyMatrix_trace_nonneg (shell : Fin n → ℕ) :
    0 ≤ trace (Hqiv.ProteinResearch.atomSiteEnergyMatrix shell) := by
  rw [Hqiv.ProteinResearch.trace_atomSiteEnergyMatrix]
  refine Finset.sum_nonneg fun i _ => latticeFullModeEnergy_nonneg _

/-- Canonical finite-site chemistry specification: one shell label per site. -/
structure FiniteSiteChemistrySpec (n : ℕ) where
  /-- HQIV shell index per residue/site. -/
  shell : Fin n → ℕ

/-- Canonical diagonal site-energy trace. -/
noncomputable def siteEnergyTrace {n : ℕ} (s : FiniteSiteChemistrySpec n) : ℝ :=
  trace (Hqiv.ProteinResearch.atomSiteEnergyMatrix s.shell)

theorem siteEnergyTrace_nonneg (s : FiniteSiteChemistrySpec n) : 0 ≤ siteEnergyTrace s :=
  atomSiteEnergyMatrix_trace_nonneg s.shell

/-- QFT-bridge finite patch budget aggregated over sites (`0..m` shell capacity per site). -/
noncomputable def siteModeBudgetTrace {n : ℕ} (s : FiniteSiteChemistrySpec n) : ℝ :=
  ∑ i : Fin n, Hqiv.Physics.accessibleModeBudgetUpToShell (s.shell i)

theorem siteModeBudgetTrace_nonneg (s : FiniteSiteChemistrySpec n) :
    0 ≤ siteModeBudgetTrace s := by
  unfold siteModeBudgetTrace
  refine Finset.sum_nonneg fun i _ => ?_
  exact Hqiv.Physics.accessibleModeBudgetUpToShell_nonneg (s.shell i)

/-- Time-angle (`φ·t`) lifted site budget: shell index inferred by the QFT bridge at each site. -/
noncomputable def siteModeBudgetTraceFromPhiTime {n : ℕ}
    (s : FiniteSiteChemistrySpec n) (t : ℝ) : ℝ :=
  ∑ i : Fin n, Hqiv.Physics.accessibleModeBudgetUpToPhiTime (s.shell i) t

theorem siteModeBudgetTraceFromPhiTime_nonneg
    (s : FiniteSiteChemistrySpec n) (t : ℝ) :
    0 ≤ siteModeBudgetTraceFromPhiTime s t := by
  unfold siteModeBudgetTraceFromPhiTime
  refine Finset.sum_nonneg fun i _ => ?_
  exact Hqiv.Physics.accessibleModeBudgetUpToPhiTime_nonneg (s.shell i) t

theorem siteModeBudgetTraceFromPhiTime_unit_eq_siteModeBudgetTrace
    (s : FiniteSiteChemistrySpec n) :
    siteModeBudgetTraceFromPhiTime s 1 = siteModeBudgetTrace s := by
  unfold siteModeBudgetTraceFromPhiTime siteModeBudgetTrace
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Hqiv.Physics.accessibleModeBudgetUpToPhiTime_eq_accessibleModeBudgetUpToShell_unit (s.shell i)

/-!
## Orbital-channel extension (`s` / `p`)

To move beyond H₂-style `s`-only calibration (e.g. LiH with active `p` channels on Li),
we keep the same shell ladder but attach a finite orbital channel tag per site.

This is still finite and algebraic (no classical PDE closure).
-/

/-- Minimal orbital-channel tag for first extension past `s`-only chemistry. -/
inductive OrbitalChannel where
  | s
  | p
deriving DecidableEq, Repr

/-- Spatial degeneracy count used as channel multiplicity weight. -/
def orbitalDegeneracy : OrbitalChannel → ℕ
  | .s => 1
  | .p => 3

theorem orbitalDegeneracy_pos (c : OrbitalChannel) : 0 < orbitalDegeneracy c := by
  cases c <;> decide

/-- Finite-site chemistry spec with a shell index and orbital channel tag at each site. -/
structure OrbitalSiteChemistrySpec (n : ℕ) where
  shell : Fin n → ℕ
  channel : Fin n → OrbitalChannel

/-- Channel-weighted site-energy trace (`s=1`, `p=3`) on the HQIV shell ladder. -/
noncomputable def orbitalWeightedSiteEnergyTrace {n : ℕ} (s : OrbitalSiteChemistrySpec n) : ℝ :=
  ∑ i : Fin n,
    (orbitalDegeneracy (s.channel i) : ℝ) * Hqiv.ProteinResearch.latticeFullModeEnergy (s.shell i)

theorem orbitalWeightedSiteEnergyTrace_nonneg (s : OrbitalSiteChemistrySpec n) :
    0 ≤ orbitalWeightedSiteEnergyTrace s := by
  unfold orbitalWeightedSiteEnergyTrace
  refine Finset.sum_nonneg (fun i _ => ?_)
  exact mul_nonneg (Nat.cast_nonneg (orbitalDegeneracy (s.channel i)))
    (latticeFullModeEnergy_nonneg (s.shell i))

/-- Channel-weighted mode-budget trace (`accessibleModeBudgetUpToShell`). -/
noncomputable def orbitalWeightedModeBudgetTrace {n : ℕ} (s : OrbitalSiteChemistrySpec n) : ℝ :=
  ∑ i : Fin n,
    (orbitalDegeneracy (s.channel i) : ℝ) * Hqiv.Physics.accessibleModeBudgetUpToShell (s.shell i)

theorem orbitalWeightedModeBudgetTrace_nonneg (s : OrbitalSiteChemistrySpec n) :
    0 ≤ orbitalWeightedModeBudgetTrace s := by
  unfold orbitalWeightedModeBudgetTrace
  refine Finset.sum_nonneg (fun i _ => ?_)
  exact mul_nonneg (Nat.cast_nonneg (orbitalDegeneracy (s.channel i)))
    (Hqiv.Physics.accessibleModeBudgetUpToShell_nonneg (s.shell i))

end Hqiv.QuantumChemistry

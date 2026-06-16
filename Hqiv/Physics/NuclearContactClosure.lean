import Hqiv.Physics.HQIVNuclei
import Hqiv.Physics.BBNNetworkFromWeights
import Hqiv.QuantumChemistry.BondStateNetwork
import Hqiv.Geometry.OctonionicLightCone

import Mathlib.Tactic

/-!
# Nuclear contact closure — zero information deficit at ⁴He

**Fully interacting particle (light-nucleus chart).** On the constructive isotope ladder
(`deuteron` → `helium3` → `helium4`), each bind step books **two** toroidal valley
overlaps. Through **⁴He** the ladder saturates the **six** pairwise nucleon–nucleon
contacts of a tetrahedral α cluster (`K₄` complete graph). Below `A = 4`, clusters carry
a **contact information deficit** — unbooked channels relative to that α closure cap.

This package proves that combinatorial bookkeeping (no fitted potentials). It aligns with
the bond-state network identity

`closed network − separated network = edge closure + hyperclosure`

(`BondStateNetwork`): at `A = 4` every explicit edge-closure slot of the four-node,
six-edge tetrahedral network is represented in the valley count.

**What is not claimed here:** a variational derivation of `referenceM = 4` from the null
lattice. The lock-in shell pin remains conventional (`OctonionicLightCone.referenceM`);
we only prove the **numeric coincidence** that the first zero-deficit mass number is `4`.
-/

namespace Hqiv.Physics

open Hqiv

/-- Pairwise nucleon–nucleon contacts in a complete `A`-body graph: `C(A,2)`. -/
def pairwiseNucleonContactCount (A : ℕ) : ℕ := Nat.choose A 2

theorem choose_four_two_eq_six : Nat.choose 4 2 = 6 := by decide

theorem pairwiseNucleonContactCount_four_eq_six :
    pairwiseNucleonContactCount 4 = 6 := by
  simp [pairwiseNucleonContactCount, choose_four_two_eq_six]

theorem constructiveValleyCap_eq_pairwise_four :
    constructiveValleyCap = pairwiseNucleonContactCount 4 := by
  rw [constructiveValleyCap_eq_six, pairwiseNucleonContactCount_four_eq_six]

theorem deuteron_valleyCount : valleyCount deuteron = 2 := rfl

theorem helium3_valleyCount : valleyCount helium3 = 4 := rfl

/-- On the canonical light-nucleus ladder, valley count is `2(A−1)` through `A ≤ 4`. -/
theorem bbnValleyCount_eq_two_mul_pred (A : ℕ) (hA : A ≤ 4) :
    bbnValleyCount A = 2 * (A - 1) := by
  interval_cases A <;> simp [bbnValleyCount, valleyCount, deuteron, helium3, helium4]

/-- Unbooked toroidal contact channels relative to ⁴He constructive closure. -/
def contactInformationDeficit (A : ℕ) : ℕ :=
  constructiveValleyCap - bbnValleyCount A

/-- A light nucleus is **fully contact-closed** when every α-scale constructive channel
is booked (zero contact information deficit). -/
def isFullyContactClosed (A : ℕ) : Prop :=
  contactInformationDeficit A = 0

theorem contactInformationDeficit_eq_cap_minus_ladder (A : ℕ) :
    contactInformationDeficit A = constructiveValleyCap - bbnValleyCount A := rfl

theorem contactInformationDeficit_A1 : contactInformationDeficit 1 = 6 := by
  simp [contactInformationDeficit, constructiveValleyCap_eq_six, bbnValleyCount]

theorem contactInformationDeficit_A2 : contactInformationDeficit 2 = 4 := by
  simp [contactInformationDeficit, constructiveValleyCap_eq_six, bbnValleyCount_two]

theorem contactInformationDeficit_A3 : contactInformationDeficit 3 = 2 := by
  simp [contactInformationDeficit, constructiveValleyCap_eq_six, bbnValleyCount_three]

theorem bbnValleyCount_zero_of_gt_four (A : ℕ) (h : 4 < A) : bbnValleyCount A = 0 := by
  unfold bbnValleyCount
  split <;> try omega

theorem contactInformationDeficit_zero_iff_four (A : ℕ) (hA : A ≤ 4) :
    contactInformationDeficit A = 0 ↔ A = 4 := by
  interval_cases A <;>
    simp [contactInformationDeficit, bbnValleyCount, bbnValleyCount_two, bbnValleyCount_three,
      bbnValleyCount_four, constructiveValleyCap_eq_six, deuteron_valleyCount, helium3_valleyCount,
      helium4_valleyCount]

theorem isFullyContactClosed_iff_four (A : ℕ) (hA : A ≤ 4) :
    isFullyContactClosed A ↔ A = 4 := by
  unfold isFullyContactClosed
  exact contactInformationDeficit_zero_iff_four A hA

theorem contactInformationDeficit_A4 : contactInformationDeficit 4 = 0 := by
  simp [contactInformationDeficit, constructiveValleyCap_eq_six, bbnValleyCount_four]

theorem isFullyContactClosed_four : isFullyContactClosed 4 := by
  simp [isFullyContactClosed, contactInformationDeficit_A4]

/-- Each added nucleon on the canonical ladder removes two units of contact deficit. -/
theorem contactInformationDeficit_succ (A : ℕ) (hlo : 1 ≤ A) (hhi : A ≤ 3) :
    contactInformationDeficit A = contactInformationDeficit (A + 1) + 2 := by
  interval_cases A <;> simp [contactInformationDeficit, bbnValleyCount, bbnValleyCount_two,
    bbnValleyCount_three, bbnValleyCount_four, constructiveValleyCap_eq_six, deuteron_valleyCount,
    helium3_valleyCount, helium4_valleyCount] <;> omega

theorem fullyContactClosed_unique_light (A : ℕ) (hA : A ≤ 4) (h : isFullyContactClosed A) :
    A = 4 :=
  (isFullyContactClosed_iff_four A hA).mp h

theorem fullyContactClosed_only_four (A : ℕ) (h : isFullyContactClosed A) : A = 4 := by
  by_cases hA : A ≤ 4
  · exact fullyContactClosed_unique_light A hA h
  · have hgt : 4 < A := by omega
    have hcount := bbnValleyCount_zero_of_gt_four A hgt
    have hdef : contactInformationDeficit A = 6 := by
      simp [contactInformationDeficit, hcount, constructiveValleyCap_eq_six]
    rw [h] at hdef
    omega

theorem choose_two_two_eq_one : Nat.choose 2 2 = 1 := by decide

theorem choose_three_two_eq_three : Nat.choose 3 2 = 3 := by decide

theorem tetrahedralEdgeCount_eq_six : tetrahedralEdgeCount = 6 := rfl

/-- First mass number where the constructive ladder equals the complete pairwise count. -/
theorem constructiveLadder_eq_pairwise_iff_four (A : ℕ) (hA : 2 ≤ A) (hA4 : A ≤ 4) :
    bbnValleyCount A = pairwiseNucleonContactCount A ↔ A = 4 := by
  interval_cases A <;>
    simp [bbnValleyCount, pairwiseNucleonContactCount, choose_four_two_eq_six,
      choose_two_two_eq_one, choose_three_two_eq_three, deuteron_valleyCount, helium3_valleyCount,
      helium4_valleyCount]

/-- Edge count for a fully interacting four-nucleon bond-state network (`K₄`). -/
def fullyInteractingTetrahedralEdgeCount : ℕ := 6

theorem fullyInteractingTetrahedralEdgeCount_eq_tetrahedral :
    fullyInteractingTetrahedralEdgeCount = tetrahedralEdgeCount := rfl

theorem helium4_valleys_eq_tetrahedral_bond_edges :
    valleyCount helium4 = fullyInteractingTetrahedralEdgeCount := by
  rw [helium4_valleyCount, fullyInteractingTetrahedralEdgeCount]

/-- Normalized fraction of α constructive contact channels booked at mass number `A`. -/
noncomputable def contactClosureFraction (A : ℕ) : ℝ :=
  (bbnValleyCount A : ℝ) / (constructiveValleyCap : ℝ)

theorem contactClosureFraction_four_eq_one :
    contactClosureFraction 4 = 1 := by
  unfold contactClosureFraction
  rw [bbnValleyCount_four, constructiveValleyCap_eq_six]
  norm_num

theorem contactClosureFraction_lt_one_of_lt_four (A : ℕ) (hA : 2 ≤ A) (hlt : A < 4) :
    contactClosureFraction A < 1 := by
  unfold contactClosureFraction
  have hcap : (constructiveValleyCap : ℝ) = 6 := by norm_num [constructiveValleyCap_eq_six]
  rw [hcap]
  have hcases : A = 2 ∨ A = 3 := by omega
  rcases hcases with rfl | rfl
  · rw [bbnValleyCount_two]; norm_num
  · rw [bbnValleyCount_three]; norm_num

theorem bbnValleyBindingFactor_eq_one_plus_count_over_six (A : ℕ) (hA : A ≤ 4) :
    bbnValleyBindingFactor A 0 = 1 + (bbnValleyCount A : ℝ) / 6 := by
  rw [bbnValleyBindingFactor_eq_ladder_for_A_le_4 A hA, bbnValleyCount_four]
  norm_num [constructiveValleyCap_eq_six]

/-- Maximal toroidal valley binding factor (`bbnValleyBindingFactor = 2`) iff zero deficit. -/
theorem no_contact_deficit_iff_max_valley_binding (A : ℕ) (hA : A ≤ 4) :
    isFullyContactClosed A ↔ bbnValleyBindingFactor A 0 = 2 := by
  rw [isFullyContactClosed_iff_four A hA, bbnValleyBindingFactor_eq_one_plus_count_over_six A hA]
  interval_cases A <;>
    simp [bbnValleyCount, bbnValleyCount_two, bbnValleyCount_three, bbnValleyCount_four,
      deuteron_valleyCount, helium3_valleyCount, helium4_valleyCount] <;>
    norm_num

/-!
### Lock-in shell coincidence (convention, not derivation)

`bbnBindingShell = referenceM` evaluates light-nucleus binding on the HQIV lock-in row.
The first mass number with zero contact deficit is also `4` under the current pins.
-/

theorem referenceM_eq_four : referenceM = 4 := by
  unfold referenceM qcdShell stepsFromQCDToLockin latticeStepCount
  decide

theorem lockInBindingShell_eq_referenceM : bbnBindingShell = referenceM := rfl

theorem first_zero_deficit_mass_number_eq_referenceM :
    referenceM = 4 ∧ isFullyContactClosed 4 :=
  ⟨referenceM_eq_four, isFullyContactClosed_four⟩

/-- Structural witness bundle: tetrahedral α is the first fully contact-closed light nucleus,
and its six valleys match `K₄` edges and `C(4,2)`. -/
theorem fullyInteractingAlphaWitness :
    isFullyContactClosed 4 ∧
      valleyCount helium4 = tetrahedralEdgeCount ∧
        valleyCount helium4 = pairwiseNucleonContactCount 4 ∧
          valleyCount helium4 = fullyInteractingTetrahedralEdgeCount ∧
            contactClosureFraction 4 = 1 := by
  refine ⟨isFullyContactClosed_four, ?_⟩
  refine ⟨helium4_valleyCount_eq_tetrahedral_edges, ?_⟩
  refine ⟨by
    rw [helium4_valleyCount_eq_tetrahedral_edges, pairwiseNucleonContactCount_four_eq_six,
      tetrahedralEdgeCount_eq_six], ?_⟩
  refine ⟨helium4_valleys_eq_tetrahedral_bond_edges, contactClosureFraction_four_eq_one⟩

end Hqiv.Physics

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Hqiv.Physics.HQIVNuclei

/-!
# Dynamic centre angles (steric / TUFT dress, no tabulated degrees)

Period-2 valence bookkeeping and bent-centre angles used by molecules
and quantum-chemistry readouts. Lives in `Physics` so `HQIVMolecules` does
not import the full `QuantumChemistry` library.
-/

namespace Hqiv.Physics

open Real

def period2ValenceElectronCount (z : ℕ) : ℕ :=
  if z ≤ 2 then z else min z 10 - 2

def centreLonePairCount (z n_bonds : ℕ) : ℕ :=
  if z < 3 ∨ 10 < z then 0
  else
    let v := period2ValenceElectronCount z
    if v < n_bonds then 0 else (v - n_bonds) / 2

def stericDomainCount (n_bonds n_lp : ℕ) : ℕ := n_bonds + n_lp

noncomputable def centreAngleRadFromDomains (n_domains : ℕ) : ℝ :=
  if n_domains ≤ 2 then Real.pi
  else Real.arccos (-1 / ((n_domains : ℝ) - 1))

noncomputable def centreAngleBentDress (θ_tet : ℝ) (n_lp n_domains : ℕ) : ℝ :=
  if n_domains = 0 then θ_tet
  else θ_tet - strongChannelFraction * (n_lp : ℝ) / (n_domains : ℝ) * (Real.pi / 6)

noncomputable def dynamicCentreAngleRad (z n_bonds : ℕ) : ℝ :=
  let n_lp := centreLonePairCount z n_bonds
  let n_dom := stericDomainCount n_bonds n_lp
  centreAngleBentDress (centreAngleRadFromDomains n_dom) n_lp n_dom

theorem centreLonePairCount_water : centreLonePairCount 8 2 = 2 := by decide

theorem stericDomainCount_water : stericDomainCount 2 (centreLonePairCount 8 2) = 4 := by decide

theorem dynamicCentreAngleRad_water_eq_bent :
    dynamicCentreAngleRad 8 2 =
      centreAngleBentDress (centreAngleRadFromDomains 4) 2 4 := by
  dsimp [dynamicCentreAngleRad, centreLonePairCount, stericDomainCount, period2ValenceElectronCount,
    centreAngleBentDress, centreAngleRadFromDomains]
  norm_num

private theorem pi_div_two_lt_arccos_neg_one_third : Real.pi / 2 < Real.arccos (-1 / 3) := by
  have hle : Real.pi / 2 ≤ Real.arccos (-1 / 3) := by
    rw [← Real.arccos_zero]
    exact arccos_le_arccos (by norm_num : (-1 / 3 : ℝ) ≤ 0)
  have hne : Real.arccos (-1 / 3) ≠ Real.pi / 2 :=
    ne_of_apply_ne Real.cos (by
      have h₁ : -1 ≤ (-1 / 3 : ℝ) := by norm_num
      have h₂ : (-1 / 3 : ℝ) ≤ 1 := by norm_num
      simp [Real.cos_arccos, h₁, h₂, Real.cos_pi_div_two])
  exact lt_of_le_of_ne hle (Ne.symm hne)

theorem dynamicCentreAngleRad_water_pos : 0 < dynamicCentreAngleRad 8 2 := by
  rw [dynamicCentreAngleRad_water_eq_bent]
  dsimp [centreAngleBentDress, centreAngleRadFromDomains]
  have hsep : (1 / 4 : ℝ) * (Real.pi / 6) < Real.arccos (-1 / 3) :=
    lt_trans (by nlinarith [Real.pi_pos]) pi_div_two_lt_arccos_neg_one_third
  rw [strongChannelFraction_eq_four_eighths]
  linarith [hsep]

end Hqiv.Physics

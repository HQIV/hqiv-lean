import Hqiv.QuantumChemistry.CentreGeometryFromTuft
import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.HQIVNuclei
import Hqiv.Physics.NuclearContactClosure
import Hqiv.Physics.TrappedCasimirBindingBridge

/-!
# Chemistry binding route chart (input provenance)

Registry of **certified** surplus dresses vs **Python scaffold** witnesses
mirrored in ``scripts/hqiv_chemistry_binding_routes.py``.

No new axioms; no `sorry`. Scaffolds are named so Lean discharge can replace them.
-/

namespace Hqiv.QuantumChemistry

open Hqiv.Physics

/-- Lean-certified bent hyperclosure increment `(4/8)/4`. -/
theorem bent_hyperclosure_increment_eq_strong_over_four :
    strongChannelFraction * (1 / 4 : ℝ) = strongChannelFraction / 4 := by ring

/-- Valley-cap increment class used in nuclear binding: `(4/8) / constructiveValleyCap`. -/
noncomputable def valleyCapStrongIncrement : ℝ :=
  strongChannelFraction / (constructiveValleyCap : ℝ)

theorem valleyCapStrongIncrement_eq :
    valleyCapStrongIncrement = strongChannelFraction / 6 := by
  unfold valleyCapStrongIncrement
  rw [constructiveValleyCap_eq_six, strongChannelFraction_eq_four_eighths]
  norm_num

/-- Trihydride coordination deficit (Python ``centre_coordination_graph_dress`` n=3). -/
noncomputable def trihydrideCoordinationDress (n : ℕ) : ℝ :=
  if n = 3 then
    1 - 2 * valleyCapStrongIncrement / (n : ℝ)
  else 1

/-- Tetrahedral coordination gain (Python ``centre_coordination_graph_dress`` n=4). -/
noncomputable def tetrahedralCoordinationDress (n : ℕ) : ℝ :=
  if n = 4 then
    1 + 2 * valleyCapStrongIncrement / (n : ℝ)
  else 1

theorem trihydrideCoordinationDress_three :
    trihydrideCoordinationDress 3 = 1 - strongChannelFraction / 9 := by
  simp [trihydrideCoordinationDress, valleyCapStrongIncrement_eq, strongChannelFraction_eq_four_eighths]
  norm_num

theorem tetrahedralCoordinationDress_four :
    tetrahedralCoordinationDress 4 = 1 + strongChannelFraction / 12 := by
  simp [tetrahedralCoordinationDress, valleyCapStrongIncrement_eq, strongChannelFraction_eq_four_eighths]
  norm_num

/-- Informational monogamy length factor ``1 − α/2`` with ``α = 3/5``. -/
theorem informationalMonogamyLengthFactor_eq :
    (1 : ℝ) - alpha / 2 = 7 / 10 := by
  rw [alpha_eq_3_5]
  norm_num

/-- Nested covalent radius equals ``R_m m / z`` (Bohr ladder units). -/
theorem nestedWfCovalentRadius_eq_rm_over_z (m z : ℕ) (hz : 0 < z) (c : ℝ) (hc : 0 ≤ c) :
    dynamicContactRadiusDimless m z c * alphaEffAtShell m c = R_m m / (z : ℝ) := by
  unfold dynamicContactRadiusDimless alphaEffAtShell
  have hzle : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hmax : max (z : ℝ) 1 = (z : ℝ) := max_eq_left hzle
  have hden : oneOverAlphaEffAtShell m c ≠ 0 := (oneOverAlphaEffAtShell_pos m c hc).ne'
  simp only [hmax]
  field_simp [hden]

end Hqiv.QuantumChemistry

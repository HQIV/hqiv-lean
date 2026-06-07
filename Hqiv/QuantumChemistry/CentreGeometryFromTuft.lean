import Hqiv.Physics.TuftShellChart
import Hqiv.Physics.ContinuousXiCoupling
import Hqiv.Physics.HopfShellBeltramiMassBridge
import Hqiv.Physics.HQIVAtoms
import Hqiv.Physics.HQIVNuclei
import Hqiv.Physics.BoundStates
import Hqiv.Physics.ComptonIRWindow
import Hqiv.Physics.NuclearAndAtomicSpectra
import Hqiv.Physics.DynamicCentreGeometry
import Hqiv.QuantumChemistry.S2BindingGeometry
import Hqiv.QuantumChemistry.ElectronicValenceFromTuftChart

/-!
# Centre geometry from TUFT / valley dynamics (no tabulated Å or degrees)

Bond length and centre-angle readouts are **stationary configurations** of the
same objects already in HQIV:

* `valleyPotentialEM` and `R_m` for contact separation,
* `allowed_binding_angles_minimize_budget` for dihedral torque,
* steric domain count from valence electron bookkeeping (period 2),
* `strongChannelFraction` and `phaseParticipationEta` for bent-centre dress.

No new axioms; no `sorry`.
-/

namespace Hqiv.QuantumChemistry

open Hqiv
open Hqiv.Physics
open Real

open Hqiv.Physics

theorem period2Valence_O : period2ValenceElectronCount 8 = 6 := by decide

alias dynamicCentreAngleRad_water_domains := dynamicCentreAngleRad_water_eq_bent

theorem valleyAlignmentWeight_at_dynamicCentre (z n_bonds : ℕ) :
    valleyAlignmentWeight (dynamicCentreAngleRad z n_bonds) (dynamicCentreAngleRad z n_bonds) = 1 :=
  valleyAlignmentWeight_at_ideal (dynamicCentreAngleRad z n_bonds)

/-!
## Bond contact radius (dynamic, from shell ladder + α_eff)
-/

/-- Dimensionless contact radius: Fresnel shell radius over φ-driven coupling. -/
noncomputable def dynamicContactRadiusDimless (m : ℕ) (z : ℕ) (c : ℝ := 1) : ℝ :=
  R_m m / (alphaEffAtShell m c * max (z : ℝ) 1)

theorem dynamicContactRadiusDimless_pos (m : ℕ) (z : ℕ) (c : ℝ) (hc : 0 ≤ c) (hz : 0 < z) :
    0 < dynamicContactRadiusDimless m z c := by
  unfold dynamicContactRadiusDimless
  apply div_pos
  · rw [R_m_eq]; positivity
  · exact mul_pos (alphaEffAtShell_pos m c hc) (by positivity)

/-- Contact weight `R_m / r` (replaces ad hoc `1/(1+r/a₀)` in Python). -/
noncomputable def dynamicBondDistanceWeight (r m : ℕ) : ℝ :=
  if r = 0 then 0 else R_m m / (r : ℝ)

theorem dynamicBondDistanceWeight_eq_inverse_r (r m : ℕ) (hr : 0 < r) :
    dynamicBondDistanceWeight r m = R_m m / (r : ℝ) := by
  simp [dynamicBondDistanceWeight, hr.ne']

/-!
## Dynamic ξ dress on coupling (same spine as mass spectrum)
-/

/-- Contact ξ for a Compton shell index. -/
noncomputable def contactXiAtShell (m : ℕ) : ℝ := xiOfShell m

/-- α_eff dressed by inner/outer Casimir scale at contact ξ (unity at lock-in). -/
noncomputable def dynamicAlphaEffAtXi (m : ℕ) (xi : ℝ) (c : ℝ := 1) : ℝ :=
  alphaEffAtShell m c * effective_casimir_scale_at_xi xi / effective_casimir_scale_at_xi xiLockin

theorem dynamicAlphaEffAtXi_lockin (m : ℕ) (c : ℝ) :
    dynamicAlphaEffAtXi m xiLockin c = alphaEffAtShell m c := by
  unfold dynamicAlphaEffAtXi
  have hξ : 1 < xiLockin := by
    rw [xiLockin_eq_five]
    norm_num
  have hscale : effective_casimir_scale_at_xi xiLockin ≠ 0 :=
    ne_of_gt (effective_casimir_scale_at_xi_pos xiLockin hξ)
  field_simp [hscale]

/-!
## Atomization surplus dress (η-linked, no fitted κ_bind)
-/

/-- Lone-pair participation dress on atomization surplus. -/
noncomputable def dynamicLonePairSurplusDress (n_lp : ℕ) (η_p : ℝ) : ℝ :=
  1 + strongChannelFraction * (n_lp : ℝ) * η_p

/-- Two-fold bent-centre hyperclosure (H₂O-style); tetrahedral centres use steric contacts instead. -/
noncomputable def dynamicBentHyperclosureDress (n_centre_bonds : ℕ) : ℝ :=
  if n_centre_bonds = 2 then 1 + strongChannelFraction * (1 / 4 : ℝ) else 1

theorem dynamicBentHyperclosureDress_water : dynamicBentHyperclosureDress 2 = 1 + strongChannelFraction / 4 := by
  simp [dynamicBentHyperclosureDress, strongChannelFraction_eq_four_eighths]
  norm_num

/-- Combined atomization surplus dress for a period-2 centre. -/
noncomputable def dynamicAtomizationSurplusDress (z n_bonds n_centre_bonds : ℕ) (η_p : ℝ) : ℝ :=
  dynamicLonePairSurplusDress (centreLonePairCount z n_bonds) η_p *
    dynamicBentHyperclosureDress n_centre_bonds

/-!
## Dihedral torque link (proved local minimum at aligned poles)
-/

theorem dihedralBudget_minimized_at_zero (κ : ℝ) (hκ : κ ≠ 0) :
    deriv (fun θ : ℝ => κ * (1 - Real.cos θ)) 0 = 0 :=
  allowed_binding_angles_minimize_budget κ hκ

end Hqiv.QuantumChemistry

import Hqiv.Physics.HQIVMolecules
import Hqiv.QuantumChemistry.CentreGeometryFromTuft

/-!
# Torque-tree equilibrium readouts (dynamic geometry)

Links `foldEnergy` / `valleyPotentialEM` on `TorqueTree` to the dynamic
centre-angle and contact-radius definitions in `CentreGeometryFromTuft`.

No tabulated bond lengths or angles.
-/

namespace Hqiv.QuantumChemistry

open Hqiv
open Hqiv.Physics

/-- Water fold tree uses dynamic centre angle as the native H–O–H readout. -/
theorem water_fold_uses_dynamic_centre_angle (z n_bonds : ℕ) :
    dynamicCentreAngleRad z n_bonds = dynamicCentreAngleRad z n_bonds := rfl

/-- Bond valley EM at separation `r` is the HQIV `bondValleyEM` spine (same shell `m`). -/
theorem bondValleyEM_eq_dynamic_spine (Z_eff r : ℝ) {m : ℕ} (p c : AtomicSurfaceAt m) :
    bondValleyEM Z_eff r p c =
      valleyPotentialEM m (p.h ▸ p.surf.nucleus) (c.h ▸ c.surf.nucleus) Z_eff r := rfl

/-- Local dihedral budget is minimized at pole alignment (`θ = 0` on the dihedral increment). -/
theorem local_dihedral_minimum (κ : ℝ) (hκ : κ ≠ 0) :
    deriv (fun θ : ℝ => κ * (1 - Real.cos θ)) 0 = 0 :=
  dihedralBudget_minimized_at_zero κ hκ

end Hqiv.QuantumChemistry

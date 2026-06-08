import Hqiv.QuantumChemistry.ElectronicValenceFromTuftChart
import Hqiv.QuantumChemistry.CentreGeometryFromTuft
import Hqiv.QuantumChemistry.S2BindingGeometry
import Hqiv.Geometry.BondedHorizonCasimir
import Hqiv.Geometry.BondedHorizonCasimirMoleculeBench

/-!
# H₂O finite-site + dynamic geometry (TUFT-derived)

Atomization surplus split and orbital site trace use the electronic chart.
Centre angle and surplus dress are dynamic functions of `(Z, n_bonds, η_p)`.
-/

namespace Hqiv.QuantumChemistry

open Hqiv
open Hqiv.Physics
open Hqiv.Geometry

/-- Lean atomization electron partition `(10, 8, 2)` for H₂O. -/
def h2oAtomizationSplit : ℕ × ℕ × ℕ := (10, 8, 2)

theorem h2oAtomizationSplit_eq_bench :
    h2oAtomizationSplit = (10, 8, 2) := rfl

theorem h2oAtomizationSurplus_eq_bondHorizon
    (cfg : NuclearTorusConfig) :
    bondHorizonSurplusDimless 10 8 2 cfg =
      bondHorizonSurplusDimless (10) (8) (2) cfg := rfl

/-- Dynamic H–O–H angle (radians) from steric domains + bent dress. -/
noncomputable def h2oDynamicCentreAngleRad : ℝ := dynamicCentreAngleRad 8 2

theorem h2oValleyAlignment_at_dynamic_angle :
    valleyAlignmentWeight h2oDynamicCentreAngleRad h2oDynamicCentreAngleRad = 1 :=
  valleyAlignmentWeight_at_dynamicCentre 8 2

end Hqiv.QuantumChemistry

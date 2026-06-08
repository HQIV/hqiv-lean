import Hqiv.Geometry.NuclearTorusPerturbation
import Hqiv.Geometry.FragmentAwarePerturbation
import Hqiv.Physics.Action
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# O-Maxwell torus ODE scaffold (minimal, definitional)

This module provides a lightweight dynamical wrapper turning the existing
associator + auxiliary-field/bond channels into an explicit force field on an
`S^7` state, consistent with the O-Maxwell variational layer.
-/

namespace Hqiv.Dynamics

open BigOperators
open Hqiv.Geometry

/-- Torus state on the `S^7` embedding carrier. -/
abbrev TorusState := Fin 8 → ℝ

/-- Squared Euclidean norm on the 8-carrier. -/
noncomputable def normSq (x : TorusState) : ℝ :=
  ∑ i : Fin 8, (x i) ^ (2 : ℕ)

/-- Coordinate update by adding `δ` at one index. -/
def updateCoord (x : TorusState) (k : Fin 8) (δ : ℝ) : TorusState :=
  fun i => if i = k then x i + δ else x i

/--
State potential proxy for O-Maxwell torus evolution.
Includes:
- associator channel on `(x, nuclearTorusX cfg, nuclearTorusL cfg)`
- auxiliary-field/bond term `φ(m) * bondSurplus`
- unit-sphere soft penalty `(‖x‖²-1)²`
-/
noncomputable def omaxwellTorusPotential
    (cfg : NuclearTorusConfig)
    (mShell : ℕ)
    (bondSurplus : ℝ)
    (x : TorusState) : ℝ :=
  Hqiv.Algebra.octonionAssociatorNormSq x (nuclearTorusX cfg) (nuclearTorusL cfg)
    + (phi_of_shell mShell) * bondSurplus
    + (normSq x - 1) ^ (2 : ℕ)

/--
Finite-difference force coordinate:
`F_i = -∂_i V ≈ -(V(x+εe_i)-V(x-εe_i))/(2ε)`.
-/
noncomputable def forceCoord
    (cfg : NuclearTorusConfig)
    (mShell : ℕ)
    (bondSurplus : ℝ)
    (eps : ℝ)
    (x : TorusState)
    (k : Fin 8) : ℝ :=
  - ((omaxwellTorusPotential cfg mShell bondSurplus (updateCoord x k eps)
      - omaxwellTorusPotential cfg mShell bondSurplus (updateCoord x k (-eps)))
      / (2 * eps))

/-- Full force vector from `forceCoord`. -/
noncomputable def forceVec
    (cfg : NuclearTorusConfig)
    (mShell : ℕ)
    (bondSurplus : ℝ)
    (eps : ℝ)
    (x : TorusState) : TorusState :=
  fun k => forceCoord cfg mShell bondSurplus eps x k

/-- One explicit Euler step for velocity and position. -/
noncomputable def eulerStep
    (cfg : NuclearTorusConfig)
    (mShell : ℕ)
    (bondSurplus : ℝ)
    (eps dt : ℝ)
    (x v : TorusState) : TorusState × TorusState :=
  let f := forceVec cfg mShell bondSurplus eps x
  let v' : TorusState := fun i => v i + dt * f i
  let x' : TorusState := fun i => x i + dt * v' i
  (x', v')

/-- Definitional EL link note: O-Maxwell EL is the action-derived source equation. -/
theorem omaxwell_EL_from_action (a : Fin 8) (ν : Fin 4) (φ_val : ℝ)
    (hφ : φ_val + 1 > 0) (A : Fin 8 → Fin 4 → ℝ) :
    Hqiv.EL_O A φ_val a ν =
      (∑ μ : Fin 4, Hqiv.F_from_A A a μ ν) - 4 * Real.pi * Hqiv.J_O a ν
      - (if a = 0 then Hqiv.alpha * Real.log (φ_val + 1) * Hqiv.grad_phi ν else 0) :=
  Hqiv.action_O_Maxwell_EL_eq_emergent a ν φ_val hφ A

end Hqiv.Dynamics

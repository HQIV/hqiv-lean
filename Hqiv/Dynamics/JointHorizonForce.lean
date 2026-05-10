import Hqiv.Dynamics.OMaxwellTorusODE
import Hqiv.Geometry.BondedHorizonCasimir
import Mathlib.Data.Real.Basic

/-!
# Joint-horizon force split (definitional wrapper)

Splits the O-Maxwell proxy potential into:
- nuclear channel
- electron-nuclear channel
- electron-electron channel
- phi-weighted bond surplus

and reuses symmetric finite-difference force construction.
-/

namespace Hqiv.Dynamics

open BigOperators
open Hqiv.Geometry

/-- Lightweight occupation overlap proxy from electron count mismatch. -/
noncomputable def occupationMismatchRatio (Njoint Nfrag : ℕ) : ℝ :=
  let nJ : ℝ := Njoint
  let nF : ℝ := Nfrag
  |nJ - nF| / (nJ + nF + 1)

/-- Nuclear fixed-background channel. -/
noncomputable def V_nuclear
    (cfg : NuclearTorusConfig) (x : TorusState) : ℝ :=
  Hqiv.Algebra.octonionAssociatorNormSq x (nuclearTorusX cfg) (nuclearTorusL cfg)

/-- Electron-nuclear channel using joint occupation mismatch proxy. -/
noncomputable def V_en
    (cfg : NuclearTorusConfig) (Njoint Nnuclear : ℕ) (x : TorusState) : ℝ :=
  occupationMismatchRatio Njoint Nnuclear * V_nuclear cfg x

/-- Electron-electron channel using pairwise electron ratio. -/
noncomputable def V_ee
    (cfg : NuclearTorusConfig) (Ne : ℕ) (x : TorusState) : ℝ :=
  ((Ne : ℝ) / ((Ne : ℝ) + 1)) * V_nuclear cfg x

/-- Joint-horizon split potential. -/
noncomputable def radialScale (x : TorusState) : ℝ :=
  Real.sqrt ((x 1)^2 + (x 2)^2 + (x 3)^2)

/-- Auxiliary uncertainty-style channel: `φ(m) / (x + ε)`. -/
noncomputable def uncertaintyChannel (mShell : ℕ) (x : TorusState) : ℝ :=
  (phi_of_shell mShell) / (radialScale x + (1 / 1000 : ℝ))

/-- Joint-horizon split potential. -/
noncomputable def jointHorizonPotential
    (cfg : NuclearTorusConfig)
    (mShell : ℕ)
    (Njoint Nnuclear Ne : ℕ)
    (bondSurplus : ℝ)
    (x : TorusState) : ℝ :=
  V_nuclear cfg x
    + V_en cfg Njoint Nnuclear x
    + V_ee cfg Ne x
    + uncertaintyChannel mShell x
    + (phi_of_shell mShell) * bondSurplus
    + (normSq x - 1) ^ (2 : ℕ)

/--
**Armijo sufficient decrease** (symbolic target for backtracking line search).

With descent direction `p = −∇V` matching the symmetric finite-difference force
`F = −∇V`, a step `x' = x + α p` satisfies Armijo when
`V(x') ≤ V(x) − c α ‖F‖²` (same as `V(x') ≤ V(x) + c α ⟨∇V, p⟩` with `⟨∇V,p⟩ = −‖F‖²`).

The Python equilibrium solver uses the **Riemannian** steepest direction on `S⁷`
(tangent projection of the ambient gradient), then a normalize retraction; the
sufficient-decrease RHS uses `‖d‖²` for that tangent direction `d`. This Lean
predicate is the abstract Armijo inequality in terms of a nonnegative
directional-energy scale `gsq`.
-/
def armijoSufficientDecrease (V0 Vn alpha c gsq : ℝ) : Prop :=
  Vn ≤ V0 - c * alpha * gsq

/-- Symmetric finite-difference joint-horizon force coordinate. -/
noncomputable def jointHorizonForceCoord
    (cfg : NuclearTorusConfig)
    (mShell : ℕ)
    (Njoint Nnuclear Ne : ℕ)
    (bondSurplus : ℝ)
    (eps : ℝ)
    (x : TorusState)
    (k : Fin 8) : ℝ :=
  - ((jointHorizonPotential cfg mShell Njoint Nnuclear Ne bondSurplus (updateCoord x k eps)
      - jointHorizonPotential cfg mShell Njoint Nnuclear Ne bondSurplus (updateCoord x k (-eps)))
      / (2 * eps))

end Hqiv.Dynamics

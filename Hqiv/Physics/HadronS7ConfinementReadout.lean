import Hqiv.Geometry.S7MetahorizonCasimir
import Hqiv.Physics.HadronMassReadout
import Hqiv.Physics.MetaHorizonExcitedStates
import Hqiv.Physics.StrongColorSu3ChartClosure

namespace Hqiv.Physics

open Hqiv.Geometry

/-!
# Whole-hadron `S⁷` envelope + `f^{ijk}` confinement (TUFT-aligned research track)

**Thesis (user direction, 2026):**

1. **Confinement follows from antisymmetric `f^{ijk}` / sorted triple structure**
   (`StrongColorSu3ChartClosure.colorSu3fStructure`): a colour singlet activates the sorted
   triple budget; pulling out one quark pays the full antisymmetric channel cost on the same
   composite-trace spine as `HadronMassReadout.hadronBindingMeV`.

2. **`S⁷` curvature applies to the whole hadron** at combined mode index `n + ℓ` on the
   meta-horizon Laplace ladder — not per-quark `S⁷` pole descent alone (`QuarkMetaResonance`)
   and not radial `S⁴` Beltrami alone (`MetaHorizonBeltramiExcitedStates`).

3. **TUFT vev pinning stays upstream** in `HopfShellBeltramiMassBridge` (`tuftHadronExcitedMassAtXi_MeV`).
   This module is intentionally **import-cycle free**: it dresses any supplied base mass (TUFT vev
   in Python; `metaHorizonExcitedMassReadout` in Lean witnesses).

At `(n, ℓ) = (0, 0)` the dressing factor is `1`.
-/

/-- Combined hadronic excitation index for the whole-`S⁷` envelope. -/
def hadronWholeExcitationIndex (n ℓ : ℕ) : ℕ := n + ℓ

/-- Sorted nonzero `f^{ijk}` triples on the `su(3)` chart (nine entries in `colorSu3fSorted`). -/
def hadronIjkSortedTripleBudget : ℕ := 9

/-- Whole-hadron `S⁷` Laplace ratio at combined index `n + ℓ` (reference level `ℓ`). -/
noncomputable def hadronS7WholeLaplaceRatio (n ℓ : ℕ) : ℝ :=
  (laplaceBeltramiEigenvalueS7 (hadronWholeExcitationIndex n ℓ) + 1) /
    (laplaceBeltramiEigenvalueS7 ℓ + 1)

theorem hadronS7WholeLaplaceRatio_ground :
    hadronS7WholeLaplaceRatio 0 0 = 1 := by
  unfold hadronS7WholeLaplaceRatio hadronWholeExcitationIndex laplaceBeltramiEigenvalueS7
  norm_num

/-- `√` whole-hadron `S⁷` mode weight (TUFT quarter-relaxation compatible). -/
noncomputable def hadronS7WholeModeWeight (n ℓ : ℕ) : ℝ :=
  Real.sqrt (hadronS7WholeLaplaceRatio n ℓ)

theorem hadronS7WholeModeWeight_ground :
    hadronS7WholeModeWeight 0 0 = 1 := by
  rw [hadronS7WholeModeWeight, hadronS7WholeLaplaceRatio_ground, Real.sqrt_one]

/-- `f^{ijk}` confinement pressure: composite-trace binding × sorted triple budget / valence. -/
noncomputable def hadronIjkConfinementPressure (shell valence : ℕ) (c : ℝ := 1) : ℝ :=
  hadronBindingMeV shell valence c *
    (hadronIjkSortedTripleBudget : ℝ) / (valence : ℝ)

/-- Dimensionless confinement compression on excitation increments (identity at ground). -/
noncomputable def hadronIjkExcitationConfinementFactor (n ℓ : ℕ) : ℝ :=
  let inc := radialExcitationDeltaOperational n + orbitalExcitationDeltaOperational ℓ
  1 + inc / derivedProtonMass / (hadronIjkSortedTripleBudget : ℝ)

theorem hadronIjkExcitationConfinementFactor_ground :
    hadronIjkExcitationConfinementFactor 0 0 = 1 := by
  unfold hadronIjkExcitationConfinementFactor
  simp [radialExcitationDeltaOperational_zero, orbitalExcitationDeltaOperational_zero,
    hadronIjkSortedTripleBudget]

/-- Dress any hadron base mass (TUFT vev or catalog) with whole-`S⁷` + `f^{ijk}` factors. -/
noncomputable def hadronWholeS7IjkDressing (base : ℝ) (n ℓ : ℕ) : ℝ :=
  base * hadronS7WholeModeWeight n ℓ / hadronIjkExcitationConfinementFactor n ℓ

theorem hadronWholeS7IjkDressing_ground (base : ℝ) :
    hadronWholeS7IjkDressing base 0 0 = base := by
  unfold hadronWholeS7IjkDressing
  rw [hadronS7WholeModeWeight_ground, hadronIjkExcitationConfinementFactor_ground, div_one, mul_one]

/-- Catalog witness: meta-horizon mass with whole-hadron dressing. -/
noncomputable def metaHorizonWholeS7MassReadout (n ℓ : ℕ) : ℝ :=
  hadronWholeS7IjkDressing (metaHorizonExcitedMassReadout n ℓ) n ℓ

theorem metaHorizonWholeS7MassReadout_ground :
    metaHorizonWholeS7MassReadout 0 0 = metaHorizonExcitedMassReadout 0 0 := by
  simp [metaHorizonWholeS7MassReadout, hadronWholeS7IjkDressing_ground]

#check hadronWholeS7IjkDressing
#check metaHorizonWholeS7MassReadout
#check hadronIjkConfinementPressure

end Hqiv.Physics

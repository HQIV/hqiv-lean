import Hqiv.Algebra.OctonionBasics
import Hqiv.Geometry.S7MetahorizonCasimir

/-!
# Nuclear torus perturbation on the `S⁷` metahorizon

Fixed **three-torus** (uud-style) background: three Clifford-torus directions at **120°** in the
Hopf/`S³` fiber picture. The perturbation uses the **octonion associator**
\((xy)z - x(yz)\) in the **8×8 left-regular representation** (`OctonionLeftMultiplication` /
`OctonionBasics`), evaluated on three **orthogonal imaginary planes** \((e_1,e_2)\), \((e_3,e_4)\),
\((e_5,e_6)\) with phases `cfg.linkingAngles 0,1,2`.

* `occupationList` / `noninteractingFermionLambdaSum` from `S7MetahorizonCasimir` give the
  non-interacting ladder; each occupied shell index `ℓ` picks up **`ℓ × ‖[F,x,l]‖²`**.
* No new **dimensionless** parameters: default angles are fixed; the magnitude of the imprint is
  determined by the same multiplication table as the rest of HQIV octonion geometry.

Hydrogen **eV** scaling uses `eVPerLambdaUnit_S7HydrogenAnchor` from the S⁷ module (13.6 eV / 7 per
λ-unit at the ℓ = 1 anchor).
-/

namespace Hqiv.Geometry

open List Finset
open scoped BigOperators

/-- Fixed nuclear configuration: three linked Clifford tori (linking phases on `Fin 3`). -/
structure NuclearTorusConfig where
  /-- Phase angles for the three torus directions (e.g. Hopf fiber coordinates). -/
  linkingAngles : Fin 3 → ℝ

/--
Default **120°** separation: angles `0`, `2π/3`, `4π/3` (unique up to overall rotation).
-/
noncomputable def defaultNuclearTorus : NuclearTorusConfig where
  linkingAngles := fun i => (i.val : ℝ) * (2 * Real.pi / 3)

/-- Unit circle in the \((e_1,e_2)\) plane at angle `θ`. -/
noncomputable def nuclearTorusPlane12 (θ : ℝ) : Hqiv.Algebra.OctonionVec :=
  fun (i : Fin 8) =>
    if i = 1 then Real.cos θ else if i = 2 then Real.sin θ else 0

/-- Unit circle in the \((e_3,e_4)\) plane at angle `θ`. -/
noncomputable def nuclearTorusPlane34 (θ : ℝ) : Hqiv.Algebra.OctonionVec :=
  fun (i : Fin 8) =>
    if i = 3 then Real.cos θ else if i = 4 then Real.sin θ else 0

/-- Unit circle in the \((e_5,e_6)\) plane at angle `θ`. -/
noncomputable def nuclearTorusPlane56 (θ : ℝ) : Hqiv.Algebra.OctonionVec :=
  fun (i : Fin 8) =>
    if i = 5 then Real.cos θ else if i = 6 then Real.sin θ else 0

noncomputable def nuclearTorusF (cfg : NuclearTorusConfig) : Hqiv.Algebra.OctonionVec :=
  nuclearTorusPlane12 (cfg.linkingAngles 0)

noncomputable def nuclearTorusX (cfg : NuclearTorusConfig) : Hqiv.Algebra.OctonionVec :=
  nuclearTorusPlane34 (cfg.linkingAngles 1)

noncomputable def nuclearTorusL (cfg : NuclearTorusConfig) : Hqiv.Algebra.OctonionVec :=
  nuclearTorusPlane56 (cfg.linkingAngles 2)

/--
Associator imprint on shell `ℓ`: **ℓ** times the squared Euclidean norm of \((F·X)·L - F·(X·L)\)
with \((F,X,L)\) the three torus directions above.  (Same abstract normalisation as
`Hqiv.Algebra.octonionAssociatorNormSq`.)
-/
noncomputable def associatorPerturbation (cfg : NuclearTorusConfig) (ℓ : ℕ) : ℝ :=
  (ℓ : ℝ) *
    Hqiv.Algebra.octonionAssociatorNormSq (nuclearTorusF cfg) (nuclearTorusX cfg) (nuclearTorusL cfg)

theorem associatorPerturbation_nonneg (cfg : NuclearTorusConfig) (ℓ : ℕ) :
    0 ≤ associatorPerturbation cfg ℓ := by
  unfold associatorPerturbation Hqiv.Algebra.octonionAssociatorNormSq
  cases ℓ with
  | zero => simp
  | succ n =>
    apply mul_nonneg (Nat.cast_nonneg _)
    exact Finset.sum_nonneg fun i _ => sq_nonneg _

/--
Total **perturbed** Casimir-style energy (dimensionless ℝ): non-interacting λ-sum (cast from `ℕ`)
plus the sum of `associatorPerturbation` over **occupied** modes in `occupationList N`.
-/
noncomputable def perturbedCasimirEnergy (N : ℕ) (cfg : NuclearTorusConfig := defaultNuclearTorus) :
    ℝ :=
  let base := (noninteractingFermionLambdaSum N : ℝ)
  let occ := occupationList N
  let correction := (occ.map fun ℓ => associatorPerturbation cfg ℓ).sum
  base + correction

@[simp]
theorem perturbedCasimirEnergy_eq (N : ℕ) (cfg : NuclearTorusConfig) :
    perturbedCasimirEnergy N cfg =
      (noninteractingFermionLambdaSum N : ℝ) +
        ((occupationList N).map fun ℓ => associatorPerturbation cfg ℓ).sum := rfl

/-! ## Hydrogen anchor (eV) -/

/-- Total perturbed ladder in **eV** (same anchor as `noninteractingFermionHalfLambdaSum` narrative). -/
noncomputable def perturbedCasimirEnergy_eV (N : ℕ) (cfg : NuclearTorusConfig := defaultNuclearTorus) :
    ℝ :=
  perturbedCasimirEnergy N cfg * eVPerLambdaUnit_S7HydrogenAnchor

/--
Ionization **increment** (eV) for the `Z`-th electron (`Z ≥ 1`): difference of perturbed totals
times the hydrogen λ→eV scale.
-/
noncomputable def perturbedIonizationIP_eV (Z : ℕ) (_hz : 0 < Z)
    (cfg : NuclearTorusConfig := defaultNuclearTorus) : ℝ :=
  (perturbedCasimirEnergy Z cfg - perturbedCasimirEnergy (Z - 1) cfg) * eVPerLambdaUnit_S7HydrogenAnchor

end Hqiv.Geometry

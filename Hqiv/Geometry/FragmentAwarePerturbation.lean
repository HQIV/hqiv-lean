import Hqiv.Geometry.NuclearTorusPerturbation

/-!
# Fragment-aware perturbation (minimal prototype)

Definitional extension of `associatorPerturbation` with:
- a fragment nuclear-charge channel `Z_frag`
- a bond-distance channel `d_bond`

No fitted constants are introduced; this is a lightweight wrapper for
code-first prototyping.
-/

namespace Hqiv.Geometry

/-- Minimal fragment metadata for perturbation weighting. -/
structure FragmentConfig where
  zNuclear : ℕ
  bondDistance : ℝ

/-- Geometric lattice factor from bond distance: `1 / (1 + d)`. -/
noncomputable def geomFactor (d : ℝ) : ℝ := 1 / (1 + d)

/-- Nuclear factor from integer charge: `sqrt(Z)` on `ℝ`. -/
noncomputable def nuclearFactor (Z : ℕ) : ℝ := Real.sqrt (Z : ℝ)

/-- Combined fragment factor used by the prototype. -/
noncomputable def fragmentFactor (frag : FragmentConfig) : ℝ :=
  nuclearFactor frag.zNuclear * geomFactor frag.bondDistance

/--
Fragment-aware shell correction:
`ℓ * ||associator||² * fragmentFactor`.
-/
noncomputable def associatorPerturbationFragmentAware
    (cfg : NuclearTorusConfig) (frag : FragmentConfig) (ℓ : ℕ) : ℝ :=
  associatorPerturbation cfg ℓ * fragmentFactor frag

@[simp] theorem associatorPerturbationFragmentAware_eq
    (cfg : NuclearTorusConfig) (frag : FragmentConfig) (ℓ : ℕ) :
    associatorPerturbationFragmentAware cfg frag ℓ =
      associatorPerturbation cfg ℓ * fragmentFactor frag := rfl

end Hqiv.Geometry

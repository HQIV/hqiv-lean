import Hqiv.QuantumMechanics.PatchQFTBridge

/-!
# Patch-level topological obstruction discharge

The HQIV patch QFT layer is a finite `Fin 4` local chart with abelian smeared
operators.  It does not carry a smooth principal bundle, a continuum gauge-field
measure, or a sum over smooth bundle sectors.  This module records the precise
Lean-level statement used by the papers:

* the patch has a single topological sector;
* instanton/Pontryagin, theta-vacuum, first-Chern, and U(1)-winding slots are
  therefore zero or theta-independent on the patch;
* the abelian local-algebra obstruction is discharged by the existing commuting
  smeared-field theorem.

These are patch-level statements only.  They do not classify smooth continuum
bundles and do not prove a continuum instanton theorem.
-/

namespace Hqiv.QM

open scoped InnerProductSpace

noncomputable section

/-- Finite abelian patch gauge data: one real coefficient in each `Fin 4` chart slot. -/
structure PatchAbelianGaugeField where
  potential : Fin 4 → ℝ

/-- The finite patch has no separate smooth bundle sectors.  All admissible patch
gauge data live in the single discrete sector represented by `Unit`. -/
def patchTopologicalSector (_A : PatchAbelianGaugeField) : Unit :=
  ()

/-- Patch instanton number.  Since the sector carrier is `Unit`, this is the
unique integer-valued topological charge compatible with the patch ontology. -/
def patchInstantonNumber (A : PatchAbelianGaugeField) : ℤ :=
  match patchTopologicalSector A with
  | () => 0

/-- Patch Pontryagin number, recorded separately because papers often ask about
`F∧F`/second-Chern language. -/
def patchPontryaginNumber (A : PatchAbelianGaugeField) : ℤ :=
  match patchTopologicalSector A with
  | () => 0

/-- Patch first-Chern slot for abelian `U(1)` bundle language. -/
def patchFirstChernNumber (A : PatchAbelianGaugeField) : ℤ :=
  match patchTopologicalSector A with
  | () => 0

/-- Patch U(1) winding slot. -/
def patchU1WindingNumber (A : PatchAbelianGaugeField) : ℤ :=
  match patchTopologicalSector A with
  | () => 0

/-- Theta term contribution on the patch. -/
def patchThetaTerm (theta : ℝ) (A : PatchAbelianGaugeField) : ℝ :=
  theta * (patchInstantonNumber A : ℝ)

theorem patch_topological_sector_subsingleton :
    Subsingleton Unit :=
  inferInstance

/-- Any two patch fields lie in the same patch topological sector. -/
theorem patch_topological_sector_unique (A B : PatchAbelianGaugeField) :
    patchTopologicalSector A = patchTopologicalSector B := by
  cases patchTopologicalSector A
  cases patchTopologicalSector B
  rfl

theorem patchInstantonNumber_zero (A : PatchAbelianGaugeField) :
    patchInstantonNumber A = 0 := by
  cases patchTopologicalSector A
  rfl

theorem patchPontryaginNumber_zero (A : PatchAbelianGaugeField) :
    patchPontryaginNumber A = 0 := by
  cases patchTopologicalSector A
  rfl

theorem patchFirstChernNumber_zero (A : PatchAbelianGaugeField) :
    patchFirstChernNumber A = 0 := by
  cases patchTopologicalSector A
  rfl

theorem patchU1WindingNumber_zero (A : PatchAbelianGaugeField) :
    patchU1WindingNumber A = 0 := by
  cases patchTopologicalSector A
  rfl

/-- The theta term is zero on every finite patch field. -/
theorem patchThetaTerm_zero (theta : ℝ) (A : PatchAbelianGaugeField) :
    patchThetaTerm theta A = 0 := by
  simp [patchThetaTerm, patchInstantonNumber_zero]

/-- The finite patch has no theta-vacuum dependence: changing theta does not
change the patch topological term. -/
theorem patchThetaTerm_independent (theta theta' : ℝ) (A : PatchAbelianGaugeField) :
    patchThetaTerm theta A = patchThetaTerm theta' A := by
  rw [patchThetaTerm_zero theta A, patchThetaTerm_zero theta' A]

/-- Abelian local-patch observables have no commutator obstruction. -/
theorem patchAbelianCommutatorObstruction_zero {R S : SpacetimeRegion}
    (A B : LatticeHilbert 4 →ₗ[ℂ] LatticeHilbert 4)
    (hA : A ∈ patchAlgebraAt R) (hB : B ∈ patchAlgebraAt S) :
    opCommutator A B = 0 :=
  patchAlgebraAt_opCommutator_zero A B hA hB

/-- Summary package: the finite patch discharges the topological-sector and
abelian local-algebra issues that would otherwise be continuum obligations. -/
structure PatchTopologicalObstructionsDischarged : Prop where
  instanton_zero : ∀ A : PatchAbelianGaugeField, patchInstantonNumber A = 0
  pontryagin_zero : ∀ A : PatchAbelianGaugeField, patchPontryaginNumber A = 0
  first_chern_zero : ∀ A : PatchAbelianGaugeField, patchFirstChernNumber A = 0
  u1_winding_zero : ∀ A : PatchAbelianGaugeField, patchU1WindingNumber A = 0
  theta_independent : ∀ theta theta' : ℝ, ∀ A : PatchAbelianGaugeField,
    patchThetaTerm theta A = patchThetaTerm theta' A
  abelian_commutator_zero :
    ∀ {R S : SpacetimeRegion} (A B : LatticeHilbert 4 →ₗ[ℂ] LatticeHilbert 4),
      A ∈ patchAlgebraAt R → B ∈ patchAlgebraAt S → opCommutator A B = 0

theorem patchTopologicalObstructionsDischarged :
    PatchTopologicalObstructionsDischarged where
  instanton_zero := patchInstantonNumber_zero
  pontryagin_zero := patchPontryaginNumber_zero
  first_chern_zero := patchFirstChernNumber_zero
  u1_winding_zero := patchU1WindingNumber_zero
  theta_independent := patchThetaTerm_independent
  abelian_commutator_zero := fun _A _B hA hB =>
    patchAbelianCommutatorObstruction_zero _A _B hA hB

end

end Hqiv.QM

import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Order.Round

import Hqiv.Story.PlasticSpiralInterceptCoverage
import Hqiv.Story.PlasticPhaseBalanceImpliesReHalf
import Hqiv.Geometry.LatticePointMaxAbsShells

/-!
# Higher-order arity-respecting diagonal symmetry for zeta zeros (theorem shape)

This module records the conjectural target in a compile-safe form:

- each nontrivial zero height `t` is associated with a `ℤ^3` lattice point,
- the point lies in its root-scale arity shell,
- the point lies on a **face 45° diagonal** of the `ℤ^3` cube (`LiesOn45Diagonal`: two
  coordinates agree — the same survivor class as `DiagonalPointHasPermutationSymmetry`
  in `PlasticPhaseBalanceImpliesReHalf`),
- and the plastic phase at the point-indexed step is close to `t`.

The nontrivial-zero predicate is kept as an explicit hypothesis slot.
-/

namespace Hqiv.Story

open Set
open Hqiv.Geometry

/-- Hypothesis slot for "nontrivial zeta zero at height `t`". -/
def IsNontrivialZero (_t : ℝ) : Prop := True

/-- Integer-lattice step index used by the plastic phase channel. -/
def latticePointStep (point : Fin 3 → ℤ) : ℕ :=
  Int.natAbs (point 0 + point 1 + point 2)

/--
On the body diagonal, `point 0 + point 1 + point 2 = 3 * point 0`, hence the
shell step is `|3 * j|` with `j = point 0` (the “`m = 3j`” bookkeeping).
-/
theorem latticePointStep_of_liesOnBodyDiagonal (point : Fin 3 → ℤ)
    (h : LiesOnBodyDiagonal point) :
    latticePointStep point = Int.natAbs (3 * point 0) := by
  rcases h with ⟨h01, h12⟩
  unfold latticePointStep
  have hsum : point 0 + point 1 + point 2 = 3 * point 0 := by
    rw [h01, h12]
    ring
  rw [hsum]

theorem latticePointStep_of_eq01 (p : Fin 3 → ℤ) (h01 : p 0 = p 1) :
    latticePointStep p = Int.natAbs (2 * p 0 + p 2) := by
  unfold latticePointStep
  have hsum : p 0 + p 1 + p 2 = 2 * p 0 + p 2 := by rw [h01]; ring
  rw [hsum]

theorem latticePointStep_of_eq02 (p : Fin 3 → ℤ) (h02 : p 0 = p 2) :
    latticePointStep p = Int.natAbs (2 * p 0 + p 1) := by
  unfold latticePointStep
  have hsum : p 0 + p 1 + p 2 = 2 * p 0 + p 1 := by rw [h02]; ring
  rw [hsum]

theorem latticePointStep_of_eq12 (p : Fin 3 → ℤ) (h12 : p 1 = p 2) :
    latticePointStep p = Int.natAbs (p 0 + 2 * p 1) := by
  unfold latticePointStep
  have hsum : p 0 + p 1 + p 2 = p 0 + 2 * p 1 := by rw [h12]; ring
  rw [hsum]

/--
Which unordered pair of coordinates is equal on a face 45° diagonal (`Fin 3 → ℤ`).

Used to package the three proved geometry branches (`p0 = p1`, `p0 = p2`, `p1 = p2`) behind
a single index for downstream lemmas (for example `liesOn45Diagonal_iff` in
`PlasticLatticePhaseImpliesZetaZero`).  Prime-slot arithmetic on the lattice step is packaged
via `prime_latticePointStep_of_linked_fta_mirrorOff`, not from geometry alone.
-/
inductive WhichPairIsEqual : Type where
  | eq01 : WhichPairIsEqual
  | eq02 : WhichPairIsEqual
  | eq12 : WhichPairIsEqual

namespace WhichPairIsEqual

/-- The coordinate equality encoded by `w`. -/
def witness (w : WhichPairIsEqual) (p : Fin 3 → ℤ) : Prop :=
  match w with
  | eq01 => p 0 = p 1
  | eq02 => p 0 = p 2
  | eq12 => p 1 = p 2

/-- Closed form for `latticePointStep` once `w.witness p` holds (matches `latticePointStep_of_eq*`). -/
def stepNatAbs (w : WhichPairIsEqual) (p : Fin 3 → ℤ) : ℕ :=
  match w with
  | eq01 => Int.natAbs (2 * p 0 + p 2)
  | eq02 => Int.natAbs (2 * p 0 + p 1)
  | eq12 => Int.natAbs (p 0 + 2 * p 1)

/-- Two-coordinate `max natAbs` shell label for `w` (equals `maxNatAbsCoord p` under `w.witness p`). -/
def pairMaxNatAbs (w : WhichPairIsEqual) (p : Fin 3 → ℤ) : ℕ :=
  match w with
  | eq01 => max (p 0).natAbs (p 2).natAbs
  | eq02 => max (p 0).natAbs (p 1).natAbs
  | eq12 => max (p 0).natAbs (p 1).natAbs

theorem latticePointStep_eq_stepNatAbs (w : WhichPairIsEqual) (p : Fin 3 → ℤ) (hw : w.witness p) :
    latticePointStep p = w.stepNatAbs p := by
  cases w <;> dsimp [witness, stepNatAbs] at hw ⊢
  · exact latticePointStep_of_eq01 p hw
  · exact latticePointStep_of_eq02 p hw
  · exact latticePointStep_of_eq12 p hw

theorem maxNatAbsCoord_eq_pairMaxNatAbs (w : WhichPairIsEqual) (p : Fin 3 → ℤ) (hw : w.witness p) :
    maxNatAbsCoord p = w.pairMaxNatAbs p := by
  cases w <;> dsimp [witness, pairMaxNatAbs] at hw ⊢
  · exact maxNatAbsCoord_eq_max_of_eq01 p hw
  · exact maxNatAbsCoord_eq_max_of_eq02 p hw
  · exact maxNatAbsCoord_eq_max_of_eq12 p hw

end WhichPairIsEqual

/-- Canonical **01-face diagonal** witness `(m, m, 0)` (two equal coordinates, third `0`). -/
noncomputable def canonical45DiagonalPoint (m : ℕ) : Fin 3 → ℤ :=
  ![(m : ℤ), (m : ℤ), 0]

/-- A 3D lattice point in the root-scale arity shell with
the higher-order diagonal preference. -/
structure ZetaZeroArityDiagonalPoint where
  /-- Imaginary part of the zero. -/
  t : ℝ
  /-- Natural root-scale arity at height `t`. -/
  kappa : ℕ
  /-- The 3D lattice point `(j, k, l)`. -/
  point : Fin 3 → ℤ
  /-- The point lies in the arity shell `[kappa - 1, kappa]` (max-abs indexing). -/
  hInShell : maxNatAbsCoord point ∈ Set.Icc (kappa - 1) kappa
  /-- The point lies on a face 45° diagonal (`LiesOn45Diagonal`). -/
  h45Diagonal : LiesOn45Diagonal point
  /-- Plastic phase at the lattice step is close to the zero height `t`. -/
  hPhaseClose : |plasticSpiralPhaseAtStep (latticePointStep point) - t| < (1 : ℝ) / 40

/-- Global conjecture target:
every nontrivial zero admits an arity-respecting diagonal lattice witness. -/
def AllZetaZerosSatisfyArityDiagonalPreference : Prop :=
  ∀ t : ℝ, IsNontrivialZero t →
    ∃ P : ZetaZeroArityDiagonalPoint, P.t = t

/--
Canonical witness data at height `t` (round-trip through `plasticSpiralPhaseAtStep` and
`canonical45DiagonalPoint`). Field proofs are still open: shell inclusion, face
diagonality, and `|φ(m) - t| < 1/40` require Diophantine or numeric input.
-/
noncomputable def buildArityDiagonalWitness (t : ℝ) (_hNontriv : IsNontrivialZero t) :
    ZetaZeroArityDiagonalPoint :=
  let tNat : ℕ := Int.toNat (round t)
  let m : ℕ := Int.toNat (round (plasticSpiralPhaseAtStep tNat))
  let pt : Fin 3 → ℤ := canonical45DiagonalPoint m
  { t := t
    kappa := maxNatAbsCoord pt
    point := pt
    hInShell := by sorry
    h45Diagonal := by
      refine ⟨(0 : Fin 3), (1 : Fin 3), ?_, ?_⟩
      · decide
      · simp [pt, canonical45DiagonalPoint]
    hPhaseClose := by sorry }

/--
3D root-scale binned field with built-in higher-order arity-diagonal symmetry
(ties `PlasticRootScaleBinnedField3D` to the zeta-zero conjecture shape).

`hPhaseCompat` duplicates the base field axiom so callers can pattern-match on
this bundle alone. By default, `coeffFromField` is `some (default3DCoeff F)` from
`PlasticSpiralInterceptCoverage` (Apéry base + diagonal boost + prime bonus); set
it to `none` if you want a different coefficient channel.
-/
structure PlasticRootScaleBinnedField3D.WithArityDiagonalSymmetry
    (F : PlasticRootScaleBinnedField3D) where
  /-- Phase compatibility (same as `F.hPhaseCompat`). -/
  hPhaseCompat : ∀ m : ℕ, F.phi_3D m = plasticSpiralPhaseAtStep m
  /-- Global diagonal-preference conjecture for nontrivial zeros. -/
  hArityDiagonal : AllZetaZerosSatisfyArityDiagonalPreference
  /-- Optional coefficient channel for the plastic `ζ(3)` candidate. -/
  coeffFromField : Option (ℕ → ℂ) := some (default3DCoeff F)

end Hqiv.Story

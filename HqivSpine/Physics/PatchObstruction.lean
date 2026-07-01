import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.PatchObstruction` — finite causal patches discharge continuum obligations

HQIV observables live on **finite causal patches** (a `Fin n` local chart), not on a smooth
manifold. This module records, as theorems, the two ways that makes notorious continuum
obligations vacuous — the companion to `Physics.CCR` (no finite-dim `[A,B]=1`):

* **No topological sectors.** A finite abelian patch field carries a single topological sector
  (`Unit`), so the instanton / Pontryagin / first-Chern / `U(1)`-winding slots are all `0` and
  the θ-term is θ-independent — there is no θ-vacuum on the patch
  (`patchInstantonNumber_zero`, …, `patchThetaTerm_independent`).
* **Automatic microcausality.** The local patch algebra is **abelian**: patch observables are
  diagonal operators on the finite chart `ℂ^n`, which commute, so every commutator vanishes
  (`patch_microcausality`) — Haag–Kastler microcausality is free, no smooth bundle needed.

These are **patch-level** statements: they do *not* classify smooth continuum bundles or prove a
continuum instanton theorem; they record that the finite ontology never incurs those debts.

Mathlib-only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Physics.Patch

open Matrix

/-! ## Topological-sector triviality -/

/-- Finite abelian patch gauge data: one real coefficient in each chart slot. -/
structure PatchGaugeField (n : ℕ) where
  potential : Fin n → ℝ

/-- The finite patch has a single discrete topological sector, represented by `Unit`. -/
def patchTopologicalSector {n : ℕ} (_A : PatchGaugeField n) : Unit := ()

/-- Patch instanton number — `0`, the unique charge compatible with a `Unit` sector. -/
def patchInstantonNumber {n : ℕ} (A : PatchGaugeField n) : ℤ :=
  match patchTopologicalSector A with | () => 0

/-- Patch Pontryagin (`F∧F` / second-Chern) number. -/
def patchPontryaginNumber {n : ℕ} (A : PatchGaugeField n) : ℤ :=
  match patchTopologicalSector A with | () => 0

/-- Patch first-Chern slot for abelian `U(1)` language. -/
def patchFirstChernNumber {n : ℕ} (A : PatchGaugeField n) : ℤ :=
  match patchTopologicalSector A with | () => 0

/-- Patch `U(1)` winding slot. -/
def patchU1WindingNumber {n : ℕ} (A : PatchGaugeField n) : ℤ :=
  match patchTopologicalSector A with | () => 0

/-- θ-term contribution on the patch. -/
def patchThetaTerm {n : ℕ} (theta : ℝ) (A : PatchGaugeField n) : ℝ :=
  theta * (patchInstantonNumber A : ℝ)

/-- Any two patch fields lie in the same (unique) topological sector. -/
theorem patch_topological_sector_unique {n : ℕ} (A B : PatchGaugeField n) :
    patchTopologicalSector A = patchTopologicalSector B :=
  Subsingleton.elim _ _

theorem patchInstantonNumber_zero {n : ℕ} (A : PatchGaugeField n) :
    patchInstantonNumber A = 0 := rfl

theorem patchPontryaginNumber_zero {n : ℕ} (A : PatchGaugeField n) :
    patchPontryaginNumber A = 0 := rfl

theorem patchFirstChernNumber_zero {n : ℕ} (A : PatchGaugeField n) :
    patchFirstChernNumber A = 0 := rfl

theorem patchU1WindingNumber_zero {n : ℕ} (A : PatchGaugeField n) :
    patchU1WindingNumber A = 0 := rfl

/-- The θ-term vanishes on every finite patch field. -/
theorem patchThetaTerm_zero {n : ℕ} (theta : ℝ) (A : PatchGaugeField n) :
    patchThetaTerm theta A = 0 := by
  simp [patchThetaTerm, patchInstantonNumber_zero]

/-- **No θ-vacuum on the patch:** the topological term is θ-independent. -/
theorem patchThetaTerm_independent {n : ℕ} (theta theta' : ℝ) (A : PatchGaugeField n) :
    patchThetaTerm theta A = patchThetaTerm theta' A := by
  rw [patchThetaTerm_zero theta A, patchThetaTerm_zero theta' A]

/-! ## Microcausality from an abelian patch algebra -/

/-- A patch observable on the finite chart `ℂ^n`: a **diagonal** operator. The local patch
algebra is the abelian algebra of such operators. -/
def IsPatchObservable {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ d : Fin n → ℂ, M = Matrix.diagonal d

/-- Diagonal operators commute (pointwise multiplication in `ℂ` is commutative). -/
theorem diagonal_commutator_zero {n : ℕ} (d e : Fin n → ℂ) :
    Matrix.diagonal d * Matrix.diagonal e - Matrix.diagonal e * Matrix.diagonal d = 0 := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    show (fun i => d i * e i) = (fun i => e i * d i) from funext fun i => mul_comm _ _,
    sub_self]

/-- **Automatic microcausality:** any two patch observables commute, so their commutator is `0` —
no smooth bundle or continuum gauge measure is needed. -/
theorem patch_microcausality {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsPatchObservable A) (hB : IsPatchObservable B) :
    A * B - B * A = 0 := by
  obtain ⟨d, rfl⟩ := hA
  obtain ⟨e, rfl⟩ := hB
  exact diagonal_commutator_zero d e

/-! ## Summary package -/

/-- The finite patch discharges the topological-sector and microcausality obligations that
would otherwise be continuum debts. -/
structure ObstructionsDischarged (n : ℕ) : Prop where
  instanton_zero : ∀ A : PatchGaugeField n, patchInstantonNumber A = 0
  pontryagin_zero : ∀ A : PatchGaugeField n, patchPontryaginNumber A = 0
  first_chern_zero : ∀ A : PatchGaugeField n, patchFirstChernNumber A = 0
  u1_winding_zero : ∀ A : PatchGaugeField n, patchU1WindingNumber A = 0
  theta_independent : ∀ theta theta' : ℝ, ∀ A : PatchGaugeField n,
    patchThetaTerm theta A = patchThetaTerm theta' A
  microcausality : ∀ A B : Matrix (Fin n) (Fin n) ℂ,
    IsPatchObservable A → IsPatchObservable B → A * B - B * A = 0

/-- All patch obstructions are discharged, for every chart size `n`. -/
theorem obstructions_discharged (n : ℕ) : ObstructionsDischarged n where
  instanton_zero := patchInstantonNumber_zero
  pontryagin_zero := patchPontryaginNumber_zero
  first_chern_zero := patchFirstChernNumber_zero
  u1_winding_zero := patchU1WindingNumber_zero
  theta_independent := patchThetaTerm_independent
  microcausality := patch_microcausality

end HqivSpine.Physics.Patch

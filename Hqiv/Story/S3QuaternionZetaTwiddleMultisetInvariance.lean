import Hqiv.Story.S3DiagonalSphereTwiddlePermutations
import Hqiv.Story.S3ThetaPartitionTwiddleAddress
import Hqiv.Story.S3SO4ZetaProjectionClosedForm
import Hqiv.Story.S3EulerSO4PrimeAxisBridge
import Hqiv.Story.PlasticTwistedEulerCharacter
import Mathlib.GroupTheory.Perm.Basic

/-!
# Quaternion-lifted ζ readout ⇒ twiddle multiset invariance

The combinatorial S₃ case split on `maxNatAbsCoord` is unnecessary once the
**quaternion / SO(4) lifted** story is in view:

1. **Euler / partition chart** — a twiddle **cell** is the unordered leg multiset
   `{a,b,c}`.  The theta partition weights cells by `1/|orbit|` (`twiddleCellPartitionWeight`),
   not by a single ordered triple.
2. **Product shell** — harmonic depth is `twiddleAddressShellDepth addr = a·b·c`, the
   same object as a multiplicative Euler factor slot.  Permuting legs does not change
   the product (proved below).
3. **Lattice-sphere label** — `κ = max(a,b,c)` is the symmetric statistic of the
   same multiset; it is the max-abs shell of the diagonal voxel chart
   (`twiddleVoxelShellLabel`).  Invariance follows from `maxNatAbsCoord` being a
   symmetric scan of coordinates (`maxNatAbsCoord_fin3_perm`).
4. **SO(4) / quaternion lift** — the projected ζ readout (`zetaSO4Projected`,
   `PrimeAxisEulerSO4Slot`) is built from **orbit** cancellation (head/tail pair,
   twisted Euler mirror on composites), not from ordering of factor legs.  The
   twiddle partition explicitly quotients by `twiddleAddressOrbitSize`.

So permutation of legs is a **gauge on the same cell**; the lifted zeta partition
cannot depend on it.  What *can* change under permutation is which **diagonal voxel**
`(a,b,c)` is hit on `ℤ³` — that is the geometric orbit
`twiddleOrbitVoxels`, distinct from the analytic cell label.

## Honesty

* Proved here: product depth, orbit set, partition weight, and max-abs shell label
  are permutation-invariant on the twiddle cell.
* Not claimed: full identification of every zero with a twiddle cell; automatic
  ζ-zeros from geometry alone.
-/

namespace Hqiv.Story

open Finset
open Hqiv.Geometry

noncomputable section

/-! ## Leg multiset is the Euler / partition label -/

theorem twiddle_leg_comp (σ τ : Equiv.Perm (Fin 3)) (addr : TwiddleFactorAddress) (i : Fin 3) :
    twiddleLeg (permuteTwiddleAddress σ (permuteTwiddleAddress τ addr)) i =
      twiddleLeg (permuteTwiddleAddress (τ * σ) addr) i := by
  simp only [twiddleLeg_permute, Equiv.Perm.mul_apply]

theorem permute_twiddle_address_one (addr : TwiddleFactorAddress) :
    permuteTwiddleAddress (1 : Equiv.Perm (Fin 3)) addr = addr := by
  rcases addr with ⟨a, b, c⟩
  dsimp [permuteTwiddleAddress, twiddleLeg, Equiv.Perm.one_apply]

/--
Leg permutation composes on display slots as `σ` after `τ`:

`permute σ (permute τ addr) = permute (τ * σ) addr`.
-/
theorem permute_twiddle_address_comp (σ τ : Equiv.Perm (Fin 3)) (addr : TwiddleFactorAddress) :
    permuteTwiddleAddress σ (permuteTwiddleAddress τ addr) =
      permuteTwiddleAddress (τ * σ) addr := by
  rcases addr with ⟨a, b, c⟩
  fin_cases σ <;> fin_cases τ <;>
    simp only [permuteTwiddleAddress, twiddleLeg, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Prod.mk.injEq]
  repeat' (first | constructor | ring)

theorem permute_twiddle_address_mul_apply (σ τ : Equiv.Perm (Fin 3)) (addr : TwiddleFactorAddress) :
    permuteTwiddleAddress (τ * σ) addr = permuteTwiddleAddress σ (permuteTwiddleAddress τ addr) :=
  (permute_twiddle_address_comp σ τ addr).symm

theorem permute_twiddle_address_inv (σ : Equiv.Perm (Fin 3)) (addr : TwiddleFactorAddress) :
    permuteTwiddleAddress σ⁻¹ (permuteTwiddleAddress σ addr) = addr := by
  rcases addr with ⟨a, b, c⟩
  fin_cases σ <;>
    simp only [permuteTwiddleAddress, twiddleLeg, twiddleLeg_permute, Equiv.symm_apply_apply,
      Equiv.swap_apply_def, Prod.mk.injEq]
  repeat' constructor

theorem mem_twiddle_address_orbit_perm_left (σ : Equiv.Perm (Fin 3))
    (addr : TwiddleFactorAddress) :
    permuteTwiddleAddress σ addr ∈ twiddleAddressOrbit addr :=
  Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, rfl⟩

theorem mem_twiddle_address_orbit_perm_right (σ : Equiv.Perm (Fin 3))
    (addr : TwiddleFactorAddress) :
    addr ∈ twiddleAddressOrbit (permuteTwiddleAddress σ addr) :=
  Finset.mem_image.mpr ⟨σ⁻¹, Finset.mem_univ _, permute_twiddle_address_inv σ addr⟩

theorem twiddle_address_orbit_perm (σ : Equiv.Perm (Fin 3)) (addr : TwiddleFactorAddress) :
    twiddleAddressOrbit (permuteTwiddleAddress σ addr) = twiddleAddressOrbit addr := by
  apply Finset.Subset.antisymm
  · intro a ha
    rcases Finset.mem_image.mp ha with ⟨τ, _, hτ⟩
    refine Finset.mem_image.mpr ⟨σ * τ, Finset.mem_univ _, ?_⟩
    rw [← permute_twiddle_address_comp τ σ addr, hτ]
  · intro a ha
    rcases Finset.mem_image.mp ha with ⟨τ, _, hτ⟩
    refine Finset.mem_image.mpr ⟨σ⁻¹ * τ, Finset.mem_univ _, ?_⟩
    rw [← permute_twiddle_address_comp τ σ⁻¹ (permuteTwiddleAddress σ addr),
      permute_twiddle_address_inv σ addr, hτ]

theorem twiddle_address_orbit_size_perm (σ : Equiv.Perm (Fin 3)) (addr : TwiddleFactorAddress) :
    twiddleAddressOrbitSize (permuteTwiddleAddress σ addr) = twiddleAddressOrbitSize addr := by
  dsimp [twiddleAddressOrbitSize]
  rw [twiddle_address_orbit_perm σ addr]

theorem twiddle_address_shell_depth_eq_prod (addr : TwiddleFactorAddress) :
    twiddleAddressShellDepth addr = ∏ i : Fin 3, twiddleLeg addr i := by
  rcases addr with ⟨a, b, c⟩
  dsimp [twiddleAddressShellDepth, twiddleLeg]
  simp [Finset.prod_fin_eq_prod_range, Finset.prod_range_succ]

/-- Product shell depth `a·b·c` is the Euler twiddle slot — invariant under leg permutation. -/
theorem twiddle_address_shell_depth_perm (σ : Equiv.Perm (Fin 3)) (addr : TwiddleFactorAddress) :
    twiddleAddressShellDepth (permuteTwiddleAddress σ addr) = twiddleAddressShellDepth addr := by
  have hprod := Equiv.prod_comp σ (fun i => twiddleLeg addr i)
  rw [twiddle_address_shell_depth_eq_prod, twiddle_address_shell_depth_eq_prod, ← hprod]
  simp [twiddleLeg_permute]

/--
Theta partition weight for a cell depends only on orbit size and slot amplitude,
both unchanged on the S₃ orbit of an address.
-/
theorem twiddle_cell_partition_weight_perm
    (addr : TwiddleFactorAddress) (σ : Equiv.Perm (Fin 3))
    {n : ℕ} (hn : 0 < n) (k : Fin n) :
    twiddleCellPartitionWeight (permuteTwiddleAddress σ addr) hn k =
      twiddleCellPartitionWeight addr hn k := by
  dsimp [twiddleCellPartitionWeight]
  rw [twiddle_address_orbit_size_perm σ addr]

/-! ## Max-abs shell from symmetric multiset scan -/

theorem finset_sup_natAbs_fin3_perm (σ : Equiv.Perm (Fin 3)) (p : Fin 3 → ℤ) :
    (univ : Finset (Fin 3)).sup (fun j => ((p ∘ σ) j).natAbs) =
      univ.sup (fun j => (p j).natAbs) := by
  apply le_antisymm
  · refine Finset.sup_le ?_
    intro i hi
    simpa [Function.comp_apply] using
      Finset.le_sup (f := fun j => (p j).natAbs) (mem_univ (σ i))
  · refine Finset.sup_le ?_
    intro i hi
    have := Finset.le_sup (f := fun j => ((p ∘ σ) j).natAbs) (mem_univ (σ.symm i))
    simpa [Function.comp_apply, Equiv.symm_apply_apply] using this

theorem maxNatAbsCoord_fin3_perm (σ : Equiv.Perm (Fin 3)) (p : Fin 3 → ℤ) :
    maxNatAbsCoord (p ∘ σ) = maxNatAbsCoord p := by
  unfold maxNatAbsCoord
  exact finset_sup_natAbs_fin3_perm σ p

theorem maxNatAbsCoord_lattice_voxel_perm (σ : Equiv.Perm (Fin 3))
    (addr : TwiddleFactorAddress) :
    maxNatAbsCoord (latticeVoxelOfPermutedTwiddle σ addr) =
      maxNatAbsCoord (latticeVoxelOfTwiddleAddress addr) := by
  have hfun :
      latticeVoxelOfPermutedTwiddle σ addr = latticeVoxelOfTwiddleAddress addr ∘ σ := by
    funext i
    exact lattice_voxel_permuted_eq_comp σ addr i
  rw [hfun, maxNatAbsCoord_fin3_perm]

/-- **Zeta/partition consequence:** max-abs sphere label is forced by the leg multiset. -/
theorem twiddle_permutation_preserves_max_abs_shell (addr : TwiddleFactorAddress) :
    TwiddlePermutationPreservesMaxAbsShell addr := by
  intro σ
  dsimp [TwiddlePermutationPreservesMaxAbsShell, twiddleVoxelShellLabel]
  exact maxNatAbsCoord_lattice_voxel_perm σ addr

/-! ## SO(4) / twisted-Euler packaging -/

/--
The quaternion-lifted readout names a **cell** (multiset + product shell), not an
ordered factor tuple.  Permuting legs is gauge on the same cell data.
-/
structure QuaternionZetaTwiddleMultisetBundle (addr : TwiddleFactorAddress) where
  /-- Product Euler / harmonic shell depth `a·b·c`. -/
  shell_depth : ℕ
  shell_depth_eq : shell_depth = twiddleAddressShellDepth addr
  /-- S₃ orbit on addresses is the partition gauge quotient. -/
  orbit_size : ℕ
  orbit_size_eq : orbit_size = twiddleAddressOrbitSize addr
  /-- Max-abs diagonal-sphere label from the same multiset. -/
  preserves_max_abs_shell : TwiddlePermutationPreservesMaxAbsShell addr

noncomputable def quaternionZetaTwiddleMultisetBundle (addr : TwiddleFactorAddress) :
    QuaternionZetaTwiddleMultisetBundle addr where
  shell_depth := twiddleAddressShellDepth addr
  shell_depth_eq := rfl
  orbit_size := twiddleAddressOrbitSize addr
  orbit_size_eq := rfl
  preserves_max_abs_shell := twiddle_permutation_preserves_max_abs_shell addr

/--
Partition weight at a slot is unchanged on the S₃ orbit when the address already
matches shell depth `n`.
-/
theorem quaternion_zeta_partition_weight_on_orbit
    (addr : TwiddleFactorAddress) (σ : Equiv.Perm (Fin 3))
    {n : ℕ} (hn : 0 < n) (k : Fin n) :
    twiddleCellPartitionWeight (permuteTwiddleAddress σ addr) hn k =
      twiddleCellPartitionWeight addr hn k :=
  twiddle_cell_partition_weight_perm addr σ hn k

/--
SO(4) projected ζ equals classical ζ on the readout slice — the lift does not
introduce a separate ordered-factor ontology (`zetaSO4Projected_eq_zeta`).
-/
theorem quaternion_lift_zeta_agrees_with_classical (s : ℂ) :
    zetaSO4Projected s = riemannZeta s :=
  zetaSO4Projected_eq_zeta s

/-!
## Status

* **Unconditional:** multiset cell invariance for product shell, partition weight,
  and max-abs sphere label; orbit set equality under S₃.
* **Interpretation:** quaternion/SO(4) lift + theta partition quotient explain *why*
  permutation cannot change shell labels — not merely that Lean checked six cases.
-/

end

end Hqiv.Story

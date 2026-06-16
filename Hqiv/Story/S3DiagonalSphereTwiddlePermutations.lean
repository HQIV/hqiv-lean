import Hqiv.Story.S3ThetaPartitionTwiddleAddress
import Hqiv.Story.PlasticPhaseBalanceImpliesReHalf
import Hqiv.Geometry.LatticePointMaxAbsShells
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Perm.Basic

/-!
# Diagonal lattice-sphere voxels addressed by twiddle permutations

The live geometric object is **not** only the symmetric `(m,m,m)` ladder with
line heights `π/(2+m)` (see `S3DeepTwiddlePoleLadder` for that **special case**).

It is: **all S₃ permutations of a twiddle-factor tuple that address a voxel on
the 45° diagonal of a discrete sphere** — lattice points in `ℤ³` grouped by
`maxNatAbsCoord` shells (`latticeMaxAbsShell`).

* **Sphere** — `latticeMaxAbsShell κ` (Chebyshev / max-|coordinate| shell).
* **Diagonal voxel** — `LiesOn45Diagonal` (at least two coordinates agree).
* **Address** — twiddle legs `(a,b,c)`; **permutation** `σ ∈ S₃` reorders legs via
  `permuteTwiddleAddress`.
* **Voxel hit** — `latticeVoxelOfPermutedTwiddle σ addr` casts the permuted legs to
  `ℤ³`.

The partition cell (`twiddleAddressOrbit`) is the multiset of legs; the
**orbit of voxels** (`twiddleOrbitVoxels`) is the set of diagonal sphere points
those permutations can hit.

## Charts (do not conflate)

| Chart | `(2,2,2)` example |
|-------|-------------------|
| Product partition shell | `2·2·2 = 8` (harmonic slot depth) |
| Lattice voxel on max-abs sphere | `(2,2,2) ∈ ℤ³` on shell `κ = 2` |
| S₃ address orbit | singleton `{ (2,2,2) }` |
| S₃ voxel orbit | singleton `{ (2,2,2) }` on body diagonal |

## Honesty

* Unconditional: permutation → diagonal voxel; orbit definitions; shell labels;
  `(2,2,2)` body diagonal on shell `2`.
* Not claimed: every zero hits one of these orbits; `π/(2+m)` for all diagonal voxels.
-/

namespace Hqiv.Story

open Hqiv.Geometry
open Finset

noncomputable section

/-! ## Twiddle legs → ℤ³ voxel -/

/-- Cast twiddle legs to a `ℤ³` lattice voxel (live voxel chart). -/
def latticeVoxelOfTwiddleAddress (addr : TwiddleFactorAddress) : Fin 3 → ℤ :=
  ![addr.1, addr.2.1, addr.2.2]

/-- Voxel reached by permuting twiddle legs with `σ`. -/
def latticeVoxelOfPermutedTwiddle (σ : Equiv.Perm (Fin 3)) (addr : TwiddleFactorAddress) :
    Fin 3 → ℤ :=
  latticeVoxelOfTwiddleAddress (permuteTwiddleAddress σ addr)

theorem lattice_voxel_of_permuted_twiddle_eq (σ : Equiv.Perm (Fin 3))
    (addr : TwiddleFactorAddress) :
    latticeVoxelOfTwiddleAddress (permuteTwiddleAddress σ addr) =
      latticeVoxelOfPermutedTwiddle σ addr :=
  rfl

theorem twiddle_leg_eq_lattice_voxel_coord (addr : TwiddleFactorAddress) (i : Fin 3) :
    twiddleLeg addr i = latticeVoxelOfTwiddleAddress addr i := by
  fin_cases i <;> rfl

theorem twiddle_leg_cast_eq_lattice_voxel_coord (addr : TwiddleFactorAddress) (i : Fin 3) :
    (twiddleLeg addr i : ℤ) = latticeVoxelOfTwiddleAddress addr i := by
  fin_cases i <;> rfl

/-! ## Diagonal voxel on a lattice sphere shell -/

/--
A **diagonal voxel** on max-abs sphere shell `κ`: a lattice point on shell `κ`
with at least two equal coordinates.
-/
structure DiagonalVoxelOnLatticeSphere (κ : ℕ) where
  point : Fin 3 → ℤ
  on_shell : point ∈ latticeMaxAbsShell κ
  on_diagonal : LiesOn45Diagonal point

/-- Max-|coordinate| shell label of the voxel from twiddle legs. -/
def twiddleVoxelShellLabel (addr : TwiddleFactorAddress) : ℕ :=
  maxNatAbsCoord (latticeVoxelOfTwiddleAddress addr)

theorem mem_twiddle_voxel_shell (addr : TwiddleFactorAddress) :
    latticeVoxelOfTwiddleAddress addr ∈ latticeMaxAbsShell (twiddleVoxelShellLabel addr) := by
  dsimp [twiddleVoxelShellLabel, latticeMaxAbsShell, mem_latticeMaxAbsShell]

/-! ## Twiddle tuple ⇒ diagonal (permutation-stable) -/

theorem twiddle_leg_pair_equal_of_twiddle_tuple (addr : TwiddleFactorAddress)
    (h : isTwiddleTuple addr) :
    ∃ i j : Fin 3, i ≠ j ∧ twiddleLeg addr i = twiddleLeg addr j := by
  rcases h with h | h | h
  · exact ⟨(0 : Fin 3), (1 : Fin 3), by decide, h⟩
  · exact ⟨(0 : Fin 3), (2 : Fin 3), by decide, h⟩
  · exact ⟨(1 : Fin 3), (2 : Fin 3), by decide, h⟩

theorem twiddle_leg_pair_equal_iff_twiddle_tuple (addr : TwiddleFactorAddress) :
    isTwiddleTuple addr ↔
      ∃ i j : Fin 3, i ≠ j ∧ twiddleLeg addr i = twiddleLeg addr j := by
  constructor
  · exact twiddle_leg_pair_equal_of_twiddle_tuple addr
  · rintro ⟨i, j, hij, he⟩
    fin_cases i <;> fin_cases j <;> simp [twiddleLeg, isTwiddleTuple] at he hij ⊢ <;> tauto

theorem twiddleLeg_permute (addr : TwiddleFactorAddress) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    twiddleLeg (permuteTwiddleAddress σ addr) i = twiddleLeg addr (σ i) := by
  dsimp [twiddleLeg, permuteTwiddleAddress]
  fin_cases i <;> rfl

theorem isTwiddleTuple_permute_addr (addr : TwiddleFactorAddress)
    (h : isTwiddleTuple addr) (σ : Equiv.Perm (Fin 3)) :
    isTwiddleTuple (permuteTwiddleAddress σ addr) := by
  rw [twiddle_leg_pair_equal_iff_twiddle_tuple]
  obtain ⟨i, j, hij, he⟩ := twiddle_leg_pair_equal_of_twiddle_tuple addr h
  refine ⟨σ.symm i, σ.symm j, ?_, ?_⟩
  · intro h_eq
    exact hij (σ.injective (by simpa [Equiv.apply_symm_apply] using h_eq))
  · rw [twiddleLeg_permute addr σ (σ.symm i), twiddleLeg_permute addr σ (σ.symm j)]
    simpa [Equiv.symm_apply_apply] using he

theorem twiddle_voxel_on_45_diagonal (addr : TwiddleFactorAddress)
    (h : isTwiddleTuple addr) : LiesOn45Diagonal (latticeVoxelOfTwiddleAddress addr) := by
  obtain ⟨i, j, hij, he⟩ := twiddle_leg_pair_equal_of_twiddle_tuple addr h
  exact ⟨i, j, hij, by
    rw [← twiddle_leg_eq_lattice_voxel_coord addr i, ← twiddle_leg_eq_lattice_voxel_coord addr j, he]⟩

theorem permuted_twiddle_voxel_on_45_diagonal (addr : TwiddleFactorAddress)
    (h : isTwiddleTuple addr) (σ : Equiv.Perm (Fin 3)) :
    LiesOn45Diagonal (latticeVoxelOfPermutedTwiddle σ addr) := by
  have h' := isTwiddleTuple_permute_addr addr h σ
  simpa [latticeVoxelOfPermutedTwiddle] using
    twiddle_voxel_on_45_diagonal (permuteTwiddleAddress σ addr) h'

theorem permuted_twiddle_voxel_on_shell (addr : TwiddleFactorAddress) (σ : Equiv.Perm (Fin 3)) :
    latticeVoxelOfPermutedTwiddle σ addr ∈
      latticeMaxAbsShell (maxNatAbsCoord (latticeVoxelOfPermutedTwiddle σ addr)) := by
  dsimp [latticeMaxAbsShell, mem_latticeMaxAbsShell]

theorem maxNatAbsCoord_cast_vec₃ (a b c : ℕ) :
    maxNatAbsCoord (![a, b, c] : Fin 3 → ℤ) = max (max a b) c := by
  unfold maxNatAbsCoord
  have huniv :
      (univ : Finset (Fin 3)) = insert (0 : Fin 3) (insert 1 {2}) := by
    ext i
    fin_cases i <;> simp
  rw [huniv, Finset.sup_insert, Finset.sup_insert, Finset.sup_singleton]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Int.natAbs_natCast,
    max_assoc, max_left_comm, max_comm]

theorem maxNatAbsCoord_lattice_voxel_eq (addr : TwiddleFactorAddress) :
    maxNatAbsCoord (latticeVoxelOfTwiddleAddress addr) =
      max (max addr.1 addr.2.1) addr.2.2 := by
  simpa [latticeVoxelOfTwiddleAddress] using
    maxNatAbsCoord_cast_vec₃ addr.1 addr.2.1 addr.2.2

theorem lattice_voxel_permuted_eq_comp (σ : Equiv.Perm (Fin 3)) (addr : TwiddleFactorAddress)
    (i : Fin 3) :
    latticeVoxelOfPermutedTwiddle σ addr i = latticeVoxelOfTwiddleAddress addr (σ i) := by
  dsimp [latticeVoxelOfPermutedTwiddle]
  rw [← twiddle_leg_cast_eq_lattice_voxel_coord (permuteTwiddleAddress σ addr) i,
    twiddleLeg_permute, twiddle_leg_cast_eq_lattice_voxel_coord]

/--
Permuting twiddle legs does not change the max-abs sphere shell label — the multiset
`{a,b,c}` of leg magnitudes is unchanged.

**Proof (not a heavy S₃ case split):** `S3QuaternionZetaTwiddleMultisetInvariance`
— the quaternion-lifted partition/Euler cell depends on the leg multiset; `max` is
a symmetric scan (`twiddle_permutation_preserves_max_abs_shell`).
-/
def TwiddlePermutationPreservesMaxAbsShell (addr : TwiddleFactorAddress) : Prop :=
  ∀ σ : Equiv.Perm (Fin 3),
    maxNatAbsCoord (latticeVoxelOfPermutedTwiddle σ addr) = twiddleVoxelShellLabel addr

theorem twiddle_orbit_voxel_on_own_max_abs_shell (addr : TwiddleFactorAddress)
    (σ : Equiv.Perm (Fin 3)) :
    latticeVoxelOfPermutedTwiddle σ addr ∈
      latticeMaxAbsShell (maxNatAbsCoord (latticeVoxelOfPermutedTwiddle σ addr)) :=
  permuted_twiddle_voxel_on_shell addr σ

/-! ## S₃ orbit of voxels vs S₃ orbit of addresses -/

/--
All `ℤ³` voxels hit by permuting the legs of `addr` — the geometric orbit on the
lattice sphere chart.
-/
noncomputable def twiddleOrbitVoxels (addr : TwiddleFactorAddress) : Finset (Fin 3 → ℤ) :=
  image (fun σ => latticeVoxelOfPermutedTwiddle σ addr) univ

theorem mem_twiddle_orbit_voxels_iff (addr : TwiddleFactorAddress) (p : Fin 3 → ℤ) :
    p ∈ twiddleOrbitVoxels addr ↔
      ∃ σ : Equiv.Perm (Fin 3), latticeVoxelOfPermutedTwiddle σ addr = p := by
  dsimp [twiddleOrbitVoxels]
  simp [mem_image]

/--
`σ` **addresses** the diagonal voxel `p` when the permuted twiddle legs cast to
`ℤ³` equal `p`.
-/
def TwiddlePermutationAddressesVoxel (addr : TwiddleFactorAddress) (p : Fin 3 → ℤ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), latticeVoxelOfPermutedTwiddle σ addr = p

theorem twiddle_permutation_addresses_voxel_iff (addr : TwiddleFactorAddress) (p : Fin 3 → ℤ) :
    TwiddlePermutationAddressesVoxel addr p ↔ p ∈ twiddleOrbitVoxels addr :=
  Iff.symm (mem_twiddle_orbit_voxels_iff addr p)

/--
A twiddle tuple's permutation orbit **addresses only diagonal voxels** on some
max-abs sphere shell.
-/
structure TwiddleDiagonalSphereAddress where
  addr : TwiddleFactorAddress
  twiddle : isTwiddleTuple addr
  shell : ℕ
  shell_eq : shell = twiddleVoxelShellLabel addr
  orbit_voxels : Finset (Fin 3 → ℤ)
  orbit_voxels_eq : orbit_voxels = twiddleOrbitVoxels addr
  orbit_on_diagonal :
    ∀ p ∈ orbit_voxels, LiesOn45Diagonal p
  /-- Each addressed voxel lies on its own max-abs sphere shell (always). -/
  orbit_on_own_shell :
    ∀ p ∈ orbit_voxels,
      ∃ κ : ℕ, p ∈ latticeMaxAbsShell κ
  /-- When `hShell` holds, every orbit voxel shares the canonical shell `κ`. -/
  orbit_on_canonical_shell :
    TwiddlePermutationPreservesMaxAbsShell addr →
      ∀ p ∈ orbit_voxels, p ∈ latticeMaxAbsShell shell

theorem twiddle_diagonal_sphere_address_orbit_on_diagonal (addr : TwiddleFactorAddress)
    (h : isTwiddleTuple addr) :
    ∀ p ∈ twiddleOrbitVoxels addr, LiesOn45Diagonal p := by
  intro p hp
  rcases mem_twiddle_orbit_voxels_iff addr p |>.mp hp with ⟨σ, rfl⟩
  exact permuted_twiddle_voxel_on_45_diagonal addr h σ

theorem twiddle_diagonal_sphere_address_orbit_on_own_shell (addr : TwiddleFactorAddress)
    (_h : isTwiddleTuple addr) :
    ∀ p ∈ twiddleOrbitVoxels addr, ∃ κ : ℕ, p ∈ latticeMaxAbsShell κ := by
  intro p hp
  rcases mem_twiddle_orbit_voxels_iff addr p |>.mp hp with ⟨σ, hσ⟩
  subst hσ
  exact ⟨maxNatAbsCoord (latticeVoxelOfPermutedTwiddle σ addr),
    twiddle_orbit_voxel_on_own_max_abs_shell addr σ⟩

theorem twiddle_diagonal_sphere_address_orbit_on_canonical_shell (addr : TwiddleFactorAddress)
    (hShell : TwiddlePermutationPreservesMaxAbsShell addr) :
    ∀ p ∈ twiddleOrbitVoxels addr, p ∈ latticeMaxAbsShell (twiddleVoxelShellLabel addr) := by
  intro p hp
  rcases mem_twiddle_orbit_voxels_iff addr p |>.mp hp with ⟨σ, hσ⟩
  subst hσ
  simp only [mem_latticeMaxAbsShell, twiddleVoxelShellLabel]
  exact hShell σ

noncomputable def twiddleDiagonalSphereAddress (addr : TwiddleFactorAddress)
    (h : isTwiddleTuple addr) : TwiddleDiagonalSphereAddress where
  addr := addr
  twiddle := h
  shell := twiddleVoxelShellLabel addr
  shell_eq := rfl
  orbit_voxels := twiddleOrbitVoxels addr
  orbit_voxels_eq := rfl
  orbit_on_diagonal := twiddle_diagonal_sphere_address_orbit_on_diagonal addr h
  orbit_on_own_shell := twiddle_diagonal_sphere_address_orbit_on_own_shell addr h
  orbit_on_canonical_shell := twiddle_diagonal_sphere_address_orbit_on_canonical_shell addr

/-! ## Canonical examples -/

theorem lattice_voxel_twiddle_222 :
    latticeVoxelOfTwiddleAddress twiddleAddress222 = ![2, 2, 2] := by
  funext i
  fin_cases i <;> simp [latticeVoxelOfTwiddleAddress, twiddleAddress222]

theorem twiddle_222_voxel_body_diagonal :
    LiesOnBodyDiagonal (latticeVoxelOfTwiddleAddress twiddleAddress222) := by
  dsimp [LiesOnBodyDiagonal, lattice_voxel_twiddle_222]
  exact ⟨rfl, rfl⟩

theorem twiddle_222_voxel_shell_label :
    twiddleVoxelShellLabel twiddleAddress222 = 2 := by
  dsimp [twiddleVoxelShellLabel, lattice_voxel_twiddle_222]
  exact maxNatAbsCoord_eq_natAbs_of_all_eq _ 2 rfl rfl rfl

theorem twiddle_222_voxel_on_lattice_sphere :
    latticeVoxelOfTwiddleAddress twiddleAddress222 ∈ latticeMaxAbsShell 2 := by
  simpa [twiddle_222_voxel_shell_label] using mem_twiddle_voxel_shell twiddleAddress222

theorem permute_twiddle_222_voxel_fixed (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    latticeVoxelOfPermutedTwiddle σ twiddleAddress222 i =
      latticeVoxelOfTwiddleAddress twiddleAddress222 i := by
  rw [lattice_voxel_permuted_eq_comp σ twiddleAddress222 i]
  have hc (j : Fin 3) : latticeVoxelOfTwiddleAddress twiddleAddress222 j = 2 := by
    fin_cases j <;> simp [latticeVoxelOfTwiddleAddress, twiddleAddress222]
  rw [hc, hc]

theorem permute_twiddle_222_voxel_fixed' (σ : Equiv.Perm (Fin 3)) :
    latticeVoxelOfPermutedTwiddle σ twiddleAddress222 =
      latticeVoxelOfTwiddleAddress twiddleAddress222 :=
  funext fun i => permute_twiddle_222_voxel_fixed σ i

theorem twiddle_222_permutation_preserves_shell :
    TwiddlePermutationPreservesMaxAbsShell twiddleAddress222 := by
  intro σ
  dsimp [TwiddlePermutationPreservesMaxAbsShell, twiddleVoxelShellLabel]
  rw [← permute_twiddle_222_voxel_fixed' σ]

theorem twiddle_222_orbit_voxels_singleton :
    twiddleOrbitVoxels twiddleAddress222 = {latticeVoxelOfTwiddleAddress twiddleAddress222} := by
  ext p
  simp only [mem_twiddle_orbit_voxels_iff, mem_singleton]
  constructor
  · rintro ⟨σ, hσ⟩
    simpa [permute_twiddle_222_voxel_fixed' σ] using hσ.symm
  · intro h
    refine ⟨Equiv.refl (Fin 3), ?_⟩
    simpa [latticeVoxelOfPermutedTwiddle, permute_twiddle_address_222_invariant] using h.symm

/-- `(m,m,1)` twiddle: a positive face-diagonal family on shell `max m 1`. -/
def twiddleAddressMM1 (m : ℕ) : TwiddleFactorAddress :=
  (m, m, 1)

theorem twiddle_address_mm1_twiddle (m : ℕ) : isTwiddleTuple (twiddleAddressMM1 m) := by
  dsimp [isTwiddleTuple, twiddleAddressMM1]
  exact Or.inl rfl

theorem twiddle_address_mm1_voxel_shell (m : ℕ) :
    twiddleVoxelShellLabel (twiddleAddressMM1 m) = max m 1 := by
  dsimp [twiddleVoxelShellLabel, twiddleAddressMM1]
  rw [maxNatAbsCoord_lattice_voxel_eq]
  simp [max_assoc, max_left_comm, max_comm]

/-! ## Link to partition address orbit -/

/--
The **partition** orbit (`twiddleAddressOrbit`) is the S₃ orbit on twiddle
**addresses**; the **voxel** orbit (`twiddleOrbitVoxels`) is the image on `ℤ³`.
Every address in the partition orbit addresses its corresponding voxel.
-/
theorem mem_twiddle_address_orbit_addresses_voxel (addr : TwiddleFactorAddress)
    (a : TwiddleFactorAddress) (ha : a ∈ twiddleAddressOrbit addr) :
    TwiddlePermutationAddressesVoxel addr (latticeVoxelOfTwiddleAddress a) := by
  rcases mem_image.mp ha with ⟨σ, _, hσ⟩
  refine ⟨σ, ?_⟩
  dsimp [latticeVoxelOfPermutedTwiddle]
  simpa [hσ]

theorem twiddle_address_orbit_subset_voxel_addresses (addr : TwiddleFactorAddress) :
    ∀ a ∈ twiddleAddressOrbit addr,
      latticeVoxelOfTwiddleAddress a ∈ twiddleOrbitVoxels addr := by
  intro a ha
  rcases mem_twiddle_address_orbit_addresses_voxel addr a ha with ⟨σ, hσ⟩
  exact mem_image.mpr ⟨σ, mem_univ _, hσ⟩

/-!
## Master geometric target (reframed)

Existence of a diagonal S³ partition witness (`EveryNontrivialZeroHasDiagonalS3Address`)
is unchanged; this module clarifies that the **geometric** content of the twiddle
cell is the **permutation orbit on diagonal lattice-sphere voxels**, with the
symmetric `(m,m,m)` / `π/(2+m)` chart as one special family.
-/

end

end Hqiv.Story

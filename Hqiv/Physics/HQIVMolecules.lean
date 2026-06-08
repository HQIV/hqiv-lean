import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

import Hqiv.Physics.HQIVAtoms
import Hqiv.Physics.HQIVNuclei
import Hqiv.Physics.DynamicCentreGeometry

/-!
# HQIV molecules: TorqueTree, fold energy, superposed densities (v2)

`TorqueTree m` fixes a common nuclear shell index `m` so `valleyPotentialEM` is
well-typed between parent and child nuclei (`AtomicSurfaceAt m`). `foldEnergy`
sums atomic electron-field energies and pairwise valley bonds.

The same tree + additive energy algebra applies **generically** to any hierarchical
assembly of interfaces (see `Hqiv.Physics.HQIVAssembly` for cross-domain naming:
grains, heterojunctions, nanoscale parts).

Induction on `TorqueTree` is the structural `TorqueTree.rec` from the nested
inductive definition. Native folds are global minima of the dihedral correction
`κ * (1 - cos θ)` at `cos θ = 1` (pole cancellation / saturated valleys).
-/

namespace Hqiv.Physics

/-- Folding `+` shifts the initial accumulator across the sum (`listSumR` helper). -/
theorem list_foldl_add_accum (xs : List ℝ) (a b : ℝ) :
    xs.foldl (fun acc x => acc + x) (a + b) = a + xs.foldl (fun acc x => acc + x) b := by
  induction xs generalizing a b with
  | nil => simp [List.foldl]
  | cons x xs ih =>
      calc
        xs.foldl (fun acc x => acc + x) ((a + b) + x) =
            xs.foldl (fun acc x => acc + x) (a + (b + x)) := by rw [add_assoc]
        _ = a + xs.foldl (fun acc x => acc + x) (b + x) := ih a (b + x)

/-- Sum of a real list. -/
noncomputable def listSumR (l : List ℝ) : ℝ :=
  l.foldl (fun acc x => acc + x) 0

@[simp] theorem listSumR_nil : listSumR ([] : List ℝ) = 0 := by simp [listSumR]

@[simp] theorem listSumR_singleton (x : ℝ) : listSumR [x] = x := by simp [listSumR]

theorem listSumR_cons (x : ℝ) (xs : List ℝ) : listSumR (x :: xs) = x + listSumR xs := by
  unfold listSumR
  rw [List.foldl_cons, add_comm (0 : ℝ) x, list_foldl_add_accum xs x 0]

theorem listSumR_append (l₁ l₂ : List ℝ) : listSumR (l₁ ++ l₂) = listSumR l₁ + listSumR l₂ := by
  induction l₁ with
  | nil =>
      simp [listSumR]
  | cons x xs ih =>
      simp [List.append, listSumR_cons, ih, add_assoc]

theorem listSumR_map_add (l : List α) (f g : α → ℝ) :
    listSumR (l.map fun a => f a + g a) = listSumR (l.map f) + listSumR (l.map g) := by
  induction l with
  | nil =>
      simp [listSumR]
  | cons x xs ih =>
      simp [List.map, listSumR_cons, ih, add_assoc, add_comm, add_left_comm]

theorem listSumR_map_abs_nonneg (l : List ℝ) : 0 ≤ listSumR (l.map fun x => |x|) := by
  induction l with
  | nil => simp [listSumR]
  | cons x xs ih =>
      rw [List.map_cons, listSumR_cons]
      exact add_nonneg (abs_nonneg x) ih

theorem listSumR_map_mul_left (c : ℝ) (l : List ℝ) :
    listSumR (l.map fun x => c * x) = c * listSumR l := by
  induction l with
  | nil => simp [listSumR]
  | cons x xs ih => simp [List.map, listSumR_cons, ih, mul_add, mul_assoc, add_comm, add_left_comm]

/-!
## Torque tree on `AtomicSurfaceAt m`
-/

/-- Molecular tree at fixed nuclear shell `m` (shared valley index for all bonds). -/
inductive TorqueTree (m : ℕ) : Type
  | leaf : AtomicSurfaceAt m → TorqueTree m
  | branch : AtomicSurfaceAt m → List (TorqueTree m) → TorqueTree m

def TorqueTree.rootAtom {m : ℕ} : TorqueTree m → AtomicSurfaceAt m
  | .leaf a => a
  | .branch a _ => a

def TorqueTree.WellFormed {m : ℕ} : TorqueTree m → Prop
  | .leaf _ => True
  | .branch _ ts => ∀ t ∈ ts, TorqueTree.WellFormed t

theorem TorqueTree.wf_leaf {m : ℕ} (a : AtomicSurfaceAt m) : TorqueTree.WellFormed (.leaf a) := by
  simp [TorqueTree.WellFormed]

theorem TorqueTree.wf_branch {m : ℕ} (a : AtomicSurfaceAt m) (ts : List (TorqueTree m))
    (h : ∀ t ∈ ts, TorqueTree.WellFormed t) : TorqueTree.WellFormed (.branch a ts) := by
  simpa [TorqueTree.WellFormed] using h

/-- Size bound for well-founded reasoning on `TorqueTree` (nested inductive has no `induction` tactic). -/
def torqueTreeSize {m : ℕ} : TorqueTree m → ℕ
  | .leaf _ => 1
  | .branch _ ts => 1 + (ts.map torqueTreeSize).foldl (· + ·) 0

theorem torqueTreeSize_pos {m : ℕ} (t : TorqueTree m) : 0 < torqueTreeSize t := by
  cases t <;> simp [torqueTreeSize, Nat.succ_pos, Nat.zero_lt_succ]

theorem Nat_list_foldl_add_init (l : List ℕ) (x : ℕ) : x + l.foldl (· + ·) 0 = l.foldl (· + ·) x := by
  induction l generalizing x with
  | nil => simp [List.foldl]
  | cons y ys ih =>
    -- `List.foldl_cons` exposes `ys.foldl` with the head absorbed into the accumulator.
    simp only [List.foldl_cons, Nat.zero_add]
    rw [(ih y).symm, ← Nat.add_assoc x y (ys.foldl (· + ·) 0), ih (x + y)]

theorem Nat_list_map_foldl_ge_mem {α : Type*} (ts : List α) (f : α → ℕ) (u : α) (hu : u ∈ ts) :
    f u ≤ (ts.map f).foldl (· + ·) 0 := by
  induction ts with
  | nil => cases hu
  | cons v vs ih =>
    simp only [List.mem_cons] at hu
    cases hu with
    | inl hEq =>
      have hf : f u = f v := congrArg f hEq
      rw [hf]
      simp only [List.map_cons, List.foldl, Nat.zero_add]
      rw [(Nat_list_foldl_add_init (List.map f vs) (f v)).symm]
      exact Nat.le_add_right (f v) ((List.map f vs).foldl (· + ·) 0)
    | inr hmem =>
      have ih' := ih hmem
      have hsum :=
        (Nat_list_foldl_add_init (List.map f vs) (f v)).symm
      simp only [List.map_cons, List.foldl, Nat.zero_add]
      rw [hsum]
      exact Nat.le_trans ih' (Nat.le_add_left ((List.map f vs).foldl (· + ·) 0) (f v))

theorem torqueTreeSize_mem_le_children_sum {m : ℕ} (ts : List (TorqueTree m)) (u : TorqueTree m)
    (hu : u ∈ ts) : torqueTreeSize u ≤ (ts.map torqueTreeSize).foldl (· + ·) 0 :=
  Nat_list_map_foldl_ge_mem ts torqueTreeSize u hu

theorem torqueTreeSize_mem_lt_branch {m : ℕ} (a : AtomicSurfaceAt m) (ts : List (TorqueTree m)) (u : TorqueTree m)
    (hu : u ∈ ts) : torqueTreeSize u < torqueTreeSize (.branch a ts) := by
  simpa [torqueTreeSize, Nat.succ_eq_add_one, Nat.add_comm] using
    Nat.lt_succ_of_le (torqueTreeSize_mem_le_children_sum ts u hu)

/-!
## Bond energy (shared `m`)
-/

/-- Valley+EM bond between two atoms at the same shell `m`. -/
noncomputable def bondValleyEM (Z_eff r : ℝ) {m : ℕ} (p c : AtomicSurfaceAt m) : ℝ :=
  valleyPotentialEM m (p.h ▸ p.surf.nucleus) (c.h ▸ c.surf.nucleus) Z_eff r

/-!
## Fold energy
-/

noncomputable def monopoleTorque {m : ℕ} (_ : TorqueTree m) : ℝ := 0

/-- Branch nodes carry no extra lumped torque beyond subtree recursion; with `monopoleTorque ≡ 0`
this matches the purely pairwise `bondValleyEM` picture in `assembly_foldEnergy_branch_eq`. -/
theorem listSumR_map_zero {α : Type*} (l : List α) : listSumR (l.map fun _ => (0 : ℝ)) = 0 := by
  induction l with
  | nil => simp [listSumR]
  | cons _ xs ih => simp only [List.map_cons, listSumR_cons, ih, add_zero]

theorem monopoleTorque_branch_eq_sum_children {m : ℕ} (a : AtomicSurfaceAt m) (ts : List (TorqueTree m)) :
    monopoleTorque (.branch a ts) = listSumR (ts.map monopoleTorque) := by
  simp [monopoleTorque]
  induction ts with
  | nil => simp [listSumR]
  | cons _ xs ih => simp [List.map, listSumR_cons, monopoleTorque, ih, add_zero]

noncomputable def sumAtomicElectronFieldEnergy {m : ℕ} (μ c Z_eff r : ℝ) : TorqueTree m → ℝ
  | .leaf a => atomic_electron_field_energy a.surf.nucleus_m a.Z μ c
  | .branch a ts =>
      atomic_electron_field_energy a.surf.nucleus_m a.Z μ c +
        listSumR (ts.map (sumAtomicElectronFieldEnergy μ c Z_eff r))

/-- Parent–child bond for valley bookkeeping (root site of the subtree). -/
theorem bondValleyEM_eq_root {m : ℕ} (Z_eff r : ℝ) (parent : AtomicSurfaceAt m) (t : TorqueTree m) :
    (match t with
        | .leaf child => bondValleyEM Z_eff r parent child
        | .branch child _ => bondValleyEM Z_eff r parent child) =
      bondValleyEM Z_eff r parent (TorqueTree.rootAtom t) := by
  cases t <;> rfl

noncomputable def sumValleyPotentialEM {m : ℕ} (μ c Z_eff r : ℝ) : TorqueTree m → ℝ
  | .leaf _ => 0
  | .branch parent ts =>
      listSumR (ts.map fun t => bondValleyEM Z_eff r parent (TorqueTree.rootAtom t)) +
        listSumR (ts.map (sumValleyPotentialEM μ c Z_eff r))

/-- Total fold energy at shell `m`. -/
noncomputable def foldEnergy {m : ℕ} (Z_eff r μ c : ℝ) (t : TorqueTree m) : ℝ :=
  sumValleyPotentialEM μ c Z_eff r t + sumAtomicElectronFieldEnergy μ c Z_eff r t +
    monopoleTorque t

theorem foldEnergy_def {m : ℕ} (Z_eff r μ c : ℝ) (t : TorqueTree m) :
    foldEnergy Z_eff r μ c t =
      sumValleyPotentialEM μ c Z_eff r t + sumAtomicElectronFieldEnergy μ c Z_eff r t +
        monopoleTorque t :=
  rfl

/-!
### Branch fold energy (used by path-shaped trees below)
-/

/-- **Branch decomposition:** energy of a parent `p` with children `ts` equals the parent's
atomic field term plus, for each child subtree, its own `foldEnergy` plus one **parent–root**
interface bond. Same algebra underlies protein subchains, grain clusters, and multi-junction
meshes. -/
theorem assembly_foldEnergy_branch_eq {m : ℕ} (Z_eff r μ c : ℝ) (p : AtomicSurfaceAt m) (ts : List (TorqueTree m)) :
    foldEnergy Z_eff r μ c (.branch p ts) =
      atomic_electron_field_energy p.surf.nucleus_m p.Z μ c +
        listSumR
          (ts.map fun t =>
            foldEnergy Z_eff r μ c t + bondValleyEM Z_eff r p (TorqueTree.rootAtom t)) := by
  induction ts with
  | nil =>
      simp [foldEnergy, sumValleyPotentialEM, sumAtomicElectronFieldEnergy, monopoleTorque, listSumR]
  | cons u us ih =>
      have hsplit :
          foldEnergy Z_eff r μ c (.branch p (u :: us)) =
            foldEnergy Z_eff r μ c u + bondValleyEM Z_eff r p (TorqueTree.rootAtom u) +
              foldEnergy Z_eff r μ c (.branch p us) := by
        unfold foldEnergy sumValleyPotentialEM sumAtomicElectronFieldEnergy monopoleTorque
        have hmap :
            (u :: us).map (fun t => bondValleyEM Z_eff r p (TorqueTree.rootAtom t)) =
              bondValleyEM Z_eff r p (TorqueTree.rootAtom u) ::
                us.map (fun t => bondValleyEM Z_eff r p (TorqueTree.rootAtom t)) := by
          simp [List.map_cons]
        simp_rw [hmap, List.map_cons, listSumR_cons]
        cases u <;> simp only [foldEnergy, sumValleyPotentialEM, sumAtomicElectronFieldEnergy, monopoleTorque,
          TorqueTree.rootAtom, add_assoc, add_comm, add_left_comm] <;> ring
      rw [hsplit, ih]
      simp [List.map, listSumR_cons, add_assoc, add_comm, add_left_comm]

/-- Corollary: two-child star (e.g. bridge site between two grains / ligands). -/
theorem assembly_foldEnergy_binary_branch {m : ℕ} (Z_eff r μ c : ℝ) (p : AtomicSurfaceAt m) (t₁ t₂ : TorqueTree m) :
    foldEnergy Z_eff r μ c (.branch p [t₁, t₂]) =
      atomic_electron_field_energy p.surf.nucleus_m p.Z μ c + foldEnergy Z_eff r μ c t₁ +
        foldEnergy Z_eff r μ c t₂ + bondValleyEM Z_eff r p (TorqueTree.rootAtom t₁) +
        bondValleyEM Z_eff r p (TorqueTree.rootAtom t₂) := by
  rw [assembly_foldEnergy_branch_eq]
  simp [List.map, listSumR_cons, listSumR_nil, add_assoc, add_comm, add_left_comm]

/-!
### Structural induction (branch bonds = `valleyPotentialEM` summands)
-/

/-- Induction on `TorqueTree`: every molecule is either a leaf atom or a branch whose
subtrees are built the same way; bond energy at each `branch` is a sum of
`bondValleyEM` / `valleyPotentialEM` edges. -/
theorem molecule_from_atoms_inductive {m : ℕ} (P : TorqueTree m → Prop)
    (h_leaf : ∀ a, P (.leaf a))
    (h_branch : ∀ (a : AtomicSurfaceAt m) (ts : List (TorqueTree m)),
        (∀ t ∈ ts, P t) → P (.branch a ts)) :
    ∀ t, TorqueTree.WellFormed t → P t := by
  intro t ht
  exact @Nat.strong_induction_on (fun (k : ℕ) => ∀ u : TorqueTree m, torqueTreeSize u = k → TorqueTree.WellFormed u → P u)
      (torqueTreeSize t) (fun n ih => by
        intro u hn hwf
        cases u with
        | leaf a =>
          simp only [torqueTreeSize] at hn
          have hn1 : n = 1 := hn.symm
          subst hn1
          exact h_leaf a
        | branch a ts =>
          have hw : ∀ t ∈ ts, TorqueTree.WellFormed t := by simpa [TorqueTree.WellFormed] using hwf
          exact h_branch a ts fun t' ht' => by
            have hlt := torqueTreeSize_mem_lt_branch a ts t' ht'
            have hltn : torqueTreeSize t' < n := by
              rw [← hn]
              exact hlt
            exact ih (torqueTreeSize t') hltn t' rfl (hw t' ht')
      ) t rfl ht

theorem molecule_valleys_additive_like_helium4 :
    valleyCount helium4 = 6 :=
  helium4_valleyCount

/-!
## Native fold = global minimum of the dihedral correction (κ ≥ 0)
-/

noncomputable def foldEnergyWithDihedral {m : ℕ} (κ θ Z_eff r μ c : ℝ) (t : TorqueTree m) : ℝ :=
  foldEnergy Z_eff r μ c t + κ * (1 - Real.cos θ)

theorem foldEnergyWithDihedral_ge_foldEnergy {m : ℕ} (κ θ Z_eff r μ c : ℝ) (t : TorqueTree m)
    (hκ : 0 ≤ κ) :
    foldEnergy Z_eff r μ c t ≤ foldEnergyWithDihedral κ θ Z_eff r μ c t := by
  unfold foldEnergyWithDihedral
  linarith [dihedral_penalty_nonneg κ θ hκ]

/-- Equality (native fold) holds exactly when the dihedral correction vanishes; for `κ ≠ 0`,
this is `cos θ = 1` (pole cancellation / `pole_cancellation_saturates_valleys`). -/
theorem minimum_energy_fold_is_native {m : ℕ} (κ θ Z_eff r μ c : ℝ) (t : TorqueTree m)
    (hκ : κ ≠ 0) :
    foldEnergyWithDihedral κ θ Z_eff r μ c t = foldEnergy Z_eff r μ c t ↔ Real.cos θ = 1 := by
  unfold foldEnergyWithDihedral
  constructor
  · intro h
    have hdiff : κ * (1 - Real.cos θ) = 0 := by
      have := congr_arg (fun z => z - foldEnergy Z_eff r μ c t) h
      simp only [add_sub_cancel_right] at this
      linarith
    have h1 : 1 - Real.cos θ = 0 := by
      rcases (mul_eq_zero.mp hdiff) with hκ0 | h1
      · exact absurd hκ0 hκ
      · exact h1
    linarith [h1]
  · intro hcos
    have h1 : 1 - Real.cos θ = 0 := by
      rw [hcos]
      simp
    simp [h1]

/-- Same pole-minimization statement with an additive shift `hb` on both sides (e.g. a fixed
contact bookkeeping term that does not couple to the fold dihedral). -/
theorem augmented_minimum_energy_fold_is_native {m : ℕ} (κ θFold Z_eff r μ c : ℝ) (hb : ℝ) (t : TorqueTree m)
    (hκ : κ ≠ 0) :
    foldEnergyWithDihedral κ θFold Z_eff r μ c t + hb =
        foldEnergy Z_eff r μ c t + hb ↔ Real.cos θFold = 1 := by
  unfold foldEnergyWithDihedral
  constructor
  · intro h
    have hdiff : κ * (1 - Real.cos θFold) = 0 := by
      have := congr_arg (fun z => z - foldEnergy Z_eff r μ c t - hb) h
      simp only [add_assoc, add_sub_cancel_right] at this
      linarith
    have h1 : 1 - Real.cos θFold = 0 := by
      rcases (mul_eq_zero.mp hdiff) with hκ0 | h1
      · exact absurd hκ0 hκ
      · exact h1
    have : Real.cos θFold = 1 := by linarith [h1]
    exact this
  · intro hcos
    have h1 : 1 - Real.cos θFold = 0 := by rw [hcos]; simp
    simp [h1, add_assoc]

theorem minimum_energy_fold_deriv_dihedral_vanishes (κ : ℝ) (hκ : κ ≠ 0) :
    deriv (fun θ : ℝ => κ * (1 - Real.cos θ)) 0 = 0 :=
  allowed_binding_angles_minimize_budget κ hκ

/-!
## Ligand docking (single bond split)
-/

/-- A ligand `L` docked to receptor `R` adds exactly one `bondValleyEM` on top of the
atomic electron-field energies of the two fragments. -/
theorem ligand_docking_energy {m : ℕ} (Z_eff r μ c : ℝ) (R L : AtomicSurfaceAt m) :
    foldEnergy Z_eff r μ c (.branch R [.leaf L]) =
      foldEnergy Z_eff r μ c (.leaf R) + foldEnergy Z_eff r μ c (.leaf L) +
        bondValleyEM Z_eff r R L := by
  unfold foldEnergy sumValleyPotentialEM sumAtomicElectronFieldEnergy monopoleTorque
  simp [listSumR, sumValleyPotentialEM, sumAtomicElectronFieldEnergy, TorqueTree.rootAtom]
  ring

/-!
## Path-shaped `TorqueTree` (sequential backbone, e.g. Cα chain)
-/

/-- Path graph rooted at the head: each residue bonds only to the next (`branch` with one child). -/
noncomputable def pathTorqueTree {m : ℕ} : (l : List (AtomicSurfaceAt m)) → l ≠ [] → TorqueTree m
  | [], h => False.elim (h rfl)
  | [a], _ => .leaf a
  | a :: b :: rest, _ => .branch a [pathTorqueTree (b :: rest) (List.cons_ne_nil b rest)]

theorem pathTorqueTree_root {m : ℕ} (a : AtomicSurfaceAt m) (as : List (AtomicSurfaceAt m)) (h : a :: as ≠ []) :
    TorqueTree.rootAtom (pathTorqueTree (a :: as) h) = a := by
  cases as with
  | nil => rfl
  | cons b rest => rfl

theorem pathTorqueTree_wellFormed {m : ℕ} (l : List (AtomicSurfaceAt m)) (hl : l ≠ []) :
    TorqueTree.WellFormed (pathTorqueTree l hl) := by
  induction l with
  | nil => contradiction
  | cons a l' ih =>
    cases l' with
    | nil =>
        exact TorqueTree.wf_leaf a
    | cons b rest =>
        refine TorqueTree.wf_branch a [pathTorqueTree (b :: rest) _] ?_
        intro t ht
        simp only [List.mem_singleton] at ht
        subst ht
        exact ih (List.cons_ne_nil b rest)

/-- Sum of `bondValleyEM` along consecutive backbone sites. -/
noncomputable def listConsecutiveBondEM (Z_eff r : ℝ) {m : ℕ} : List (AtomicSurfaceAt m) → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => bondValleyEM Z_eff r a b + listConsecutiveBondEM Z_eff r (b :: rest)

/-- Per-site `atomic_electron_field_energy` along a backbone list. -/
noncomputable def listAtomicFieldEnergy (μ c : ℝ) {m : ℕ} (l : List (AtomicSurfaceAt m)) : ℝ :=
  listSumR (l.map fun a => atomic_electron_field_energy a.surf.nucleus_m a.Z μ c)

theorem path_foldEnergy_eq_sum_bonds_and_atoms {m : ℕ} (Z_eff r μ c : ℝ) (l : List (AtomicSurfaceAt m))
    (hl : l ≠ []) :
    foldEnergy Z_eff r μ c (pathTorqueTree l hl) =
      listAtomicFieldEnergy μ c l + listConsecutiveBondEM Z_eff r l := by
  induction l with
  | nil => contradiction
  | cons a l' ih =>
    cases l' with
    | nil =>
        simp [pathTorqueTree, foldEnergy, sumValleyPotentialEM, sumAtomicElectronFieldEnergy, monopoleTorque,
          listAtomicFieldEnergy, listConsecutiveBondEM, listSumR]
    | cons b rest =>
        have hsub : b :: rest ≠ [] := List.cons_ne_nil b rest
        have hroot := pathTorqueTree_root b rest hsub
        calc
          foldEnergy Z_eff r μ c (pathTorqueTree (a :: b :: rest) hl) =
              foldEnergy Z_eff r μ c (.branch a [pathTorqueTree (b :: rest) hsub]) := rfl
          _ = atomic_electron_field_energy a.surf.nucleus_m a.Z μ c +
                foldEnergy Z_eff r μ c (pathTorqueTree (b :: rest) hsub) +
                bondValleyEM Z_eff r a (TorqueTree.rootAtom (pathTorqueTree (b :: rest) hsub)) := by
                rw [assembly_foldEnergy_branch_eq]; simp [listSumR, List.map, add_assoc]
          _ = atomic_electron_field_energy a.surf.nucleus_m a.Z μ c +
                foldEnergy Z_eff r μ c (pathTorqueTree (b :: rest) hsub) + bondValleyEM Z_eff r a b := by
                simp [add_assoc, hroot]
          _ = atomic_electron_field_energy a.surf.nucleus_m a.Z μ c +
                (listAtomicFieldEnergy μ c (b :: rest) + listConsecutiveBondEM Z_eff r (b :: rest)) +
                bondValleyEM Z_eff r a b := by
                rw [ih hsub]
          _ = listAtomicFieldEnergy μ c (a :: b :: rest) + listConsecutiveBondEM Z_eff r (a :: b :: rest) := by
                simp [listAtomicFieldEnergy, listConsecutiveBondEM, listSumR_cons, List.map_cons, add_assoc,
                  add_comm, add_left_comm]

/-- Node count for structural recursion (each `leaf` / `branch` head is one step). -/
def torqueTreeNodes {m : ℕ} : TorqueTree m → ℕ
  | .leaf _ => 1
  | .branch _ ts => 1 + (ts.map torqueTreeNodes).foldl (· + ·) 0

theorem path_torqueTree_nodes_eq_length {m : ℕ} (l : List (AtomicSurfaceAt m)) (hl : l ≠ []) :
    torqueTreeNodes (pathTorqueTree l hl) = l.length := by
  induction l with
  | nil => contradiction
  | cons a l' ih =>
    cases l' with
    | nil => simp [pathTorqueTree, torqueTreeNodes, List.map, List.foldl]
    | cons b rest =>
        have hsub : b :: rest ≠ [] := List.cons_ne_nil b rest
        simp [pathTorqueTree, torqueTreeNodes, List.map, List.foldl, Nat.add_assoc, Nat.add_comm, ih hsub]

/-- Evaluating `foldEnergy` / `sumValleyPotentialEM` on `pathTorqueTree` unrolls once per residue along the
backbone (Θ(n) scalar adds for fixed `m`, matching a sequential neighbor list in code). -/
theorem path_foldEnergy_linear_in_nodes {m : ℕ} (l : List (AtomicSurfaceAt m)) (hl : l ≠ []) :
    torqueTreeNodes (pathTorqueTree l hl) = l.length :=
  path_torqueTree_nodes_eq_length l hl

theorem path_sumValley_eq_consecutive_bonds {m : ℕ} (μ c Z_eff r : ℝ) (l : List (AtomicSurfaceAt m))
    (hl : l ≠ []) :
    sumValleyPotentialEM μ c Z_eff r (pathTorqueTree l hl) = listConsecutiveBondEM Z_eff r l := by
  induction l with
  | nil => contradiction
  | cons a l' ih =>
    cases l' with
    | nil => simp [pathTorqueTree, sumValleyPotentialEM, listConsecutiveBondEM, listSumR]
    | cons b rest =>
        have hsub : b :: rest ≠ [] := List.cons_ne_nil b rest
        have hroot := pathTorqueTree_root b rest hsub
        calc
          sumValleyPotentialEM μ c Z_eff r (pathTorqueTree (a :: b :: rest) hl) =
              sumValleyPotentialEM μ c Z_eff r (.branch a [pathTorqueTree (b :: rest) hsub]) := rfl
          _ = bondValleyEM Z_eff r a (TorqueTree.rootAtom (pathTorqueTree (b :: rest) hsub)) +
                sumValleyPotentialEM μ c Z_eff r (pathTorqueTree (b :: rest) hsub) := by
                simp [sumValleyPotentialEM, listSumR, List.map, bondValleyEM_eq_root]
          _ = bondValleyEM Z_eff r a b + sumValleyPotentialEM μ c Z_eff r (pathTorqueTree (b :: rest) hsub) := by
                rw [hroot]
          _ = bondValleyEM Z_eff r a b + listConsecutiveBondEM Z_eff r (b :: rest) := by rw [ih hsub]
          _ = listConsecutiveBondEM Z_eff r (a :: b :: rest) := rfl

/-!
### Generic hierarchical assembly (any domain: biomolecules, grains, heterojunctions, …)

`TorqueTree` is a **tree of bonded sites** sharing one horizon shell `m`. The same
additive energy bookkeeping applies whenever interfaces are modelled as pairwise
`valleyPotentialEM` edges plus per-site `atomic_electron_field_energy` budgets.

Branch decomposition lemmas live earlier as `assembly_foldEnergy_branch_eq`.
-/

/-- Two ligands `L₁`, `L₂` on the same receptor site `R`: two `bondValleyEM` edges, three leaf budgets. -/
theorem ligand_docking_energy_two_leaves {m : ℕ} (Z_eff r μ c : ℝ) (R L₁ L₂ : AtomicSurfaceAt m) :
    foldEnergy Z_eff r μ c (.branch R [.leaf L₁, .leaf L₂]) =
      foldEnergy Z_eff r μ c (.leaf R) + foldEnergy Z_eff r μ c (.leaf L₁) +
        foldEnergy Z_eff r μ c (.leaf L₂) + bondValleyEM Z_eff r R L₁ + bondValleyEM Z_eff r R L₂ := by
  rw [assembly_foldEnergy_binary_branch]
  simp [foldEnergy, sumValleyPotentialEM, sumAtomicElectronFieldEnergy, monopoleTorque, listSumR, TorqueTree.rootAtom,
    add_assoc, add_comm, add_left_comm]

/-!
## Electron density superposition
-/

noncomputable def rhoProtein (ms : List ℕ) : ℝ :=
  listSumR (ms.map fun m => (availableModesNat m : ℝ) / R_m m)

theorem protein_electron_density_superposition (ms : List ℕ) :
    rhoProtein ms = listSumR (ms.map fun m => (Hqiv.available_modes m) / R_m m) := by
  unfold rhoProtein
  simp_rw [availableModesNat_cast]

/-- Example tripeptide shell stack (three identical shells) for density bookkeeping. -/
noncomputable def tripeptide_density_map_example : ℝ :=
  rhoProtein [3, 3, 3]

/-!
## Dynamic H₂O centre angle (TUFT steric geometry; no tabulated degree anchor)
-/

/-- H–O–H angle in radians from dynamic steric geometry (period-2 O, two bonds). -/
noncomputable def waterDynamicCentreAngleRad : ℝ := dynamicCentreAngleRad 8 2

/-- Legacy degree alias for witnesses (computed from radians, not a separate constant). -/
noncomputable def waterBondAngleDeg : ℝ :=
  waterDynamicCentreAngleRad * 180 / Real.pi

theorem waterBondAngleDeg_from_dynamic_radians :
    waterBondAngleDeg = waterDynamicCentreAngleRad * 180 / Real.pi := rfl

theorem water_dynamic_angle_positive : 0 < waterDynamicCentreAngleRad :=
  dynamicCentreAngleRad_water_pos

/-!
## Examples
-/

noncomputable def h2_fold_example {m : ℕ} (Z_eff r μ c : ℝ) (a : AtomicSurfaceAt m) : ℝ :=
  foldEnergy Z_eff r μ c (.leaf a)

noncomputable def water_fold_example {m : ℕ} (Z_eff r μ c : ℝ) (o h₁ h₂ : AtomicSurfaceAt m) : ℝ :=
  foldEnergy Z_eff r μ c (.branch o [.leaf h₁, .leaf h₂])

end Hqiv.Physics

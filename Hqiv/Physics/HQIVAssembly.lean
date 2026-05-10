import Hqiv.Physics.HQIVMolecules

/-!
# Generic hierarchical assembly (HQIV)

This module packages the **same** mathematical objects used for biomolecular folding
(`TorqueTree`, `foldEnergy`) under **domain-neutral** names:

* **Polycrystalline metals:** `TorqueTree` = tree of grains / sub-grains; `bondValleyEM` =
  grain-boundary or phase-interface energy; `foldEnergy` = total interface + bulk-site budget.
* **Semiconductors:** junction tree (epi layers, heterointerfaces); shared shell `m` = common
  horizon index for matched Brillouin / Casimir bookkeeping.
* **Nanoscale manufacturing:** part–part attachment graph with pairwise EM+valley edges.

All theorems are proved in `HQIVMolecules`; this file is the **conceptual bridge** so
applications share one formal substrate without biology-specific naming. (Long-range contact
scaffolding lives in `Hqiv.Archive.Physics.HQIVLongRange` and is not part of default builds.)
-/

namespace Hqiv.Physics

/-- Site carrying atomic Casimir data at a fixed horizon shell (generic “node”). -/
abbrev AssemblySite (m : ℕ) :=
  AtomicSurfaceAt m

/-- Hierarchical bonding graph at shell `m` (generic “assembly tree”). -/
abbrev AssemblyGraph (m : ℕ) :=
  TorqueTree m

/-- Structural induction on any assembly graph (same as `molecule_from_atoms_inductive`). -/
theorem assembly_graph_inductive {m : ℕ} (P : TorqueTree m → Prop)
    (h_leaf : ∀ a : AssemblySite m, P (.leaf a))
    (h_branch : ∀ (a : AssemblySite m) (ts : List (TorqueTree m)),
        (∀ t ∈ ts, P t) → P (.branch a ts)) :
    ∀ t, TorqueTree.WellFormed t → P t :=
  molecule_from_atoms_inductive P h_leaf h_branch

/-- Total assembly / folding energy (interfaces + site budgets). -/
noncomputable abbrev assemblyEnergy {m : ℕ} (Z_eff r μ c : ℝ) (g : AssemblyGraph m) : ℝ :=
  foldEnergy Z_eff r μ c g

/-- Branch energy = parent site budget + Σ (subtree + one parent–root interface). -/
theorem assembly_energy_branch_decomposition {m : ℕ} (Z_eff r μ c : ℝ) (p : AssemblySite m)
    (ts : List (AssemblyGraph m)) :
    assemblyEnergy Z_eff r μ c (.branch p ts) =
      atomic_electron_field_energy p.surf.nucleus_m p.Z μ c +
        listSumR
          (ts.map fun t =>
            assemblyEnergy Z_eff r μ c t + bondValleyEM Z_eff r p (TorqueTree.rootAtom t)) :=
  assembly_foldEnergy_branch_eq Z_eff r μ c p ts

/-- Linear backbone (e.g. sequential Cα proxies): same bond-sum + per-site field split as
`assembly_foldEnergy_branch_eq` specialized to a path child list (`HQIVMolecules.path_foldEnergy_eq_sum_bonds_and_atoms`). -/
theorem assembly_path_foldEnergy_eq {m : ℕ} (Z_eff r μ c : ℝ) (l : List (AssemblySite m)) (hl : l ≠ []) :
    assemblyEnergy Z_eff r μ c (pathTorqueTree l hl) =
      listAtomicFieldEnergy μ c l + listConsecutiveBondEM Z_eff r l :=
  path_foldEnergy_eq_sum_bonds_and_atoms Z_eff r μ c l hl

/-- Superposed mode-density stack (e.g. shell-resolved occupancy in any layered solid). -/
noncomputable abbrev rho_layered_stack (ms : List ℕ) : ℝ :=
  rhoProtein ms

theorem layered_stack_density_superposition (ms : List ℕ) :
    rho_layered_stack ms = listSumR (ms.map fun m => (Hqiv.available_modes m) / R_m m) :=
  protein_electron_density_superposition ms

/-- Dihedral-style penalty plus an additive shift `hb`: native alignment unchanged (`HQIVMolecules`). -/
theorem assembly_dihedral_argmin_unchanged_by_contact {m : ℕ} (κ θFold Z_eff r μ c : ℝ) (hb : ℝ)
    (t : AssemblyGraph m) (hκ : κ ≠ 0) :
    foldEnergyWithDihedral κ θFold Z_eff r μ c t + hb =
        foldEnergy Z_eff r μ c t + hb ↔ Real.cos θFold = 1 :=
  augmented_minimum_energy_fold_is_native κ θFold Z_eff r μ c hb t hκ

end Hqiv.Physics

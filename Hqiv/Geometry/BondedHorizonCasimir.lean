import Hqiv.Geometry.NuclearTorusPerturbation

/-!
# Bonded horizons: dissociation surplus from joint vs separated perturbed ladders

Given **one** global `S⁷` metahorizon and the **same** `perturbedCasimirEnergy` on each fragment,
the **surplus**
`P(N_total) - P(N_frag₁) - P(N_frag₂)` measures how much the **joint** Pauli filling + associator
imprint on `occupationList N_total` differs from treating the two pieces as **independent** Fermi
seas (same nuclear torus background `cfg`).

This is the minimal **parameter-free** bond-energy scaffold:

* **Ionic narrative** — far-separated fragments: use `N_total = N_frag₁ + N_frag₂` with integer
  electron counts per fragment (charge neutrality is a chemistry constraint, not enforced here).
* **Covalent narrative** — shared sea: same surplus formula; a symmetric split is the two-electron
  dimer witness `N_total = 2`, `N_frag₁ = N_frag₂ = 1`.
* **Metallic narrative** — delocalized bulk vs localized peel: same formula with a peel count
  `N_peel` and bulk `N_bulk = N_total - N_peel`.

**Sign:** binding corresponds to **negative** surplus (joint lower than sum of parts) in a
thermodynamic convention where lower `perturbedCasimirEnergy` is deeper.  The raw surplus here is
`joint - separated`; negate for “binding energy” if desired.

All **eV** values use the single hydrogen anchor `eVPerLambdaUnit_S7HydrogenAnchor` from
`S7MetahorizonCasimir` (no new scales).
-/

namespace Hqiv.Geometry

/-!
## Generic joint − separated surplus
-/

/--
**Dimensionless** dissociation-style surplus:
`perturbedCasimirEnergy(N_total) - perturbedCasimirEnergy(N₁) - perturbedCasimirEnergy(N₂)`.

The joint ladder uses a **single** greedy `occupationList N_total`; fragments use **independent**
lists at `N₁` and `N₂` — this is exactly where non-additivity (bonding bookkeeping) appears.
-/
noncomputable def bondHorizonSurplusDimless (N_total N_frag₁ N_frag₂ : ℕ)
    (cfg : NuclearTorusConfig := defaultNuclearTorus) : ℝ :=
  perturbedCasimirEnergy N_total cfg
    - perturbedCasimirEnergy N_frag₁ cfg
    - perturbedCasimirEnergy N_frag₂ cfg

/-- Same surplus in **eV** (hydrogen λ-anchor). -/
noncomputable def bondHorizonSurplus_eV (N_total N_frag₁ N_frag₂ : ℕ)
    (cfg : NuclearTorusConfig := defaultNuclearTorus) : ℝ :=
  bondHorizonSurplusDimless N_total N_frag₁ N_frag₂ cfg * eVPerLambdaUnit_S7HydrogenAnchor

@[simp]
theorem bondHorizonSurplus_eV_eq (N_total N_frag₁ N_frag₂ : ℕ) (cfg : NuclearTorusConfig) :
    bondHorizonSurplus_eV N_total N_frag₁ N_frag₂ cfg =
      bondHorizonSurplusDimless N_total N_frag₁ N_frag₂ cfg * eVPerLambdaUnit_S7HydrogenAnchor := rfl

/-!
## Named scenarios (same formula; narrative differs only in how `(N_total, N₁, N₂)` is chosen)
-/

/--
**Ionic-style** balanced electron count: `N_total = N₁ + N₂`, fragments carry `N₁` and `N₂`
electrons separately (minimal associator overlap story in prose).
-/
noncomputable def ionicBondSurplusDimless (N_frag₁ N_frag₂ : ℕ)
    (cfg : NuclearTorusConfig := defaultNuclearTorus) : ℝ :=
  bondHorizonSurplusDimless (N_frag₁ + N_frag₂) N_frag₁ N_frag₂ cfg

noncomputable def ionicBondSurplus_eV (N_frag₁ N_frag₂ : ℕ)
    (cfg : NuclearTorusConfig := defaultNuclearTorus) : ℝ :=
  ionicBondSurplusDimless N_frag₁ N_frag₂ cfg * eVPerLambdaUnit_S7HydrogenAnchor

/--
**Covalent two-electron dimer** witness: joint 2-electron sea vs two 1-electron fragments
(`H₂`-style electron count for the toy ladder).
-/
noncomputable def covalentDimerTwoElectronSurplusDimless
    (cfg : NuclearTorusConfig := defaultNuclearTorus) : ℝ :=
  bondHorizonSurplusDimless 2 1 1 cfg

noncomputable def covalentDimerTwoElectronSurplus_eV
    (cfg : NuclearTorusConfig := defaultNuclearTorus) : ℝ :=
  covalentDimerTwoElectronSurplusDimless cfg * eVPerLambdaUnit_S7HydrogenAnchor

/--
**Metallic peel**: bulk holds `N_bulk` electrons, localized peel `N_peel`, total `N_bulk + N_peel`.
-/
noncomputable def metallicPeelSurplusDimless (N_bulk N_peel : ℕ)
    (cfg : NuclearTorusConfig := defaultNuclearTorus) : ℝ :=
  bondHorizonSurplusDimless (N_bulk + N_peel) N_bulk N_peel cfg

noncomputable def metallicPeelSurplus_eV (N_bulk N_peel : ℕ)
    (cfg : NuclearTorusConfig := defaultNuclearTorus) : ℝ :=
  metallicPeelSurplusDimless N_bulk N_peel cfg * eVPerLambdaUnit_S7HydrogenAnchor

/-! ## First dissociation-scale witness (two-electron joint vs separated) -/

/-- First **two-electron** dissociation surplus (dimensionless), same as `covalentDimerTwoElectronSurplusDimless`. -/
noncomputable def firstDissociationTwoElectronSurplusDimless
    (cfg : NuclearTorusConfig := defaultNuclearTorus) : ℝ :=
  covalentDimerTwoElectronSurplusDimless cfg

noncomputable def firstDissociationTwoElectronSurplus_eV
    (cfg : NuclearTorusConfig := defaultNuclearTorus) : ℝ :=
  covalentDimerTwoElectronSurplus_eV cfg

end Hqiv.Geometry

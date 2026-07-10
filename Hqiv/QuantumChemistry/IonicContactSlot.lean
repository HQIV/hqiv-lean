import Hqiv.Geometry.BondedHorizonCasimir

/-!
# Ionic contact slots on the curvature contact network

Structural link: **ionic bonds use the same joint−separated horizon surplus**
as covalent bonds; only the electron-count partition `(N₁, N₂)` differs
(`BondedHorizonCasimir.ionicBondSurplus`).

Python witnesses: ``scripts/hqiv_ionic_bond_network.py``,
``scripts/hqiv_salt_phase_response.py`` (melting point + solid refractive index).

Numerics and phase diagrams remain in Python; this module records the
shared-spine theorems only.
-/

namespace Hqiv.QuantumChemistry

open Hqiv.Geometry

/-- Ionic surplus is the bond surplus on summed electron seas (definition bridge). -/
theorem ionicBondSurplus_eq_bondHorizonSurplus_sum (N₁ N₂ : ℕ) (cfg : NuclearTorusConfig) :
    ionicBondSurplusDimless N₁ N₂ cfg =
      bondHorizonSurplusDimless (N₁ + N₂) N₁ N₂ cfg := rfl

/-- Ionic eV readout uses the same hydrogen λ-anchor as covalent bond surplus. -/
theorem ionicBondSurplus_eV_eq_scale (N₁ N₂ : ℕ) (cfg : NuclearTorusConfig) :
    ionicBondSurplus_eV N₁ N₂ cfg =
      ionicBondSurplusDimless N₁ N₂ cfg * eVPerLambdaUnit_S7HydrogenAnchor := by
  rfl

/--
Light-cation Casimir promotion on alkali–halide routes:
``N_cation_eff = max(N_cation, Z_anion)``.

Li⁺ (N=2) is lifted to the partner nuclear-charge floor so surplus sits on the
same plateau as Na⁺/K⁺ salts.  Python: ``ionic_surplus_electron_counts``.
-/
def ionicSurplusCationElectronCount (nCation zAnion : ℕ) : ℕ :=
  max nCation zAnion

theorem ionicSurplusCationElectronCount_ge_cation (nCation zAnion : ℕ) :
    nCation ≤ ionicSurplusCationElectronCount nCation zAnion :=
  Nat.le_max_left _ _

theorem ionicSurplusCationElectronCount_ge_anion_Z (nCation zAnion : ℕ) :
    zAnion ≤ ionicSurplusCationElectronCount nCation zAnion :=
  Nat.le_max_right _ _

theorem ionicSurplusCationElectronCount_LiF :
    ionicSurplusCationElectronCount 2 9 = 9 := rfl

end Hqiv.QuantumChemistry

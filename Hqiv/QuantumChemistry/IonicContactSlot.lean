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

end Hqiv.QuantumChemistry

import Hqiv.Geometry.BondedHorizonCasimir

/-!
# Metallic contact slots on the curvature contact network

Structural link: **metallic bonds use the peel surplus**
`metallicPeelSurplusDimless N_bulk N_peel` — joint electron sea vs separated
delocalized bulk and localized peel (`BondedHorizonCasimir`).

Python witnesses: ``scripts/hqiv_metallic_bond_network.py``,
``scripts/hqiv_metallic_phase_response.py`` (melting point + solid ρ).

Numerics and phase diagrams remain in Python; this module records the
shared-spine theorems only.
-/

namespace Hqiv.QuantumChemistry

open Hqiv.Geometry

/-- Metallic peel surplus is the bond surplus on bulk + peel partition (definition bridge). -/
theorem metallicPeelSurplus_eq_bondHorizonSurplus_sum (N_bulk N_peel : ℕ) (cfg : NuclearTorusConfig) :
    metallicPeelSurplusDimless N_bulk N_peel cfg =
      bondHorizonSurplusDimless (N_bulk + N_peel) N_bulk N_peel cfg := rfl

/-- Metallic eV readout uses the same hydrogen λ-anchor as ionic / covalent surplus. -/
theorem metallicPeelSurplus_eV_eq_scale (N_bulk N_peel : ℕ) (cfg : NuclearTorusConfig) :
    metallicPeelSurplus_eV N_bulk N_peel cfg =
      metallicPeelSurplusDimless N_bulk N_peel cfg * eVPerLambdaUnit_S7HydrogenAnchor := by
  rfl

end Hqiv.QuantumChemistry

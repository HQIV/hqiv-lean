# TUFT (Nielsen) → HQIV mass-spectrum mining

**Source:** Jenny Lorraine Nielsen, *Topological Unified Field Theory on the Complex Hopf Fibration* (TUFT). PhilArchive [`NIETTU`](https://philarchive.org/rec/NIETTU). Bib: `NielsenTUFT2026`.

**Lean entry points:**

- [`Hqiv/Physics/HopfShellBeltramiMassBridge.lean`](../Hqiv/Physics/HopfShellBeltramiMassBridge.lean)
- [`Hqiv/Physics/HalfStepBeltramiShellBridge.lean`](../Hqiv/Physics/HalfStepBeltramiShellBridge.lean) — `4/3` vs half-step `ξ_G`
- [`Hqiv/Physics/FanoActionToDetuningJet.lean`](../Hqiv/Physics/FanoActionToDetuningJet.lean) — 8-channel action → 1-jet → `detunedShellSurface`

---

## What we imported (high value)

### 1. Beltrami spectrum on `S³` ↔ existing HQIV sphere data

TUFT: coexact Beltrami operator `B = ⋆d` on `S³` with eigenvalues `λ_ℓ = ℓ(ℓ+2)`.

HQIV already has the same formula as **scalar** Laplace–Beltrami on `S³` in
`Hqiv/Geometry/QuaternionMaxwellS3OMaxwellS4Spectral.lean`.

Lean bridge: `beltramiPeterWeylEigenvalueS3 ℓ = laplaceBeltramiEigenvalueS3 ℓ`.

**Caveat:** TUFT’s *fundamental* coexact normalization uses `λ₁ = 2`; Peter–Weyl level
`ℓ = 1` gives `3`. We keep both labels (`tuftFundamentalBeltramiEigenvalueS3` vs
`beltramiPeterWeylEigenvalueS3`) and prove they differ — no silent identification.

### 2. Three generations from fiber winding (not fitted)

TUFT: integrable torus sectors `n = 1,2,3` (unknot / Hopf link / trefoil); hyperbolic
transition at `n = 4` → no fourth fermion generation.

HQIV: `ResonanceGeneration = Fin 3`, charged-lepton and quark generation slots.

Lean: `HopfFiberWinding`, `tuftMinimalBeltramiEigenvalue n = n+1`, strict order
`2 < 3 < 4` for `n = 1,2,3`.

### 3. Spectral ratios vs `geometricResonanceStep`

TUFT: sector determinants factor over fiber winding; mass ratios from spectral invariants.

HQIV: `geometricResonanceStep m_from m_to = detunedShellSurface m_from / m_to`.

Lean: `tuftBeltramiResonanceRatio` (`4/3` for windings `3→2`, `3/2` for `2→1`).

**Proved (lock-in chart `m = n + 1`):** `tuftBeltramiResonanceRatio 3 2 = geometricResonanceStep 4 3 = 4/3`
(`HalfStepBeltramiShellBridge`). This is **not** `resonance_k_tau_mu` (175/76 on shells 33/15).

**Proved mismatch:** `tuftBeltramiResonanceRatio 2 1 = 3/2` but `geometricResonanceStep 3 2 = 35/24`.
The overconstrained brace half-step `xiHalfStep = 7/2` sits between integer shells `m=2` and `m=3`
(`ξ = 3` and `ξ = 4`), not at the lepton ladder shells.

**Next steps (proved):**

- `holonomyRowRhs fanoVertexHeavyGen / fanoVertexMiddle = 3/2` (`ContinuousXiCoupling`)
- `structureXiWitness.residualNorm < halfStepXiWitness.residualNorm` (scan ordering)
- Lepton `resonance_k_*` factorized as shell/jet quotients; ≠ Beltrami/holonomy charts
  (`LeptonResonanceChartComposite.lean`)

### 4. Informational energy + spectral correction

TUFT: intrinsic scales from zeta-regularized Gaussian determinants.

HQIV: `E_tot = m + 1/Θ(ξ)` (`InformationalEnergyMass`).

Lean scaffold: `informationalEnergyAtXiWithBeltrami` adds `beltramiSpectralWeightS3 ℓ =
(λ_ℓ + 1)⁻¹`. Next step: show leading behavior matches a sector determinant expansion
around `effCorrected` / `OctonionicZeta`.

### 5. Nested shells vs Fano / null lattice

| TUFT shell | Gauge sector | HQIV analogue (working map) |
|------------|--------------|-----------------------------|
| `S¹` fiber | U(1) EM | Fano line / octonion phase |
| `S³` (`n=1`) | SU(2) weak | Quaternion Maxwell block (`Fin 4`) |
| `S⁵` (`n=2`) | SU(3) strong | Colour-preferred axis / `G₂` |
| `S⁹` (`n=4`) | neutrino / high | Outer-horizon / continuous `ξ` chart |

Do **not** force `referenceM = 4` to equal TUFT’s `n=1` shell index — different charts.

---

## What we did not import

- Universality theorem (“any U(1)-complete theory must be Hopf”).
- Full Ray–Singer / ζ(3) sector determinant assembly.
- Single Fermi-constant input (HQIV uses α\_EM brace + geometric axioms).
- Complex Hopf base `CP^∞` as primary space (HQIV is null-lattice + horizon-first).

---

## Open Lean milestones (mass spectrum)

| ID | Target | Module |
|----|--------|--------|
| T1 | Prove `resonance_k_tau_mu` / `resonance_k_mu_e` bound from Beltrami ratios + lock-in shells | `HopfShellBeltramiMassBridge` → `ChargedLeptonResonance` |
| T2 | Derive `detunedShellSurface` from O-Maxwell + Fano projection (not parallel axiom) | **Partial:** `FanoSectorSpectralMassEmergence` proves `detunedShellSurface = sectorGaussianLeadingWeight = S/jet`; full action derivation still open |
| T3 | Replace τ-PDG anchor with spectral gap at `referenceM` | `MassSpectrumWitness`, `DerivedGaugeAndLeptonSector` |
| T4 | Hadron masses: link `laplaceBeltramiEigenvalueS4` to meta-horizon quark shells | `QuaternionMaxwellS3OMaxwellS4Spectral`, `HadronMassReadout` |
| T5 | CKM/PMNS: holonomy phases on Fano cycles | `imprint` modules, TUFT §4.23 |

---

## Citation

```bibtex
@unpublished{NielsenTUFT2026,
  author = {Nielsen, Jenny Lorraine},
  title  = {The Topological Unified Field Theory on the Complex Hopf Fibration ...},
  year   = {2026},
  url    = {https://philarchive.org/rec/NIETTU}
}
```

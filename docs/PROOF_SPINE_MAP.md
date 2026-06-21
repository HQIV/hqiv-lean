# HQIV Proof Spine Map

Self-reinforcing dependency graph for the flavor → EW → QCD → cosmology → formal QFT proof ladder.
Status labels: **proved**, **witness**, **scaffold**.

## Layer 0 — Axioms and carrier

| Module | Status | Key objects |
|--------|--------|-------------|
| `Hqiv/Geometry/OctonionicLightCone.lean` | proved | `referenceM = 4`, discrete null lattice, `alpha`, `gamma_HQIV` |
| `Hqiv/Geometry/HQVMetric.lean` | proved | `gamma_eq_2_5`, `alpha_eq_3_5`, curvature imprint |
| `Hqiv/Algebra/PhaseLiftDelta.lean` | proved | π/2 phase lift in (e₁,e₇) plane |
| `Hqiv/Algebra/AnomalyCancellation.lean` | proved | per-generation SM anomaly traces zero |

## Layer 1 — Fano / holonomy overlap

| Module | Status | Key objects |
|--------|--------|-------------|
| `Hqiv/Physics/ContinuousXiCoupling.lean` | proved | `holonomyRowRhs`, `generationVerticesFormAdmissibleCycle` |
| `Hqiv/Physics/ReadoutGaugeSeed.lean` | proved | `imprintWeightedReadoutPhase`, discrete holonomy = 1 |
| `Hqiv/Physics/FanoHolonomyOverlap.lean` | proved | generation overlap weights, phase-lift skew |
| `Hqiv/Physics/FanoMixingMatrix.lean` | proved | `MixingMatrix3`, row/col unitarity, Jarlskog |

## Layer 2 — Flavor mixing matrices

| Module | Status | Key objects |
|--------|--------|-------------|
| `Hqiv/Physics/HepDecayReadout.lean` | proved | CKM slot squares, `cpOddFanoHolonomySkew`, ledger unitarity |
| `Hqiv/Physics/CkmHolonomyReadout.lean` | proved | full CKM magnitudes + phases, Jarlskog, triangle angles |
| `Hqiv/Physics/HopfShellBeltramiMassBridge.lean` | proved | T10 PMNS angles, overlap matrix |
| `Hqiv/Physics/PMNSHolonomyReadout.lean` | proved | canonical PMNS readout on shared matrix infrastructure |
| `Hqiv/Physics/RareDecayReadout.lean` | proved | K→πνν, Bs→μμ, b→sγ ledger |
| `Hqiv/Physics/FlavorCPObservable.lean` | proved | R_K, angular moments, CP asymmetry routing |

## Layer 3 — Electroweak precision

| Module | Status | Key objects |
|--------|--------|-------------|
| `Hqiv/Physics/DerivedGaugeAndLeptonSector.lean` | proved | M_W, M_Z, Higgs witnesses |
| `Hqiv/Physics/TuftElectroweakBosonReadout.lean` | proved | geometric sin²θ_W, boson masses at ξ |
| `Hqiv/Physics/ElectroweakMassObservation.lean` | witness | facility dressing (comparison layer) |
| `Hqiv/Physics/HiggsSelfCouplingReadout.lean` | proved | λ₃, λ₄, κ modifiers |
| `Hqiv/Physics/SMEFTDiscreteExporter.lean` | proved | dimension-6 coefficient records |

## Layer 4 — Strong sector / collider

| Module | Status | Key objects |
|--------|--------|-------------|
| `Hqiv/Physics/PartonCarrierEvolution.lean` | proved | PDF moments, discrete DGLAP transport |
| `Hqiv/Physics/PatchScatteringUnitarity.lean` | proved | 2→2 optical theorem scaffold discharge |

## Layer 5 — Cosmology / formal QFT

| Module | Status | Key objects |
|--------|--------|-------------|
| `Hqiv/Physics/CosmologicalPerturbationReadout.lean` | proved | Friedmann + perturbation witness records |
| `Hqiv/Physics/LightConeMaxwellQFTBridge.lean` | witness | QFT closure hub |
| `Hqiv/QuantumMechanics/ContinuumManyBodyQFTScaffold.lean` | scaffold | renormalization, microcausality gaps |

## Dependency flow

```
OctonionicLightCone → ContinuousXiCoupling → FanoHolonomyOverlap → FanoMixingMatrix
                                                              ↓
                    HepDecayReadout ─────────────────→ CkmHolonomyReadout
                    HopfShellBeltramiMassBridge ───→ PMNSHolonomyReadout
                                                              ↓
                                         RareDecayReadout / FlavorCPObservable
                                                              ↓
                    AnomalyCancellation ──→ HiggsSelfCouplingReadout / SMEFTDiscreteExporter
                                                              ↓
                    PartonCarrierEvolution / PatchScatteringUnitarity
                                                              ↓
                    CosmologicalPerturbationReadout / ContinuumManyBodyQFTScaffold
```

## Build targets

- Daily physics: `lake build HQIVPhysics`
- Flavor mixing paper closure: `lake build paper_flavor_mixing`
- Inventory module: `Hqiv/Physics/ProofSpineInventory.lean`

## Synthesis paper

Programme overview citing the capstone: `papers/proof_spine_synthesis/hqiv_proof_spine_synthesis.tex`

Export: `python3 scripts/hqiv_proof_spine_synthesis_export.py`

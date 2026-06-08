import Hqiv.Physics.BaryogenesisCore
import Hqiv.Story.Chapter08_ClayMillennium
import Problems.YangMills.Quantum

/-!
# Mass-gap wiring — what is proved, where the **gap** is, how to close it

This module is the **inventory** for the Story exercise: all HQIV-side pieces already exist in the
library; the Clay / Lean Dojo Yang–Mills statement asks for a **different** finished object. Here we
name the boundary so later work can target it without confusing symbols (`G` = compact **gauge**
group in Dojo, not Newton `G`, not a single SO(8) generator).

## A. What the Story spine **already proves** (`Hqiv.Story.MassGap`)

| Region | Content | Lean anchors |
|--------|---------|----------------|
| Discrete horizon + φ ladder | Temperature / imprint substrate | `Chapter01`–`02`, `AuxiliaryField`, `OctonionicLightCone` |
| Metric phase | Time-angle monotonicity on each `φ(m)` | `Chapter02`, `HQVMetric.timeAngle_mono_t` |
| Conservations / DOF pin | Phase on `[0,2π]`, dim-28 shell narrative | `Chapter03`, `Conservations` |
| **Octonion SO(8) Lie DOF (Story = re-export of closure pack)** | 28 `so8Generator` matrices: bracket closure + linear indep. (`so(8)`-sized Lie algebra) | `OctonionLieDOF` discharges the backbone from `Hqiv.SO8ClosureInterface` (pre-build `HQIVSO8Closure` for a cold cache) — *not* the same as choosing `G` in Dojo |
| Shell couplings + binding shape | α\_eff / hydrogenic packaging | `Chapter04`, `HarmonicLadderMass` |
| Lock-in readouts | `shell_shape_abs m_lockin > 0`, Ω\_k = 1, ladder IDs | `Chapter05`, `BaryogenesisCore` |
| Fluid scaffold (sign) | HQIV eddy viscosity ≥ 0 at `m_lockin` | `Chapter06`, `HQIVFluidClosureScaffold` |
| Patch QFT | **Abelian** smeared operators: commutators vanish on regions | `Chapter07`, `PatchQFTBridge.patchAlgebraAt_opCommutator_zero` |

**One-line proved endpoint:** `MassGap.mass_gap_story_through_patch_commutator_of_axioms` — the full chain
through `step07_patchAbelianCommutator`.

**Manifold + “uniqueness” (what did *not* get dropped):** In `Problems/YangMills/Quantum.lean`, **spacetime
for the YM scaffold** is `MillenniumYangMillsDefs.Spacetime := EuclideanSpace ℝ (Fin 4)` (ℝ⁴ with the
Borel/ℓ² setup used downstream). The octonion **SO(8) closure** lives in **8×8 matrix** generators
(Lie *internal* / adjoint-size bookkeeping). That is *orthogonal* to “which manifold the field theory
lives on”: it does not mean we threw away “half” of ℝ⁴, or that ℝ⁴ was replaced by a smaller
spacetime — only the **QFT+Clay** and **matrix Lie** tracks sit in *different* modules on purpose
(composition, not replacement).

The Dojo/Clay `Prop` `YangMillsExistenceAndMassGap` in `Millennium.lean` is an **existential**:
`∃ (qft : …) (Δ : ℝ), …` with `HasMassGapSpectrum` / `FiniteMassSpectrum`. It is **not** a theorem
schema that the physical gap is the **uniquely determined** real number for all admissible data (that
would be a *stronger* target than the formalized Millennium statement). Uniqueness of a **lowest
energy** state is part of the *Wightman narrative* in the docstrings; pinning a **unique numeric**
`Δ` to match HQIV’s ladder in a *proved* way is the separate spectrum–bridge work (§C.3) — and
it was never a consequence of the SO(8) Lie-closure file alone, because closure is not a Hamiltonian
spectrum theorem on ℝ⁴.

## B. Physical “gap exists” (baryogenesis + paper) vs Dojo formalism

In HQIV’s own narrative, **confinement / a mass-scale gap** is not an afterthought: the same curvature
imprint \(\delta_E(m)\) and shell ladder that fix **\(\Omega_k\)** and the **baryogenesis** window also
supply the scale structure for colour dynamics (see the baryogenesis / QCD / confinement discussion in
`HQIV/paper/main.tex` — repo path `HQIV/paper/main.tex` alongside this Lean project). On the Lean
side, that line is anchored in **`Hqiv.Physics.BaryogenesisCore`** (geometry-only Ω\_k / ladder
readouts), **`Hqiv.Physics.BaryogenesisWitness`** / **`Baryogenesis`** where η meets the discrete
horizon machinery, and the spin–colour / octonion story in **`Hqiv.Physics.Forces`** /
**`Hqiv.Algebra.SMEmbedding`** — i.e. the **baryogenesis area is where “existence of the gap” lives**
physically.

That is **not the same statement** as `MillenniumYangMillsDefs.HasMassGapSpectrum`, which is a
**Wightman–Hamiltonian spectrum** hypothesis for a completed `QuantumYangMillsTheory G` on \(\mathbb R^4\).
So: **one gap, two formalisations** — (i) HQIV discrete + curvature + baryogenesis/confinement (paper +
Lean physics modules), (ii) Clay/Dojo spectral-gap predicate (vendored Millennium). Section **C** below
is the current roadmap; section **D** lists `Hqiv` modules that can feed the remaining (ii) work without
conflating them with what is already proved.

## C. Roadmap and status (Story + bridge audit)

### C.1 Proved in `Hqiv.Story` (no Clay body assumed)

- **Ch 1–7 spine** through abelian patch commutators: `mass_gap_story_through_patch_commutator_of_axioms` →
  `step07_patchAbelianCommutator`.
- **Ladder / lock-in “gap scale” and finiteness hooks** — `Hqiv.Story.LadderGapCandidateWell`: concrete
  `ladderGapCandidate`, proved `ladderGapCandidate_pos`, and a positive finite mode bound at lock-in
  (`finiteModeBoundAtLockin`, `r8 m_lockin`). `SketchesConsumedLadderWell` **re-exports** the same names
  for spectral packaging that still needs `DiscreteOMaxwellHQIVInstance` (completion spine).
- **Promotion-style obligations as theorems (given any `qft`)** — `Hqiv.Story.YMRemainingObligations`: e.g.
  `hqivPatchWitnessPromotionMorphism_realizesLocalOperators`, locality/covariance/OPE from `qft` fields;
  `hqivSpectralFromDynamicsFromCore` records `0 < ladderGapCandidate` for `delta_positive_from_ladder`
  and packages spectral **props**; `hqivSpectralFromDynamicsFromCore_witnesses` unpacks `core.hGap` /
  `core.hFin` from an **assumed** `ClayYangMillsCompletionData`.
- **Iff packaging** — `Hqiv.Story.MassGapCompletionBundle`: `YangMillsExistenceAndMassGap G ↔ Nonempty (ClayYangMillsCompletionData G)` and substrate products.

### C.2 Partially reduced (structure present; body not derived from HQIV alone)

(The 28-generator SO(8) backbone in `Hqiv.Story.OctonionLieDOF` is **not** in this list — it is fully
re-exported from `Hqiv.SO8ClosureInterface`; pre-build `HQIVSO8Closure` on a cold cache.)

- **`HasMassGapSpectrum` / `FiniteMassSpectrum` from ladder** — the **positivity of a ladder-chosen scale**
  is proved (`ladderGapCandidate_pos`). A **theorem** that the **Wightman Hamiltonian** of a **specific
  constructed** `qft` has spectrum disjoint from `(0, Δ)` for that (or a related) `Δ` is **not** in the
  Story: it is still what `ClayYangMillsCompletionData` **assumes** in `hGap` / `hFin` until a model is built.
- **Weak Hilbert / patch ↔ `localOperators` alignment** — the right `Prop`s are in `YMRemainingObligations`
  (`hqiv_hilbert_bridge_local_operator_compat`, `…_weak`); discharging them for a **concrete** bridge on a
  **concrete** carrier is not automatic.

### C.3 Open by design: axioms in `Hqiv.Story.MillenniumBridgeToyWitness`

To get a **first** end-to-end **certificate** with the `S₃` Story gauge, the file uses **axioms** (not
proved from `Hqiv` alone): `millenniumBridgeClayCore` (full `ClayYangMillsCompletionData`), `millenniumBridgePatchBridge`,
`millenniumBridge_hilbert_local_operator_compat`. Discharging these is the same as **constructing** the
Dojo `QuantumYangMillsTheory` + spectral clauses + patch alignment — the intended “second half” of the
project, not a missing lemma in the Ch 1–7 chain.

### C.4 Toy Wightman at a point (done in-file)

- `Hqiv.Story.MillenniumBridgePoincareWightman.schwartzMap_real_eqAt_zero` is proved (ContDiff bump at
  `0 : Spacetime`, `HasCompactSupport.toSchwartzMap`, then scale to any `c : ℝ`). The **1D** Wightman
  toy cyclic-density path is fully packaged in that module.

### C.5 Dependency-ordered work (what to build next)

1. **Replace `MillenniumBridgeToyWitness` axioms** — either **construct** a `ClayYangMillsCompletionData G`
   in Lean (full `QuantumYangMillsTheory` + `Δ` + `hExist` / `hGap` / `hFin`) or **import a vendored model**
   and package it. Until then, `millenniumBridge_yangMillsExistenceAndMassGap` is “from completion data by
   axiom,” not from discrete HQIV.
2. **Spectral bridge** — prove (not assume in `core`) a link from **ladder** data to **`HasMassGapSpectrum`**
   for the **same** Hamiltonian as in the chosen `qft` (or prove equivalence to an axiomatized model).
3. **Gauge `G` for a physics claim** — keep `GaugeGroupFromHQIVSketch` / `S₃` for small examples; for SM-colour
   alignment, add a path from `Hqiv.Physics.HQIVYangMillsPackage` + algebra embedding facts to a
   `CompactSimpleGaugeGroup` instance the Dojo file can use (or document why the Clay statement is stated
   for a different `G`).

`step07_yangMillsWitnessBundle G` is **definitionally** `YangMillsExistenceAndMassGap G` (see
`Chapter08_ClayMillennium`); the bridge from Ch 1–7 **abelian** patch data to the **non-abelian** Clay
`Prop` is **not** a short lemma — it goes through (1–2) above.

### C.6 Import graph fix (Chapter 8 ↔ HQIV QFT)

`MillenniumBridgePatchPoincareWightman` now imports **`LadderGapCandidateWell`** for the ladder
Hamiltonian scale instead of **`SketchesConsumedLadderWell`**, breaking the cycle
`Chapter08 → … → Patch Wightman → Sketches → MassGapCompletionBundle → Chapter08`.
So **`Chapter08_ClayMillennium` imports `QuantumYangMillsFromPatchHQIV`** and records
`MassGap.nonempty_hqivInterface_quantumYangMills` alongside the older `nonempty_poincareToy_quantumYangMills`.

### C.7 Step 4 (still open)

Cycle removal **does not** identify `hqivPatchJetOperatorValuedDistribution` with `field_operators`; that
remains the Schwartz / Wightman / Hilbert-bridge work in `YMRemainingObligations` (see module doc there).

## D. `Hqiv` namespace: what can feed the gaps (and what cannot)

| Target gap / axiom | `Hqiv` modules to pull forward | What they provide | What they do *not* provide |
|----------------------|--------------------------------|-------------------|----------------------------|
| Continuum + ladder ↔ field / renormalization **scaffolds** | `Hqiv.Physics.LightConeMaxwellQFTBridge`, `Hqiv.Physics.ContinuumOmaxwellClosure`, `Hqiv.Physics.PromotedOMaxwell`, `Hqiv.Physics.OMaxwellAlgebraSeed` | Single import hub: null ladder → continuum φ–Maxwell, chart gradients, action/EL alignment hooks; `OMaxwellAlgebraSeed` ties `G₂ ∪ {Δ}` to the Maxwell stack and `so(8)` blocks. | A `QuantumYangMillsTheory` or `HasMassGapSpectrum` — no automatic Dojo inhabitant. |
| Shell masses / α\_eff / binding | `Hqiv.Physics.HarmonicLadderMass`, `Hqiv.Physics.BaryogenesisCore`, `Hqiv.Physics.Baryogenesis` | Proved definitional chains and vital readouts for the **discrete** “gap scale” story. | Wightman Hamiltonian spectrum on ℝ⁴. |
| Octonion **Lie** + SM alignment (finite-dim) | `Hqiv.Physics.HQIVYangMillsPackage`, `Hqiv.Algebra.SO8ClosureAbstract`, `Hqiv.Algebra.SMEmbedding`, `Hqiv.Algebra.G2Embedding`, `Hqiv.Algebra.Triality` | `hqivGaugeCarrier` finrank 28, `g2`/`su2`/hypercharge in span, unification/rapidity *statements* packaged. Module doc of `HQIVYangMillsPackage` **explicitly** disclaims the **analytic** Clay existence theorem. | `CompactSimpleGaugeGroup` for `SU(3)` or a constructed non-abelian `qft` — unless you add new instances. |
| Abelian **patch** operators | `Hqiv.QuantumMechanics.PatchQFTBridge` (Story uses via Ch 7) | `patchAlgebraAt`, commutator vanishing — the proved Ch 7 layer. | Non-abelian `localOperators` identification without further work. |
| Clay ↔ Story packaging | `Hqiv.Bridge.LeanDojoClayMillennium` | Re-exports / naming for Millennium targets. | Proofs of existence. |
| **Unification** narrative (Yang–Mills wording) | `Hqiv.Physics.SM_GR_Unification` | `YangMills_SM_GR_Unification_statement` and related mass/GUT narrative (see file). | Not `MillenniumYangMills.YangMillsExistenceAndMassGap` unless wired by new theorems. |
| Geometry / rapidity (auxiliary) | `Hqiv.Geometry.SATRapidityGapBridge`, `Hqiv.Geometry.SATRapidityManifold`, `Hqiv.Physics.RapidityZetaPhaseBridge` (as used from `HQIVYangMillsPackage`) | Chart/rapidity **structure** for phase alignment. | Dojo `G` or Hamiltonian gap. |

**Principle:** `Hqiv` already contains strong **discrete + continuum classical/QM scaffolds + finite-dimensional
Lie and SM-embedding** material. Filling the **Dojo axioms** means **composing** those into a **typeclass
witness** for `QuantumYangMillsTheory` (or an imported model) plus **proving** the spectral
`Prop`s or relating them to ladder data — not a single missing import.

## E. Numeric / calibration (not a proof) — `scripts/cubic_phase_relax_probe.py`

The repo script `scripts/cubic_phase_relax_probe.py` is an **exploratory numeric mirror** of relaxed-quarter /
cubic-phase readouts aligned with the same discrete geometry as the Story (`shell_surface`, `shell_shape`,
`omega_k_at_horizon`, `REFERENCE_M`, …) plus triality / spectral weights. It is **evidence** toward
relating **spectral relaxation** on sphere bridges to **shell** detuning; it does not construct
`QuantumYangMillsTheory` or prove `HasMassGapSpectrum`.

This file adds **no new axioms**; it documents, re-exports, and adds **packaging lemmas** that split
or join existing results (no new mathematical content beyond named conjunctions / implications).
-/

namespace Hqiv.Story.MassGapWiring

open Hqiv
open Hqiv.Story.MassGap
open MillenniumYangMillsDefs

/-- Proved Story endpoint (Ch 1–7): abelian patch commutator layer. -/
abbrev patchMicrocausalityFromStory : step07_patchAbelianCommutator :=
  mass_gap_story_through_patch_commutator_of_axioms

/-- Clay YM + mass gap **given** an explicit Dojo witness bundle (bridge elimination). -/
abbrev clayYangMillsMassGap_ofWitness (G : Type) [CompactSimpleGaugeGroup G]
    (h : step07_yangMillsWitnessBundle G) : step08_yangMillsExistenceAndMassGap G :=
  yangMills_existence_and_mass_gap_of_dojo_witness G h

/-!
## F. Lemmas “together”: `BaryogenesisCore` ↔ Ch 5 witness ∧ patch layer

`step05_referenceShellGapWitness` is exactly **positive lock-in shell imprint** plus
`Hqiv.baryogenesis_vital_readout` (Ω_k + ladder temperature IDs), proved as
`baryogenesis_vital_omega_T_no_eta`.
-/

/-- Ch 5 witness implies the Ω_k / temperature block from `BaryogenesisCore`. -/
theorem step05_baryogenesis_vital_component (h : step05_referenceShellGapWitness) :
    Hqiv.baryogenesis_vital_readout := by
  rcases h with ⟨_, hω, hTC, hTL⟩
  exact ⟨hω, hTC, hTL⟩

/-- Assemble Ch 5 from a positive `shell_shape_abs` readout and a vital readout. -/
theorem step05_of_shell_pos_and_baryogenesis_vital_readout
    (hσ : 0 < shell_shape_abs m_lockin) (hv : Hqiv.baryogenesis_vital_readout) :
    step05_referenceShellGapWitness := by
  rcases hv with ⟨hω, hTC, hTL⟩
  exact ⟨hσ, hω, hTC, hTL⟩

/-- Ch 5 witness ↔ imprint positivity ∧ vital Ω_k/T block (pure unpacking). -/
theorem step05_iff_positive_shell_and_baryogenesis_vital_readout :
    step05_referenceShellGapWitness ↔ 0 < shell_shape_abs m_lockin ∧ Hqiv.baryogenesis_vital_readout := by
  constructor
  · intro h
    exact ⟨h.1, step05_baryogenesis_vital_component h⟩
  · intro ⟨hσ, hv⟩
    exact step05_of_shell_pos_and_baryogenesis_vital_readout hσ hv

/-- Recover Ch 5 by pairing `shell_shape_abs_pos` with `baryogenesis_vital_omega_T_no_eta`. -/
theorem step05_of_shell_shape_abs_pos_and_baryogenesis_vital_theorem :
    step05_referenceShellGapWitness :=
  step05_of_shell_pos_and_baryogenesis_vital_readout (shell_shape_abs_pos m_lockin)
    baryogenesis_vital_omega_T_no_eta

/-- **Single bundle:** lock-in / Ω_k / ladder readouts (Ch 5) **and** abelian patch commutator layer (Ch 7). -/
theorem baryogenesis_lockin_readouts_and_patch_microcausality :
    step05_referenceShellGapWitness ∧ step07_patchAbelianCommutator :=
  ⟨step05_referenceShellGapWitness_holds, patchMicrocausalityFromStory⟩

end Hqiv.Story.MassGapWiring

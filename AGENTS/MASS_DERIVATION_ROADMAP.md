# Roadmap: light-cone mass derivation (status-tracked ladder)

This document is a **proof and implementation path** for agents working on the
HQIV mass story. Its purpose is to keep the repo honest about which masses are
already tied faithfully to the **discrete light cone + monogamy** backbone, and
which ones are still carried by **anchors, provisional shell picks, or witness
definitions**.

The organizing rule is simple:

1. Start from the **light-cone / shell / monogamy** spine.
2. Prefer **outer-horizon closure** before charged-fermion numerology.
3. Treat hadrons as the **inner/meta-horizon realization** of the same shell
   story, not as an independent phenomenological patch.

This file follows the same discipline as the other `AGENTS` roadmaps: **name
what is proved, name what is a witness, and name what is still open**.

**Modal closure (design):** the long-term picture—shells as **eigen / resonance
conditions** of the **lifted** O-Maxwell + \(\varphi\) dynamics with **Fano
projections** replacing hand-picked quark shell tables—is stated in
[`O_MAXWELL_EIGEN_SHELL_SELECTION.md`](./O_MAXWELL_EIGEN_SHELL_SELECTION.md).

**Parallel mining (TUFT / Hopf):** Nielsen’s topological unified field theory on the
complex Hopf fibration (PhilArchive `NIETTU`, bib `NielsenTUFT2026`) supplies Beltrami
contact spectra, fiber-winding generation rigidity, and zeta-determinant mass scales.
Actionable HQIV mapping and open Lean milestones are in
[`TUFT_HOPF_SPECTRAL_MINING.md`](./TUFT_HOPF_SPECTRAL_MINING.md); proofs start in
[`Hqiv/Physics/HopfShellBeltramiMassBridge.lean`](../Hqiv/Physics/HopfShellBeltramiMassBridge.lean).

---

## 0. Effective narrative (what we are trying to formalize)

The intended HQIV mass hierarchy is:

1. **Light-cone combinatorics** fix the shell ladder and the curvature/monogamy
   constants: `referenceM`, `alpha = 3/5`, `gamma = 2/5`.
2. **Auxiliary-field / temperature ladder** fixes `T(m)` and `phi_of_shell m`.
3. **Outer-horizon closure** turns those ingredients into bosonic and neutrino
   mass witnesses with no charged-lepton shell table.
4. **Charged leptons** should eventually come from a genuine outer-horizon
   support rule. The current `OuterHorizonLeptonShellSelection` interface is a
   useful exact-shell proxy, but the more physical target may be a shell band /
   support region rather than one shell integer.
5. **Hadrons** should then be expressed as the inner/meta-horizon analog:
   constituent-plus-binding, but with binding generated from the same shell
   objects rather than by hiding the answer in anchors.

The goal is **not** “some masses exist in Lean.” The goal is:

- the **same** HQIV primitives should drive every sector,
- each remaining anchor should be **visible and isolated**,
- and each milestone should reduce the anchor burden rather than move it around.

---

## Status snapshot (now)

### In place (strongest anchors agents can cite)

- **M0 — Light-cone backbone (done):**
  [`Hqiv/Geometry/OctonionicLightCone.lean`](../Hqiv/Geometry/OctonionicLightCone.lean)
  fixes the mode-counting story, `referenceM`, and `alpha = 3/5`.
- **M1 — Temperature / φ ladder (done):**
  [`Hqiv/Geometry/AuxiliaryField.lean`](../Hqiv/Geometry/AuxiliaryField.lean)
  gives `T m = 1 / (m + 1)` and `phi_of_shell m = 2 (m + 1)`.
- **M2 — Outer-horizon closure witnesses (done):**
  [`Hqiv/Physics/DerivedGaugeAndLeptonSector.lean`](../Hqiv/Physics/DerivedGaugeAndLeptonSector.lean)
  defines `outerClosureScale`, `M_W_derived`, `M_Z_derived`, `m_H_derived`, and
  the neutrino witnesses from `referenceM`, `T_lockin`, and adjacent
  outer-horizon surfaces.
- **M2a — Algebra-first gauge / Maxwell packaging (done, structural):**
  [`Hqiv/Physics/OMaxwellAlgebraSeed.lean`](../Hqiv/Physics/OMaxwellAlgebraSeed.lean),
  [`Hqiv/Physics/ModifiedMaxwell.lean`](../Hqiv/Physics/ModifiedMaxwell.lean), and
  [`Hqiv/Physics/HQIVYangMillsPackage.lean`](../Hqiv/Physics/HQIVYangMillsPackage.lean)
  now make the `G₂ ∪ {Δ}` seed, the extracted H-block / EM block, and the
  rapidity slot explicit. This does **not** yet derive the boson masses by
  itself, but it gives the mass story a cleaner algebra-facing provenance than
  the old “start from `phi_of_T`” presentation.
- **M3 — Charged-lepton shell interface (done, but not solved):**
  [`Hqiv/Physics/LeptonGenerationLockin.lean`](../Hqiv/Physics/LeptonGenerationLockin.lean)
  now separates the **interface**
  `OuterHorizonLeptonShellSelection` from the current provisional witness.
  This should now be read as a minimal exact-shell proxy, not necessarily as the
  final physics interface for a standing-wave mode.
- **M4 — Meta-horizon hadron structure (partial):**
  [`Hqiv/Physics/BoundStates.lean`](../Hqiv/Physics/BoundStates.lean)
  and [`Hqiv/Physics/QuarkMetaResonance.lean`](../Hqiv/Physics/QuarkMetaResonance.lean)
  express binding through `E_bind_from_network` /
  `E_bind_from_composite_trace`, with the proton lock-in condition made explicit.
- **M4a — Hadron mass readout export (2026-05):**
  [`Hqiv/Physics/HadronMassReadout.lean`](../Hqiv/Physics/HadronMassReadout.lean)
  wires the calculator/benchmark stack: valence-scaled `hadronBindingMeV`,
  meson `l²` factor **4/9** (`hadronIntrinsicScale_meson_eq_four_ninths`),
  informational `hadronMassFromXiAfterGround`, and operational excitation deltas
  (`radialExcitationDeltaOperational`, `orbitalExcitationDeltaOperational`).
  Python mirror: `scripts/hqiv_mass_calculator_core.py`, `scripts/hqiv_excited_states.py`.

### Faithful now

These are the mass-like outputs most faithfully tied to the light-cone story:

- **Bosonic closure witnesses**
  from [`DerivedGaugeAndLeptonSector.lean`](../Hqiv/Physics/DerivedGaugeAndLeptonSector.lean):
  `M_W_derived`, `M_Z_derived`, `m_H_derived`.
- **Boson comparison theorems**
  from the same file:
  `boson_witness_values` (and `boson_witness_M_W` / `M_Z` / `m_H`),
  `raw_ew_boson_W_H_below_PDG_Z_above`,
  `age_adjusted_boson_witness_values`,
  `age_adjusted_boson_masses_exceed_PDG_centrals`
  (documents that the published age ratio is **not** an electroweak-scale refinement once quantum lifts are included).
- **Neutrino witnesses**
  from the same file:
  `m_nu_e_derived`, `m_nu_mu_derived`, `m_nu_tau_derived`,
  together with `m_nu_e_derived_eq_suppression_times_M_Z`.
- **Structural hadronic binding witness**
  from [`QuarkMetaResonance.lean`](../Hqiv/Physics/QuarkMetaResonance.lean):
  `nucleonSharedBinding_MeV`.
- **Isospin split witness**
  from the same file:
  `nucleonIsospinGap_MeV = 1`.

These are faithful because they are already written as consequences of:

- `referenceM`,
- the shell/temperature/φ ladder,
- `alpha` / `gamma`,
- the outer-horizon surface bookkeeping,
- and the explicit 8×8 binding functional.

### Partially faithful

These have a real HQIV structure, but still depend on anchors or provisional
choices:

- **Charged-lepton resonance ladder**
  in [`LeptonGenerationLockin.lean`](../Hqiv/Physics/LeptonGenerationLockin.lean)
  and [`ChargedLeptonResonance.lean`](../Hqiv/Physics/ChargedLeptonResonance.lean):
  τ has an age-normalized heavy readout in
  [`AgeNormalizedHeavyMass.lean`](../Hqiv/Physics/AgeNormalizedHeavyMass.lean);
  `m_tau_from_resonance` remains only a legacy GeV comparison witness. Exact
  shell occupancy may itself be too rigid: a standing-wave mode may live on a
  support band or potential difference rather than one exact shell.
- **Quark ladders**
  in [`QuarkMetaResonance.lean`](../Hqiv/Physics/QuarkMetaResonance.lean):
  geometric resonance drops are real. The heavy up/top channel now has an
  age-normalized readout in `AgeNormalizedHeavyMass.lean`; `m_top_GeV` is kept
  as a legacy comparison/export literal. `m_bottom_GeV` and the shell tables are
  still witness inputs.
- **Proton / neutron masses**
  in [`QuarkMetaResonance.lean`](../Hqiv/Physics/QuarkMetaResonance.lean)
  and [`DerivedNucleonMass.lean`](../Hqiv/Physics/DerivedNucleonMass.lean):
  the proton is held fixed by the explicit boundary condition
  `protonAnchorMass_MeV = 938.272`.
- **Boson-to-observation closure**
  in [`DerivedGaugeAndLeptonSector.lean`](../Hqiv/Physics/DerivedGaugeAndLeptonSector.lean):
  EW gauge and scalar **quantum-number lifts** bring `M_W` and `m_H` into a
  sensible GeV band relative to PDG centrals; **`M_Z` uses `(g_SU2 + g_U1) · vev`
  only** (no imported weak mixing), so the neutral-vector closure sits **above**
  the PDG `M_Z` central—consistent with treating β-decay / mixing physics in other
  modules. The published apparent-age ratio is not an electroweak refinement at
  this scale.

### Not faithful yet

These should **not** be described as derived from first principles yet:

- the **full charged-lepton GeV table** without comparison witnesses,
- the **μ/e shell integers** as axiom outputs,
- the **full quark mass table** without bottom/shell-table witnesses,
- the **proton mass** as a prediction rather than a boundary condition,
- any claim that the current Lean files already prove numerical agreement for
  `M_W`, `M_Z`, `m_H`, or the charged fermions.

---

## Honesty table (agents)

| Question | Honest answer now |
|----------|-------------------|
| Can we derive any masses from the light cone faithfully now? | **Yes, but mainly bosonic / neutrino closure witnesses and structural binding quantities.** |
| Does the published universe-age ratio close the boson gap by itself? | **No.** At the current EW-scale lifted witnesses it **overshoots** PDG; it was only a useful comparison layer for the older small raw masses. |
| Is there a formal horizon-localized layer on top of age compression? | **Yes, as bookkeeping** (`ageAndHorizonAdjustedMass`), but it is not claimed to improve PDG agreement at electroweak scale. |
| Are charged leptons first-principles yet? | **Closer, not closed.** τ now has an age/lapse heavy readout (`ageNormalizedTauMass`), while `m_tau_from_resonance` is a comparison witness. μ/e still inherit the detuned-surface representative-shell machinery, which may only be a proxy for broader support bands. |
| Are hadrons first-principles yet? | **Not fully.** The binding form is HQIV-shaped, but the proton mass remains an explicit boundary condition. |
| Is the repo already at “particle masses from the light cone” in the strongest sense? | **No.** It has a credible derivation spine plus isolated anchors, not a fully closed fermion-mass theory. |

---

## Ladder (milestones — step by step)

Work in this order. Each step should remove a specific anchor, not just rename it.

| Milestone | Goal | Done when |
|-----------|------|-----------|
| **M0 — Backbone lock** | Keep `referenceM`, `alpha`, `gamma`, `T`, and `phi_of_shell` as the only universal shell inputs. | Already in place via `OctonionicLightCone` + `AuxiliaryField`. |
| **M1 — Outer closure first** | Treat bosonic and neutrino masses as the canonical first derivation layer. | Already in place structurally in `DerivedGaugeAndLeptonSector`; next step is to tie those witnesses more tightly to the algebra-first gauge / Maxwell package and to isolate exactly which comparison factors are local vs published. |
| **M2 — Replace provisional exact shells with derived support** | Replace provisional μ/e shell integers with a theorem-level support rule, possibly upgrading `OuterHorizonLeptonShellSelection` to a shell-band / support-region interface. | Charged leptons are no longer represented primarily by fixed provisional numerals; the downstream resonance ladder reads from a derived support object, with exact shells used only as peaks/representatives if still needed. |
| **M3 — Remove τ as an external scale witness** | Tie the absolute charged-lepton scale to HQIV age/lapse or outer-horizon closure rather than `m_tau_Pl` / `m_tau_from_resonance`. | Partially in place via `ageNormalizedTauMass`; remaining work is comparison/export migration and support-band sharpening. |
| **M4 — Reduce quark anchor count** | Replace one of the heavy quark anchors and/or one shell table with a theorem from the same shell ladder. | Partially in place for the heavy up/top channel via `ageNormalizedTopMass`; bottom and shell-table witnesses remain. |
| **M5 — Proton from constituent-plus-binding only** | Keep `referenceM = 4`, but stop feeding `938.272` in as an input. | `protonMassFromMetaHarmonics_MeV` is no longer definitionally forced by `protonAnchorMass_MeV`. |
| **M6 — Unified outer/inner mass spine** | Make bosons, leptons, and hadrons all read as one shell program. | The paper and Lean exports can tell a single story without special pleading for any sector. |

---

## Smallest next steps (recommended order)

### Step A — Make outer-horizon closure numerically sharper and structurally cleaner

Focus file:
[`Hqiv/Physics/DerivedGaugeAndLeptonSector.lean`](../Hqiv/Physics/DerivedGaugeAndLeptonSector.lean)

Supporting files:
- [`Hqiv/Physics/OMaxwellAlgebraSeed.lean`](../Hqiv/Physics/OMaxwellAlgebraSeed.lean)
- [`Hqiv/Physics/ModifiedMaxwell.lean`](../Hqiv/Physics/ModifiedMaxwell.lean)
- [`Hqiv/Physics/HQIVYangMillsPackage.lean`](../Hqiv/Physics/HQIVYangMillsPackage.lean)

Add theorem targets that compare the closure witnesses to the existing “paper
alignment” scales without introducing new anchors. This is the easiest place to
improve confidence while staying faithful to the current backbone.

The immediate theorem-level anchors are already visible and should now be used
as the roadmap baseline:

- `outerClosureScale_eq_reference_step`
- `m_nu_e_derived_eq_suppression_times_M_Z`
- `boson_witness_values` / `raw_ew_boson_W_H_below_PDG_Z_above`
- `age_adjusted_boson_masses_exceed_PDG_centrals`

The next refinement should be:

1. distinguish **raw local closure**, **published age compression**, and
   **extra horizon-localization** as three separate layers,
2. make clear which of those layers follows from the algebra-first Maxwell /
   gauge package and which is still paper-level comparison bookkeeping, and
3. avoid narrating `phi_of_T` as the primary boson-coupling source now that the
   Maxwell ladder has been refactored algebra-first.

### Step B — Replace the provisional charged-lepton exact-shell witness

Focus files:
- [`Hqiv/Physics/LeptonGenerationLockin.lean`](../Hqiv/Physics/LeptonGenerationLockin.lean)
- [`Hqiv/Physics/ChargedLeptonResonance.lean`](../Hqiv/Physics/ChargedLeptonResonance.lean)

The next real leap is to replace the current exact-shell witness with an actual
theorem about charged-lepton **support** on the outer horizon. That may still
first pass through `OuterHorizonLeptonShellSelection`, but the more physical end
state may be a band/support object rather than a single shell index.

Right now the exact-shell seam is already visible in Lean, but the first real
derived constructor has landed:

- `OuterHorizonLeptonShellSelection`
- `provisionalOuterHorizonLeptonShellSelection`
- `currentOuterHorizonLeptonShellSelection`
- `leptonResonanceThresholdPred`
- `firstShellAtOrAboveResonanceThreshold`
- `derivedLeptonMuonShell`
- `derivedLeptonElectronShell`
- `leptonMuonShell_eq_derived`
- `leptonElectronShell_eq_derived`
- `charged_lepton_resonance_uses_current_shell_selection`
- `resonance_k_tau_mu_eq_geometricResonanceStep`
- `resonance_k_mu_e_eq_geometricResonanceStep`

So the roadmap target should be read very concretely:

1. produce a **derived selection constructor** in
   `LeptonGenerationLockin.lean`,
2. prove it satisfies the two order fields required by
   `OuterHorizonLeptonShellSelection`,
3. switch `currentOuterHorizonLeptonShellSelection` from the provisional
   witness to that derived constructor, and only then
4. let `ChargedLeptonResonance.lean` inherit the new shells **without**
   changing its resonance formulas.

That exact minimal target is now in place: the active selector is no longer the
provisional shell record, and the resonance formulas downstream were kept
unchanged.

If the exact-shell interface turns out to be too rigid, the same four-step plan
should be re-run with a support object such as a shell band or shell-support
record, and the current exact shells treated as summary statistics of that
support.

### Step B1 — Minimal theorem target

The smallest nontrivial win is **not** “derive the exact electron mass.” It is:

- define a shell-selection rule using only existing HQIV ladder data
  (`referenceM`, `T`, `phi_of_shell`, `shellSurface`, `effectiveSurface`,
  `geometricResonanceStep`, optional `selfClockPhase`, or other already
  formalized shell quantities),
- package it as a value of type `OuterHorizonLeptonShellSelection`,
- and prove that the current resonance chain can be rewritten through that
  derived value.

That would already remove the explicit dependence on bare numerals from the
interface layer, even if the first derived rule is still imperfect physically.

Status: this has now been met in the minimal exact-shell proxy form. The current
Lean selector still uses the existing detuned-surface `geometricResonanceStep`
and picks the **first shell crossing** where the ratio of detuned horizon areas
reaches the required standing-wave lift. That should now be read as a **readout
effect**, not the reason the particle exists. The stronger physics target is:
particles occupy closed horizon-supported standing-wave surfaces; detuned ratios
are what an observer reads when comparing representative closed surfaces. The
same proxy target is used for τ→μ and μ→e. The support-band / closed-surface
upgrade remains open.

### Step B1a — Lapse-normalized shell readout

[`Hqiv/Physics/LapseMassReadout.lean`](../Hqiv/Physics/LapseMassReadout.lean)
now isolates the generic readout pattern:

- `shellLapse m Φ t = HQVM_lapse Φ (phi_of_shell m) t`,
- `lapseMassReadout raw m Φ t = raw m / shellLapse m Φ t`,
- proton/neutron recovery theorems at `referenceM`,
- `ShellSupportSelector` / `ShellSupportBand` for Furey- or Clifford-shaped
  state-to-shell support rules,
- `rawHadronMassFromNetwork` and `rawHadronMassFromCompositeTrace`, keeping
  hadrons on the constituent-minus-8×8-network path,
- `ShellSpectralTower`, a KK-style **shell tower** record with an explicit
  `HQIVNative` guard so it is not read as a compactified extra dimension.

This is not yet a particle-spectrum derivation. Its purpose is to make the
three layers reusable and auditable: classification chooses the channel,
HQIV shell/network dynamics supplies raw energy, and the lapse supplies the
observer readout. The missing theorem remains state-to-support selection: why a
given Furey/Clifford channel occupies a specific shell or shell band without
importing mass tables.

An equally acceptable next move is to introduce a **support-band** interface
instead, where the exact shell is only a peak, center, or representative index.
That may be the better long-term home for:

- **excited states**, as reorganizations or promotions within a support band,
- **angular momentum**, as additional structure carried by the supported
  standing-wave mode rather than by a single shell integer,
- and **looser outer generations**, whose physical support may naturally spread
  over multiple adjacent shells.

`LeptonGenerationLockin.lean` now contains a naming guard for this direction:
`OuterHorizonClosedSurfaceSupport` and
`detunedRatioReadoutOfClosedSupport`. The current exact-shell selector is
packaged only as `thresholdProxyClosedSurfaceSupport`, explicitly recording the
roadblock that the support condition is still a threshold predicate rather than
a genuine closed-surface theorem.

Candidate-theorem pass:

- **Accepted:** `modalQuarterClosedSurfaceSupport` packages modal quarter-period
  closure at any representative shell. This gives a closed-surface support
  condition without using detuned ratios as the cause.
- **Accepted:** `leptonHeavyVertexShell_has_modal_closed_surface_support`,
  `derivedLeptonMuonShell_has_modal_closed_surface_support`, and
  `derivedLeptonElectronShell_has_modal_closed_surface_support` instantiate that
  support for the current τ/μ/e representative shells.
- **Accepted:** `resonance_k_tau_mu_eq_closed_support_readout` and
  `resonance_k_mu_e_eq_closed_support_readout` in
  `ChargedLeptonResonance.lean` rewrite the active detuned factors as readouts
  between representative closed-support surfaces.
- **Rejected as the wrong theorem:** equating the threshold proxy with modal
  closed support. Their representative shell can be shared, but the propositions
  are different: threshold crossing is still a selector/readout proxy, while
  modal quarter-period closure is a support condition. Collapsing them would
  recreate the “effect as reason” problem.

### Step B2 — Acceptable first proof shapes

The first derived rule does **not** need to solve all charged-lepton physics in
one shot. Any of the following would count as real progress:

- a **closed-surface support rule** whose detuned-surface ratio is proved only
  afterward as a readout effect,
- a **monotone threshold proxy** on shell quantities
  (for example, the first shell where a detuned-surface ratio, rapidity signal,
  or other shell observable crosses a generation threshold), clearly marked as
  a proxy rather than the physical cause,
- a **two-stage outer-horizon rule**:
  one theorem selecting μ as the first shell after `referenceM` with a stated
  property, and a second theorem selecting e as the first shell after μ with the
  analogous property,
- a **support-band rule**:
  one theorem assigning each charged lepton a nonempty shell band or support
  region, together with a peak/representative shell if needed for exported
  resonance formulas,
- a **resonance-fit rule** stated entirely in HQIV shell language, where any
  comparison to PDG-style mass ratios appears only as a **check**, not as a
  hand-picked threshold in the shell selector.

### Step B2b — Cross-cutting constraints from the existing Lean stack

The charged-lepton shell theorem must remain compatible with more than the local
mass file pair.

1. **Spin / triality layer**
   `SpinStatistics.lean` is no longer only abstract: its current concrete HQIV
   realization already packages shell-aware fermionic horizon modes, bosonic
   triality observables carrying patch support, and a nontrivial same-shell
   patch-Minkowski spacelike relation consumed downstream by the continuum
   closure package. So a future lepton support rule should be narratable as a
   selection on the **fermionic** horizon modes, not as an isolated arithmetic
   trick on shell integers.
2. **Standing-wave / self-clock layer**
   The standing-wave side of the story is more plausible than any one specific
   phase-clock parametrization: on a horizon / holographic medium, there are only
   so many ways to encode quantum-number-like structure, and standing-wave
   organization is a natural candidate. `SurfaceWaveSelfClock.lean` and
   `ComptonHorizonPhase.lean` then provide one current **configuration/state**
   language on top of that picture: τ is written at lock-in with
   `selfClockPhase leptonHeavyVertexShell 0 = compton_quarter_turn_at_T_lockin`,
   while cumulative rapidity updates the phase additively. The future
   charged-lepton shell theorem may reasonably aim to stay compatible with a
   standing-wave encoding, but it should not be forced to depend on the specific
   self-clock realization unless the repo grows substantially stronger evidence
   for that exact bridge.
3. **Detuned-surface / global-detuning layer**
   `ChargedLeptonResonance.lean`, `FanoResonance.lean`, and
   `LeptonResonanceGlobalDetuning.lean` all rewrite the current resonance ratios
   through `detunedShellSurface`, `effectiveSurface`, `effCorrected`, and
   `geometricResonanceStep`. These ratios should be treated as readout effects
   of closed/support surfaces, not as the reason the states exist. This means
   the future selector/support rule should expose representative surfaces in the
   same language, so the resonance theorems survive by inheritance rather than
   by re-derivation.
4. **Continuum / horizon package layer**
   `HorizonLimitedRenormLocality.lean` already injects the HQIV spin-statistics
   statement into the horizon-limited closure package. That does **not** force a
   charged-lepton shell theorem today, but it does mean the shell story should
   stay consistent with horizon-limited causality / locality language rather than
   moving to a completely disconnected phenomenological parametrization.

In short: the selector/support rule should be **flexible in proof shape**. It
should read as a horizon/triality object when viewed from the rest of the repo,
and it may well be naturally expressible in standing-wave language. Exact shells
may survive only as peaks or representatives of a broader support region, which
also leaves room for excited states and angular momentum. But the specific
self-clock story should remain optional unless and until it is supported much
more strongly.

### Step B3 — What would count as a strong completion

Step B should be called genuinely complete only when all of the following are
true:

- `currentOuterHorizonLeptonShellSelection` is no longer definitionally equal
  to `provisionalOuterHorizonLeptonShellSelection`,
- the lemmas `leptonMuonShell_eq_provisional` and
  `leptonElectronShell_eq_provisional` are deleted or demoted to archive-only
  historical notes,
- downstream theorems like
  `resonance_k_tau_mu_eq_geometricResonanceStep` and
  `resonance_k_mu_e_eq_geometricResonanceStep` survive unchanged except for
  reading from the new derived shells,
- the new selection theorem is narratable in the paper without saying
  “we choose 81 and 16336.”

Current status: the exact-shell proxy has now reached this bar. What remains
open is the stronger physical upgrade from a first-threshold crossing shell to
a genuine shell band / support-region statement.

If the band-support upgrade lands first, replace the two “provisional shell”
lemmas with the analogous statement about provisional support bands, and treat
any retained exact shell index as a derived peak/representative rather than the
whole physical mode.

### Step B4 — Anti-goals

The following should **not** be mistaken for progress:

- hiding `81` and `16336` behind new definition names,
- adding more witness constants without a selection theorem,
- replacing the current provisional witness with a more complicated provisional
  witness,
- deriving a shell rule from PDG masses directly,
- treating a standing-wave support region as if it must collapse to one exact
  shell before excited states or angular momentum can be discussed.

The correct direction is: **shell theorem first, resonance inheritance second,
absolute mass calibration third**.

### Step C — Tie the charged-lepton absolute scale to outer closure

Focus files:
- [`Hqiv/Physics/ChargedLeptonResonance.lean`](../Hqiv/Physics/ChargedLeptonResonance.lean)
- [`Hqiv/Physics/SM_GR_Unification.lean`](../Hqiv/Physics/SM_GR_Unification.lean)

Once shell selection is real, remove dependence on `m_tau_Pl` /
`m_tau_from_resonance` as independent witnesses.

Current incremental progress:

- `ChargedLeptonResonance.lean` now contains a **τ candidate**
  `m_tau_from_lockin_surface_candidate`, built from the heavy lock-in shell, the
  charged-lepton content count, and the local detuned surface.
- The same file now also carries detuned descendants
  `m_mu_from_lockin_surface_candidate` and
  `m_e_from_lockin_surface_candidate`,
  obtained by relaxing that τ candidate through the existing τ→μ and μ→e
  resonance ratios.
- Lean proves the explicit value
  `m_tau_from_lockin_surface_candidate = 16 / 9`
  and the comparison lemma
  `m_tau_from_lockin_surface_candidate_approx_resonance`.
- Lean also proves that the μ/e descendants inherit the same relative-tolerance
  relation to the existing resonance witnesses, because they are obtained by
  dividing by the same detuning ratios.
- `ChargedLeptonResonance.lean` now isolates the exact single remaining
  normalization
  `tauLockinToResonanceScale = m_tau_from_resonance / m_tau_from_lockin_surface_candidate`.
  The theorem `chargedLepton_resonance_ladder_eq_scaled_lockin_candidate_ladder`
  proves that this one factor maps the whole τ/μ/e lock-in candidate ladder to
  the active resonance ladder. This is real progress: the ratios are no longer
  the obstacle; only the absolute τ normalization is.
- `AgeNormalizedHeavyMass.lean` now defines `ageNormalizedTauMass` from
  `AgeLapseNowScale`, `intrinsicWaveComplexity`, and the same `effCorrected`
  surface rule used by the heavy top readout. This gives a τ absolute-scale path
  whose mass unit comes from the universe-age/lapse now-scale rather than the
  `1776.86e-3` comparison literal.

This still does **not** finish the full charged-lepton table: the repo keeps
`m_tau_from_resonance` as a legacy GeV comparison/export witness, and the
support-band story for μ/e is still only represented by exact representative
shells. But it is now no longer true that the τ absolute scale has to start from
the PDG-style literal.

### Step D — Remove the proton anchor without losing the shell spine

Focus files:
- [`Hqiv/Physics/BoundStates.lean`](../Hqiv/Physics/BoundStates.lean)
- [`Hqiv/Physics/QuarkMetaResonance.lean`](../Hqiv/Physics/QuarkMetaResonance.lean)
- [`Hqiv/Physics/DerivedNucleonMass.lean`](../Hqiv/Physics/DerivedNucleonMass.lean)

This step is now partially closed: the current triadic trace witness still uses
the same three-channel composite binding at `referenceM`, but the proton mass is
no longer solved backward from `938.272`. Instead, the baryon side now uses a
common constituent baseline from the network binding plus a dressed light-quark
ladder contribution, so `protonMassFromMetaHarmonics_MeV` is a genuine
bottom-up expression again.

---

## Suggested proof priorities

If an agent has one session and wants maximum leverage:

1. Work on **Step B** if the goal is real first-principles progress.
2. Work on **Step A** if the goal is strengthening what is already most honest.
   This is now especially valuable because the boson side already has real
   theorems for the age / PDG comparison question.
3. Work on **Step D** only after the outer-horizon story is cleaner, because
   hadrons are structurally harder and currently carry more anchor burden.

---

## Paper replacement draft (Furey-forward framing)

For the current peg-hole audit of theorem-backed HQIV anchors versus Furey-style
algebraic targets, see [FUREY_ALIGNMENT_GAP_ANALYSIS.md](./FUREY_ALIGNMENT_GAP_ANALYSIS.md).

This section is intended as a **replacement target** for the current paper
discussion of particle masses. It is written to build more directly on
**Furey et al.** rather than treating the octonionic fermion story as if HQIV
had to reinvent that classification from scratch.

### Core stance

The cleanest way to present the HQIV mass program is:

1. **Furey et al. provide the algebraic classification layer.**
   The octonionic / minimal-left-ideal program gives the most natural existing
   language for fermion quantum numbers, chirality slots, and generation-style
   algebraic packaging. In HQIV terms, this is the right place to anchor the
   statement that quarks and leptons occupy specific algebraic channels inside a
   division-algebra / triality framework.
2. **HQIV provides the dynamical shell layer.**
   The light cone, monogamy split, and auxiliary-field ladder then decide where
   those algebraic channels live on the horizon ladder: `referenceM`, `T(m)`,
   `phi_of_shell m`, outer-horizon closure, and inner/meta-horizon binding.
3. **Masses should emerge only after those two layers are composed.**
   Furey-style algebra tells us **which state** we are talking about; HQIV shell
   dynamics should tell us **which shell**, **which closure scale**, and **which
   binding functional** that state picks up.

That is a stronger and more credible division of labor than asking HQIV to do
both algebraic classification and dynamical mass generation at once.

### Replacement narrative

Use the following framing in place of a stronger “all particle masses are
already derived in Lean” claim:

> We build on the octonionic fermion-classification program developed by
> Furey and collaborators, treating it as the algebraic bookkeeping layer for
> quark and lepton states. HQIV then adds the missing dynamical layer: the
> discrete light-cone shell ladder, the monogamy split `alpha + gamma = 1`, the
> auxiliary field `phi_of_shell`, and the distinction between outer-horizon
> closure and inner/meta-horizon binding. In the present formalization, the
> cleanest derived mass witnesses are bosonic and neutrino closure scales on the
> outer horizon. Charged leptons and hadrons are only partially closed: their
> algebraic placement is compatible with the Furey-style octonionic program, but
> some shell selections and absolute mass scales remain carried by explicit
> witnesses or boundary conditions rather than by fully derived theorems.

### What this lets the paper say honestly

- HQIV is **not** claiming to replace Furey's algebraic work; it is claiming to
  add a horizon-dynamical mechanism on top of it.
- The present Lean code already supports a credible statement that:
  - the **light-cone ladder** fixes `referenceM`, `alpha`, `gamma`, `T`, and
    `phi_of_shell`,
  - the **outer-horizon closure** gives the cleanest current mass witnesses,
  - and the **inner/meta-horizon** is the right place to formulate hadronic
    binding.
- The present Lean code does **not** yet support the stronger statement that
  all charged-fermion masses are already first-principles consequences of that
  combined program.

### Concrete Furey-facing roadmap consequence

If we want to “build upon Furey more directly,” the next technical steps should
be phrased this way:

1. Replace provisional charged-lepton shell picks with a theorem-level shell
   rule attached to a Furey-style algebraic state classification.
2. Replace quark shell tables with shell-selection rules that are likewise tied
   to the algebraic channel, rather than inserted as independent numerals.
3. Feed those algebraically classified states into the `8×8` binding layer so
   the composite trace is not just structural HQIV bookkeeping, but a direct
   dynamical continuation of the octonionic state assignment.

### Citation guidance

For the paper-facing version of this section, cite **Furey et al.** at the
points where the algebraic classification of fermions, minimal left ideals, and
octonionic state organization are introduced. Then cite HQIV only for the
additional dynamical claims:

- shell ladder from the light-cone combinatorics,
- monogamy-driven split `alpha`, `gamma`,
- outer-horizon closure witnesses,
- inner/meta-horizon binding.

This keeps the attribution clean: **Furey for algebraic fermion organization;
HQIV for horizon dynamics and mass-generation ambitions.**

### Do not overclaim

Until Milestones **M2–M5** are solved, the paper replacement section should
avoid saying:

- that `mu/e` shells are already first-principles outputs,
- that the proton mass is already predicted rather than boundary-fixed,
- or that the current Lean library closes the full fermion spectrum numerically.

The strongest honest claim today is narrower:

- **bosonic and neutrino closure witnesses are already light-cone faithful,**
- **charged leptons and hadrons have a credible shared architecture,**
- and **Furey-style octonionic classification is the right algebraic scaffold on
  which to finish the fermion mass program.**

---

## Yang-Mills scratchpad (target object vs dead ends)

This section is the working scratchpad for the harder claim behind the paper
replacement: if HQIV is going to say something genuinely rigorous about
**Yang–Mills**, what is the strongest algebraic object the repo can actually aim
to construct, and where does the current program still dead-end?

### The strongest candidate object currently visible

The best current algebraic target is **not** yet “a solution to Yang–Mills” in
the Clay sense. It is a more modest but still meaningful object:

1. a concrete Lie algebra inside `Matrix (Fin 8) (Fin 8) ℝ`,
2. generated from octonionic left-multiplication / derivation data,
3. carrying explicit `G₂`, `SU(2)_L`, hypercharge, and triality structure,
4. together with a faithful carrier for the fermionic bookkeeping layer,
5. and later extended by a connection / curvature formalism.

In current repo terms, the pieces already closest to that target are:

- [`Hqiv/Algebra/G2Embedding.lean`](../Hqiv/Algebra/G2Embedding.lean):
  concrete antisymmetric `8×8` generators, commutator structure, and `G₂ ⊂ so(8)`.
- [`Hqiv/Algebra/SMEmbedding.lean`](../Hqiv/Algebra/SMEmbedding.lean):
  explicit `SU(2)_L` generators, hypercharge assignments, branching bookkeeping,
  and triality-aware generation counting.
- [`Hqiv/Algebra/Triality.lean`](../Hqiv/Algebra/Triality.lean):
  honest representation cycling on `So8RepIndex`.
- [`Hqiv/Algebra/SO8ClosureAbstract.lean`](../Hqiv/Algebra/SO8ClosureAbstract.lean):
  the strongest current statement about `so(8)` closure and the key warning that
  **linear span is not the same as Lie-generated closure**.
- [`Hqiv/Physics/SM_GR_Unification.lean`](../Hqiv/Physics/SM_GR_Unification.lean):
  the top-level proposition bundle
  `YangMills_SM_GR_Unification_statement`.

### What that object should become, rigorously

If we want the most rigorous algebraic object possible before touching analytic
Yang–Mills, the target should be a record or package with fields roughly of the form:

- a Lie algebra `g`,
- a proof that `g ≃ so(8)` or a named Lie subalgebra of the `8×8` matrices,
- distinguished subalgebras / generators for `G₂`, `SU(3)_c`, `SU(2)_L`, and `U(1)_Y`,
- a triality action on the relevant representation carriers,
- a Furey-style fermion state space or minimal-left-ideal carrier,
- and a connection / curvature interface over that algebra.

That would be a real algebraic answer to the question:

> “What is the exact gauge algebra / representation object from which the HQIV
> Yang–Mills narrative is supposed to flow?”

It would **not yet** answer the Clay Yang–Mills problem, but it would replace
the current mixture of algebra theorems, witness assignments, and proposition
bundles with one canonical mathematical object.

### The immediate rigorous next milestone

The highest-value next algebra step is:

**Replace the current “span/closure” story with an actual Lie-subalgebra object
generated by `G₂ ∪ {Δ}`.**

This is the exact place where the current repo is closest to rigor and also
closest to dead-ending if we are not careful.

Why this matters:

- `SO8ClosureAbstract` already proves that the **linear span** of the 14 `G₂`
  generators plus `Δ` cannot equal all of `so(8)` as a plain vector space.
- `ASSUMPTIONS.md` explicitly says this was a mistaken target and that the
  correct notion is the **Lie-subalgebra generated by iterated brackets**.
- So the honest next theorem is **not**
  `spanℝ(G₂ ∪ {Δ}) = so(8)`;
  it is a theorem that the **Lie closure** generated by those elements equals
  the desired `so(8)` object.

Until that object exists, the Yang–Mills story is still structurally plausible
but not algebraically packaged in the strongest possible way.

### Current dead ends

These are the real places the program dead-ends today if one asks for a fully
rigorous Yang–Mills answer:

1. **Linear span dead end**

   This dead end is already known and documented:

   - the bare vector-space span of `G₂ ∪ {Δ}` has dimension at most `15`,
   - `so(8)` here is `28`-dimensional,
   - so any attempt to prove closure by plain `Submodule.span` is mathematically
     the wrong target.

   This is not fatal, but it means the proof must move to the correct category:
   **Lie subalgebras**, not linear spans.

2. **Representation bookkeeping is ahead of the canonical object**

   `Triality.lean` and `SMEmbedding.lean` already expose useful pieces, but they
   are not yet assembled into one canonical “HQIV gauge object.” In particular,
   some parts are still bookkeeping-level rather than a final structural package.

3. **No connection/curvature object yet**

   The repo has the gauge algebra ingredients, but not yet a single canonical
   Yang–Mills connection / curvature package built on top of them. Without that,
   the story remains an embedding / classification story rather than a true
   gauge-theoretic object.

4. **Analytic Yang–Mills dead end**

   Even if the full algebraic object were completed, that still would **not** be
   the Clay Yang–Mills existence-and-mass-gap result. The analytic jump to a
   nonperturbative quantum Yang–Mills construction is simply not present in this
   repo right now.

### Honest interpretation of the current top-level theorem

`Hqiv.HQIV_satisfies_YangMills_SM_GR_Unification` should currently be read as a
**proposition bundle expressing the intended unification statement**, not as the
end of the algebraic story.

The strongest honest reading is:

- the repo has enough proved algebraic and witness-level structure to state a
  coherent HQIV unification proposition,
- but the **canonical gauge object** underlying that proposition is still only
  partially assembled,
- and the analytic Yang–Mills layer is still open.

### Best rigorous path forward

If the goal is “the most rigorous algebraic object possible,” the roadmap should
now prefer this order:

1. Keep the explicit generated object
   `Hqiv.Algebra.g2DeltaGeneratedLie := LieSubalgebra.lieSpan ℝ (G₂ ∪ {Δ})`
   as the base theorem target.
2. Use the now-proved equality
   `g2DeltaGeneratedLie = so8LieSubalgebra` and the resulting
   `so8Generator_mem_g2DeltaGeneratedLie` bridge theorem as the algebraic base.
3. Package the resulting algebra as the canonical HQIV gauge object.
4. Attach the `SMEmbedding` and `Triality` data to that object, rather than
   leaving them in parallel files.
5. Only then build a connection / curvature / Yang–Mills action layer on top.
6. Only after all of that ask whether any genuine analytic Yang–Mills theorem is
   even in reach.

### Current packaging status

There is now a concrete package target for the **current strongest assembled
object**: `Hqiv.Physics.HQIVYangMillsPackage`. The intent of that module is not
to claim the final generated Lie-subalgebra theorem, but to stop scattering the
current ingredients across unrelated files. It bundles:

- the canonical finite-dimensional carrier `span ℝ (range so8Generator)`,
- the 28-generator bracket/basis package from `GeneratorsLieClosure`,
- membership witnesses for `G₂`, `Δ`, `SU(2)_L`, and hypercharge,
- the triality `= 3` counting witness,
- and the already-proved shell-dynamical attachments (`α = 3/5`,
  `γ = 2/5`, rapidity/polar-angle phase alignment, unification proposition
  bundle).

That is a **real packaging improvement**, because future theorems can now target
one explicit object instead of repeatedly restating the same carrier/basis/data
facts. But it is still not the end of the story.

There is now also a **package-level generated-carrier abstraction**
`Hqiv.Physics.hqivGeneratedGaugeCarrier`, and the canonical
`hqivYangMillsPackage` is phrased in terms of that name rather than directly in
terms of `span ℝ (range so8Generator)`. For now this is intentionally a
lightweight alias to the old span carrier, because promoting
`Hqiv.Algebra.G2DeltaGeneratedLie` into the normal compiled dependency graph is
still expensive enough to be disruptive during ordinary package work. This is a
deliberate staging move, not a claim that the heavy bridge has been eliminated.

There is now also a lightweight algebra module
`Hqiv.Algebra.G2DeltaGeneratedLie` that makes the first honest generated-object
step explicit:

- `G2UnionDelta` is defined as the physical seed set,
- `g2DeltaGeneratedLie := LieSubalgebra.lieSpan ℝ (G₂ ∪ {Δ})`,
- the seed generators are proved to lie in that generated Lie algebra,
- an explicit 28-element witness family is constructed inside that generated Lie
  algebra,
- the generated Lie algebra is shown to have full dimension `28`,
- the honest skew-adjoint Euclidean `so(8)` model is also shown to have
  dimension `28`,
- and the generated Lie algebra is therefore identified with that honest
  `so(8)` model.

So the repo is no longer missing either the *definition* of the generated
object or the bridge from the physical seed set to the packaged `so(8)` basis:
`so8Generator_mem_g2DeltaGeneratedLie` now gives that inclusion explicitly.

The next theorem that would genuinely tighten rigor is:

> rebase the packaged HQIV gauge object and the attached SM/triality structure
> directly on `Hqiv.Algebra.g2DeltaGeneratedLie` as a built dependency, so that
> the temporary package-level alias can be replaced by the actual generated Lie
> carrier without relying on the old span package as an implementation detail.

### Where we likely stop, for now

If we are strict about rigor, the likely stopping point in the near term is:

- a well-packaged **finite-dimensional algebraic HQIV gauge object**,
- with explicit subalgebras, representations, and triality,
- plus shell-dynamical HQIV attachments,
- but **without** claiming a solved classical or quantum Yang–Mills existence
  theory.

That is not failure. It is probably the correct honest endpoint of the current
formalization horizon unless the repo pivots much harder into constructive gauge
theory or PDE/QFT formalization.

---

## Post-Step-B closure ladder

The previous lepton-shell roadmap target is now closed at the **exact-shell proxy**
level: `currentOuterHorizonLeptonShellSelection` is no longer the provisional
numeral witness, and the resonance formulas downstream inherit a derived
threshold selector.

That means the next mass roadmap should no longer be organized primarily as “pick
better shell integers.” The better organizing question is now:

> which quantum-number decorations are added, in what order, to a stable
> horizon-supported standing-wave closure?

The current best HQIV working order is:

1. **Bosonic closure / neutral outer-horizon layer first**
   The repo already has a clean boson/neutrino outer-closure sector in
   `DerivedGaugeAndLeptonSector.lean`. This is the least entangled first-principles
   mass layer presently available.
2. **Spin-first neutral fermion layer**
   Treat the minimal matter closure as a neutral spin-carrying mode. In current
   physics language this is the neutrino-like rung: no charge decoration, no
   colour bookkeeping, just the minimal fermionic closure class.
3. **Charge decoration layer**
   Charged leptons should be read as the next enrichment of the same standing-wave
   closure story: spin closure plus an internal charge orientation / handed phase
   bias, still without colour.
4. **Colour composition layer**
   Quarks and baryons enter only after the colour/triality composition data is
   added. This is a genuinely more complicated closure class than the charged
   lepton layer, not just “another fermion with a different decimal mass”.
5. **Gravity is not another particle rung**
   The working HQIV target should be that rapidity / lapse / transport already
   carry the gravitational sector. Any spin-2-looking readout is to be treated as
   a collective field mode or continuum transport statement, not automatically as
   evidence for a fundamental graviton.

### New milestone order

| Milestone | Goal | Done when |
|-----------|------|-----------|
| **M2.5 — Closure hierarchy packaging** | Re-express the existing ν / charged-lepton / quark bridge as a spin/charge/colour closure hierarchy rather than only as a numeric mass comparison. | The bridge files can say “ν = spin-only closure, charged lepton = spin+charge, quark = spin+charge+colour” in theorem-backed terms. |
| **M3 — Neutral spin-first rung** | Make the neutrino sector the canonical first fermionic rung after bosonic closure. | There is a theorem-backed statement that the derived ν witnesses are the minimal neutral fermionic closure layer and sit below the charged-lepton layer without importing extra mass tables. |
| **M4 — Charge-decorated lepton rung** | Rebuild the charged-lepton story as charge-decoration of the same closure program, rather than as an isolated shell arithmetic module. | The τ/μ/e ladder is narratable as a charge-decorated standing-wave closure, with shell selectors acting as support readouts rather than the ontology itself. |
| **M5 — Colour-composite baryon rung** | Reframe quark/baryon masses as colour/triality-enriched closure data rather than just separate shell tables. | The quark/baryon modules expose colour/triality composition as the reason the baryon sector sits above the charged-lepton sector. |
| **M6 — No fundamental graviton target** | State gravity as a transport/field sector and isolate what would need to be shown to avoid a fundamental spin-2 particle ontology. | The roadmap has a theorem target of the form “gravity requires no isolated one-particle spin-2 HQIV carrier”, even if the full proof remains open. |

### Current pinned gaps (M3-M6)

**M3 — Neutral spin-first rung**

- **Now theorem-backed:** the ν ladder is explicitly rewritten through `neutralClosureWitness`
  in `ConservedContentMassBridge.lean`, and ν is the `spinOnly` closure class in the
  current closure taxonomy. The consolidated theorem
  `neutrino_ladder_is_current_neutral_spin_first_rung` now packages the ν ladder,
  `neutralClosureWitness`, and the minimal-rank statement over the current
  `FermionContentClass` enumeration.
- **Gap:** this is still only the **smallest enumerated closure class**, not a stronger
  uniqueness/minimality theorem over a wider fermionic closure space.
- **Best next theorem target:** define the wider closure search space, or explicitly
  decide that the next useful step is M4 packaging instead of trying to prove a
  global uniqueness theorem too early.

**M4 — Charge-decorated lepton rung**

- **Now theorem-backed:** the τ/μ/e candidate ladder is packaged as a
  `chargeDecorated` closure in `ConservedContentMassBridge.lean`, and the active μ/e
  shell selector is now theorem-backed as the first `chargeDecorated` support
  crossing in `LeptonGenerationLockin.lean`. The theorem
  `chargedLepton_ladder_is_chargeDecorated_rung_on_neutral_base` now packages
  the charge-decorated rung above the neutral base, signed visible charges, and
  the τ→μ→e candidate relaxation order.
- **Gap:** the charged-lepton story still does **not** remove the active
  `m_tau_from_resonance` GeV witness from every export; that remains comparison
  migration work. `AgeNormalizedHeavyMass.lean` now supplies
  `ageNormalizedTauMass`, an absolute age/lapse readout path for the heavy
  charged-lepton scale.
- **Best next theorem target:** either connect the support selector more directly
  to the package theorem, or move to Step C and test whether the lock-in τ
  candidate can replace the active τ resonance witness without breaking the
  exported comparisons.

**M5 — Colour-composite baryon rung**

- **Now theorem-backed:** the quark/baryon rung is tied to the `colorComposed`
  closure class in `ConservedContentMassBridge.lean`, and baryon binding is now
  explicitly packaged as a three-channel composite-trace / network mass at
  `referenceM`; additionally, `QuarkMetaResonance.lean` now derives the proton
  and neutron from a common constituent baseline plus a dressed light-quark
  ladder, rather than feeding `protonAnchorMass_MeV` back in as an input. The
  repo also now exposes a theorem-backed **visible-state / residual split**:
  visible shell states are `neutral / positive / negative`, while the quark
  fractions `2/3` and `-1/3` are isolated as internal algebraic residual
  bookkeeping; the top and heavy charged-lepton sectors are aligned at the
  shared lock-in index `referenceM`. The heavy up/top channel now also has the
  age/lapse readout `ageNormalizedTopMass`; the legacy `m_top_GeV` literal is a
  comparison/export witness. The public heavy color band is still retained for
  existing APIs, and the down-like heavy band
  is now theorem-backed through the heavy-shell cross-detuning and the `2 × 3`
  visible-state bookkeeping budget, so the active API no longer treats the full
  down branch as a naive `top / 2` copy.
- **Gap:** the proton anchor has been removed from the constituent definition
  path, and the constituent/proton ladder now reads both light channels from
  the active visible-state API. The current nucleon layer uses one shared
  light-rung dressing scale plus one smaller residual detuning scale; on the
  present witness numerics this lands near `m_p ≈ 970.41 MeV`,
  `m_n ≈ 971.76 MeV`, `Δ ≈ 1.35 MeV`.
- **Gap:** the old shell tables still drive the resonance-product bookkeeping,
  and the down-type legacy comparison ladder still carries `m_bottom_GeV` as a
  witness. The strongest exported cross-sector theorem is still
  `ν < τ_candidate < heavy_color_band`, rather than a fully closure-native
  baryon/lepton mass package. The proton is now in a much more reasonable band,
  but the active ladder still has only one shell-bookkeeping story, not yet a
  deeper proof that the visible compression and constituent energy budget are
  the unique HQIV realization.
- **Best next theorem targets:** (i) replace the remaining legacy down-type
  comparison witnesses with the same heavy-shell detuning and visible-budget
  story used by the active API, and (ii) promote the new visible-state
  hierarchy into a direct
  baryon-vs-charged-lepton exported mass package.

**M6 — No fundamental graviton target**

- **Now theorem-backed:** gravity is formalized as a lapse / scalar-field /
  homogeneous-Friedmann / first-order `g_tt` readout sector (`HQVMetric`,
  `GRFromMaxwell`, `LightConeMaxwellQFTBridge`, `HQVMPerturbations`), i.e. as a
  transport-fed field/readout package rather than a particle module.
- **Milestone (interface packaging):** `Hqiv.Physics.HQIVGravityReadoutScalars` records
  the roadmap’s **(i)** target in Lean: `HQVM_lapse` is exhausted by the three real
  slots `(Φ, φ, t)` (`HQVMGravityLapseArgumentTuple`), first-order lapse and `g_tt`
  linearization use only the declared differentials / one scalar `δN`, and a would-be
  tensor polarization index is intentionally **`Fin 0`** (`HQIVFormalGravitonPolarizationIdx_elim`).
  **Narrative surface:** the same file proves the **fixed null-lattice vs time** split
  (`latticeSimplexCount_*_constant_in_observerTime`, `shellSurface_*_constant_in_observerTime`) and
  that **coordinate time** drives lapse / `timeAngle` when `(Φ, φ)` are fixed (`timeAngle_diff`,
  `HQVM_lapse_diff_fixedPotentials`), with `g_tt = -N²` (`HQVM_g_tt_eq_neg_sq_lapse`). This is the
  formal “time is the dynamical knob; the grid is not a function of `t`” story—not a full affine
  connection geodesic theorem.
  **(ii)** is stated at the **type** level: `SMGaugeCarrierMat8` names the usual `8 × 8`
  matrix bookkeeping for SO(8) generators vs scalar lapse values in `ℝ`—not a
  Hilbert-space disjointness theorem.
- **Gap (still open):** no metaphysical “fundamental gravitons do not exist” theorem;
  no full spin-2 / TT projector classification; no uniqueness proof that no future
  extension may adjoin tensor modes.
- **Best next theorem targets (beyond the packaging file):** strengthen readout
  claims if the metric API gains spatial anisotropy; relate any new modes explicitly
  to `ObserverChart` / patch nets so “no extra particle carrier” is a structural
  statement, not only a documentation guard.

### Attack now

The first clean attack should be **M2.5 / M3**, not the graviton claim.

Concretely:

1. keep `ConservedContentMassBridge.lean` as the current spin / charge / colour
   hierarchy package; M3 now has the consolidated theorem
   `neutrino_ladder_is_current_neutral_spin_first_rung`,
2. do **not** pretend this is a global uniqueness theorem over all possible
   fermionic closure spaces; the proof is intentionally scoped to the current
   three-class bridge,
3. charged leptons now have the package theorem
   `chargedLepton_ladder_is_chargeDecorated_rung_on_neutral_base`; do not
   confuse that with Step C’s still-open absolute τ-scale problem,
4. the **M6 interface milestone** is now in `HQIVGravityReadoutScalars`; a full
   “no fundamental spin-2 carrier” claim remains future work once the transport /
   patch formalism is richer.

### Honest boundary

This new roadmap is **not** yet a theorem that HQIV has derived all quantum
numbers from first principles. It is a better ordering principle for the next
formalization steps:

- bosonic/neutral closure first,
- then minimal fermionic spin closure,
- then charge decoration,
- then colour composition,
- and only after that the gravity-as-field / no-graviton question.

When comparing witness numerics to PDG values, keep the uncertainty language
honest:

- a candidate may be **close as an HQIV witness** without lying inside the
  laboratory error bars,
- the experimental uncertainty remains the measurement uncertainty,
- while the current HQIV theory/readout uncertainty is typically larger because
  lapse normalization, support selection, and other observer/readout layers are
  not yet collapsed to a unique final observable prediction.

### Presentational audit (substrate vs machinery vs anchors)

Use this checklist when explaining the mass story to a new reader—**narrative gaps** are mostly
**documentation and uniqueness** questions, not “missing `sorry` cleanup”:

- **Lowest discrete pins:** `qcdShell`, `latticeStepCount` (hence `referenceM`) in
  `OctonionicLightCone` are **explicit `Nat` definitions**. Proved `α`/`γ` and `T_lockin` identities are
  **downstream given** those indices—not a proof that “4” is the unique shell from pure combinatorics
  inside this file.
- **Charged leptons:** τ at lock-in matches quark narrative; μ/e shells use a **clean** detuned-surface
  threshold (`octave = 2`) instead of legacy integer smuggling. The heavy τ scale can now use
  `ageNormalizedTauMass`; `m_tau_from_resonance` (PDG central) remains a legacy GeV comparison
  witness. Ratios use the same geometric factors as quarks. `m_tau_from_lockin_surface_candidate`
  is a **separate normalization**; the `≈` lemma is an alignment check between languages.
- **Quarks / baryons:** resonance spine + composite-trace nucleon packaging reuse the **same**
  `geometricResonanceStep` formalism; the heavy top channel has the new `ageNormalizedTopMass`
  route, while shell tables and `m_top_GeV` / `m_bottom_GeV` remain legacy comparison/export
  witnesses, not uniqueness theorems.
- **Spin / charge / colour bridge:** `ConservedContentMassBridge` delivers **proved ordering** and a
  clear taxonomy; read it as **classification + inequalities** anchored to the resonance modules, not
  as a replacement for those anchors.

## Maintainer actions

When this roadmap changes materially:

- add newly solid mass outputs to [`THEOREMS.md`](./THEOREMS.md),
- record any new explicit anchors or witness assumptions in
  [`ASSUMPTIONS.md`](./ASSUMPTIONS.md),
- and keep the paper narrative aligned with the same “faithful / partial /
  open” distinctions.

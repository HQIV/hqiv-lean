# Furey Alignment Gap Analysis

This note is a **peg-hole audit** for agents: how much of a Furey-style
algebraic fermion/classification program already has a theorem-backed HQIV peg,
where the repo is only narratively compatible, and which holes are still open.

The point is **not** to import Furey's Clifford/minimal-left-ideal machinery
wholesale. The point is to identify the strongest **accepted anchor point** in
this repo from which a serious bridge can honestly be built.

## Scope

Use this note when the question is:

- "What in HQIV already lines up with Furey?"
- "Where are we only saying compatible things in prose?"
- "What is the best accepted algebraic anchor to cite before the mass bridge is complete?"

This note does **not** claim that HQIV has already formalized Furey's program,
nor that Furey's minimal-left-ideal language has already been replaced by an
equally strong HQIV-native theorem layer.

## Recommended anchor

The strongest currently acceptable HQIV anchor point is the bundle:

- [`Hqiv/Algebra/OctonionSpinorCarrier.lean`](../Hqiv/Algebra/OctonionSpinorCarrier.lean)
- [`Hqiv/Algebra/SMEmbedding.lean`](../Hqiv/Algebra/SMEmbedding.lean)
- [`Hqiv/Algebra/Triality.lean`](../Hqiv/Algebra/Triality.lean)
- [`Hqiv/Physics/HQIVYangMillsPackage.lean`](../Hqiv/Physics/HQIVYangMillsPackage.lean)

That bundle already gives:

- a theorem-backed 8-dimensional spinor carrier,
- explicit SM-facing generator and hypercharge bookkeeping,
- triality/generation counting,
- and one packaged algebraic object that downstream work can cite.

The honest limitation is that this anchor is **not yet equivalent** to a
Furey-style minimal-left-ideal formalization. It is the strongest **accepted
HQIV-native peg**, not a proof of Furey equivalence.

## Target matrix

| Furey-style target | Best HQIV peg now | Status | Why this is or is not enough |
|---|---|---|---|
| Fermion state space / carrier | [`OctonionSpinorCarrier.lean`](../Hqiv/Algebra/OctonionSpinorCarrier.lean) | theorem-backed but weaker/different | We do have a concrete `8s` carrier as `Fin 8 -> R`, but not minimal left ideals, no Clifford action layer, and no theorem identifying HQIV's carrier with Furey's preferred state space. |
| Quantum-number assignment and chirality bookkeeping | [`SMEmbedding.lean`](../Hqiv/Algebra/SMEmbedding.lean) | theorem-backed but mixed with placeholders | There are explicit `SU(2)_L` generators, hypercharge assignments, charge bookkeeping, chirality counts, and now explicit witness lemmas separating fractional quark-slot charges (`2/3`, `-1/3`) from the integer/neutral lepton-visible charges. But `G2_contains_SM_subgroup : True` and `hyperchargeBlockCorrect : Prop := True` show that some bridge claims are still placeholder-level rather than deep structural theorems. |
| Triality / generation structure | [`Triality.lean`](../Hqiv/Algebra/Triality.lean), [`SMEmbedding.lean`](../Hqiv/Algebra/SMEmbedding.lean) | theorem-backed but weaker/different | Triality is real in the repo as a 3-cycle on `So8RepIndex`, and generation count is theorem-backed as `Fin 3` arithmetic. But this is still a label/combinatorics layer more than a full "lightcone axioms force Furey-style generations" theorem. |
| Gauge-subalgebra and hypercharge embedding | [`G2Embedding.lean`](../Hqiv/Algebra/G2Embedding.lean), [`SMEmbedding.lean`](../Hqiv/Algebra/SMEmbedding.lean), [`HQIVYangMillsPackage.lean`](../Hqiv/Physics/HQIVYangMillsPackage.lean) | theorem-backed with explicit gaps | This is currently the strongest bridgeable layer. The package records G2/Delta membership, `SU(2)_L`, hypercharge, triality count, and `alpha/gamma`. But the strongest claims still depend on some witness-level bookkeeping and do not yet amount to a Furey-style representation theorem. |
| Spin/statistics and locality realization | [`SpinStatistics.lean`](../Hqiv/Physics/SpinStatistics.lean) | theorem-backed but still weaker/different | The concrete HQIV realization now uses shell-aware fermion/boson mode carriers, a nontrivial same-shell patch-Minkowski spacelike relation, and a bilinear that preserves patch support. But it is still not a full operator-level null-lattice realization of the desired structure. |
| How algebraic labels feed the mass ladder | [`ConservedContentMassBridge.lean`](../Hqiv/Physics/ConservedContentMassBridge.lean), [`LeptonGenerationLockin.lean`](../Hqiv/Physics/LeptonGenerationLockin.lean), [`ChargedLeptonResonance.lean`](../Hqiv/Physics/ChargedLeptonResonance.lean), [`AGENTS/MASS_DERIVATION_ROADMAP.md`](./MASS_DERIVATION_ROADMAP.md) | theorem-backed visible-state split, but still not a full algebra-to-shell selector | HQIV now has theorem-backed content-count / resonance bridges plus an explicit split between visible shell states (`neutral / positive / negative`) and quark residuals generated from simple loop multiplicities over the color-composed denominator. The public heavy quark band is now top-anchored at lock-in, while the down-like heavy visible state is exported through heavy-shell detuning and the `2 × 3` visible-state budget rather than a naive half-weight rule. But the stronger Furey-style claim, namely that algebraic state classification uniquely chooses the shell/support rule, is still roadmap-level rather than theorem-backed. |

## Strong pegs already present

These are the strongest theorem-backed HQIV pegs worth building around.

### 1. A concrete 8-dimensional spinor carrier

[`OctonionSpinorCarrier.lean`](../Hqiv/Algebra/OctonionSpinorCarrier.lean)
keeps the carrier lightweight and theorem-backed:

- `OctonionSpinorCarrier := Fin 8 -> R`
- module/additive structure
- `octonionSpinorCarrier_dim`

This is enough to say "HQIV has a real 8-dimensional spinor carrier."
It is **not** enough to say "HQIV has formalized Furey's minimal left ideals."

### 2. A usable SM bookkeeping layer

[`SMEmbedding.lean`](../Hqiv/Algebra/SMEmbedding.lean) already packages:

- `so8ActOn8s`
- `su2_L_gen_*`
- `hyperchargeGenerator`
- `hypercharge_assignments_correct`
- `chirality_and_nu_R`
- `sm_quantum_numbers_one_generation`

That means HQIV does have a theorem-backed place to attach Furey-style
questions about:

- quantum numbers,
- chirality slots,
- and generation-style representation bookkeeping.

But this file also contains explicit signs that the bridge is incomplete:

- `G2_contains_SM_subgroup : True := trivial`
- `hyperchargeBlockCorrect : Prop := True`

So this is a real peg with visible unfinished joints.

### 3. Triality as a real label structure

[`Triality.lean`](../Hqiv/Algebra/Triality.lean) gives:

- `trialityCycle`
- `triality_cycle_order_3`
- `triality_cycles_reps`
- `card_so8_eight_dim_irreps`
- `exactly_three_fermion_generations_from_HQIV_axioms`

This is enough to support the honest statement:

> HQIV has theorem-backed triality/generation counting at the level of a
> three-label representation cycle.

It is **not** yet enough to support:

> HQIV has derived Furey-style fermion generations from the lightcone axioms in
> the strong algebraic sense.

One warning sign is `triality_preserves_bracket`, whose proof is just `rfl`;
that is a formal identity, not a deep realization of the outer automorphism on
the full algebraic data.

### 4. A single packaged algebraic object

[`HQIVYangMillsPackage.lean`](../Hqiv/Physics/HQIVYangMillsPackage.lean) is the
best current "accepted anchor point" because it packages:

- the gauge carrier,
- basis/bracket expansion,
- `G2`/`Delta` membership,
- `SU(2)_L` and hypercharge membership,
- triality rep count,
- forced `alpha/gamma`,
- rapidity/phase alignment,
- and the current unification statement.

If the question is "what one object should we cite before building a Furey
bridge?", this is the best answer currently in the repo.

## Places where the bridge is only narrative

These are the places where the repo currently **sounds** more Furey-aligned than
it has actually proved.

### `SpinStatistics`

[`SpinStatistics.lean`](../Hqiv/Physics/SpinStatistics.lean) proves a useful
abstract theorem:

- `spin_statistics_from_axioms`
- `HQIV_satisfies_SpinStatistics_from_triality_and_causality`

The concrete realization is now materially better than a toy placeholder:

- fermionic modes carry shell index, local patch, and octonion-spinor data,
- bosonic observables remember the patch support of the bilinear,
- locality is checked with the patch-Minkowski chart from `PatchQFTBridge`,
- the file proves both a spacelike witness and a non-spacelike witness,
- and `SpinStatisticsOperatorBridge` now sends HQIV mode pairs to concrete
  smeared interval-max operators whose observable and Pauli commutator vanish on
  spacelike patch support.

So this is now a real bridge anchor for the QM/QFT side. The remaining gap is
that it is still not a full interacting operator-level or full physical
null-lattice realization of the desired structure.

### `NuclearAndAtomicSpectra`

[`NuclearAndAtomicSpectra.lean`](../Hqiv/Physics/NuclearAndAtomicSpectra.lean)
mentions Furey explicitly in prose:

- "Furey algebraic classification + HQIV horizons"
- "full HQIV + Furey construction"
- "`Fermion` ... implemented via Furey-style minimal left ideals"

But the actual file is clear that its theorems are definitional repackagings of
existing HQIV structures. So the Furey layer here is a **narrative target**, not
a proved algebraic input.

### Mass roadmap

[`AGENTS/MASS_DERIVATION_ROADMAP.md`](./MASS_DERIVATION_ROADMAP.md) already has
a strong and honest Furey-forward framing:

- Furey = algebraic classification layer
- HQIV = dynamical shell/mass layer

That is currently the right framing, but it is still a **roadmap claim**. The
actual theorem bridge from "Furey-style algebraic channel" to "HQIV shell/support
selection" does not yet exist.

## Explicit holes / blockers

These are the main holes that keep the bridge from being stronger.

1. No theorem-backed minimal-left-ideal or Clifford replacement layer in Lean.
2. No theorem identifying the HQIV spinor carrier with a Furey-style fermion
   state space.
3. No strong branching theorem from the actual algebra to the full stated SM
   decomposition; some bridge claims are still placeholders/witnesses.
4. No full interacting operator-level null-lattice locality realization in
   `SpinStatistics`; the current package now reaches mode level plus smeared
   interval-max operator witnesses, but is still not the final physical
   realization.
5. No theorem that triality/generation structure is forced by the lightcone
   ladder rather than by the chosen finite label type.
6. No theorem that algebraic classification chooses the charged-lepton or quark
   shell/support rule.

## What HQIV should probably keep, translate, or reject

### Translate into HQIV-native algebra

- fermion-classification ambitions
- quantum-number/chirality bookkeeping
- triality-aware generation structure
- algebra-to-mass bridge goals

These should be translated into HQIV's own lightcone/rapidity/gauge package
rather than imported as a Clifford-first formalism.

### Keep as conceptual compatibility only

- broad comparisons between minimal-left-ideal organization and HQIV's octonion
  carrier bookkeeping
- the claim that Furey gives the right algebraic *shape* for fermion
  classification

These are useful, but should remain explicitly conceptual until theorem-backed.

### Reject as required bridge prerequisites

- the idea that HQIV must formalize Clifford/minimal-left-ideal machinery in
  order to have any accepted algebraic anchor
- the idea that Furey alignment is all-or-nothing

The current repo already has an HQIV-native algebraic anchor strong enough to
support a serious bridge audit, even though it does not yet reproduce Furey's
preferred formalism.

## Best accepted anchor to cite now

If the user wants one concise statement, the best honest version is:

> HQIV's best accepted algebraic anchor point is the package made from
> `OctonionSpinorCarrier`, `SMEmbedding`, `Triality`, and `HQIVYangMillsPackage`.
> This is strong enough to support a meaningful comparison with Furey-style
> octonionic fermion classification, but not yet strong enough to claim formal
> minimal-left-ideal equivalence or a completed fermion-state bridge.

## Best next bridge steps

If future work wants to strengthen the comparison without overcommitting:

1. Replace placeholder bridge slots in [`SMEmbedding.lean`](../Hqiv/Algebra/SMEmbedding.lean)
   with sharper algebraic statements.
2. Split `Triality.lean` into "representation-label counting" versus any future
   deeper automorphism realization, so agents do not overread the current file.
3. Upgrade `SpinStatistics.lean` from the current patch-Minkowski
   mode-plus-smeared-operator realization toward a genuinely interacting
   operator-level null-lattice locality model.
4. Add a theorem-facing bridge from algebraic state classification to shell or
   support selection in the mass ladder.

Until those land, the correct stance is:

- **real algebraic pegs exist,**
- **the bridge to Furey is partly open,**
- and **the accepted anchor should be HQIV-native, not a narrative promise of
  minimal-left-ideal equivalence.**

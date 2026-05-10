# HQIV for working physicists (primer)

This note is a **bridge** from Hamiltonian language to the **sequential digital** layer formalized in Lean (`Hqiv/QuantumComputing/HamiltonianToGateMapping.lean`). It is not a substitute for the axiom text in the main HQIV programme; it only fixes vocabulary so bench physicists can read the code without category-theory detours.

## What problem the module solves

In continuum QM you write \(H\) and evolve with \(U(t)=\exp(-\mathrm{i}Ht)\). In the HQIV **finite** carrier, there is no claim that an arbitrary spatially extended \(H\) acts simultaneously on the whole register while preserving the proved inner-product story. Instead, the formal layer asks you to **sequence** local updates: at each tick you declare which shell/slot is active, which gates fire, and which monogamy certificate backs that tick.

## Mental model

1. **State:** `DiscreteState L` — amplitudes on the harmonic index grid at cutoff \(L\).
2. **One tick:** `HQIVEvolutionStep` = monogamy metadata × finite gate list × skew/lapse increment.
3. **Schedule:** `SequentialHQIVEvolution` = ordered list of ticks (head first in the chosen lapse gauge).
4. **Run (dense, fully certified with existing IP/norm lemmas):** `runSequentialEvolution E f` applies the same composition as `E.toEquiv` / `digitalEvolution`.
5. **Run (sparse bookkeeping):** `runSparseSequentialOSH E r` folds `OSHoracle.applyGateSparse` over flattened gates; Lean proves worst-case support scaling (`oshSparseSequentialFold_length`, `nBodySequentialSparseLength_bound`), **not** bitwise equivalence with dense evolution for all inputs.

## How to translate a Hamiltonian (checklist)

The module docstring spells this out verbatim; in one sentence: **expand \(H\) into a sum/product of patch-local terms, order them causally, attach a `correctedCkwMonogamyPhi` proof per tick, and map each term to admissible `HQIVGate`s plus a `SkewIncrement`.**

## Worked patterns in Lean

- **Frequency-staged HO proxy:** `hoFrequencyBeatingSequential` alternates \(\ell=0\) and \(\ell=1\) `phaseGate` pulses and uses `SkewIncrement.hoFrequencySkew` so the skew record tracks \(\phi_{\mathrm{rat}}(\ell)\) and a lapse schedule \(N=\mathrm{HQVM\_lapse}(\Phi,\phi,k\delta t)\).
- **Two-body term without simultaneous coupling:** `twoBodySequentialSlots` applies slot **A** then slot **B** with **different** CKW data on the second tick (`correctedCkwMonogamyPhi_quarter_pair`), illustrating sequentialization rather than a tensor two-qubit gate.

## Where to read next

- `papers/paper/octonion_lightcone_to_oshoracle.tex` — digital gates, sparse pipeline, and (updated) paragraph on `HamiltonianToGateMapping`.
- `Hqiv/QuantumComputing/DiscreteSchrodinger.lean` — `digitalEvolution` and append lemmas used by `toEquiv`.

# Mass ladder: phenomenology vs first-principles (HQIV_LEAN)

## What the axioms actually fix

- Discrete null-lattice / lock-in structure supplies **`referenceM`**, **`T_lockin`**, and shared **detuned surface** combinatorics (`shellSurface`, `rindlerDetuningShared`, `geometricResonanceStep` in `Hqiv.Physics.FanoResonance` / `GlobalDetuning`).
- **Octonionic zeta / mod‑7 partition / `fano_prime`** are lattice-native bookkeeping (see `OctonionicZeta`): one global shell index `m`, terms tagged by residue mod `7`. **Target design:** each Fano direction gets its **own** motivated shell ladder and associated “prime” slot — **not** arrived at in the current proofs.

## What is *not* derived from those axioms (current repo state)

The following still contain **explicit ℕ shells and/or GeV anchors** chosen (or left as placeholders) so that **derived masses sit near PDG-style reference values** or so that SM unification lemmas can be stated. That layer is **phenomenological overlay**, not a uniqueness proof from the lattice:

- `Hqiv.Physics.QuarkMetaResonance` — quark shell triples and `m_top_GeV` / `m_bottom_GeV` anchors; `light_quark_masses_near_paper_pdg` is *closeness to chosen refs*, not “PDG from O”.
- `Hqiv.Physics.LeptonGenerationLockin` — μ/e shells **`81`**, **`16336`** are documented placeholders.
- `Hqiv.Physics.ChargedLeptonResonance` — lepton resonance factors from that shell table + τ mass anchor.

They remain under `Hqiv/Physics/` because **`SM_GR_Unification`**, **`ConservedContentMassBridge`**, and other modules import them. A future refactor could move this **numeric table** into `archive/` and replace imports with minimal stubs (lock-in + geometry only).

## Archived witness script

- `archive/scripts/check_mass_ladder_pdg_witness.py` — Python mirror of the **table numerics** for regression / sanity checks only. It is **not** a claim that HQIV proves those masses.

## Related historical file

- `archive/abandoned/GenerationResonanceTauHighestShell.lean` — older τ-shell story; not in default `lake` targets.

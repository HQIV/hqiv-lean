import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Equiv.Fin.Rotate

import Hqiv.Physics.DivisionAlgebraZetaScaffold
import Hqiv.Physics.LatticeNextPrimeGenerator
import Hqiv.QuantumComputing.DigitalGates
import Hqiv.QuantumComputing.OSHoracle

open Hqiv.Physics

/-!
# QC scaffolding for the lattice next-prime pipeline (proved fragments)

## Classical pipeline: **not** a working algorithm

The composed classical story in `Hqiv.Physics.LatticeNextPrimeGenerator` is **documented there as scaffold
only**: greedy `decompose_to_fano_moduli` is **not** a valid decomposition of `x`; `spherePackingAtShell` and
`rapidity_effect_on_sphere` are **not** used by `next_prime_generator`; and `next_prime_generator` is only
`next_lattice_prime` from an ad hoc `decompose_last_shell`. **This module does not repair that** — it proves
unrelated small lemmas plus optional OSHoracle hooks.

## What is actually proved here

Small facts aligned with the [QUANTUM_CIRCUIT_NEXT_PRIME_PROBE.md](../../AGENTS/QUANTUM_CIRCUIT_NEXT_PRIME_PROBE.md) **metaphor** (not a correctness proof for any next-prime procedure):

1. **Fano register (7 lines):** `finRotate 7` is a **permutation** of `Fin 7`. Acting on a unary / probability mass assignment **preserves the total** \(\sum_i p_i\) (`fano_line_probability_mass_invariant`). This is the mathematical content of “cyclic symmetry on the Fano lines” at the level of **classical** mass.
2. **Digital gates:** `HQIVGate` composition `trans` **preserves** `discreteIp` (already in `DigitalGates`); we re-export the pattern as `hqiv_gate_trans_preserves_ip`.
3. **Pipeline arity:** a doc constant `4` (`lattice_next_prime_pipeline_stages_eq_four`) **labels** four narrative stages; it does **not** assert that the classical code implements all four or that the composition is correct.
4. **OSHoracle sparse step (`OSHoracle.lean`):** one horizon-causal gate application `applyGateSparse` **preserves** the discrete norm squared of the **dense** state obtained after `causalExpandSupport` (`lattice_next_prime_oshoracle_preserves_dense_norm_sq`). Support length **doubles** per step (`lattice_next_prime_oshoracle_step_doubles_support`), and **flip-based pruning** keeps a practical little-o style bound relative to that doubled length (`lattice_next_prime_oshoracle_pruned_support_little_o`).

**Not proved:** equivalence between a concrete `List (HQIVGate L)` and `next_prime_generator`, Grover complexity, or sub-linear time in the angular basis size (the formal `applyGateSparse` still builds a dense `DiscreteState`).

**Deferred (later pass):** tighter binding of this module to `next_prime_generator`, classical prime semantics, or end-to-end pipeline correctness — revisit once the geometric and generator layers have moved forward (this file stays **proved fragments + OSHoracle hooks** only).
-/

namespace Hqiv.QuantumComputing

open scoped BigOperators

open Fintype

/-- Cyclic shift on the 7 Fano-line labels (`Fin 7`), matching the mod‑7 residue story. -/
def fanoLineCyclicPerm : Equiv.Perm (Fin 7) :=
  finRotate 7

/-- Probability (or amplitude-squared) mass on the 7-line register is preserved under cyclic rotation.

This is the \(S_7\) / permutation-invariance of \(\sum_i p_i\) specialized to `finRotate 7`. -/
theorem fano_line_probability_mass_invariant (p : Fin 7 → ℝ) :
    (∑ i : Fin 7, p (fanoLineCyclicPerm i)) = ∑ i : Fin 7, p i :=
  Equiv.sum_comp fanoLineCyclicPerm p

theorem fano_line_cyclic_eq_finRotate : fanoLineCyclicPerm = finRotate 7 :=
  rfl

/-- Same shell residue as `fano_vertex_of_shell` (bridge to `DivisionAlgebraZetaScaffold`). -/
theorem fano_vertex_val_eq_mod_seven (m : ℕ) : (fano_vertex_of_shell m).val = m % 7 :=
  fano_vertex_of_shell_val m

/-- Composition of HQIV digital gates preserves the informational inner product (from `HQIVGate.trans`). -/
theorem hqiv_gate_trans_preserves_ip {L : ℕ} [DecidableEq (HarmonicIndex L)] (G₁ G₂ : HQIVGate L)
    (f g : DiscreteState L) :
    discreteIp ((G₁.trans G₂).toEquiv f) ((G₁.trans G₂).toEquiv g) = discreteIp f g :=
  (G₁.trans G₂).preserves_ip f g

/-- Number of **conceptual** stages in `LatticeNextPrimeGenerator` (documentation constant). -/
def latticeNextPrimePipelineStageCount : ℕ :=
  4

theorem lattice_next_prime_pipeline_stages_eq_four : latticeNextPrimePipelineStageCount = 4 :=
  rfl

/-! ### OSHoracle hook (sparse register + horizon-causal gate step)

The design note’s “sparse circuit picture” for the lattice next-prime pipeline is anchored here on
the same `applyGateSparse` / `causalExpandSupport` / `pruneToFlipped` API as protein and density
crossover modules.
-/

section LatticeNextPrimeOSHoracleBridge

variable {L : ℕ}

/-- One sparse OSHoracle step: causal expand, dense lift, `HQIVGate` bijection, sparse map back. -/
noncomputable abbrev latticeNextPrimeOSHoracleGateStep (g : HQIVGate L) (r : SparseRegister L) :
    SparseRegister L :=
  applyGateSparse g r

/-- `HQIVGate` is norm-preserving on the dense state that the sparse layer feeds into the bijection. -/
theorem lattice_next_prime_oshoracle_preserves_dense_norm_sq (g : HQIVGate L) (r : SparseRegister L) :
    discreteNormSq (g.toEquiv (denseOfSparse (causalExpandSupport L r))) =
      discreteNormSq (denseOfSparse (causalExpandSupport L r)) :=
  HQIVGate.preserves_normSq g _

theorem lattice_next_prime_oshoracle_step_doubles_support (g : HQIVGate L) (r : SparseRegister L) :
    (latticeNextPrimeOSHoracleGateStep g r).length = 2 * r.length :=
  applyGateSparse_length_eq_two_mul g r

theorem lattice_next_prime_oshoracle_pruned_support_little_o (g : HQIVGate L) (r : SparseRegister L) :
    practicalLittleO (2 * r.length)
      (pruneToFlipped (detectFlippedKets r (applyGateSparse g r)) (applyGateSparse g r)).length :=
  horizonCausal_support_o_twoPow_practice r g

end LatticeNextPrimeOSHoracleBridge

/-- Pruning to flipped kets leaves sparse norm unchanged when every active index is kept. -/
theorem lattice_next_prime_prune_preserves_sparse_norm_sq {L : ℕ} (flipped : List Nat)
    (r : SparseRegister L) (hkeep : ∀ x ∈ r, x.1 ∈ flipped) :
    sparseNormSq (pruneToFlipped (L := L) flipped r) = sparseNormSq r :=
  pruneToFlipped_preserves_discreteIp_norm (L := L) flipped r hkeep

end Hqiv.QuantumComputing

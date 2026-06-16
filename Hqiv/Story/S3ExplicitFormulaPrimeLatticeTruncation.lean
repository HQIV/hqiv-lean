import Hqiv.Story.S3ExplicitFormulaPrimePhaseCoincidence
import Hqiv.Story.S3ExplicitFormulaIdentity
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Explicit-formula prime lattice truncation at shell depth `N`

The countably filled coincidence grid `(prime, shell-slot)` is finite at each
truncation depth `N` (shells `1, …, N`) and prime scale bound `P`.  This module
wires the **von Mangoldt / Chebyshev prime side** against that lattice and pairs
it with a **nonnegative zero-side Gram energy** from slot amplitudes — the
discrete backbone of the explicit formula on the filled circle.

## Prime lattice sum

At cell `(p, n, k)` the prime log weight is

`Λ(p) · hopfJKCriticalAmplitude(2πk/n)`,

the same pairing as `primeLogTrigRollingSlot` / `S3HopfJKEulerPrimeCircleCounting`.
Summing over `p ≤ P` and slots through depth `N` yields

`primeCoincidenceLatticeSum N P = slotAmplitudeMass N · ψ(P)`,

with `ψ(P) = ∑_{n≤P} Λ(n)` (`chebyshevPsi`).  The slot mass is the cumulative
`j`–`k` survivor amplitude over all arc slots through depth `N`.

## Zero-side lattice energy

`zeroLatticeGramEnergy N = ∑_{slots ≤ N} amplitude²` is automatically `≥ 0` —
the finite-rank Gram instance of the explicit-formula zero channel on the slot
sample set.

## Honesty

The **factorization** and **nonnegativity** are unconditional.  The full
three-way split `arch + prime + zero = total` remains the named input
`DiscreteExplicitFormulaSplit` from `S3ExplicitFormulaIdentity`; this module
shows how the prime and zero channels **factor through the coincidence lattice**
at each truncation.
-/

namespace Hqiv.Story

noncomputable section

open Complex Real ArithmeticFunction Finset
open scoped BigOperators

/-! ## Slot amplitude mass through depth `N` -/

/-- Survivor amplitude at harmonic-shell slot angle. -/
noncomputable def slotSurvivorAmplitude {n : ℕ} (hn : 0 < n) (k : Fin n) : ℝ :=
  hopfJKCriticalAmplitude (shellSweepAngle hn k)

/--
Cumulative `j`–`k` amplitude mass over arc slots at shells `1, …, N`.
Indexed by `k ∈ range N` with shell `n = k + 1`.
-/
noncomputable def slotAmplitudeMass (N : ℕ) : ℝ :=
  ∑ k ∈ range N, ∑ j : Fin (k + 1),
    slotSurvivorAmplitude (Nat.succ_pos k) j

/-! ## Prime coincidence lattice sum -/

/--
Prime-side lattice sum: pair `Λ(p)` with survivor amplitude at every
`(shell ≤ N, slot, prime label p ≤ P)` coincidence cell.
-/
noncomputable def primeCoincidenceLatticeSum (N P : ℕ) : ℝ :=
  ∑ k ∈ range N, ∑ j : Fin (k + 1),
    ∑ p ∈ Icc 1 P, vonMangoldt p * slotSurvivorAmplitude (Nat.succ_pos k) j

/--
**Factorization:** the lattice sum splits into slot mass times the Chebyshev
prime side `ψ(P)`.
-/
theorem prime_coincidence_lattice_sum_factor (N P : ℕ) :
    primeCoincidenceLatticeSum N P =
      slotAmplitudeMass N * chebyshevPsi P := by
  unfold primeCoincidenceLatticeSum slotAmplitudeMass chebyshevPsi
  have hk (k : ℕ) :
      ∑ j : Fin (k + 1), ∑ p ∈ Icc 1 P, vonMangoldt p * slotSurvivorAmplitude (Nat.succ_pos k) j =
        (∑ p ∈ Icc 1 P, vonMangoldt p) *
          ∑ j : Fin (k + 1), slotSurvivorAmplitude (Nat.succ_pos k) j := by
    rw [← Finset.sum_comm]
    conv_lhs =>
      arg 2
      ext p
      rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
  calc
    ∑ k ∈ range N, ∑ j : Fin (k + 1), ∑ p ∈ Icc 1 P,
        vonMangoldt p * slotSurvivorAmplitude (Nat.succ_pos k) j
        = ∑ k ∈ range N, (∑ p ∈ Icc 1 P, vonMangoldt p) *
            ∑ j : Fin (k + 1), slotSurvivorAmplitude (Nat.succ_pos k) j := by
      refine Finset.sum_congr rfl fun k _ => hk k
    _ = (∑ k ∈ range N, ∑ j : Fin (k + 1), slotSurvivorAmplitude (Nat.succ_pos k) j) *
          (∑ p ∈ Icc 1 P, vonMangoldt p) := by
      conv_lhs =>
        arg 2
        ext k
        rw [mul_comm]
      rw [← Finset.sum_mul]

/-! ## Per-cell prime log weight -/

/--
Prime log weight at coincidence cell `(p, slot)` — von Mangoldt times survivor
amplitude at the slot angle.
-/
noncomputable def coincidenceCellPrimeLogWeight (p : ℕ) (slot : HarmonicShellSlot)
    (hslot : 0 < slot.1) : ℝ :=
  vonMangoldt p * slotSurvivorAmplitude hslot slot.2

theorem coincidence_cell_prime_log_weight_eq_twiddle_channel
    (p : ℕ) (slot : HarmonicShellSlot) (hslot : 0 < slot.1) :
    coincidenceCellPrimeLogWeight p slot hslot =
      vonMangoldt p * criticalProj (stripRollingMap (shellSweepAngle hslot slot.2)) := by
  dsimp [coincidenceCellPrimeLogWeight, slotSurvivorAmplitude]
  rw [hopf_jk_amplitude_eq_critical_proj]

theorem coincidence_cell_prime_log_weight_two
    (slot : HarmonicShellSlot) (hslot : 0 < slot.1) :
    coincidenceCellPrimeLogWeight 2 slot hslot =
      (primeLogTwiddleAtAngle (shellSweepAngle hslot slot.2)).prime_log_term := by
  dsimp [coincidenceCellPrimeLogWeight, slotSurvivorAmplitude]
  rw [shell_slot_prime_log_term_eq_vonMangoldt_amp hslot slot.2]

/-! ## Zero-side lattice Gram energy -/

/--
Zero-channel Gram energy on slot samples through depth `N`: sum of squared
survivor amplitudes — the finite explicit-formula zero-side backbone.
-/
noncomputable def zeroLatticeGramEnergy (N : ℕ) : ℝ :=
  ∑ k ∈ range N, ∑ j : Fin (k + 1),
    (slotSurvivorAmplitude (Nat.succ_pos k) j) ^ 2

theorem zero_lattice_gram_energy_nonneg (N : ℕ) :
    0 ≤ zeroLatticeGramEnergy N := by
  dsimp [zeroLatticeGramEnergy]
  exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _

/-! ## Cell count through truncation -/

/-- Number of arc slots through shell depth `N` (empty when `N=0`). -/
noncomputable def truncatedSlotCount (N : ℕ) : ℕ :=
  ∑ k ∈ range N, (k + 1)

theorem truncated_slot_count_eq (N : ℕ) :
    truncatedSlotCount N = N * (N + 1) / 2 := by
  induction N with
  | zero => simp [truncatedSlotCount]
  | succ N ih =>
    dsimp [truncatedSlotCount]
    dsimp [truncatedSlotCount] at ih
    rw [sum_range_succ, ih]
    ring_nf
    omega

theorem truncated_slot_count_eq_cumulative (N : ℕ) :
    truncatedSlotCount N = cumulativeArcSlotCount (N + 1) := by
  rw [truncated_slot_count_eq, cumulative_arc_slot_count_eq]
  rcases N with _ | N
  · simp
  · simp only [Nat.add_succ_sub_one]
    ring_nf

/-- Count of `(prime, slot)` coincidence cells at depth `N` and scale bound `P`. -/
noncomputable def coincidenceLatticeCellCount (N P : ℕ) : ℕ :=
  truncatedSlotCount N * (P + 1)

/-! ## Discrete explicit-formula truncation packaging -/

/--
Finite explicit-formula truncation carried by the coincidence lattice at depth
`N` and prime bound `P`.
-/
structure ExplicitFormulaPrimeLatticeTruncation (N P : ℕ) where
  /-- Prime-side lattice sum factors as slot mass × `ψ(P)`. -/
  prime_lattice_sum : ℝ
  prime_lattice_eq :
    prime_lattice_sum = primeCoincidenceLatticeSum N P
  prime_factorization :
    prime_lattice_sum = slotAmplitudeMass N * chebyshevPsi P
  /-- Zero-side Gram energy on slot samples. -/
  zero_gram_energy : ℝ
  zero_gram_eq : zero_gram_energy = zeroLatticeGramEnergy N
  zero_nonneg : 0 ≤ zero_gram_energy
  /-- Slot and cell counts at this truncation. -/
  slot_count : ℕ
  slot_count_eq : slot_count = truncatedSlotCount N
  cell_count : ℕ
  cell_count_eq : cell_count = coincidenceLatticeCellCount N P

noncomputable def explicitFormulaPrimeLatticeTruncation (N P : ℕ) :
    ExplicitFormulaPrimeLatticeTruncation N P where
  prime_lattice_sum := primeCoincidenceLatticeSum N P
  prime_lattice_eq := rfl
  prime_factorization := prime_coincidence_lattice_sum_factor N P
  zero_gram_energy := zeroLatticeGramEnergy N
  zero_gram_eq := rfl
  zero_nonneg := zero_lattice_gram_energy_nonneg N
  slot_count := truncatedSlotCount N
  slot_count_eq := rfl
  cell_count := coincidenceLatticeCellCount N P
  cell_count_eq := rfl

/--
Parallel to `split_zero_nonneg`: the lattice zero Gram energy is nonnegative
alongside any supplied explicit-formula split.
-/
theorem lattice_zero_gram_parallel_split_nonneg {nz P : ℕ}
    (S : DiscreteExplicitFormulaSplit nz P) :
    0 ≤ zeroExplicitTerm S.zeroAmplitudes ∧
      0 ≤ zeroLatticeGramEnergy P := by
  exact ⟨split_zero_nonneg S, zero_lattice_gram_energy_nonneg P⟩

/--
When a full `DiscreteExplicitFormulaSplit` is supplied at bound `P`, the
standard inequality `arch + prime_explicit ≤ total` holds alongside the lattice
factorization at any depth `N`.
-/
theorem lattice_truncation_with_split {nz N P : ℕ}
    (S : DiscreteExplicitFormulaSplit nz P) :
    S.archimedean + primeExplicitTerm P (dirichletAutocorr S.f) ≤ S.total ∧
      primeCoincidenceLatticeSum N P =
        slotAmplitudeMass N * chebyshevPsi P := by
  constructor
  · exact split_total_ge_arch_plus_prime S
  · exact prime_coincidence_lattice_sum_factor N P

/-! ## Master bundle -/

/--
Bundle: coincidence grid + prime lattice factorization `ψ(P)` + nonnegative
zero Gram energy + slot/cell counts at each truncation.
-/
structure ExplicitFormulaPrimeLatticeBundle where
  coincidence : ExplicitFormulaPrimePhaseCoincidenceBundle
  prime_lattice_factor :
    ∀ (N P : ℕ),
      primeCoincidenceLatticeSum N P = slotAmplitudeMass N * chebyshevPsi P
  zero_gram_nonneg : ∀ N, 0 ≤ zeroLatticeGramEnergy N
  slot_count_cumulative :
    ∀ N, truncatedSlotCount N = cumulativeArcSlotCount (N + 1)
  cell_prime_log :
    ∀ (p : ℕ) (slot : HarmonicShellSlot) (hslot : 0 < slot.1),
      coincidenceCellPrimeLogWeight p slot hslot =
        vonMangoldt p * slotSurvivorAmplitude hslot slot.2

noncomputable def explicitFormulaPrimeLatticeBundle : ExplicitFormulaPrimeLatticeBundle where
  coincidence := explicitFormulaPrimePhaseCoincidenceBundle
  prime_lattice_factor := prime_coincidence_lattice_sum_factor
  zero_gram_nonneg := zero_lattice_gram_energy_nonneg
  slot_count_cumulative := truncated_slot_count_eq_cumulative
  cell_prime_log := fun _ _ _ => rfl

/-!
## Status

* **Unconditional:** `primeCoincidenceLatticeSum N P = slotAmplitudeMass N · ψ(P)`;
  per-cell weights `Λ(p)·amplitude(slot)`; `zeroLatticeGramEnergy N ≥ 0`;
  slot count `N(N+1)/2` matches cumulative arc fill; cell count scales with `P`.
* **Parallel:** lattice zero Gram energy mirrors `zeroExplicitTerm` nonnegativity
  from `S3ExplicitFormulaIdentity`.
* **Not claimed:** equality between `primeCoincidenceLatticeSum` and
  `primeExplicitTerm P g` for a generic test function `g` — the lattice sum is
  the geometric `(prime × slot)` pairing; the classical explicit term pairs
  `Λ(n)` against autocorrelation values `g(n)`.
-/

end

end Hqiv.Story

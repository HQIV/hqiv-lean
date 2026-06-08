import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic
import Hqiv.Geometry.FactorDivisibilityBridge
import Hqiv.Geometry.HQIVOSHIntegratedFactorDriver
import Hqiv.Geometry.QuantumFactorGateFrontier
import Hqiv.Geometry.ReverseShorClassicalOSHPeriodSelector
import Hqiv.Geometry.SemiprimeOrthogonalDiagonal
import Hqiv.QuantumComputing.OctonionicFT
import Hqiv.QuantumComputing.ShoreOracle

/-!
# Semiprime orthogonal-diagonal Shor — quantum specification + classical post-processing

This file formalizes the **hybrid sparse phase-estimation** variant specialized to semiprimes:

* **Quantum layer (specification):** register budgets, gate schedules, and dominant-eigenphase
  readout — *not* a full Hilbert-space simulation or NISQ noise model.
* **Classical layer (proved):** even-period Shor `gcd`, continued-fraction denominator
  certification when order is verified, and reuse of `OddCoreFactorWitness` /
  `ReverseShorClassicalOSHPeriodSelector` sound extraction.

## What is proved here

1. Qubit-budget inequalities: orthogonal-diagonal pivot+mirror+work ≤ textbook `3L` proxy.
2. Circuit-depth accounting: diagonal-reflection schedule ≤ dense-QFT schedule (on the gate tag model).
3. Classical Shor `gcd` candidates yield `OddCoreFactorWitness` when nontrivial.
4. CF denominator yields a verified-order witness when `a^q ≡ 1 (mod n)`.
5. `N = 15` bridge: dominant period `4` matches `ShoreOracle` / `period4InterferenceProb`.
6. End-to-end **classical post-processing soundness** from a bundled witness.

## What is *not* proved

* Unitary correctness of modular exponentiation or diagonal reflection on a quantum computer.
* That measurement samples the dominant eigenphase with high probability.
* Polynomial-time completeness for all composites.
-/

namespace Hqiv.QuantumComputing.SemiprimeOrthogonalDiagonalQuantum

open Hqiv.QuantumComputing
open Hqiv.Geometry
open Hqiv.Geometry.HQIVOSHIntegratedFactorDriver
open Hqiv.Geometry.ReverseShorClassicalOSHPeriodSelector
open Hqiv.Geometry.SemiprimeOrthogonalDiagonal
open Hqiv.Geometry.QuantumFactorGateFrontier
open scoped BigOperators

/-! ## Input scale and qubit budgets -/

/-- Standard bit-length proxy `L = ⌊log₂ n⌋` (at least `1`). -/
def shorBitLength (n : ℕ) : ℕ :=
  max 1 (Nat.log 2 (max 2 n))

/-- Textbook first-register size `2L` for frequency resolution. -/
def textbookControlQubits (n : ℕ) : ℕ :=
  2 * shorBitLength n

/-- Textbook coarse budget `≈ 3L` (control + work, no ancilla slack counted). -/
def textbookShorQubitBudget (n : ℕ) : ℕ :=
  3 * shorBitLength n

/-- Orthogonal-diagonal pivot flat: at most `L` qubits. -/
def pivotFlatQubits (n : ℕ) : ℕ :=
  shorBitLength n

/-- Mirror flat: same order as pivot in the half-sparse layout. -/
def mirrorFlatQubits (n : ℕ) : ℕ :=
  shorBitLength n

/-- Work register for modular exponentiation (standard `L`). -/
def workRegisterQubits (n : ℕ) : ℕ :=
  shorBitLength n

/-- Dominant-phase orthogonal-diagonal budget: pivot + mirror + work. -/
def orthogonalDiagonalQubitBudget (n : ℕ) : ℕ :=
  pivotFlatQubits n + mirrorFlatQubits n + workRegisterQubits n

theorem orthogonalDiagonalQubits_le_textbook (n : ℕ) :
    orthogonalDiagonalQubitBudget n ≤ textbookShorQubitBudget n := by
  unfold orthogonalDiagonalQubitBudget textbookShorQubitBudget
        pivotFlatQubits mirrorFlatQubits workRegisterQubits
  omega

/-! ## Refined register layout (shared work register) -/

/-- Ancilla budget for diagonal-reflection control: `3·log₂ L + 10` (spec constant). -/
def diagonalReflectionAncillaBudget (L : ℕ) : ℕ :=
  3 * Nat.log 2 (max 2 L) + 10

/--
Register layout with **one** work register reused between pivot and mirror flats:
`L` phase + `L` work + ancilla.
-/
structure SharedWorkRegisterLayout (L : ℕ) where
  phaseRegister : ℕ
  sharedWork : ℕ
  diagonalAncilla : ℕ
  hphase : phaseRegister = L
  hwork : sharedWork = L
  hanc : diagonalAncilla = diagonalReflectionAncillaBudget L

/-- Canonical shared layout at scale `L`. -/
def sharedWorkRegisterLayout (L : ℕ) : SharedWorkRegisterLayout L where
  phaseRegister := L
  sharedWork := L
  diagonalAncilla := diagonalReflectionAncillaBudget L
  hphase := rfl
  hwork := rfl
  hanc := rfl

def sharedWorkRegisterLayoutQubits (L : ℕ) : ℕ :=
  let lay := sharedWorkRegisterLayout L
  lay.phaseRegister + lay.sharedWork + lay.diagonalAncilla

theorem sharedWorkRegisterLayoutQubits_eq (L : ℕ) :
    sharedWorkRegisterLayoutQubits L = 2 * L + diagonalReflectionAncillaBudget L := by
  simp [sharedWorkRegisterLayoutQubits, sharedWorkRegisterLayout, diagonalReflectionAncillaBudget]
  omega

theorem sharedWorkRegisterLayoutQubits_le_formula (L : ℕ) :
    sharedWorkRegisterLayoutQubits L ≤ 2 * L + 3 * Nat.log 2 (max 2 L) + 10 := by
  rw [sharedWorkRegisterLayoutQubits_eq, diagonalReflectionAncillaBudget]
  rfl

def refinedOrthogonalDiagonalQubitBudget (n : ℕ) : ℕ :=
  sharedWorkRegisterLayoutQubits (shorBitLength n)

theorem refinedOrthogonalDiagonal_le_2L_plus_log (n : ℕ) :
    refinedOrthogonalDiagonalQubitBudget n ≤
      2 * shorBitLength n + 3 * Nat.log 2 (max 2 (shorBitLength n)) + 10 := by
  unfold refinedOrthogonalDiagonalQubitBudget
  rw [sharedWorkRegisterLayoutQubits_eq, diagonalReflectionAncillaBudget]
  exact le_rfl

private theorem three_log_plus_ten_lt_pow2 {k : ℕ} (hk : 5 ≤ k) : 3 * k + 10 < 2 ^ k := by
  refine Nat.le_induction ?base ?step k hk
  · decide
  · intro k ih hk'
    rw [Nat.pow_succ]
    omega

/-- For `L ≥ 32`, ancilla `3·log₂ L + 10` is strictly below `L` (enables qubit saving vs `3L`). -/
theorem diagonalReflectionAncilla_lt_L {L : ℕ} (hL : 32 ≤ L) :
    diagonalReflectionAncillaBudget L < L := by
  unfold diagonalReflectionAncillaBudget
  have hmax : max 2 L = L := max_eq_right (by omega)
  rw [hmax]
  set k := Nat.log 2 L
  have hk_lower : 5 ≤ k := by
    apply Nat.le_log_of_pow_le one_lt_two
    calc
      2 ^ 5 = 32 := by norm_num
      _ ≤ L := hL
  have hk_pow : 2 ^ k ≤ L := Nat.pow_log_le_self 2 (by omega)
  have hk_lt := three_log_plus_ten_lt_pow2 hk_lower
  omega

theorem refined_lt_textbook_when_large (L : ℕ) (hL : 32 ≤ L) :
    sharedWorkRegisterLayoutQubits L < textbookShorQubitBudget (2 ^ L) := by
  have hL1 : 1 ≤ L := by omega
  have hs : shorBitLength (2 ^ L) = L := by
    unfold shorBitLength
    have hle : 2 ≤ 2 ^ L := by
      calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL1
    have hmax : max 2 (2 ^ L) = 2 ^ L := max_eq_right hle
    have hlog : Nat.log 2 (2 ^ L) = L := Nat.log_pow (show 1 < 2 from by norm_num) (by omega)
    rw [hmax, hlog]
    exact max_eq_right hL1
  rw [sharedWorkRegisterLayoutQubits_eq, textbookShorQubitBudget, hs]
  have hanc := diagonalReflectionAncilla_lt_L hL
  simp only [diagonalReflectionAncillaBudget, max_eq_right (by omega)] at hanc ⊢
  omega

theorem refined_lt_textbook_of_bitlength (n : ℕ) (hL : 32 ≤ shorBitLength n) :
    refinedOrthogonalDiagonalQubitBudget n < textbookShorQubitBudget n := by
  unfold refinedOrthogonalDiagonalQubitBudget textbookShorQubitBudget
  rw [sharedWorkRegisterLayoutQubits_eq]
  have hanc := diagonalReflectionAncilla_lt_L hL
  simp only [diagonalReflectionAncillaBudget, max_eq_right (by omega)] at hanc ⊢
  omega

theorem shorBitLength_le_log_succ (n : ℕ) :
    shorBitLength n ≤ Nat.log 2 (max 2 n) + 1 := by
  simp only [shorBitLength, max_le_iff]
  omega

/-! ## Gate schedules (specification algebra, not unitaries) -/

inductive QuantumGateTag
  | prepareSuperposition
  | controlledModExp
  | fullQFT
  | diagonalReflection
  | measureEigenphase
  deriving DecidableEq, Repr

def gateDepth (g : QuantumGateTag) : ℕ :=
  match g with
  | .prepareSuperposition => 1
  | .controlledModExp => 4  -- mod-exp block (tag-level; same in both schedules)
  | .fullQFT => 0  -- counted via `fullQFTDepth`
  | .diagonalReflection => 2
  | .measureEigenphase => 1

def circuitDepth (gates : List QuantumGateTag) : ℕ :=
  gates.foldl (fun acc g => acc + gateDepth g) 0

/-- Textbook Shor on the tag model: H → mod-exp → dense QFT → measure. -/
def textbookShorGateList (n : ℕ) : List QuantumGateTag :=
  [.prepareSuperposition, .controlledModExp, .fullQFT, .measureEigenphase]

/-- Orthogonal-diagonal semiprime schedule: replace dense QFT with diagonal reflection. -/
def orthogonalDiagonalGateList (n : ℕ) : List QuantumGateTag :=
  [.prepareSuperposition, .controlledModExp, .diagonalReflection, .measureEigenphase]

def fullQFTDepth (n : ℕ) : ℕ :=
  max 2 ((shorBitLength n) ^ 2)

def textbookShorCircuitDepth (n : ℕ) : ℕ :=
  circuitDepth [.prepareSuperposition, .controlledModExp, .measureEigenphase] + fullQFTDepth n

def orthogonalDiagonalCircuitDepth (n : ℕ) : ℕ :=
  circuitDepth (orthogonalDiagonalGateList n)

theorem orthogonalDiagonal_depth_le_textbook (n : ℕ) :
    orthogonalDiagonalCircuitDepth n ≤ textbookShorCircuitDepth n := by
  unfold orthogonalDiagonalCircuitDepth textbookShorCircuitDepth circuitDepth
        orthogonalDiagonalGateList gateDepth fullQFTDepth
  simp only [List.foldl, gateDepth, QuantumGateTag.casesOn]
  have htail : 2 ≤ max 2 ((shorBitLength n) ^ 2) := Nat.le_max_left _ _
  simp only [shorBitLength]
  omega

/-! ## Dominant eigenphase readout (classical data from quantum measurement idealization) -/

/--
Rational peak `(k/r)` from a single-bucket measurement: `0 < k < r`.
This is the input to continued-fraction post-processing (classical).
-/
structure EigenphaseMeasurement where
  k : ℕ
  r : ℕ
  hk_pos : 0 < k
  hk_lt_r : k < r

def EigenphaseMeasurement.phaseNum (m : EigenphaseMeasurement) : ℕ :=
  m.k

def EigenphaseMeasurement.phaseDen (m : EigenphaseMeasurement) : ℕ :=
  m.r

/-! ## Classical post-processing (proved soundness) -/

/-- `base - 1` for modular Shor gcd (Nat-safe). -/
def natPred (x : ℕ) : ℕ :=
  if x > 0 then x - 1 else 0

/--
Classical Shor candidates from an **even** period: `gcd(a^{r/2} ± 1, n)`.
Python: `shor_gcd_candidates_from_period`.
-/
def shorEvenPeriodGcdCandidates (a n r : ℕ) : List ℕ :=
  if r % 2 = 0 then
    let half := r / 2
    let base := a ^ half % n
    [natPred base |>.gcd n, (base + 1).gcd n]
  else
    []

theorem mem_shorEvenPeriodGcd_candidates {a n r d : ℕ}
    (hd : d ∈ shorEvenPeriodGcdCandidates a n r) :
    d = Nat.gcd (natPred (a ^ (r / 2) % n)) n ∨ d = Nat.gcd (a ^ (r / 2) % n + 1) n := by
  unfold shorEvenPeriodGcdCandidates at hd
  by_cases h : r % 2 = 0
  · simp only [h, reduceIte, List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with hd | hd
    · left; simpa [natPred, Nat.gcd_comm] using hd
    · right; simpa [Nat.gcd_comm] using hd
  · simp [h] at hd

/--
If `d` is a nontrivial gcd output from the even-period channel, it is a sound odd-core factor.
-/
theorem shor_even_period_gcd_extraction_sound {odd a r d : ℕ}
    (hd : d ∈ shorEvenPeriodGcdCandidates a odd r)
    (h₁ : 1 < d) (h₂ : d < odd) :
    ∃ cert : OddCoreFactorWitness odd, cert.d = d ∧ cert.d * (odd / cert.d) = odd := by
  rcases mem_shorEvenPeriodGcd_candidates (a := a) (n := odd) (r := r) (d := d) hd with h | h
  · subst h
    refine
      ⟨oddCoreWitness_of_gcd (x := natPred (a ^ (r / 2) % odd)) h₁ h₂, rfl,
        OddCoreFactorWitness.reconstructs _⟩
  · subst h
    refine
      ⟨oddCoreWitness_of_gcd (x := a ^ (r / 2) % odd + 1) h₁ h₂, rfl,
        OddCoreFactorWitness.reconstructs _⟩

/--
Continued-fraction denominator candidate: once `a^q ≡ 1 (mod n)` is **verified**, `q` is an
order multiple; Shor gcd may be applied when `q` is even.
-/
structure ContinuedFractionPeriodWitness where
  a : ℕ
  n : ℕ
  q : ℕ
  hq_pos : 0 < q
  horder : a ^ q % n = 1

def continuedFractionPeriodGcdCandidates (w : ContinuedFractionPeriodWitness) : List ℕ :=
  shorEvenPeriodGcdCandidates w.a w.n w.q

theorem continued_fraction_period_gcd_sound {odd : ℕ}
    (w : ContinuedFractionPeriodWitness) (d : ℕ)
    (hd : d ∈ continuedFractionPeriodGcdCandidates w)
    (h₁ : 1 < d) (h₂ : d < odd) (hn : w.n = odd) :
    ∃ cert : OddCoreFactorWitness odd, cert.d = d ∧ cert.d * (odd / cert.d) = odd := by
  subst hn
  exact shor_even_period_gcd_extraction_sound (a := w.a) (r := w.q) hd h₁ h₂

/-! ## Quantum-classical algorithm bundle -/

/--
Full hybrid specification: quantum schedule tag + classical post-processing witness.

The quantum fields are **scheduling metadata**; sound factorization is carried by the
classical `OddCoreFactorWitness`.
-/
structure SemiprimeOrthogonalDiagonalQuantumAlgorithm (n : ℕ) where
  a : ℕ
  hcoprime : Nat.Coprime a n
  gates : List QuantumGateTag
  hgates : gates = orthogonalDiagonalGateList n
  eigenphase : EigenphaseMeasurement
  periodVerified : a ^ eigenphase.r % n = 1
  divisor : ℕ
  hodd_witness : OddCoreFactorWitness n
  hdiv_eq : hodd_witness.d = divisor

theorem algorithm_reconstructs (A : SemiprimeOrthogonalDiagonalQuantumAlgorithm n) :
    A.divisor * (n / A.divisor) = n := by
  simpa [A.hdiv_eq] using A.hodd_witness.reconstructs

theorem algorithm_gates_are_sparse (A : SemiprimeOrthogonalDiagonalQuantumAlgorithm n) :
    A.gates = [.prepareSuperposition, .controlledModExp, .diagonalReflection, .measureEigenphase] := by
  simpa [orthogonalDiagonalGateList] using A.hgates

/-! ## Geometry bridge: semiprime slots + period selector -/

/--
Classical carrier geometry witness implies the same divisibility certificate chain as the
quantum post-processing layer.
-/
theorem semiprime_geometry_factors_sound {L odd d : ℕ}
    (w : SemiprimeDiagonalWitness L odd)
    (h₁ : 1 < d) (h₂ : d < odd) (hdiv : d ∣ odd)
    (hsel : IsPeriodSelectorCandidate w.periodWitness d) :
    ∃ cert : OddCoreFactorWitness odd, cert.d = d ∧ cert.d * (odd / cert.d) = odd :=
  semiprime_diagonal_extraction_sound w h₁ h₂ hdiv hsel

/-! ## `N = 15` exemplar (dominant period matches ShoreOracle) -/

def dominantPeriod_n15 : ℕ :=
  4

theorem shorBitLength_n15 : shorBitLength 15 = 3 := by
  native_decide

theorem orthogonalDiagonal_budget_n15 :
    orthogonalDiagonalQubitBudget 15 = 9 := by
  native_decide

theorem textbook_budget_n15 : textbookShorQubitBudget 15 = 9 := by
  native_decide

theorem orthogonalDiagonal_qubits_n15_le :
    orthogonalDiagonalQubitBudget 15 ≤ textbookShorQubitBudget 15 := by
  native_decide

/-- Dominant eigenphase for the period-4 shell: `k = 1`, `r = 4`. -/
def eigenphaseMeasurement_n15 : EigenphaseMeasurement where
  k := 1
  r := 4
  hk_pos := by decide
  hk_lt_r := by decide

theorem eigenphase_n15_matches_period4 :
    eigenphaseMeasurement_n15.r = factors15Outcome.period := by
  rfl

theorem shoreOracle_period4_support :
    factors15Outcome.support = period4Support16 := by
  rfl

/--
Bridge: the orthogonal-diagonal dominant period for factoring `15` agrees with the
`ShoreOracle` period-4 outcome specification.
-/
theorem orthogonal_diagonal_n15_agrees_shoreOracle :
    dominantPeriod_n15 = (run (shorCircuit 15)).period ∧
      period4Support16 = factors15Outcome.support := by
  refine ⟨?_, shoreOracle_period4_support⟩
  simp [dominantPeriod_n15, run, shorCircuit, factors15Outcome]

theorem trace_hidden_probs_n15_uniform :
    [bornControlProb15 0, bornControlProb15 4, bornControlProb15 8, bornControlProb15 12] =
      factors15Outcome.probabilityDistribution := by
  exact trace_hidden_probs_15

/-! ## Statement checklist (proved vs specification-only) -/

/--
Checklist Prop for agents: which slots of the hybrid algorithm are formally discharged.
-/
structure SemiprimeQuantumFormalizationStatus : Prop where
  qubit_saving : ∀ n, orthogonalDiagonalQubitBudget n ≤ textbookShorQubitBudget n
  refined_qubit_formula :
    ∀ n, refinedOrthogonalDiagonalQubitBudget n ≤
      2 * shorBitLength n + 3 * Nat.log 2 (max 2 (shorBitLength n)) + 10
  refined_saving_large :
    ∀ n, 32 ≤ shorBitLength n →
      refinedOrthogonalDiagonalQubitBudget n < textbookShorQubitBudget n
  depth_saving : ∀ n, orthogonalDiagonalCircuitDepth n ≤ textbookShorCircuitDepth n
  gcd_postprocess_sound :
    ∀ {odd a r d : ℕ},
      d ∈ shorEvenPeriodGcdCandidates a odd r →
        1 < d → d < odd → ∃ cert : OddCoreFactorWitness odd, cert.d = d
  n15_bridge : dominantPeriod_n15 = (run (shorCircuit 15)).period

theorem semiprime_quantum_formalization_status : SemiprimeQuantumFormalizationStatus where
  qubit_saving := orthogonalDiagonalQubits_le_textbook
  refined_qubit_formula := refinedOrthogonalDiagonal_le_2L_plus_log
  refined_saving_large := refined_lt_textbook_of_bitlength
  depth_saving := orthogonalDiagonal_depth_le_textbook
  gcd_postprocess_sound := fun hd h₁ h₂ => by
    rcases shor_even_period_gcd_extraction_sound hd h₁ h₂ with ⟨cert, hcert, _⟩
    exact ⟨cert, hcert⟩
  n15_bridge := orthogonal_diagonal_n15_agrees_shoreOracle.1

#print SemiprimeOrthogonalDiagonalQuantumAlgorithm
#print orthogonalDiagonalQubits_le_textbook
#print shor_even_period_gcd_extraction_sound
#print orthogonal_diagonal_n15_agrees_shoreOracle
#print semiprime_quantum_formalization_status

#check SemiprimeOrthogonalDiagonalQuantumAlgorithm
#check orthogonalDiagonalQubits_le_textbook
#check orthogonalDiagonal_depth_le_textbook
#check shor_even_period_gcd_extraction_sound
#check continued_fraction_period_gcd_sound
#check semiprime_geometry_factors_sound
#check orthogonal_diagonal_n15_agrees_shoreOracle
#check semiprime_quantum_formalization_status

end Hqiv.QuantumComputing.SemiprimeOrthogonalDiagonalQuantum

import Hqiv.QuantumComputing.SparseScheduleCost

/-!
# Symbolic frequency slices imply polynomial classical simulation

This module moves the frequency-certificate story above generated witnesses.  A
`SymbolicFrequencySlice` is a family-level abstraction: it provides metrics and acceptance
obligations for every input size `n`, rather than relying on one concrete exported JSON run.

The main theorem is conditional and symbolic:

* if a circuit family admits an accepted frequency slice for every `n`;
* if support, frequency χ, and route count have fixed polynomial witnesses;
* then the family is classically polynomial-simulable under the sparse schedule cost model.

The contradictory theorem states the boundary in proof form: if a family is not polynomially
simulable, then it cannot satisfy all symbolic frequency-slice obligations.
-/

namespace Hqiv.QuantumComputing

/-- Abstract circuit-family tag.  Semantics are supplied by the slice obligations below. -/
structure CircuitFamily where
  name : String
  deriving Repr

/-- A natural-valued metric over problem size. -/
abbrev SizeMetric : Type := Nat → Nat

/-- Uniform polynomial boundedness with the same envelope used by certificate witnesses. -/
def PolynomiallyBounded (metric : SizeMetric) : Prop :=
  ∃ d, ∀ n, 1 ≤ n → metric n ≤ polyEnvelope n d

/--
Family-level frequency slice data.  These are symbolic obligations over all input sizes, not
per-run computations.  `gateSemanticsCovered` marks the Lean-backed fast-step coverage boundary.
-/
structure SymbolicFrequencySlice (F : CircuitFamily) where
  maxSupport : SizeMetric
  maxChiFrequencyBand : SizeMetric
  routeCount : SizeMetric
  maxChiBound : SizeMetric
  denseFallbackCount : SizeMetric
  parityOk : Nat → Bool
  frequencyCutUsed : Nat → Bool
  gateSemanticsCovered : Nat → Prop

namespace SymbolicFrequencySlice

/-- Acceptance obligations at one problem size. -/
def acceptedAt {F : CircuitFamily} (S : SymbolicFrequencySlice F) (n : Nat) : Prop :=
  S.parityOk n = true ∧
  S.denseFallbackCount n = 0 ∧
  S.maxChiFrequencyBand n ≤ S.maxChiBound n ∧
  S.maxSupport n > 0 ∧
  S.routeCount n > 0 ∧
  S.gateSemanticsCovered n

/-- Sparse schedule cost induced by the symbolic slice at size `n`. -/
def costAt {F : CircuitFamily} (S : SymbolicFrequencySlice F) (n : Nat) : Nat :=
  scheduleCost (S.routeCount n) (S.maxSupport n) (S.maxChiFrequencyBand n)

end SymbolicFrequencySlice

/--
Fixed polynomial witnesses for a symbolic frequency slice.  These are the symbolic analogue of
Python-exported `PolynomialWitness`, but quantified over the whole family.
-/
structure FrequencySlicePolynomialWitness {F : CircuitFamily} (S : SymbolicFrequencySlice F) where
  witness : PolynomialWitness
  supportBound :
    ∀ n, 1 ≤ n → S.maxSupport n ≤ polyEnvelope n witness.polyDegreeSupport
  frequencyChiBound :
    ∀ n, 1 ≤ n → S.maxChiFrequencyBand n ≤ polyEnvelope n witness.polyDegreeFrequencyChi
  routeCountBound :
    ∀ n, 1 ≤ n → S.routeCount n ≤ polyEnvelope n witness.polyDegreeRouteCount

/-- The symbolic condition: this family is a certified frequency slice with polynomial metrics. -/
structure FrequencySliceToP (F : CircuitFamily) where
  slice : SymbolicFrequencySlice F
  acceptedAll : ∀ n, 1 ≤ n → slice.acceptedAt n
  polynomialWitness : FrequencySlicePolynomialWitness slice

/-- Propositional wrapper for the symbolic frequency-slice condition. -/
def HasFrequencySliceToP (F : CircuitFamily) : Prop :=
  Nonempty (FrequencySliceToP F)

/-- Classical polynomial simulability under the abstract sparse schedule cost model. -/
def ClassicalPolynomialSimulable (F : CircuitFamily) : Prop :=
  ∃ S : SymbolicFrequencySlice F, PolynomiallyBounded S.costAt

theorem FrequencySlicePolynomialWitness.support_polynomial
    {F : CircuitFamily} {S : SymbolicFrequencySlice F}
    (W : FrequencySlicePolynomialWitness S) :
    PolynomiallyBounded S.maxSupport :=
  ⟨W.witness.polyDegreeSupport, W.supportBound⟩

theorem FrequencySlicePolynomialWitness.frequency_chi_polynomial
    {F : CircuitFamily} {S : SymbolicFrequencySlice F}
    (W : FrequencySlicePolynomialWitness S) :
    PolynomiallyBounded S.maxChiFrequencyBand :=
  ⟨W.witness.polyDegreeFrequencyChi, W.frequencyChiBound⟩

theorem FrequencySlicePolynomialWitness.route_count_polynomial
    {F : CircuitFamily} {S : SymbolicFrequencySlice F}
    (W : FrequencySlicePolynomialWitness S) :
    PolynomiallyBounded S.routeCount :=
  ⟨W.witness.polyDegreeRouteCount, W.routeCountBound⟩

/-- Fixed symbolic witnesses imply a fixed polynomial bound on the induced sparse schedule cost. -/
theorem frequencySliceCost_polynomial
    {F : CircuitFamily} {S : SymbolicFrequencySlice F}
    (W : FrequencySlicePolynomialWitness S) :
    PolynomiallyBounded S.costAt := by
  refine ⟨schedulePolyDegree W.witness, ?_⟩
  intro n hn
  exact scheduleCost_le_polyEnvelope_of_bounds
    W.witness n (S.routeCount n) (S.maxSupport n) (S.maxChiFrequencyBand n)
    hn (W.routeCountBound n hn) (W.supportBound n hn) (W.frequencyChiBound n hn)

/--
Main symbolic theorem: if a family satisfies the frequency-slice obligations with fixed polynomial
witnesses, then it is classically polynomial-simulable under the schedule cost model.
-/
theorem frequency_slice_simulates_in_P
    {F : CircuitFamily} (h : FrequencySliceToP F) :
    ClassicalPolynomialSimulable F :=
  ⟨h.slice, frequencySliceCost_polynomial h.polynomialWitness⟩

/--
Contradictory boundary theorem.  Any family that is not polynomially simulable must fail the
symbolic frequency-slice condition: a dense fallback, parity break, super-polynomial metric,
uncovered gate semantic, or another slice obligation must fail somewhere.
-/
theorem not_frequency_slice_if_not_P
    {F : CircuitFamily} (hnotP : ¬ ClassicalPolynomialSimulable F) :
    ¬ HasFrequencySliceToP F :=
  fun hslice => hslice.elim (fun h => hnotP (frequency_slice_simulates_in_P h))

/-- If symbolic frequency-slice assumptions hold, each accepted size has no dense fallback. -/
theorem frequency_slice_no_dense_fallback
    {F : CircuitFamily} (h : FrequencySliceToP F) {n : Nat} (hn : 1 ≤ n) :
    h.slice.denseFallbackCount n = 0 :=
  (h.acceptedAll n hn).2.1

/-- If symbolic frequency-slice assumptions hold, each accepted size has frequency χ ≤ global χ. -/
theorem frequency_slice_chi_le_global
    {F : CircuitFamily} (h : FrequencySliceToP F) {n : Nat} (hn : 1 ≤ n) :
    h.slice.maxChiFrequencyBand n ≤ h.slice.maxChiBound n :=
  (h.acceptedAll n hn).2.2.1

/-- If symbolic frequency-slice assumptions hold, every size has Lean-backed gate semantics. -/
theorem frequency_slice_gate_semantics_covered
    {F : CircuitFamily} (h : FrequencySliceToP F) {n : Nat} (hn : 1 ≤ n) :
    h.slice.gateSemanticsCovered n :=
  (h.acceptedAll n hn).2.2.2.2.2

end Hqiv.QuantumComputing

import Hqiv.QuantumComputing.SymbolicDomainCover

/-!
# Frequency slices embed into domain covers

This is the first compositional proof linking the two symbolic layers:

* a family with an accepted `FrequencySliceToP` certificate;
* induces a `DomainCoverToP` certificate whose sole route per size is frequency-local;
* therefore inherits the combined shell/frequency/hybrid polynomial simulation theorem.

This does **not** prove BQP = P.  It proves that the frequency-only certified subclass is already
inside the combined domain-cover class.
-/

namespace Hqiv.QuantumComputing

namespace FrequencySliceToP

variable {F : CircuitFamily}

/-- Canonical frequency-local route obligation induced by slice metrics at size `n`. -/
def frequencyRoute (h : FrequencySliceToP F) (n : Nat) : RouteObligation :=
  { domain := DecompositionDomain.frequency
  , support := h.slice.maxSupport n
  , chi := h.slice.maxChiFrequencyBand n
  , shellSupport := 1
  , frequencyChi := h.slice.maxChiFrequencyBand n
  , gateSemanticsCovered := h.slice.gateSemanticsCovered n }

theorem frequencyRoute_covered (h : FrequencySliceToP F) (n : Nat) (hn : 1 ≤ n) :
    (h.frequencyRoute n).CoveredByPDomain := by
  refine Or.inr (Or.inl ⟨rfl, rfl, (h.acceptedAll n hn).2.2.2.2.2⟩)

theorem frequencyRoute_metrics_bounded (h : FrequencySliceToP F) (n : Nat) :
    (h.frequencyRoute n).support ≤ h.slice.maxSupport n ∧
      (h.frequencyRoute n).chi ≤ h.slice.maxChiFrequencyBand n := by
  simp [frequencyRoute]

/-- Lift a frequency slice to a domain cover with one frequency-local route per size. -/
def toDomainCover (h : FrequencySliceToP F) : SymbolicDomainCover F :=
  { routes := fun n => [h.frequencyRoute n]
  , maxSupport := h.slice.maxSupport
  , maxChi := h.slice.maxChiFrequencyBand
  , routeCount := h.slice.routeCount
  , parityOk := h.slice.parityOk
  , denseFallbackCount := h.slice.denseFallbackCount }

theorem toDomainCover_accepted (h : FrequencySliceToP F) (n : Nat) (hn : 1 ≤ n) :
    h.toDomainCover.acceptedAt n := by
  have hacc := h.acceptedAll n hn
  have hrpos : 0 < h.slice.routeCount n := hacc.2.2.2.2.1
  refine ⟨hacc.1, hacc.2.1, ?_, Nat.succ_le_of_lt hrpos, ?_⟩
  · intro r hr
    simp [toDomainCover, frequencyRoute] at hr
    subst hr
    exact h.frequencyRoute_covered n hn
  · intro r hr
    simp [toDomainCover, frequencyRoute] at hr
    subst hr
    exact h.frequencyRoute_metrics_bounded n

/-- Lift polynomial witnesses from the frequency slice to the induced domain cover. -/
def toDomainCoverWitness (h : FrequencySliceToP F) :
    DomainCoverPolynomialWitness h.toDomainCover :=
  { witness := h.polynomialWitness.witness
  , supportBound := h.polynomialWitness.supportBound
  , chiBound := h.polynomialWitness.frequencyChiBound
  , routeCountBound := h.polynomialWitness.routeCountBound }

def toDomainCoverToP (h : FrequencySliceToP F) : DomainCoverToP F :=
  { cover := h.toDomainCover
  , acceptedAll := h.toDomainCover_accepted
  , polynomialWitness := h.toDomainCoverWitness }

end FrequencySliceToP

/-- **Embedding:** frequency-slice certificates are domain-cover certificates. -/
def frequency_slice_implies_domain_cover
    {F : CircuitFamily} (h : FrequencySliceToP F) : DomainCoverToP F :=
  h.toDomainCoverToP

def frequency_slice_implies_has_domain_cover
    {F : CircuitFamily} (h : FrequencySliceToP F) :
    HasDomainCoverToP F :=
  ⟨FrequencySliceToP.toDomainCoverToP h⟩

theorem frequency_slice_implies_domain_cover_in_P
    {F : CircuitFamily} (h : FrequencySliceToP F) :
    ClassicalPolynomialSimulableByDomainCover F :=
  shell_or_frequency_coverage_to_P (FrequencySliceToP.toDomainCoverToP h)

/-- The induced domain cover has the same schedule cost as the frequency slice at every size. -/
theorem frequency_slice_domain_cover_cost_eq
    {F : CircuitFamily} (h : FrequencySliceToP F) (n : Nat) :
    (FrequencySliceToP.toDomainCover h).costAt n = h.slice.costAt n := by
  simp [SymbolicDomainCover.costAt, SymbolicFrequencySlice.costAt, FrequencySliceToP.toDomainCover]

end Hqiv.QuantumComputing

import Hqiv.QuantumComputing.DomainCoverFromFrequencySlice
import Hqiv.QuantumComputing.FrequencyCertificate

/-!
# Generated frequency certificates lift to domain-cover certificates

Python-exported `FrequencyPolynomialCertificate` objects induce a symbolic frequency slice whose
metrics are the polynomial envelopes from the witness degrees.  Accepted obligations discharge
`FrequencySliceToP`, which embeds into `DomainCoverToP` via `DomainCoverFromFrequencySlice`.

This path avoids `decide` on domain-cover acceptance: route coverage uses `True` gate semantics
and the frequency-local embedding supplies one route per size.
-/

namespace Hqiv.QuantumComputing

def circuitFamilyFromCert (cert : FrequencyPolynomialCertificate) : CircuitFamily :=
  { name := cert.obligations.circuitId }

def frequencySliceFromCert (cert : FrequencyPolynomialCertificate) :
    SymbolicFrequencySlice (circuitFamilyFromCert cert) :=
  { maxSupport := fun n => polyEnvelope n cert.witness.polyDegreeSupport
  , maxChiFrequencyBand := fun n => polyEnvelope n cert.witness.polyDegreeFrequencyChi
  , routeCount := fun n => polyEnvelope n cert.witness.polyDegreeRouteCount
  , maxChiBound := fun n => polyEnvelope n cert.witness.polyDegreeFrequencyChi
  , denseFallbackCount := fun _ => cert.obligations.denseFallbackCount
  , parityOk := fun _ => cert.obligations.parityOk
  , frequencyCutUsed := fun _ => cert.obligations.frequencyCutUsed
  , gateSemanticsCovered := fun _ => True }

theorem frequencySliceFromCert_accepted (cert : FrequencyPolynomialCertificate) (n : Nat)
    (_hn : 1 ≤ n) (hacc : cert.obligations.accepted) :
    (frequencySliceFromCert cert).acceptedAt n := by
  unfold SymbolicFrequencySlice.acceptedAt frequencySliceFromCert
  refine ⟨FrequencyObligations.accepted_parity hacc, ?_, le_rfl, ?_, ?_, trivial⟩
  · exact FrequencyObligations.accepted_no_dense_fallback hacc
  · exact Nat.lt_of_lt_of_le (by decide : 0 < 1) (one_le_polyEnvelope n cert.witness.polyDegreeSupport)
  · exact Nat.lt_of_lt_of_le (by decide : 0 < 1) (one_le_polyEnvelope n cert.witness.polyDegreeRouteCount)

def frequencySliceFromCertWitness (cert : FrequencyPolynomialCertificate) :
    FrequencySlicePolynomialWitness (frequencySliceFromCert cert) :=
  { witness := cert.witness
  , supportBound := by intro n _hn; rfl
  , frequencyChiBound := by intro n _hn; rfl
  , routeCountBound := by intro n _hn; rfl }

def frequencySliceToPFromCert (cert : FrequencyPolynomialCertificate)
    (hacc : cert.obligations.accepted) : FrequencySliceToP (circuitFamilyFromCert cert) :=
  { slice := frequencySliceFromCert cert
  , acceptedAll := fun n hn => frequencySliceFromCert_accepted cert n hn hacc
  , polynomialWitness := frequencySliceFromCertWitness cert }

def domainCoverToPFromCert (cert : FrequencyPolynomialCertificate)
    (hacc : cert.obligations.accepted) : DomainCoverToP (circuitFamilyFromCert cert) :=
  FrequencySliceToP.toDomainCoverToP (frequencySliceToPFromCert cert hacc)

def frequency_cert_acceptedPolynomial_domain_cover
    (cert : FrequencyPolynomialCertificate) (n : Nat) (hn : 1 ≤ n)
    (h : cert.acceptedPolynomial n) :
    DomainCoverToP (circuitFamilyFromCert cert) :=
  domainCoverToPFromCert cert (FrequencyPolynomialCertificate.accepted_of_acceptedPolynomial h)

theorem frequency_cert_acceptedPolynomial_in_P
    (cert : FrequencyPolynomialCertificate) (n : Nat) (hn : 1 ≤ n)
    (h : cert.acceptedPolynomial n) :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert cert) :=
  shell_or_frequency_coverage_to_P (frequency_cert_acceptedPolynomial_domain_cover cert n hn h)

/-- When witness degrees are `n = 1` sound, concrete obligation values fit every envelope. -/
theorem obligations_polyBoundedAt_all_of_witness_degree_at_one
    (c : FrequencyObligations) (w : PolynomialWitness) (n : Nat) (hn : 1 ≤ n)
    (h : c.polyBoundedAt w 1) : c.polyBoundedAt w n := by
  constructor
  · exact polyEnvelope_witness_degree_sound hn h.1
  · constructor
    · exact polyEnvelope_witness_degree_sound hn h.2.1
    · exact polyEnvelope_witness_degree_sound hn h.2.2

end Hqiv.QuantumComputing

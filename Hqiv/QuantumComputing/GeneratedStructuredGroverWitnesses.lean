import Hqiv.QuantumComputing.CertificateDomainCover
import Hqiv.QuantumComputing.FrequencyCertificate
import Hqiv.QuantumComputing.SparseScheduleCost

/-!
Auto-generated polynomial certificate witnesses (`hqiv-obligation-certificate/lean-witness/v1`).
Do not edit by hand; regenerate from Python boundary/scaling harness.
-/

namespace HQIVGeneratedWitness

open Hqiv.QuantumComputing


def scale_grover_n11_i1 : FrequencyPolynomialCertificate := {
  obligations := {
    circuitId := "scale_grover_n11_i1"
    nQubits := 11
    depth := 79
    maxChiBound := 256
    maxChiFrequencyBand := 3
    maxSupport := 512
    denseFallbackCount := 0
    parityOk := true
    frequencyCutUsed := true
    frequencyBasis := FrequencyBasis.harmonic
  }
  witness := {
    polyDegreeSupport := 9
    polyDegreeFrequencyChi := 1
    polyDegreeRouteCount := 6
  }
}

theorem scale_grover_n11_i1_obligations_accepted : scale_grover_n11_i1.obligations.accepted := by
  unfold FrequencyObligations.accepted
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide
  · decide
  · decide

theorem scale_grover_n11_i1_acceptedPolynomial : scale_grover_n11_i1.acceptedPolynomial 11 :=
  FrequencyPolynomialCertificate.acceptedPolynomial_of_obligations_and_witness_at_one
    (by decide : 1 ≤ 11) scale_grover_n11_i1_obligations_accepted
    (by decide : 512 ≤ polyEnvelope 1 9)
    (by decide : 3 ≤ polyEnvelope 1 1)
    (by decide : 79 ≤ polyEnvelope 1 6)

theorem scale_grover_n11_i1_domainCoverInP_via_frequency_bridge :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert scale_grover_n11_i1) :=
  frequency_cert_acceptedPolynomial_in_P scale_grover_n11_i1 11 (by decide : 1 ≤ 11) scale_grover_n11_i1_acceptedPolynomial

def scale_grover_n12_i1 : FrequencyPolynomialCertificate := {
  obligations := {
    circuitId := "scale_grover_n12_i1"
    nQubits := 12
    depth := 86
    maxChiBound := 508
    maxChiFrequencyBand := 3
    maxSupport := 1024
    denseFallbackCount := 0
    parityOk := true
    frequencyCutUsed := true
    frequencyBasis := FrequencyBasis.harmonic
  }
  witness := {
    polyDegreeSupport := 9
    polyDegreeFrequencyChi := 1
    polyDegreeRouteCount := 6
  }
}

theorem scale_grover_n12_i1_obligations_accepted : scale_grover_n12_i1.obligations.accepted := by
  unfold FrequencyObligations.accepted
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide
  · decide
  · decide

theorem scale_grover_n12_i1_acceptedPolynomial : scale_grover_n12_i1.acceptedPolynomial 12 :=
  FrequencyPolynomialCertificate.acceptedPolynomial_of_obligations_and_witness_at_one
    (by decide : 1 ≤ 12) scale_grover_n12_i1_obligations_accepted
    (by decide : 1024 ≤ polyEnvelope 1 9)
    (by decide : 3 ≤ polyEnvelope 1 1)
    (by decide : 86 ≤ polyEnvelope 1 6)

theorem scale_grover_n12_i1_domainCoverInP_via_frequency_bridge :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert scale_grover_n12_i1) :=
  frequency_cert_acceptedPolynomial_in_P scale_grover_n12_i1 12 (by decide : 1 ≤ 12) scale_grover_n12_i1_acceptedPolynomial

end HQIVGeneratedWitness

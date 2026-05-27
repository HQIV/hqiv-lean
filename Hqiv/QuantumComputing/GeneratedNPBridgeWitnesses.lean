import Hqiv.QuantumComputing.CertificateDomainCover
import Hqiv.QuantumComputing.FrequencyCertificate
import Hqiv.QuantumComputing.SparseScheduleCost

/-!
Auto-generated polynomial certificate witnesses (`hqiv-obligation-certificate/lean-witness/v1`).
Do not edit by hand; regenerate from Python boundary/scaling harness.
-/

namespace HQIVNPBridgeWitness

open Hqiv.QuantumComputing


def sat_n7_qasmbench : FrequencyPolynomialCertificate := {
  obligations := {
    circuitId := "sat_n7_qasmbench"
    nQubits := 7
    depth := 40
    maxChiBound := 3
    maxChiFrequencyBand := 1
    maxSupport := 8
    denseFallbackCount := 0
    parityOk := true
    frequencyCutUsed := false
    frequencyBasis := FrequencyBasis.harmonic
  }
  witness := {
    polyDegreeSupport := 5
    polyDegreeFrequencyChi := 1
    polyDegreeRouteCount := 6
  }
}

theorem sat_n7_qasmbench_obligations_accepted : sat_n7_qasmbench.obligations.accepted := by
  unfold FrequencyObligations.accepted
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide
  · decide
  · decide

theorem sat_n7_qasmbench_acceptedPolynomial : sat_n7_qasmbench.acceptedPolynomial 7 :=
  FrequencyPolynomialCertificate.acceptedPolynomial_of_obligations_and_witness_at_one
    (by decide : 1 ≤ 7) sat_n7_qasmbench_obligations_accepted
    (by decide : 8 ≤ polyEnvelope 1 5)
    (by decide : 1 ≤ polyEnvelope 1 1)
    (by decide : 40 ≤ polyEnvelope 1 6)

theorem sat_n7_qasmbench_domainCoverInP_via_frequency_bridge :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert sat_n7_qasmbench) :=
  frequency_cert_acceptedPolynomial_in_P sat_n7_qasmbench 7 (by decide : 1 ≤ 7) sat_n7_qasmbench_acceptedPolynomial

def sat_n11_qasmbench : FrequencyPolynomialCertificate := {
  obligations := {
    circuitId := "sat_n11_qasmbench"
    nQubits := 11
    depth := 91
    maxChiBound := 13
    maxChiFrequencyBand := 1
    maxSupport := 32
    denseFallbackCount := 0
    parityOk := true
    frequencyCutUsed := false
    frequencyBasis := FrequencyBasis.harmonic
  }
  witness := {
    polyDegreeSupport := 5
    polyDegreeFrequencyChi := 1
    polyDegreeRouteCount := 6
  }
}

theorem sat_n11_qasmbench_obligations_accepted : sat_n11_qasmbench.obligations.accepted := by
  unfold FrequencyObligations.accepted
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide
  · decide
  · decide

theorem sat_n11_qasmbench_acceptedPolynomial : sat_n11_qasmbench.acceptedPolynomial 11 :=
  FrequencyPolynomialCertificate.acceptedPolynomial_of_obligations_and_witness_at_one
    (by decide : 1 ≤ 11) sat_n11_qasmbench_obligations_accepted
    (by decide : 32 ≤ polyEnvelope 1 5)
    (by decide : 1 ≤ polyEnvelope 1 1)
    (by decide : 91 ≤ polyEnvelope 1 6)

theorem sat_n11_qasmbench_domainCoverInP_via_frequency_bridge :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert sat_n11_qasmbench) :=
  frequency_cert_acceptedPolynomial_in_P sat_n11_qasmbench 11 (by decide : 1 ≤ 11) sat_n11_qasmbench_acceptedPolynomial

def atsp_demo_n3_grover_i2 : FrequencyPolynomialCertificate := {
  obligations := {
    circuitId := "atsp_demo_n3_grover_i2"
    nQubits := 3
    depth := 43
    maxChiBound := 2
    maxChiFrequencyBand := 2
    maxSupport := 8
    denseFallbackCount := 0
    parityOk := true
    frequencyCutUsed := true
    frequencyBasis := FrequencyBasis.harmonic
  }
  witness := {
    polyDegreeSupport := 2
    polyDegreeFrequencyChi := 0
    polyDegreeRouteCount := 5
  }
}

theorem atsp_demo_n3_grover_i2_obligations_accepted : atsp_demo_n3_grover_i2.obligations.accepted := by
  unfold FrequencyObligations.accepted
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide
  · decide
  · decide

theorem atsp_demo_n3_grover_i2_acceptedPolynomial : atsp_demo_n3_grover_i2.acceptedPolynomial 3 :=
  FrequencyPolynomialCertificate.acceptedPolynomial_of_obligations_and_witness_at_one
    (by decide : 1 ≤ 3) atsp_demo_n3_grover_i2_obligations_accepted
    (by decide : 8 ≤ polyEnvelope 1 2)
    (by decide : 2 ≤ polyEnvelope 1 0)
    (by decide : 43 ≤ polyEnvelope 1 5)

theorem atsp_demo_n3_grover_i2_domainCoverInP_via_frequency_bridge :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert atsp_demo_n3_grover_i2) :=
  frequency_cert_acceptedPolynomial_in_P atsp_demo_n3_grover_i2 3 (by decide : 1 ≤ 3) atsp_demo_n3_grover_i2_acceptedPolynomial

def atsp_demo_n3_via_sat : FrequencyPolynomialCertificate := {
  obligations := {
    circuitId := "atsp_demo_n3_via_sat"
    nQubits := 6
    depth := 122
    maxChiBound := 8
    maxChiFrequencyBand := 3
    maxSupport := 64
    denseFallbackCount := 0
    parityOk := true
    frequencyCutUsed := true
    frequencyBasis := FrequencyBasis.harmonic
  }
  witness := {
    polyDegreeSupport := 5
    polyDegreeFrequencyChi := 1
    polyDegreeRouteCount := 6
  }
}

theorem atsp_demo_n3_via_sat_obligations_accepted : atsp_demo_n3_via_sat.obligations.accepted := by
  unfold FrequencyObligations.accepted
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide
  · decide
  · decide

theorem atsp_demo_n3_via_sat_acceptedPolynomial : atsp_demo_n3_via_sat.acceptedPolynomial 6 :=
  FrequencyPolynomialCertificate.acceptedPolynomial_of_obligations_and_witness_at_one
    (by decide : 1 ≤ 6) atsp_demo_n3_via_sat_obligations_accepted
    (by decide : 64 ≤ polyEnvelope 1 5)
    (by decide : 3 ≤ polyEnvelope 1 1)
    (by decide : 122 ≤ polyEnvelope 1 6)

theorem atsp_demo_n3_via_sat_domainCoverInP_via_frequency_bridge :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert atsp_demo_n3_via_sat) :=
  frequency_cert_acceptedPolynomial_in_P atsp_demo_n3_via_sat 6 (by decide : 1 ≤ 6) atsp_demo_n3_via_sat_acceptedPolynomial

end HQIVNPBridgeWitness

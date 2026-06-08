import Hqiv.QuantumComputing.CertificateDomainCover
import Hqiv.QuantumComputing.FrequencyCertificate
import Hqiv.QuantumComputing.SparseScheduleCost

/-!
Auto-generated polynomial certificate witnesses (`hqiv-obligation-certificate/lean-witness/v1`).
Do not edit by hand; regenerate from Python boundary/scaling harness.
-/

namespace HQIVGeneratedWitness

open Hqiv.QuantumComputing


def scale_qft_n11 : FrequencyPolynomialCertificate := {
  obligations := {
    circuitId := "scale_qft_n11"
    nQubits := 11
    depth := 71
    maxChiBound := 1025
    maxChiFrequencyBand := 3
    maxSupport := 2048
    denseFallbackCount := 0
    parityOk := true
    frequencyCutUsed := true
    frequencyBasis := FrequencyBasis.harmonic
  }
  witness := {
    polyDegreeSupport := 11
    polyDegreeFrequencyChi := 1
    polyDegreeRouteCount := 6
  }
}

theorem scale_qft_n11_obligations_accepted : scale_qft_n11.obligations.accepted := by
  unfold FrequencyObligations.accepted
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide
  · decide
  · decide

theorem scale_qft_n11_acceptedPolynomial : scale_qft_n11.acceptedPolynomial 11 :=
  FrequencyPolynomialCertificate.acceptedPolynomial_of_obligations_and_witness_at_one
    (by decide : 1 ≤ 11) scale_qft_n11_obligations_accepted
    (by decide : 2048 ≤ polyEnvelope 1 11)
    (by decide : 3 ≤ polyEnvelope 1 1)
    (by decide : 71 ≤ polyEnvelope 1 6)

theorem scale_qft_n11_domainCoverInP_via_frequency_bridge :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert scale_qft_n11) :=
  frequency_cert_acceptedPolynomial_in_P scale_qft_n11 11 (by decide : 1 ≤ 11) scale_qft_n11_acceptedPolynomial

def scale_qaoa_n11_p3 : FrequencyPolynomialCertificate := {
  obligations := {
    circuitId := "scale_qaoa_n11_p3"
    nQubits := 11
    depth := 77
    maxChiBound := 266
    maxChiFrequencyBand := 3
    maxSupport := 2048
    denseFallbackCount := 0
    parityOk := true
    frequencyCutUsed := true
    frequencyBasis := FrequencyBasis.harmonic
  }
  witness := {
    polyDegreeSupport := 11
    polyDegreeFrequencyChi := 1
    polyDegreeRouteCount := 6
  }
}

theorem scale_qaoa_n11_p3_obligations_accepted : scale_qaoa_n11_p3.obligations.accepted := by
  unfold FrequencyObligations.accepted
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide
  · decide
  · decide

theorem scale_qaoa_n11_p3_acceptedPolynomial : scale_qaoa_n11_p3.acceptedPolynomial 11 :=
  FrequencyPolynomialCertificate.acceptedPolynomial_of_obligations_and_witness_at_one
    (by decide : 1 ≤ 11) scale_qaoa_n11_p3_obligations_accepted
    (by decide : 2048 ≤ polyEnvelope 1 11)
    (by decide : 3 ≤ polyEnvelope 1 1)
    (by decide : 77 ≤ polyEnvelope 1 6)

theorem scale_qaoa_n11_p3_domainCoverInP_via_frequency_bridge :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert scale_qaoa_n11_p3) :=
  frequency_cert_acceptedPolynomial_in_P scale_qaoa_n11_p3 11 (by decide : 1 ≤ 11) scale_qaoa_n11_p3_acceptedPolynomial

def scale_clifford_t_n11_d51 : FrequencyPolynomialCertificate := {
  obligations := {
    circuitId := "scale_clifford_t_n11_d51"
    nQubits := 11
    depth := 80
    maxChiBound := 32
    maxChiFrequencyBand := 3
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

theorem scale_clifford_t_n11_d51_obligations_accepted : scale_clifford_t_n11_d51.obligations.accepted := by
  unfold FrequencyObligations.accepted
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide
  · decide
  · decide

theorem scale_clifford_t_n11_d51_acceptedPolynomial : scale_clifford_t_n11_d51.acceptedPolynomial 11 :=
  FrequencyPolynomialCertificate.acceptedPolynomial_of_obligations_and_witness_at_one
    (by decide : 1 ≤ 11) scale_clifford_t_n11_d51_obligations_accepted
    (by decide : 32 ≤ polyEnvelope 1 5)
    (by decide : 3 ≤ polyEnvelope 1 1)
    (by decide : 80 ≤ polyEnvelope 1 6)

theorem scale_clifford_t_n11_d51_domainCoverInP_via_frequency_bridge :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert scale_clifford_t_n11_d51) :=
  frequency_cert_acceptedPolynomial_in_P scale_clifford_t_n11_d51 11 (by decide : 1 ≤ 11) scale_clifford_t_n11_d51_acceptedPolynomial

def scale_random_embed_n11_d36 : FrequencyPolynomialCertificate := {
  obligations := {
    circuitId := "scale_random_embed_n11_d36"
    nQubits := 11
    depth := 36
    maxChiBound := 64
    maxChiFrequencyBand := 3
    maxSupport := 64
    denseFallbackCount := 0
    parityOk := true
    frequencyCutUsed := false
    frequencyBasis := FrequencyBasis.harmonic
  }
  witness := {
    polyDegreeSupport := 5
    polyDegreeFrequencyChi := 1
    polyDegreeRouteCount := 5
  }
}

theorem scale_random_embed_n11_d36_obligations_accepted : scale_random_embed_n11_d36.obligations.accepted := by
  unfold FrequencyObligations.accepted
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide
  · decide
  · decide

theorem scale_random_embed_n11_d36_acceptedPolynomial : scale_random_embed_n11_d36.acceptedPolynomial 11 :=
  FrequencyPolynomialCertificate.acceptedPolynomial_of_obligations_and_witness_at_one
    (by decide : 1 ≤ 11) scale_random_embed_n11_d36_obligations_accepted
    (by decide : 64 ≤ polyEnvelope 1 5)
    (by decide : 3 ≤ polyEnvelope 1 1)
    (by decide : 36 ≤ polyEnvelope 1 5)

theorem scale_random_embed_n11_d36_domainCoverInP_via_frequency_bridge :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert scale_random_embed_n11_d36) :=
  frequency_cert_acceptedPolynomial_in_P scale_random_embed_n11_d36 11 (by decide : 1 ≤ 11) scale_random_embed_n11_d36_acceptedPolynomial

def scale_vqe_n11_l2 : FrequencyPolynomialCertificate := {
  obligations := {
    circuitId := "scale_vqe_n11_l2"
    nQubits := 11
    depth := 42
    maxChiBound := 121
    maxChiFrequencyBand := 3
    maxSupport := 2048
    denseFallbackCount := 0
    parityOk := true
    frequencyCutUsed := true
    frequencyBasis := FrequencyBasis.harmonic
  }
  witness := {
    polyDegreeSupport := 11
    polyDegreeFrequencyChi := 1
    polyDegreeRouteCount := 5
  }
}

theorem scale_vqe_n11_l2_obligations_accepted : scale_vqe_n11_l2.obligations.accepted := by
  unfold FrequencyObligations.accepted
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide
  · decide
  · decide

theorem scale_vqe_n11_l2_acceptedPolynomial : scale_vqe_n11_l2.acceptedPolynomial 11 :=
  FrequencyPolynomialCertificate.acceptedPolynomial_of_obligations_and_witness_at_one
    (by decide : 1 ≤ 11) scale_vqe_n11_l2_obligations_accepted
    (by decide : 2048 ≤ polyEnvelope 1 11)
    (by decide : 3 ≤ polyEnvelope 1 1)
    (by decide : 42 ≤ polyEnvelope 1 5)

theorem scale_vqe_n11_l2_domainCoverInP_via_frequency_bridge :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert scale_vqe_n11_l2) :=
  frequency_cert_acceptedPolynomial_in_P scale_vqe_n11_l2 11 (by decide : 1 ≤ 11) scale_vqe_n11_l2_acceptedPolynomial

def scale_qpe_n11_p4 : FrequencyPolynomialCertificate := {
  obligations := {
    circuitId := "scale_qpe_n11_p4"
    nQubits := 11
    depth := 12
    maxChiBound := 1
    maxChiFrequencyBand := 1
    maxSupport := 1
    denseFallbackCount := 0
    parityOk := true
    frequencyCutUsed := false
    frequencyBasis := FrequencyBasis.harmonic
  }
  witness := {
    polyDegreeSupport := 0
    polyDegreeFrequencyChi := 0
    polyDegreeRouteCount := 3
  }
}

theorem scale_qpe_n11_p4_obligations_accepted : scale_qpe_n11_p4.obligations.accepted := by
  unfold FrequencyObligations.accepted
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide
  · decide
  · decide

theorem scale_qpe_n11_p4_acceptedPolynomial : scale_qpe_n11_p4.acceptedPolynomial 11 :=
  FrequencyPolynomialCertificate.acceptedPolynomial_of_obligations_and_witness_at_one
    (by decide : 1 ≤ 11) scale_qpe_n11_p4_obligations_accepted
    (by decide : 1 ≤ polyEnvelope 1 0)
    (by decide : 1 ≤ polyEnvelope 1 0)
    (by decide : 12 ≤ polyEnvelope 1 3)

theorem scale_qpe_n11_p4_domainCoverInP_via_frequency_bridge :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert scale_qpe_n11_p4) :=
  frequency_cert_acceptedPolynomial_in_P scale_qpe_n11_p4 11 (by decide : 1 ≤ 11) scale_qpe_n11_p4_acceptedPolynomial

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

def scale_quantum_walk_n11_s6 : FrequencyPolynomialCertificate := {
  obligations := {
    circuitId := "scale_quantum_walk_n11_s6"
    nQubits := 11
    depth := 126
    maxChiBound := 1
    maxChiFrequencyBand := 1
    maxSupport := 1
    denseFallbackCount := 0
    parityOk := true
    frequencyCutUsed := true
    frequencyBasis := FrequencyBasis.harmonic
  }
  witness := {
    polyDegreeSupport := 0
    polyDegreeFrequencyChi := 0
    polyDegreeRouteCount := 7
  }
}

theorem scale_quantum_walk_n11_s6_obligations_accepted : scale_quantum_walk_n11_s6.obligations.accepted := by
  unfold FrequencyObligations.accepted
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide
  · decide
  · decide

theorem scale_quantum_walk_n11_s6_acceptedPolynomial : scale_quantum_walk_n11_s6.acceptedPolynomial 11 :=
  FrequencyPolynomialCertificate.acceptedPolynomial_of_obligations_and_witness_at_one
    (by decide : 1 ≤ 11) scale_quantum_walk_n11_s6_obligations_accepted
    (by decide : 1 ≤ polyEnvelope 1 0)
    (by decide : 1 ≤ polyEnvelope 1 0)
    (by decide : 126 ≤ polyEnvelope 1 7)

theorem scale_quantum_walk_n11_s6_domainCoverInP_via_frequency_bridge :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert scale_quantum_walk_n11_s6) :=
  frequency_cert_acceptedPolynomial_in_P scale_quantum_walk_n11_s6 11 (by decide : 1 ≤ 11) scale_quantum_walk_n11_s6_acceptedPolynomial

def scale_qft_n12 : FrequencyPolynomialCertificate := {
  obligations := {
    circuitId := "scale_qft_n12"
    nQubits := 12
    depth := 84
    maxChiBound := 2025
    maxChiFrequencyBand := 3
    maxSupport := 4096
    denseFallbackCount := 0
    parityOk := true
    frequencyCutUsed := true
    frequencyBasis := FrequencyBasis.harmonic
  }
  witness := {
    polyDegreeSupport := 11
    polyDegreeFrequencyChi := 1
    polyDegreeRouteCount := 6
  }
}

theorem scale_qft_n12_obligations_accepted : scale_qft_n12.obligations.accepted := by
  unfold FrequencyObligations.accepted
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide
  · decide
  · decide

theorem scale_qft_n12_acceptedPolynomial : scale_qft_n12.acceptedPolynomial 12 :=
  FrequencyPolynomialCertificate.acceptedPolynomial_of_obligations_and_witness_at_one
    (by decide : 1 ≤ 12) scale_qft_n12_obligations_accepted
    (by decide : 4096 ≤ polyEnvelope 1 11)
    (by decide : 3 ≤ polyEnvelope 1 1)
    (by decide : 84 ≤ polyEnvelope 1 6)

theorem scale_qft_n12_domainCoverInP_via_frequency_bridge :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert scale_qft_n12) :=
  frequency_cert_acceptedPolynomial_in_P scale_qft_n12 12 (by decide : 1 ≤ 12) scale_qft_n12_acceptedPolynomial

def scale_qaoa_n12_p3 : FrequencyPolynomialCertificate := {
  obligations := {
    circuitId := "scale_qaoa_n12_p3"
    nQubits := 12
    depth := 84
    maxChiBound := 465
    maxChiFrequencyBand := 3
    maxSupport := 4096
    denseFallbackCount := 0
    parityOk := true
    frequencyCutUsed := true
    frequencyBasis := FrequencyBasis.harmonic
  }
  witness := {
    polyDegreeSupport := 11
    polyDegreeFrequencyChi := 1
    polyDegreeRouteCount := 6
  }
}

theorem scale_qaoa_n12_p3_obligations_accepted : scale_qaoa_n12_p3.obligations.accepted := by
  unfold FrequencyObligations.accepted
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide
  · decide
  · decide

theorem scale_qaoa_n12_p3_acceptedPolynomial : scale_qaoa_n12_p3.acceptedPolynomial 12 :=
  FrequencyPolynomialCertificate.acceptedPolynomial_of_obligations_and_witness_at_one
    (by decide : 1 ≤ 12) scale_qaoa_n12_p3_obligations_accepted
    (by decide : 4096 ≤ polyEnvelope 1 11)
    (by decide : 3 ≤ polyEnvelope 1 1)
    (by decide : 84 ≤ polyEnvelope 1 6)

theorem scale_qaoa_n12_p3_domainCoverInP_via_frequency_bridge :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert scale_qaoa_n12_p3) :=
  frequency_cert_acceptedPolynomial_in_P scale_qaoa_n12_p3 12 (by decide : 1 ≤ 12) scale_qaoa_n12_p3_acceptedPolynomial

def scale_clifford_t_n12_d54 : FrequencyPolynomialCertificate := {
  obligations := {
    circuitId := "scale_clifford_t_n12_d54"
    nQubits := 12
    depth := 81
    maxChiBound := 64
    maxChiFrequencyBand := 3
    maxSupport := 64
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

theorem scale_clifford_t_n12_d54_obligations_accepted : scale_clifford_t_n12_d54.obligations.accepted := by
  unfold FrequencyObligations.accepted
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide
  · decide
  · decide

theorem scale_clifford_t_n12_d54_acceptedPolynomial : scale_clifford_t_n12_d54.acceptedPolynomial 12 :=
  FrequencyPolynomialCertificate.acceptedPolynomial_of_obligations_and_witness_at_one
    (by decide : 1 ≤ 12) scale_clifford_t_n12_d54_obligations_accepted
    (by decide : 64 ≤ polyEnvelope 1 5)
    (by decide : 3 ≤ polyEnvelope 1 1)
    (by decide : 81 ≤ polyEnvelope 1 6)

theorem scale_clifford_t_n12_d54_domainCoverInP_via_frequency_bridge :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert scale_clifford_t_n12_d54) :=
  frequency_cert_acceptedPolynomial_in_P scale_clifford_t_n12_d54 12 (by decide : 1 ≤ 12) scale_clifford_t_n12_d54_acceptedPolynomial

def scale_random_embed_n12_d38 : FrequencyPolynomialCertificate := {
  obligations := {
    circuitId := "scale_random_embed_n12_d38"
    nQubits := 12
    depth := 38
    maxChiBound := 32
    maxChiFrequencyBand := 2
    maxSupport := 32
    denseFallbackCount := 0
    parityOk := true
    frequencyCutUsed := false
    frequencyBasis := FrequencyBasis.harmonic
  }
  witness := {
    polyDegreeSupport := 5
    polyDegreeFrequencyChi := 1
    polyDegreeRouteCount := 5
  }
}

theorem scale_random_embed_n12_d38_obligations_accepted : scale_random_embed_n12_d38.obligations.accepted := by
  unfold FrequencyObligations.accepted
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide
  · decide
  · decide

theorem scale_random_embed_n12_d38_acceptedPolynomial : scale_random_embed_n12_d38.acceptedPolynomial 12 :=
  FrequencyPolynomialCertificate.acceptedPolynomial_of_obligations_and_witness_at_one
    (by decide : 1 ≤ 12) scale_random_embed_n12_d38_obligations_accepted
    (by decide : 32 ≤ polyEnvelope 1 5)
    (by decide : 2 ≤ polyEnvelope 1 1)
    (by decide : 38 ≤ polyEnvelope 1 5)

theorem scale_random_embed_n12_d38_domainCoverInP_via_frequency_bridge :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert scale_random_embed_n12_d38) :=
  frequency_cert_acceptedPolynomial_in_P scale_random_embed_n12_d38 12 (by decide : 1 ≤ 12) scale_random_embed_n12_d38_acceptedPolynomial

def scale_vqe_n12_l2 : FrequencyPolynomialCertificate := {
  obligations := {
    circuitId := "scale_vqe_n12_l2"
    nQubits := 12
    depth := 46
    maxChiBound := 230
    maxChiFrequencyBand := 3
    maxSupport := 4096
    denseFallbackCount := 0
    parityOk := true
    frequencyCutUsed := true
    frequencyBasis := FrequencyBasis.harmonic
  }
  witness := {
    polyDegreeSupport := 11
    polyDegreeFrequencyChi := 1
    polyDegreeRouteCount := 5
  }
}

theorem scale_vqe_n12_l2_obligations_accepted : scale_vqe_n12_l2.obligations.accepted := by
  unfold FrequencyObligations.accepted
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide
  · decide
  · decide

theorem scale_vqe_n12_l2_acceptedPolynomial : scale_vqe_n12_l2.acceptedPolynomial 12 :=
  FrequencyPolynomialCertificate.acceptedPolynomial_of_obligations_and_witness_at_one
    (by decide : 1 ≤ 12) scale_vqe_n12_l2_obligations_accepted
    (by decide : 4096 ≤ polyEnvelope 1 11)
    (by decide : 3 ≤ polyEnvelope 1 1)
    (by decide : 46 ≤ polyEnvelope 1 5)

theorem scale_vqe_n12_l2_domainCoverInP_via_frequency_bridge :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert scale_vqe_n12_l2) :=
  frequency_cert_acceptedPolynomial_in_P scale_vqe_n12_l2 12 (by decide : 1 ≤ 12) scale_vqe_n12_l2_acceptedPolynomial

def scale_qpe_n12_p4 : FrequencyPolynomialCertificate := {
  obligations := {
    circuitId := "scale_qpe_n12_p4"
    nQubits := 12
    depth := 12
    maxChiBound := 1
    maxChiFrequencyBand := 1
    maxSupport := 1
    denseFallbackCount := 0
    parityOk := true
    frequencyCutUsed := false
    frequencyBasis := FrequencyBasis.harmonic
  }
  witness := {
    polyDegreeSupport := 0
    polyDegreeFrequencyChi := 0
    polyDegreeRouteCount := 3
  }
}

theorem scale_qpe_n12_p4_obligations_accepted : scale_qpe_n12_p4.obligations.accepted := by
  unfold FrequencyObligations.accepted
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide
  · decide
  · decide

theorem scale_qpe_n12_p4_acceptedPolynomial : scale_qpe_n12_p4.acceptedPolynomial 12 :=
  FrequencyPolynomialCertificate.acceptedPolynomial_of_obligations_and_witness_at_one
    (by decide : 1 ≤ 12) scale_qpe_n12_p4_obligations_accepted
    (by decide : 1 ≤ polyEnvelope 1 0)
    (by decide : 1 ≤ polyEnvelope 1 0)
    (by decide : 12 ≤ polyEnvelope 1 3)

theorem scale_qpe_n12_p4_domainCoverInP_via_frequency_bridge :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert scale_qpe_n12_p4) :=
  frequency_cert_acceptedPolynomial_in_P scale_qpe_n12_p4 12 (by decide : 1 ≤ 12) scale_qpe_n12_p4_acceptedPolynomial

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

def scale_quantum_walk_n12_s6 : FrequencyPolynomialCertificate := {
  obligations := {
    circuitId := "scale_quantum_walk_n12_s6"
    nQubits := 12
    depth := 138
    maxChiBound := 1
    maxChiFrequencyBand := 1
    maxSupport := 1
    denseFallbackCount := 0
    parityOk := true
    frequencyCutUsed := true
    frequencyBasis := FrequencyBasis.harmonic
  }
  witness := {
    polyDegreeSupport := 0
    polyDegreeFrequencyChi := 0
    polyDegreeRouteCount := 7
  }
}

theorem scale_quantum_walk_n12_s6_obligations_accepted : scale_quantum_walk_n12_s6.obligations.accepted := by
  unfold FrequencyObligations.accepted
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide
  · decide
  · decide

theorem scale_quantum_walk_n12_s6_acceptedPolynomial : scale_quantum_walk_n12_s6.acceptedPolynomial 12 :=
  FrequencyPolynomialCertificate.acceptedPolynomial_of_obligations_and_witness_at_one
    (by decide : 1 ≤ 12) scale_quantum_walk_n12_s6_obligations_accepted
    (by decide : 1 ≤ polyEnvelope 1 0)
    (by decide : 1 ≤ polyEnvelope 1 0)
    (by decide : 138 ≤ polyEnvelope 1 7)

theorem scale_quantum_walk_n12_s6_domainCoverInP_via_frequency_bridge :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert scale_quantum_walk_n12_s6) :=
  frequency_cert_acceptedPolynomial_in_P scale_quantum_walk_n12_s6 12 (by decide : 1 ≤ 12) scale_quantum_walk_n12_s6_acceptedPolynomial

end HQIVGeneratedWitness

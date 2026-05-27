import Hqiv.QuantumComputing.GeneratedNPBridgeWitnesses
import Hqiv.QuantumComputing.SymbolicDomainCoverExamples
import Hqiv.QuantumComputing.NPBridgeDecision

/-!
Auto-generated NP-bridge instance discharge module.
Links exported instance certificates to symbolic family anchors and schedule/readout bounds.
Do not edit by hand; regenerate via `scripts/discharge_np_obligations.py`.
-/

namespace Hqiv.QuantumComputing.NPBridgeInstanceCover

open Hqiv.QuantumComputing
open Hqiv.QuantumComputing.NPBridgeDecision
open HQIVNPBridgeWitness


/-- Instance-level P simulation for `sat_n7_qasmbench` (frequency-bridge export). -/
theorem sat_n7_qasmbench_instance_in_P :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert sat_n7_qasmbench) :=
  sat_n7_qasmbench_domainCoverInP_via_frequency_bridge

/-- Polynomial schedule cost bound for `sat_n7_qasmbench` at n=7. -/
theorem sat_n7_qasmbench_schedule_poly (hn : 1 ≤ 7) :
    ∃ d, scheduleCost sat_n7_qasmbench.obligations.depth sat_n7_qasmbench.obligations.maxSupport
        sat_n7_qasmbench.obligations.maxChiFrequencyBand ≤ polyEnvelope 7 d :=
  scheduleCost_polynomial_of_acceptedPolynomial sat_n7_qasmbench 7 hn sat_n7_qasmbench_acceptedPolynomial

/-- Symbolic family anchor backing `sat_n7_qasmbench`. -/
theorem sat_n7_qasmbench_family_in_P : ClassicalPolynomialSimulableByDomainCover satGroverFamily :=
  sat_grover_symbolic_in_P

/-- Instance-level P simulation for `sat_n11_qasmbench` (frequency-bridge export). -/
theorem sat_n11_qasmbench_instance_in_P :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert sat_n11_qasmbench) :=
  sat_n11_qasmbench_domainCoverInP_via_frequency_bridge

/-- Polynomial schedule cost bound for `sat_n11_qasmbench` at n=11. -/
theorem sat_n11_qasmbench_schedule_poly (hn : 1 ≤ 11) :
    ∃ d, scheduleCost sat_n11_qasmbench.obligations.depth sat_n11_qasmbench.obligations.maxSupport
        sat_n11_qasmbench.obligations.maxChiFrequencyBand ≤ polyEnvelope 11 d :=
  scheduleCost_polynomial_of_acceptedPolynomial sat_n11_qasmbench 11 hn sat_n11_qasmbench_acceptedPolynomial

/-- Symbolic family anchor backing `sat_n11_qasmbench`. -/
theorem sat_n11_qasmbench_family_in_P : ClassicalPolynomialSimulableByDomainCover satGroverFamily :=
  sat_grover_symbolic_in_P

/-- Instance-level P simulation for `atsp_demo_n3_grover_i2` (frequency-bridge export). -/
theorem atsp_demo_n3_grover_i2_instance_in_P :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert atsp_demo_n3_grover_i2) :=
  atsp_demo_n3_grover_i2_domainCoverInP_via_frequency_bridge

/-- Polynomial schedule cost bound for `atsp_demo_n3_grover_i2` at n=3. -/
theorem atsp_demo_n3_grover_i2_schedule_poly (hn : 1 ≤ 3) :
    ∃ d, scheduleCost atsp_demo_n3_grover_i2.obligations.depth atsp_demo_n3_grover_i2.obligations.maxSupport
        atsp_demo_n3_grover_i2.obligations.maxChiFrequencyBand ≤ polyEnvelope 3 d :=
  scheduleCost_polynomial_of_acceptedPolynomial atsp_demo_n3_grover_i2 3 hn atsp_demo_n3_grover_i2_acceptedPolynomial

/-- Symbolic family anchor backing `atsp_demo_n3_grover_i2`. -/
theorem atsp_demo_n3_grover_i2_family_in_P : ClassicalPolynomialSimulableByDomainCover atspGroverFamily :=
  atsp_grover_symbolic_in_P

/-- Instance-level P simulation for `atsp_demo_n3_via_sat` (frequency-bridge export). -/
theorem atsp_demo_n3_via_sat_instance_in_P :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert atsp_demo_n3_via_sat) :=
  atsp_demo_n3_via_sat_domainCoverInP_via_frequency_bridge

/-- Polynomial schedule cost bound for `atsp_demo_n3_via_sat` at n=6. -/
theorem atsp_demo_n3_via_sat_schedule_poly (hn : 1 ≤ 6) :
    ∃ d, scheduleCost atsp_demo_n3_via_sat.obligations.depth atsp_demo_n3_via_sat.obligations.maxSupport
        atsp_demo_n3_via_sat.obligations.maxChiFrequencyBand ≤ polyEnvelope 6 d :=
  scheduleCost_polynomial_of_acceptedPolynomial atsp_demo_n3_via_sat 6 hn atsp_demo_n3_via_sat_acceptedPolynomial

/-- Symbolic family anchor backing `atsp_demo_n3_via_sat`. -/
theorem atsp_demo_n3_via_sat_family_in_P : ClassicalPolynomialSimulableByDomainCover satGroverFamily :=
  sat_grover_symbolic_in_P

end Hqiv.QuantumComputing.NPBridgeInstanceCover

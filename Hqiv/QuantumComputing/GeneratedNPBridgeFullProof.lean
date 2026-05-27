import Hqiv.QuantumComputing.GeneratedNPBridgeWitnesses
import Hqiv.QuantumComputing.NPBridgeUniversal
import Hqiv.QuantumComputing.NPBridgeDecision

/-!
Auto-generated NP-bridge **full discharge** module.
Bundles polynomial search/readout, domain-cover simulation, and rational measurement witnesses.
Regenerate via `scripts/discharge_np_obligations.py`.
Do not edit by hand.
-/

namespace Hqiv.QuantumComputing.NPBridgeFullProof

open Hqiv.QuantumComputing
open Hqiv.QuantumComputing.NPBridgeDecision
open Hqiv.QuantumComputing.NPBridgeUniversal
open HQIVNPBridgeWitness


def sat_n7_qasmbench_measurement : MeasurementOutcomeWitness :=
  MeasurementOutcomeWitness.ofRationals 1 2 13 16

theorem sat_n7_qasmbench_measurement_thresholdMet :
    sat_n7_qasmbench_measurement.thresholdMet := by
  unfold MeasurementOutcomeWitness.thresholdMet sat_n7_qasmbench_measurement
  decide

/-- Polynomial search/readout discharge for `sat_n7_qasmbench`. -/
def sat_n7_qasmbench_search_discharge : NPSearchDischarge sat_n7_qasmbench 7 :=
  NPSearchDischarge.of_acceptedPolynomial sat_n7_qasmbench 7 (by decide : 1 ≤ 7) sat_n7_qasmbench_acceptedPolynomial

theorem sat_n7_qasmbench_domain_cover :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert sat_n7_qasmbench) :=
  sat_n7_qasmbench_domainCoverInP_via_frequency_bridge

/-- Full bundled discharge: poly search/readout + domain cover + measurement threshold. -/
theorem sat_n7_qasmbench_full_discharge :
    NPSearchDischarge sat_n7_qasmbench 7 ∧
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert sat_n7_qasmbench) ∧
    sat_n7_qasmbench_measurement.thresholdMet := by
  refine ⟨sat_n7_qasmbench_search_discharge, sat_n7_qasmbench_domain_cover, sat_n7_qasmbench_measurement_thresholdMet⟩

def sat_n11_qasmbench_measurement : MeasurementOutcomeWitness :=
  MeasurementOutcomeWitness.ofRationals 1 20 25 256

theorem sat_n11_qasmbench_measurement_thresholdMet :
    sat_n11_qasmbench_measurement.thresholdMet := by
  unfold MeasurementOutcomeWitness.thresholdMet sat_n11_qasmbench_measurement
  decide

/-- Polynomial search/readout discharge for `sat_n11_qasmbench`. -/
def sat_n11_qasmbench_search_discharge : NPSearchDischarge sat_n11_qasmbench 11 :=
  NPSearchDischarge.of_acceptedPolynomial sat_n11_qasmbench 11 (by decide : 1 ≤ 11) sat_n11_qasmbench_acceptedPolynomial

theorem sat_n11_qasmbench_domain_cover :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert sat_n11_qasmbench) :=
  sat_n11_qasmbench_domainCoverInP_via_frequency_bridge

/-- Full bundled discharge: poly search/readout + domain cover + measurement threshold. -/
theorem sat_n11_qasmbench_full_discharge :
    NPSearchDischarge sat_n11_qasmbench 11 ∧
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert sat_n11_qasmbench) ∧
    sat_n11_qasmbench_measurement.thresholdMet := by
  refine ⟨sat_n11_qasmbench_search_discharge, sat_n11_qasmbench_domain_cover, sat_n11_qasmbench_measurement_thresholdMet⟩

def atsp_demo_n3_grover_i2_measurement : MeasurementOutcomeWitness :=
  MeasurementOutcomeWitness.ofRationals 1 2 121 128

theorem atsp_demo_n3_grover_i2_measurement_thresholdMet :
    atsp_demo_n3_grover_i2_measurement.thresholdMet := by
  unfold MeasurementOutcomeWitness.thresholdMet atsp_demo_n3_grover_i2_measurement
  decide

/-- Polynomial search/readout discharge for `atsp_demo_n3_grover_i2`. -/
def atsp_demo_n3_grover_i2_search_discharge : NPSearchDischarge atsp_demo_n3_grover_i2 3 :=
  NPSearchDischarge.of_acceptedPolynomial atsp_demo_n3_grover_i2 3 (by decide : 1 ≤ 3) atsp_demo_n3_grover_i2_acceptedPolynomial

theorem atsp_demo_n3_grover_i2_domain_cover :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert atsp_demo_n3_grover_i2) :=
  atsp_demo_n3_grover_i2_domainCoverInP_via_frequency_bridge

/-- Full bundled discharge: poly search/readout + domain cover + measurement threshold. -/
theorem atsp_demo_n3_grover_i2_full_discharge :
    NPSearchDischarge atsp_demo_n3_grover_i2 3 ∧
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert atsp_demo_n3_grover_i2) ∧
    atsp_demo_n3_grover_i2_measurement.thresholdMet := by
  refine ⟨atsp_demo_n3_grover_i2_search_discharge, atsp_demo_n3_grover_i2_domain_cover, atsp_demo_n3_grover_i2_measurement_thresholdMet⟩

def atsp_demo_n3_via_sat_measurement : MeasurementOutcomeWitness :=
  MeasurementOutcomeWitness.ofRationals 1 20 9454 36035

theorem atsp_demo_n3_via_sat_measurement_thresholdMet :
    atsp_demo_n3_via_sat_measurement.thresholdMet := by
  unfold MeasurementOutcomeWitness.thresholdMet atsp_demo_n3_via_sat_measurement
  decide

/-- Polynomial search/readout discharge for `atsp_demo_n3_via_sat`. -/
def atsp_demo_n3_via_sat_search_discharge : NPSearchDischarge atsp_demo_n3_via_sat 6 :=
  NPSearchDischarge.of_acceptedPolynomial atsp_demo_n3_via_sat 6 (by decide : 1 ≤ 6) atsp_demo_n3_via_sat_acceptedPolynomial

theorem atsp_demo_n3_via_sat_domain_cover :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert atsp_demo_n3_via_sat) :=
  atsp_demo_n3_via_sat_domainCoverInP_via_frequency_bridge

/-- Full bundled discharge: poly search/readout + domain cover + measurement threshold. -/
theorem atsp_demo_n3_via_sat_full_discharge :
    NPSearchDischarge atsp_demo_n3_via_sat 6 ∧
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert atsp_demo_n3_via_sat) ∧
    atsp_demo_n3_via_sat_measurement.thresholdMet := by
  refine ⟨atsp_demo_n3_via_sat_search_discharge, atsp_demo_n3_via_sat_domain_cover, atsp_demo_n3_via_sat_measurement_thresholdMet⟩

/-- All benchmark instances in this batch have polynomial NP-bridge search discharge. -/
theorem np_bridge_benchmark_batch_search_discharged :
    NPSearchDischarge sat_n7_qasmbench 7 ∧
    NPSearchDischarge sat_n11_qasmbench 11 ∧
    NPSearchDischarge atsp_demo_n3_grover_i2 3 ∧
    NPSearchDischarge atsp_demo_n3_via_sat 6 := by
  refine ⟨sat_n7_qasmbench_search_discharge, sat_n11_qasmbench_search_discharge, atsp_demo_n3_grover_i2_search_discharge, atsp_demo_n3_via_sat_search_discharge⟩

end Hqiv.QuantumComputing.NPBridgeFullProof

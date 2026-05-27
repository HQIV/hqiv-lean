import Hqiv.QuantumComputing.CarrierPeaking
import Hqiv.QuantumComputing.FrequencyCertificate
import Hqiv.QuantumComputing.SparseScheduleCost

/-!
# Frequency route semantics ↔ carrier / OSH fast paths

Connects Python `partition_domain="frequency"` routes to Lean carrier and sparse gate kinds.
Diagonal and permutation routes have proved carrier fast paths in `CarrierPeaking`; local-mix
routes cite `localMixCertifiedGate` / `twoLevelUnitaryGate` as the semantic anchor.
-/

namespace Hqiv.QuantumComputing

/-- Route tag exported by Python certificates. -/
inductive FrequencyRouteDomain where
  | shell
  | frequency
  deriving DecidableEq, Repr

/-- Sparse gate kinds eligible for frequency-local O(k) routing. -/
inductive FrequencyLocalGateKind where
  | diagonal
  | permutation
  | localMix
  deriving DecidableEq, Repr

def FrequencyLocalGateKind.toSparseGateKind : FrequencyLocalGateKind → SparseGateKind
  | .diagonal => .diagonal
  | .permutation => .permutation
  | .localMix => .local_mix

/-- One certified frequency-local route step (abstract, pre-gate). -/
structure FrequencyRouteStep where
  domain : FrequencyRouteDomain
  gateKind : FrequencyLocalGateKind
  support : Nat
  chiFrequencyBand : Nat
  deriving Repr

namespace FrequencyRouteStep

/-- Step cost under the schedule model. -/
def stepCost (s : FrequencyRouteStep) : Nat :=
  frequencySparseStepCost s.support s.chiFrequencyBand

/-- Frequency-local routes use the frequency domain. -/
def isFrequencyLocal (s : FrequencyRouteStep) : Prop :=
  s.domain = FrequencyRouteDomain.frequency

end FrequencyRouteStep

/-- Diagonal frequency route: carrier π-phase fast path (no dense rebuild). -/
theorem diagonal_frequency_route_carrier (L : Nat) (flat : ℕ) (c : SuperpositionCarrier L) :
    carrierNormSq (applyPhaseCarrier c flat) = carrierNormSq c :=
  applyPhaseCarrier_preserves_carrierNormSq c flat

/-- Permutation frequency route: carrier relabeling with proved norm preservation (id case). -/
theorem permutation_frequency_route_carrier_id (L : Nat) (c : SuperpositionCarrier L)
    (hnodup : c.support.Nodup) (hw : ∀ k ∈ c.support, wrapIdx L k = k) :
    carrierNormSq (applyPermutationCarrier c id) = carrierNormSq c :=
  applyPermutationCarrier_preserves_carrierNormSq_id c hnodup hw

/-- Local-mix frequency route: semantic anchor is certified two-level unitary gate. -/
def localMixFrequencyRouteCertified {L : Nat} [DecidableEq (HarmonicIndex L)]
    (ij₀ ij₁ : HarmonicIndex L) (hij : ij₀ ≠ ij₁) (U : TwoLevelOctonionUnitary) :
    SparseCertifiedGate L :=
  localMixCertifiedGate ij₀ ij₁ hij U

theorem localMixFrequencyRoute_preserves_norm {L : Nat} [DecidableEq (HarmonicIndex L)]
    (ij₀ ij₁ : HarmonicIndex L) (hij : ij₀ ≠ ij₁) (U : TwoLevelOctonionUnitary)
    (f : DiscreteState L) :
    discreteNormSq
        ((localMixFrequencyRouteCertified (L := L) ij₀ ij₁ hij U).gate.toEquiv f) =
      discreteNormSq f :=
  (localMixFrequencyRouteCertified (L := L) ij₀ ij₁ hij U).preserves_discreteNormSq f

/-- If every route step is frequency-local with bounds from an accepted certificate, schedule cost
matches the certificate layer bound. -/
def scheduleFromRoutes (steps : List FrequencyRouteStep) : Nat :=
  steps.foldl (fun acc s => acc + s.stepCost) 0

/-- Link certificate obligations to per-step frequency route bounds. -/
def routeStepFromObligations (c : FrequencyObligations) (kind : FrequencyLocalGateKind) :
    FrequencyRouteStep :=
  { domain := FrequencyRouteDomain.frequency
  , gateKind := kind
  , support := c.maxSupport
  , chiFrequencyBand := c.maxChiFrequencyBand }

theorem routeStepFromObligations_cost (c : FrequencyObligations) (kind : FrequencyLocalGateKind) :
    (routeStepFromObligations c kind).stepCost = certificateWorkBound c := by
  rfl

theorem scheduleCost_eq_depth_mul_routeStep
    (c : FrequencyObligations) (kind : FrequencyLocalGateKind) :
    scheduleCost c.depth c.maxSupport c.maxChiFrequencyBand =
      c.depth * (routeStepFromObligations c kind).stepCost := by
  rfl

end Hqiv.QuantumComputing

import Hqiv.QuantumMechanics.FanoAssociatorMergePulse
import Hqiv.QuantumComputing.OSHoracle
import Hqiv.QuantumComputing.CarrierPeaking
import Hqiv.QuantumMechanics.MonogamyTanglesPhiConditions
import Hqiv.Geometry.OctonionicLightCone

/-!
# FAN near-term QC ↔ OSHoracle carrier bridge

Maps the Tier~II / near-term FAN merge protocol (`FanoAssociatorMergePulse`) onto the
**sparse octonion carrier** bookkeeping in `OSHoracle` / `CarrierPeaking`.

**HQIV-native simulator (OSHoracle):**

1. Preload the product register with shell-indexed carrier noise (`FanCarrierNoise`).
2. Hold the merge core as a single-track `SuperpositionCarrier` with octonion amplitude.
3. Apply two APPEND/PREPEND primitives per shot (`fanApplyMergeOnCarrier` mirrors
   `fanApplyMergeOp`; Python driver `fan_qc_osh_sim.py`).
4. Read Born weights on the octonion basis (`fanOshBornProb`).

The same gate schedule exports to Qiskit on 3 logical qubits; OSH keeps the full
octonion carrier and optional φ-ladder preload. Tier~I table tags stay quarantined.
-/

namespace Hqiv.QM.FanoMerge

open Hqiv.QuantumComputing
open Hqiv.Algebra
open Hqiv.Geometry

def fanOshCutoffL : ℕ := 2

theorem fanOshBasisCard : sparseBasisCard fanOshCutoffL = fanOctonionBasisCount + 1 := by
  native_decide

def fanFlatIndexOfBasis (a : Fin 8) : ℕ := a.val

theorem fanFlatIndexOfBasis_lt (a : Fin 8) :
    fanFlatIndexOfBasis a < sparseBasisCard fanOshCutoffL := by
  unfold fanFlatIndexOfBasis sparseBasisCard fanOshCutoffL
  fin_cases a <;> decide

def fanSiteCarrier (shell : ℕ) : OctonionVec :=
  octonionBasis ⟨shell % 8, Nat.mod_lt _ (by decide : 0 < 8)⟩

structure FanCarrierNoise where
  shells : List ℕ
  weight : ℝ

noncomputable def fanPreloadCarrierNoise (ψ : OctonionVec) (noise : FanCarrierNoise) : OctonionVec :=
  noise.shells.foldl (fun acc s => acc + noise.weight • fanSiteCarrier s) ψ

noncomputable def fanLockinCarrierNoise : FanCarrierNoise where
  shells := [referenceM, referenceM + 1, referenceM + 2]
  weight := etaModePhi referenceM

theorem fanLockinCarrierNoise_weight :
    fanLockinCarrierNoise.weight = 1 / 30 := fanMerge_etaPhi_lockin

def fanQcCarrierSupport : List ℕ := [0]

def fanQcCarrierAmp (arm : FanQcArm) : ℕ → OctonionVec
  | 0 => fanQcInitState arm
  | _ => 0

def fanQcSuperpositionCarrier (arm : FanQcArm) : SuperpositionCarrier fanOshCutoffL where
  support := fanQcCarrierSupport
  amp := fanQcCarrierAmp arm

def fanQcSparseRegister (arm : FanQcArm) : SparseRegister fanOshCutoffL :=
  sparseOfCarrier (fanQcSuperpositionCarrier arm)

theorem fanQcSparseRegister_length (arm : FanQcArm) :
    (fanQcSparseRegister arm).length = 1 := by
  cases arm <;> simp [fanQcSparseRegister, sparseOfCarrier, fanQcSuperpositionCarrier,
    fanQcCarrierSupport, fanQcCarrierAmp, List.map]

/-- One OSH merge tick on the octonion amplitude at flat index `0`. -/
def fanApplyMergeOnCarrier (op : FanMergeOp) (c : SuperpositionCarrier fanOshCutoffL) :
    SuperpositionCarrier fanOshCutoffL :=
  { support := c.support
    , amp := fun i => if i = 0 then fanApplyMergeOp op (c.amp 0) else c.amp i }

theorem fanApplyMergeOnCarrier_amp0 (op : FanMergeOp) (c : SuperpositionCarrier fanOshCutoffL) :
    (fanApplyMergeOnCarrier op c).amp 0 = fanApplyMergeOp op (c.amp 0) := by
  simp [fanApplyMergeOnCarrier]

def fanRunMergeOnCarrier (ops : List FanMergeOp) (c : SuperpositionCarrier fanOshCutoffL) :
    SuperpositionCarrier fanOshCutoffL :=
  ops.foldl (fun acc op => fanApplyMergeOnCarrier op acc) c

/-- Semantic readout after OSH carrier merge (noise-free path = `fanQcFinalState`). -/
def fanOshFinalState (arm : FanQcArm) : OctonionVec :=
  fanQcFinalState arm

theorem fanOshFinalState_eq_fanQcFinal (arm : FanQcArm) :
    fanOshFinalState arm = fanQcFinalState arm := rfl

noncomputable def fanOshNoisyFinalState (arm : FanQcArm) (noise : FanCarrierNoise) : OctonionVec :=
  fanRunMergeOps (fanQcMergeOps arm) (fanPreloadCarrierNoise (fanQcInitState arm) noise)

theorem fanOshNoisyFinalState_zero_noise (arm : FanQcArm) :
    fanOshNoisyFinalState arm { shells := [], weight := 0 } = fanQcFinalState arm := by
  unfold fanOshNoisyFinalState fanPreloadCarrierNoise fanQcFinalState
  simp [fanRunMergeOps]

noncomputable def fanOshBornProb (arm : FanQcArm) (a : Fin 8) : ℝ :=
  fanOctonionBornProb (fanOshFinalState arm) a

theorem fanOshBornProb_eq_fanQc (arm : FanQcArm) (a : Fin 8) :
    fanOshBornProb arm a = fanOctonionBornProb (fanQcFinalState arm) a := by
  rw [fanOshBornProb, fanOshFinalState_eq_fanQcFinal]

theorem fanOshLeft_peak3 : fanOshBornProb .leftTopology 3 = 1 := by
  rw [fanOshBornProb_eq_fanQc, fanQcLeft_born_peak3]

theorem fanOshRight_peak4 : fanOshBornProb .rightTopology 4 = 1 := by
  rw [fanOshBornProb_eq_fanQc, fanQcRight_born_peak4]

theorem fanOshQcDeltaP_paren_index4_eq_one :
    |fanOshBornProb .leftTopology 4 - fanOshBornProb .rightTopology 4| = 1 := by
  have h := fanQcDeltaP_paren_index4_eq_one
  unfold fanQcDeltaP_paren_index at h
  simpa [fanOshBornProb_eq_fanQc] using h

end Hqiv.QM.FanoMerge

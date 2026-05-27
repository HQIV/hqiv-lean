import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Dedup
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Dedup
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Hqiv.QuantumComputing.DigitalGates
import Hqiv.QuantumComputing.OSHoracle

namespace Hqiv.QuantumComputing

open Hqiv.Algebra

instance carrierPeakingDecidableEqHarmonicIndex (L : ℕ) : DecidableEq (HarmonicIndex L) := by
  unfold HarmonicIndex
  infer_instance

/-!
# Superposition carrier + logic-mirror peaking

Direct updates on sparse superposition bookkeeping without materializing a full
`DiscreteState L` for certified gate kinds (π-phase, index permutation).

The dense path `applyGateSparse` remains the reference oracle; carrier operations
are proved compatible on explicit support and for norm preservation under π-phase.
-/

/-- Octonion carrier (same as sparse layer). -/
abbrev CarrierOctonion : Type := OctonionVec

private theorem carrier_octonionInner_neg_neg (x : CarrierOctonion) :
    octonionInner (-x) (-x) = octonionInner x x := by
  simp [octonionInner]
  refine Finset.sum_congr rfl ?_
  intro i _
  exact neg_mul_neg (x i) (x i)

private lemma wrapIdx_of_lt (L i : ℕ) (hi : i < sparseBasisCard L) : wrapIdx L i = i := by
  simp [wrapIdx, hi, Nat.mod_eq_of_lt]

/-- Constructive superposition: explicit support list + amplitude lookup. -/
structure SuperpositionCarrier (L : ℕ) where
  support : List ℕ
  amp : ℕ → CarrierOctonion

/-- Fold sparse list into carrier (merge colliding wrapped indices by addition). -/
noncomputable def carrierOfSparse {L : ℕ} (r : SparseRegister L) : SuperpositionCarrier L :=
  { support := (r.map fun x => wrapIdx L x.1).eraseDups
    , amp := fun i =>
        r.foldl (fun acc x => if wrapIdx L x.1 = i then acc + x.2 else acc) 0 }

/-- Carrier back to sparse register (one pair per support entry). -/
def sparseOfCarrier {L : ℕ} (c : SuperpositionCarrier L) : SparseRegister L :=
  c.support.map fun i => (i, c.amp i)

/-- Dense semantic bridge: sparse list → `denseOfSparse`. -/
noncomputable def carrierDense {L : ℕ} (c : SuperpositionCarrier L) : DiscreteState L :=
  denseOfSparse (sparseOfCarrier c)

/-- Carrier informational norm (octonion inner sum on support). -/
noncomputable def carrierNormSq {L : ℕ} (c : SuperpositionCarrier L) : ℝ :=
  (c.support.map fun i => octonionInner (c.amp i) (c.amp i)).sum

/-- Local canary mass at a wrapped flat carrier index. -/
def carrierKetMass {L : ℕ} (c : SuperpositionCarrier L) (flat : ℕ) : ℝ :=
  let i := wrapIdx L flat
  octonionInner (c.amp i) (c.amp i)

/--
A canary probe checks one carrier ket against an allowed mass window.  This is
the formal version of a cheap go/no-go readout: evolve the carrier, inspect a
few selected flat slots, and only promote to a fuller simulation when a probe
fails.
-/
structure CanaryProbe where
  flat : ℕ
  lower : ℝ
  upper : ℝ

namespace CanaryProbe

/-- Evaluate this probe's local carrier mass. -/
def mass {L : ℕ} (p : CanaryProbe) (c : SuperpositionCarrier L) : ℝ :=
  carrierKetMass c p.flat

/-- The canary passes when the selected local mass lies in its certified window. -/
def passes {L : ℕ} (p : CanaryProbe) (c : SuperpositionCarrier L) : Prop :=
  p.lower ≤ p.mass c ∧ p.mass c ≤ p.upper

end CanaryProbe

/-- A finite canary suite passes when every selected carrier ket passes. -/
def carrierCanaryPasses {L : ℕ} (probes : List CanaryProbe) (c : SuperpositionCarrier L) : Prop :=
  ∀ p ∈ probes, p.passes c

/-- Componentwise negation (π phase on one octonion slot). -/
def negOctonion (v : CarrierOctonion) : CarrierOctonion :=
  -v

/-- Direct π-phase on carrier at wrapped flat index `flat`. -/
def applyPhaseCarrier {L : ℕ} (c : SuperpositionCarrier L) (flat : ℕ) : SuperpositionCarrier L :=
  let i := wrapIdx L flat
  { support := c.support
    , amp := fun j => if j = i then negOctonion (c.amp j) else c.amp j }

/-- Direct index permutation on carrier support. -/
def applyPermutationCarrier {L : ℕ} (c : SuperpositionCarrier L) (perm : ℕ → ℕ) :
    SuperpositionCarrier L :=
  let mapIdx k := wrapIdx L (perm k)
  { support := (c.support.map mapIdx).dedup
    , amp := fun j =>
        (c.support.filter fun k => mapIdx k = j).foldl
          (fun acc k => acc + c.amp k) 0 }

/-- Bit `q` of ket label `i` (computational basis indexing). -/
def bitAt (q i : ℕ) : Bool :=
  i.testBit q

/-- Mirror map flips target qubit bit at pivot `i`. -/
def mirrorFlipsBit (mirror : ℕ → ℕ) (targetQubit i : ℕ) : Bool :=
  bitAt targetQubit (mirror i) != bitAt targetQubit i

/-- Witness: logic mirror exposes a target-qubit flip at a pivot index. -/
structure LogicMirrorPeak where
  mirror : ℕ → ℕ
  targetQubit : ℕ
  pivot : ℕ
  flipsTarget : Bool

/-- Build a peak witness with the mirror flip bit checked. -/
def logicMirrorPeak (mirror : ℕ → ℕ) (targetQubit pivot : ℕ) : LogicMirrorPeak :=
  { mirror := mirror, targetQubit := targetQubit, pivot := pivot
    , flipsTarget := mirrorFlipsBit mirror targetQubit pivot }

/-- Peaking readout (decidable): pivot + mirror on support and flip bit. -/
def peakSupportPair {L : ℕ} (c : SuperpositionCarrier L) (peak : LogicMirrorPeak) : Bool :=
  let i := wrapIdx L peak.pivot
  let j := wrapIdx L (peak.mirror peak.pivot)
  (i ∈ c.support) && (j ∈ c.support) && peak.flipsTarget

/-- When the mirror flips the target bit, pivot and mirror labels disagree on that bit. -/
theorem peak_qubit_flip_obvious (mirror : ℕ → ℕ) (targetQubit pivot : ℕ)
    (h : mirrorFlipsBit mirror targetQubit pivot = true) :
    bitAt targetQubit (mirror pivot) != bitAt targetQubit pivot := by
  simpa [mirrorFlipsBit, bitAt] using h

private lemma wrapIdx_zero (L : ℕ) : wrapIdx L 0 = 0 := by
  simp [wrapIdx, sparseBasisCard]

private lemma carrierOfSparse_singleton_support (L : ℕ) (amp : CarrierOctonion) :
    (carrierOfSparse (L := L) [(0, amp)]).support = [0] := by
  simp [carrierOfSparse, wrapIdx_zero, List.map]
  grind

private lemma carrierOfSparse_singleton_amp (L : ℕ) (amp : CarrierOctonion) (i : ℕ) :
    (carrierOfSparse (L := L) [(0, amp)]).amp i = if i = 0 then amp else 0 := by
  simp [carrierOfSparse, wrapIdx_zero, List.foldl, eq_comm]

/-- π-phase carrier update preserves carrier norm on support. -/
theorem applyPhaseCarrier_preserves_carrierNormSq {L : ℕ} (c : SuperpositionCarrier L) (flat : ℕ) :
    carrierNormSq (applyPhaseCarrier c flat) = carrierNormSq c := by
  classical
  dsimp [carrierNormSq, applyPhaseCarrier, negOctonion]
  induction c.support with
  | nil => simp
  | cons k ks ih =>
    simp only [List.map_cons, List.sum_cons]
    by_cases h : k = wrapIdx L flat
    · simp only [if_pos h, carrier_octonionInner_neg_neg, ih]
    · simp [if_neg h, ih]

/-- A certified π-phase carrier step does not change any canary ket mass. -/
theorem applyPhaseCarrier_preserves_carrierKetMass {L : ℕ}
    (c : SuperpositionCarrier L) (phaseFlat probeFlat : ℕ) :
    carrierKetMass (applyPhaseCarrier c phaseFlat) probeFlat = carrierKetMass c probeFlat := by
  dsimp [carrierKetMass, applyPhaseCarrier, negOctonion]
  by_cases h : wrapIdx L probeFlat = wrapIdx L phaseFlat
  · simp [h, carrier_octonionInner_neg_neg]
  · simp [h]

/-- A certified π-phase carrier step preserves a single canary pass/fail decision. -/
theorem applyPhaseCarrier_preserves_canaryPass {L : ℕ}
    (c : SuperpositionCarrier L) (phaseFlat : ℕ) (probe : CanaryProbe) :
    probe.passes (applyPhaseCarrier c phaseFlat) ↔ probe.passes c := by
  simp [CanaryProbe.passes, CanaryProbe.mass, applyPhaseCarrier_preserves_carrierKetMass]

/-- A certified π-phase carrier step preserves an entire finite canary suite. -/
theorem applyPhaseCarrier_preserves_carrierCanaryPasses {L : ℕ}
    (c : SuperpositionCarrier L) (phaseFlat : ℕ) (probes : List CanaryProbe) :
    carrierCanaryPasses probes (applyPhaseCarrier c phaseFlat) ↔ carrierCanaryPasses probes c := by
  constructor
  · intro h probe hprobe
    exact (applyPhaseCarrier_preserves_canaryPass c phaseFlat probe).mp (h probe hprobe)
  · intro h probe hprobe
    exact (applyPhaseCarrier_preserves_canaryPass c phaseFlat probe).mpr (h probe hprobe)

/-- Flat index surrogate aligned with Python `flat_index` (ℓ² + m). -/
def harmonicFlatIndex {L : ℕ} (ij : HarmonicIndex L) : ℕ :=
  ij.1.val * ij.1.val + ij.2.val

/-- Singleton sparse register → carrier preserves sparse norm squared. -/
theorem sparseNormSq_singleton_carrier_roundtrip (L : ℕ) (amp : CarrierOctonion) :
    sparseNormSq (L := L) (sparseOfCarrier (L := L) (carrierOfSparse (L := L) [(0, amp)])) =
      sparseNormSq (L := L) [(0, amp)] := by
  simp [sparseNormSq, sparseOfCarrier, carrierOfSparse_singleton_support,
    carrierOfSparse_singleton_amp, List.map, octonionInner]

private lemma denseOfSparse_singleton {L : ℕ} (amp : CarrierOctonion) (ij : HarmonicIndex L) :
    denseOfSparse (L := L) [(0, amp)] ij =
      if decodeIdx (L := L) 0 = ij then amp else 0 := by
  simp [denseOfSparse, List.foldl, decodeIdx]

private lemma denseOfSparse_singleton_neg {L : ℕ} (amp : CarrierOctonion) (ij : HarmonicIndex L)
    (h : decodeIdx (L := L) 0 = ij) :
    denseOfSparse (L := L) [(0, negOctonion amp)] ij = -denseOfSparse (L := L) [(0, amp)] ij := by
  subst h
  simp [denseOfSparse_singleton, negOctonion]

/-- Dense bridge: carrier π-phase at flat `0` matches `phaseGate` on `decodeIdx 0`. -/
theorem applyPhaseCarrier_matches_phaseGate_singleton (L : ℕ) (amp : CarrierOctonion) :
    carrierDense (applyPhaseCarrier (carrierOfSparse [(0, amp)]) 0) =
      (phaseGate (decodeIdx (L := L) 0)).toEquiv (carrierDense (carrierOfSparse [(0, amp)])) := by
  funext ij
  simp only [carrierDense, phaseGate, Equiv.coe_fn_mk, applyPhaseCarrier,
    carrierOfSparse_singleton_amp, carrierOfSparse_singleton_support, sparseOfCarrier, wrapIdx_zero]
  by_cases h : decodeIdx (L := L) 0 = ij
  · subst h
    simp [denseOfSparse_singleton, negOctonion]
  · simp [denseOfSparse_singleton, h]

/-- Certified sparse phase step without dense rebuild. -/
noncomputable def applyPhaseCarrierSparseStep {L : ℕ} (flat : ℕ) (r : SparseRegister L) :
    SparseRegister L :=
  sparseOfCarrier (applyPhaseCarrier (carrierOfSparse r) flat)

/-- Logic-mirror peaking shortcut: flipped-index witness when support pair is present. -/
def peakQubitFlipWitness {L : ℕ} (c : SuperpositionCarrier L) (peak : LogicMirrorPeak) :
    Option (ℕ × ℕ) :=
  if peakSupportPair c peak = true then
    some (wrapIdx L peak.pivot, wrapIdx L (peak.mirror peak.pivot))
  else
    none

/-- Peaking witness is nonempty exactly when `peakSupportPair` holds. -/
theorem peakQubitFlipWitness_some_iff {L : ℕ} (c : SuperpositionCarrier L) (peak : LogicMirrorPeak) :
    (peakQubitFlipWitness c peak).isSome ↔ (peakSupportPair c peak = true) := by
  unfold peakQubitFlipWitness peakSupportPair
  by_cases hb : peakSupportPair c peak = true <;> simp

/-- Align with OSH flip detection on a single phase step (bookkeeping). -/
theorem detectFlipped_after_phase_carrier {L : ℕ} (flat : ℕ) (r : SparseRegister L) :
    let after := applyPhaseCarrierSparseStep flat r
    (detectFlippedKets r after).length ≤ r.length + after.length := by
  intro after
  exact detectFlippedKets_length_le_sum r after

private lemma carrierNormSq_eq_finset {L : ℕ} (c : SuperpositionCarrier L) (hnodup : c.support.Nodup) :
    carrierNormSq c = ∑ i ∈ c.support.toFinset, octonionInner (c.amp i) (c.amp i) := by
  simp only [carrierNormSq]
  rw [← List.sum_toFinset (fun i => octonionInner (c.amp i) (c.amp i)) hnodup]

private lemma support_filter_perm_singleton {L : ℕ} (support : List ℕ) (perm : ℕ → ℕ) (j k : ℕ)
    (hnodup : support.Nodup) (hk : k ∈ support) (hkj : wrapIdx L (perm k) = j)
    (hinj : ∀ k₁ k₂, k₁ ∈ support → k₂ ∈ support → wrapIdx L (perm k₁) = wrapIdx L (perm k₂) → k₁ = k₂) :
    (support.filter fun k' => decide (wrapIdx L (perm k') = j)) = [k] := by
  induction support generalizing k j with
  | nil => simp at hk
  | cons hd tl ih =>
    have hd_not : hd ∉ tl := (List.nodup_cons.mp hnodup).1
    have hnodup_tl : tl.Nodup := (List.nodup_cons.mp hnodup).2
    rcases List.mem_cons.mp hk with hr | hk_tl
    · rcases hr with rfl
      have hk_not : k ∉ tl := hd_not
      have htail : tl.filter (fun k' => decide (wrapIdx L (perm k') = j)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy heq
        rw [decide_eq_true_iff] at heq
        have hy' : y ∈ k :: tl := List.mem_cons_of_mem k hy
        have heq' : wrapIdx L (perm y) = wrapIdx L (perm k) := heq.trans hkj.symm
        have hy_eq : y = k := hinj y k hy' (by simp) heq'
        subst hy_eq
        exact absurd hy hk_not
      rw [List.filter_cons, decide_eq_true_iff.2 hkj, htail]
      rfl
    · have hdk : hd ≠ k := fun h => by subst h; exact hd_not hk_tl
      have hk_tl' : k ∈ hd :: tl := List.mem_cons_of_mem hd hk_tl
      have hd_mem : hd ∈ hd :: tl := by simp
      have hpx : wrapIdx L (perm hd) ≠ j := fun heq' =>
        hdk (hinj hd k hd_mem hk_tl' (heq'.trans hkj.symm))
      have hinj_tl : ∀ k₁ k₂, k₁ ∈ tl → k₂ ∈ tl → wrapIdx L (perm k₁) = wrapIdx L (perm k₂) → k₁ = k₂ :=
        fun k₁ k₂ hk₁ hk₂ heq =>
          hinj k₁ k₂ (List.mem_cons_of_mem hd hk₁) (List.mem_cons_of_mem hd hk₂) heq
      simpa [List.filter_cons, decide_eq_true_iff, hpx] using ih j k hnodup_tl hk_tl hkj hinj_tl

private lemma applyPermutationCarrier_filter_singleton {L : ℕ} (c : SuperpositionCarrier L)
    (perm : ℕ → ℕ) (j k : ℕ) (hnodup : c.support.Nodup) (hk : k ∈ c.support) (hkj : wrapIdx L (perm k) = j)
    (hinj : ∀ k₁ k₂, k₁ ∈ c.support → k₂ ∈ c.support → wrapIdx L (perm k₁) = wrapIdx L (perm k₂) →
      k₁ = k₂) :
    (c.support.filter fun k' => decide (wrapIdx L (perm k') = j)) = [k] :=
  support_filter_perm_singleton c.support perm j k hnodup hk hkj hinj

private lemma applyPermutationCarrier_amp_preimage {L : ℕ} (c : SuperpositionCarrier L)
    (perm : ℕ → ℕ) (j k : ℕ) (hnodup : c.support.Nodup) (hk : k ∈ c.support) (hkj : wrapIdx L (perm k) = j)
    (hinj : ∀ k₁ k₂, k₁ ∈ c.support → k₂ ∈ c.support → wrapIdx L (perm k₁) = wrapIdx L (perm k₂) →
      k₁ = k₂) :
    (applyPermutationCarrier c perm).amp j = c.amp k := by
  dsimp [applyPermutationCarrier]
  rw [applyPermutationCarrier_filter_singleton (L := L) (c := c) (perm := perm) (j := j) (k := k)
    hnodup hk hkj hinj]
  simp only [List.foldl_cons, List.foldl_nil, zero_add]

/-- Permutation carrier preserves norm when `mapIdx` bijects canonical support indices. -/
theorem applyPermutationCarrier_preserves_carrierNormSq {L : ℕ} (c : SuperpositionCarrier L)
    (perm : ℕ → ℕ) (hnodup : c.support.Nodup)
    (hinj : ∀ k₁ k₂, k₁ ∈ c.support → k₂ ∈ c.support → wrapIdx L (perm k₁) = wrapIdx L (perm k₂) → k₁ = k₂)
    (_hmapto : ∀ k ∈ c.support, wrapIdx L (perm k) ∈ c.support)
    (_hsurj : ∀ j ∈ c.support, ∃ k ∈ c.support, wrapIdx L (perm k) = j) :
    carrierNormSq (applyPermutationCarrier c perm) = carrierNormSq c := by
  let mapIdx k := wrapIdx L (perm k)
  have hinjOn : ∀ x ∈ c.support, ∀ y ∈ c.support, mapIdx x = mapIdx y → x = y := by
    intro x hx y hy heq
    exact hinj x y hx hy heq
  have hnodup_map : (c.support.map mapIdx).Nodup :=
    (List.nodup_map_iff_inj_on hnodup).mpr hinjOn
  have hsupport :
      (applyPermutationCarrier c perm).support = c.support.map mapIdx := by
    unfold applyPermutationCarrier
    exact List.Nodup.dedup hnodup_map
  have hnodup' : (applyPermutationCarrier c perm).support.Nodup := by
    simpa [hsupport] using hnodup_map
  rw [carrierNormSq_eq_finset (applyPermutationCarrier c perm) hnodup', carrierNormSq_eq_finset c hnodup]
  apply Eq.symm
  refine Finset.sum_bij (fun k _ => mapIdx k) ?_ ?_ ?_ ?_
  · intro k hk
    have hk' : k ∈ c.support := List.mem_toFinset.mp hk
    simpa [hsupport, List.mem_toFinset] using List.mem_map.mpr ⟨k, hk', rfl⟩
  · intro k₁ hk₁ k₂ hk₂ heq
    exact hinj k₁ k₂ (List.mem_toFinset.mp hk₁) (List.mem_toFinset.mp hk₂) heq
  · intro b hb
    have hb' : b ∈ (applyPermutationCarrier c perm).support := List.mem_toFinset.mp hb
    rw [hsupport] at hb'
    rcases List.mem_map.mp hb' with ⟨k, hk, rfl⟩
    exact ⟨k, List.mem_toFinset.mpr hk, rfl⟩
  · intro k hk
    have hk' : k ∈ c.support := List.mem_toFinset.mp hk
    dsimp only [applyPermutationCarrier]
    rw [applyPermutationCarrier_filter_singleton (L := L) (c := c) (perm := perm)
        (j := mapIdx k) (k := k) hnodup hk' (by rfl) hinj]
    simp only [List.foldl_cons, List.foldl_nil, zero_add]

/-- Identity permutation on wrapped support indices preserves norm. -/
theorem applyPermutationCarrier_preserves_carrierNormSq_id {L : ℕ} (c : SuperpositionCarrier L)
    (hnodup : c.support.Nodup) (hw : ∀ k ∈ c.support, wrapIdx L k = k) :
    carrierNormSq (applyPermutationCarrier c id) = carrierNormSq c := by
  have hinj_id : ∀ k₁ k₂, k₁ ∈ c.support → k₂ ∈ c.support → wrapIdx L k₁ = wrapIdx L k₂ → k₁ = k₂ :=
    fun k₁ k₂ hk₁ hk₂ heq => (hw k₁ hk₁).symm.trans heq |>.trans (hw k₂ hk₂)
  apply applyPermutationCarrier_preserves_carrierNormSq c id hnodup hinj_id
  · intro k hk
    simpa [hw k hk] using hk
  · intro j hj
    exact ⟨j, hj, hw j hj⟩

/-- Certified sparse permutation step without dense rebuild. -/
noncomputable def applyPermutationCarrierSparseStep {L : ℕ} (c : SuperpositionCarrier L)
    (perm : ℕ → ℕ) : SuperpositionCarrier L :=
  applyPermutationCarrier c perm

noncomputable def applyPermutationCarrierSparseStepReg {L : ℕ} (perm : ℕ → ℕ) (r : SparseRegister L) :
    SparseRegister L :=
  sparseOfCarrier (applyPermutationCarrierSparseStep (carrierOfSparse r) perm)

end Hqiv.QuantumComputing

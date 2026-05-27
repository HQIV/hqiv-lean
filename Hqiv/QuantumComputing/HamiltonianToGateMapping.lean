/-
# Hamiltonian → sequential gate schedules (patch QM on the observable patch)

This is **not** continuum interacting QFT with simultaneous spatially-extended couplings,
nor a formalization of many-body Hamiltonians acting on the whole universe at once.
HQIV evolution on the observable patch is modeled as **one causal step at a time** on
the discrete light-cone bookkeeping: at each tick only channels compatible with the
current **ηφ-weighted CKW** budget (`Hqiv.QM.MonogamyTangles`) may carry coherence, and
the **lapse / skew time-phase** story (`HQVM_lapse`, Axiom 4 skew mediator `Ψ(t) ≈ s(t) exp(θ(t)Δ)`)
orients each mediated interaction before the next sequential gate push.

**Dense reference:** `SequentialHQIVEvolution.toEquiv` / `runSequentialEvolution` compose `HQIVGate`s
via `digitalEvolution` (`DiscreteSchrodinger`); this is where **norm / IP preservation** is proved.

**Sparse driver:** `runSparseSequentialOSH` chains `OSHoracle.applyGateSparse` on a
`SparseRegister`. Each OSH step causal-expands support before the dense gate slice; proving
bit-identical agreement with `toEquiv` for arbitrary sparse data is **future work**
(`LatticeNextPrimeQCAlgorithm`, `SparseSimulationDensityCrossover`).

---

## How to translate a Hamiltonian (working physicists)

1. Pick cutoff `L` and `HarmonicIndex L` slots; amplitudes live in `DiscreteState L`.
2. Expand the Hamiltonian into a **sequence** of local ticks (`HQIVEvolutionStep`), not simultaneous
   whole-register couplings unless monogamy certifies that budget.
3. Supply `QM.correctedCkwMonogamyPhi` on each tick (upgrade flat CKW with
   `QM.corrected_monogamy_of_ckw_phi` if needed).
4. Record skew/lapse in `SkewIncrement`; use `phaseGate` / other `HQIVGate`s for the digital burst.
5. **Simulate:** `runSequentialEvolution` for the proved dense trajectory; `runSparseSequentialOSH`
   for the OSHoracle list algebra on sparse registers.
6. **Scale checks:** `oshSparseSequentialFold_length` / `nBodySequentialSparseLength_bound` track
   worst-case `2^{#gates}` support growth without pruning.

**Out of scope:** continuum limits, unbounded simultaneous many-body updates, and full `(L+1)^2`
Hilbert simulation claims. Continuous single-qubit rotations are only in scope through the certified
two-level realification witness in `DigitalGates.twoLevelUnitaryGate`; Hamiltonian-wide continuum
flows still require separate modeling.
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Hqiv.QuantumComputing.DiscreteSchrodinger
import Hqiv.QuantumComputing.DiscreteQuantumState
import Hqiv.QuantumComputing.OSHoracle
import Hqiv.QuantumMechanics.MonogamyTangles
import Hqiv.Algebra.PhaseLiftDelta
import Hqiv.Geometry.HQVMetric
import Hqiv.Geometry.AuxiliaryFieldSmeared

namespace Hqiv.QuantumComputing

open Hqiv
open Hqiv.Algebra

variable {L : ℕ}

/-! ## Skew / lapse mediation (Axiom 4 packaging)

We record **increments** `(s, θ)` alongside each sequential interaction. The matrix
generator `Δ` is `phaseLiftDeltaMatrix`; coupling `θ * Δ` in a full Lie lift is not
materialized in the digital `HQIVGate` API—only scheduled here for alignment with
`HQVM_lapse Φ φ t` and smeared auxiliary-field windows (`smearedAuxField`).
-/

/-- Increment of the skew time-phase mediator `Ψ(t) = s(t) * exp(θ(t) * Δ)` between two
sequential digital steps (`s` is the real sign factor, `θ` the rotation increment). -/
structure SkewIncrement where
  /-- Sign factor `s(t)` at the step (typically `±1` in discrete models). -/
  s : ℝ
  /-- Phase increment `θ(t)` coupled to `phaseLiftDeltaMatrix` in the continuum lift. -/
  theta : ℝ
  /-- Lapse `N = HQVM_lapse Φ φ t` at the causal tick mediating proper separation. -/
  lapse : ℝ

/-- Trivial skew increment: unit sign, zero phase, Minkowski lapse `N = 1`. -/
def SkewIncrement.minkowski : SkewIncrement where
  s := 1
  theta := 0
  lapse := HQVM_lapse 0 0 0

/-- Skew record with `θ = φ_rat(ℓ)` (cast to ℝ; equals `phi_of_shell ℓ` by `phiRat_coe_eq_phi_of_shell`)
and lapse `N = HQVM_lapse Φ φ t` at the tick. Used as a **frequency-weighted** mediator in the
truncated HO schedule (`hoFrequencyBeatingSequential`). -/
noncomputable def SkewIncrement.hoFrequencySkew (ℓ : ℕ) (Φ φ t : ℝ) : SkewIncrement where
  s := 1
  theta := (phiRat ℓ : ℝ)
  lapse := HQVM_lapse Φ φ t

/-! ## Monogamy-tagged interaction metadata

Each step carries an **ηφ–CKW certificate** so the schedule never exceeds the
mode-corrected monogamy budget at the declared shell.
-/

/-- Metadata for one **sequentially active** interaction channel on the digital ladder.

`shell` indexes the HQIV shell used in `correctedCkwMonogamyPhi` bookkeeping; `desc` is
documentation-only (harmonic slot, Pauli axis proxy, etc.). -/
structure MonogamyAllowedInteraction (L : ℕ) [DecidableEq (HarmonicIndex L)] where
  shell : ℕ
  /-- Harmonic slot touched in this step (single-slot = patch-local). -/
  slot : Option (HarmonicIndex L)
  τAB : ℝ
  τAC : ℝ
  τA_BC : ℝ
  hPhi : QM.correctedCkwMonogamyPhi shell τAB τAC τA_BC
  /-- Human-readable tag for Hamiltonian source (HO / Zeeman / Rabi / potential …). -/
  desc : String

/-- Predicate: every step in the evolution carries a φ–CKW certificate. -/
def EvolutionRespectsMonogamyPhi [DecidableEq (HarmonicIndex L)]
    (steps : List (MonogamyAllowedInteraction L × List (HQIVGate L) × SkewIncrement)) : Prop :=
  ∀ p ∈ steps, QM.correctedCkwMonogamyPhi p.1.shell p.1.τAB p.1.τAC p.1.τA_BC

/-! ## Sequential HQIV evolution container -/

abbrev GateSequence (L : ℕ) [DecidableEq (HarmonicIndex L)] :=
  List (HQIVGate L)

/-- One causal tick: monogamy metadata, gate burst, skew/lapse increment. -/
abbrev HQIVEvolutionStep (L : ℕ) [DecidableEq (HarmonicIndex L)] :=
  MonogamyAllowedInteraction L × GateSequence L × SkewIncrement

/-- Full **sequential** schedule: list of ticks, each tick patch-local on the digital cone.

**Not** a tensor product of simultaneous Hamiltonians over the whole universe. -/
structure SequentialHQIVEvolution (L : ℕ) [DecidableEq (HarmonicIndex L)] where
  /-- Causal-ordered steps (head = earliest tick along the chosen lapse gauge). -/
  steps : List (HQIVEvolutionStep L)

/-! ## CKW certificates (examples share the zero tangle budget). -/

theorem correctedCkwMonogamyPhi_trivial (m : ℕ) : QM.correctedCkwMonogamyPhi m 0 0 1 := by
  unfold QM.correctedCkwMonogamyPhi QM.correctedPairTanglePhi
  have hη : 0 ≤ QM.etaModePhi m := QM.etaModePhi_nonneg m
  nlinarith

/-- Flat CKW with pairwise budget `1/4 + 1/4 ≤ 1` (used for a richer two-body step witness). -/
theorem ckw_quarter_quarter_one : QM.ckwMonogamy (1 / 4 : ℝ) (1 / 4 : ℝ) 1 := by
  unfold QM.ckwMonogamy
  norm_num

theorem correctedCkwMonogamyPhi_quarter_pair (m : ℕ) :
    QM.correctedCkwMonogamyPhi m (1 / 4 : ℝ) (1 / 4 : ℝ) 1 :=
  QM.corrected_monogamy_of_ckw_phi m ckw_quarter_quarter_one

/-! ## Gate flattening and correctness (partial, fully proved where stated) -/

/-- Flatten stepwise gate bursts in causal order for `digitalEvolution` / OSHoracle. -/
def SequentialHQIVEvolution.flattenGates [DecidableEq (HarmonicIndex L)]
    (E : SequentialHQIVEvolution L) : List (HQIVGate L) :=
  (E.steps.map fun p => p.2.1).flatten

/-- Combined equivalence from the flattened schedule. -/
noncomputable def SequentialHQIVEvolution.toEquiv [DecidableEq (HarmonicIndex L)]
    (E : SequentialHQIVEvolution L) : DiscreteState L ≃ DiscreteState L :=
  digitalEvolution (SequentialHQIVEvolution.flattenGates E)

/-- **Digital projection** `Π` used in v1: the identity on `DiscreteState L`.

Future work may quotient octonion-fiber redundancies or map to a continuum sector; for
the sparse pipeline `Π = id` is the correct book-keeping starting point. -/
def discreteProjectionPi {L : ℕ} (f : DiscreteState L) : DiscreteState L :=
  f

@[simp] theorem discreteProjectionPi_id {L : ℕ} (f : DiscreteState L) :
    discreteProjectionPi f = f :=
  rfl

theorem SequentialHQIVEvolution_preserves_discreteIp [DecidableEq (HarmonicIndex L)]
    (E : SequentialHQIVEvolution L) (f g : DiscreteState L) :
    discreteIp (E.toEquiv f) (E.toEquiv g) = discreteIp f g := by
  unfold SequentialHQIVEvolution.toEquiv
  exact digitalEvolution_preserves_ip (SequentialHQIVEvolution.flattenGates E) f g

theorem SequentialHQIVEvolution_preserves_discreteNormSq [DecidableEq (HarmonicIndex L)]
    (E : SequentialHQIVEvolution L) (f : DiscreteState L) :
    discreteNormSq (E.toEquiv f) = discreteNormSq f := by
  simpa [discreteNormSq] using SequentialHQIVEvolution_preserves_discreteIp E f f

/-- **Projection compatibility (v1):** after `Π = id`, inner products agree with the
sequential digital evolution (hence with the ideal unitary on the digital sector up to
the global phase story carried by `SkewIncrement`, not yet quotiented in `HQIVGate`). -/
theorem SequentialHQIVEvolution_preserves_ip_after_Pi [DecidableEq (HarmonicIndex L)]
    (E : SequentialHQIVEvolution L) (f g : DiscreteState L) :
    discreteIp (discreteProjectionPi (E.toEquiv f)) (discreteProjectionPi (E.toEquiv g)) =
      discreteIp (discreteProjectionPi f) (discreteProjectionPi g) := by
  simp [SequentialHQIVEvolution_preserves_discreteIp]

private theorem List_flatten_append {α : Type*} (xs ys : List (List α)) :
    (xs ++ ys).flatten = xs.flatten ++ ys.flatten := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp [List.flatten, ih, List.append_assoc]

theorem flattenGates_steps_append [DecidableEq (HarmonicIndex L)]
    (E₁ E₂ : SequentialHQIVEvolution L) :
    SequentialHQIVEvolution.flattenGates { steps := E₁.steps ++ E₂.steps } =
      SequentialHQIVEvolution.flattenGates E₁ ++ SequentialHQIVEvolution.flattenGates E₂ := by
  simp_rw [SequentialHQIVEvolution.flattenGates, List.map_append, List_flatten_append]

theorem SequentialHQIVEvolution_toEquiv_append [DecidableEq (HarmonicIndex L)]
    (E₁ E₂ : SequentialHQIVEvolution L) :
    SequentialHQIVEvolution.toEquiv { steps := E₁.steps ++ E₂.steps } =
      (E₁.toEquiv).trans E₂.toEquiv := by
  unfold SequentialHQIVEvolution.toEquiv
  rw [flattenGates_steps_append E₁ E₂, digitalEvolution_append]

/-! ## Sparse OSHoracle driver + dense certified run -/

variable [DecidableEq (HarmonicIndex L)]

/-- Full angular calibration list: one wrapped index per `i < (L+1)²` in lockstep with `decodeIdx`. -/
noncomputable def discreteStateToSparseFull (f : DiscreteState L) : SparseRegister L :=
  (List.range (Fintype.card (HarmonicIndex L))).map fun i : Nat => (i, f (decodeIdx (L := L) i))

/-- Fold the OSHoracle `applyGateSparse` step along a gate list (no pruning between steps). -/
noncomputable def oshSparseSequentialFold (gates : List (HQIVGate L)) (r : SparseRegister L) :
    SparseRegister L :=
  gates.foldl (fun acc g => applyGateSparse g acc) r

/-- Sparse trajectory for `E` using the same flattened gates as `toEquiv`. -/
noncomputable def runSparseSequentialOSH (E : SequentialHQIVEvolution L) (r : SparseRegister L) :
    SparseRegister L :=
  oshSparseSequentialFold (SequentialHQIVEvolution.flattenGates E) r

/-- **Certified dense evolution** (matches `SequentialHQIVEvolution.toEquiv`): use this for
norm / inner-product theorems. -/
noncomputable def runSequentialEvolution (E : SequentialHQIVEvolution L) (f : DiscreteState L) :
    DiscreteState L :=
  E.toEquiv f

@[simp] theorem runSequentialEvolution_eq_toEquiv (E : SequentialHQIVEvolution L)
    (f : DiscreteState L) : runSequentialEvolution E f = E.toEquiv f :=
  rfl

omit [DecidableEq (HarmonicIndex L)] in
theorem oshSparseSequentialFold_length (gates : List (HQIVGate L)) (r : SparseRegister L) :
    (oshSparseSequentialFold gates r).length = 2 ^ gates.length * r.length := by
  induction gates generalizing r with
  | nil =>
      simp [oshSparseSequentialFold]
  | cons g gs ih =>
      have h := ih (applyGateSparse g r)
      simp [oshSparseSequentialFold, List.foldl, applyGateSparse_length_eq_two_mul, List.length_cons] at h ⊢
      rw [h]
      simp [pow_succ, Nat.mul_assoc, Nat.mul_comm]

/-- Count of flattened digital gates (exponent base-2 in `oshSparseSequentialFold_length`). -/
noncomputable def sequentialSparseSupportExponent (E : SequentialHQIVEvolution L) : ℕ :=
  (SequentialHQIVEvolution.flattenGates E).length

theorem runSparseSequentialOSH_length (E : SequentialHQIVEvolution L) (r : SparseRegister L) :
    (runSparseSequentialOSH E r).length =
      2 ^ sequentialSparseSupportExponent E * r.length := by
  simpa [runSparseSequentialOSH, sequentialSparseSupportExponent] using
    oshSparseSequentialFold_length (SequentialHQIVEvolution.flattenGates E) r

/-! **n-body style scaling (bookkeeping):** worst-case sparse register length after `n` OSH steps
from an `r`-ket scales as `2^n * r.length` (no pruning). -/
omit [DecidableEq (HarmonicIndex L)] in
theorem nBodySequentialSparseLength_bound (n : ℕ) (gates : List (HQIVGate L)) (r : SparseRegister L)
    (hg : gates.length = n) :
    (oshSparseSequentialFold gates r).length = 2 ^ n * r.length := by
  simpa [hg] using oshSparseSequentialFold_length gates r

/-! ## Hamiltonian → schedule translators -/

/-- Canonical `ℓ = 0` angular slot (`m = 0` within that shell). -/
def harmonicSlotShell0 (L : ℕ) : HarmonicIndex L :=
  ⟨⟨0, Nat.succ_pos L⟩, ⟨0, by simp⟩⟩

/-- Canonical `ℓ = 1` slot (first `m` index); requires `0 < L` so `ℓ = 1` lies in `Fin (L+1)`. -/
def harmonicSlotShell1 (L : ℕ) (hL : 0 < L) : HarmonicIndex L :=
  ⟨⟨1, by omega⟩, ⟨0, by omega⟩⟩

/--
**Truncated harmonic oscillator (frequency beating):** alternate `π` phases between the
`ℓ = 0` and `ℓ = 1` slots so the digital layer sees **frequency-dependent** scheduling through
different `HarmonicIndex` labels, while `SkewIncrement.hoFrequencySkew` ties `θ` to `φ_rat(ℓ)`
and advances lapse via `HQVM_lapse Φ φ (k·δt)` on tick `k`.

This schedule remains a **discrete π-phase** oscillator proxy (`phaseGate` only). Continuous
single-qubit rotations now live separately as certified two-level local mixes in
`DigitalGates.twoLevelUnitaryGate`; this HO translator does not claim a continuous `U(1)` flow.
-/
noncomputable def hoFrequencyBeatingSequential (hL : 0 < L) (Φ φ δt : ℝ) (m : ℕ) (n : ℕ) :
    SequentialHQIVEvolution L where
  steps :=
    (List.range n).map fun k : Nat =>
      (if _ : k % 2 = 0 then
        (⟨{
            shell := m
            slot := some (harmonicSlotShell0 L)
            τAB := 0
            τAC := 0
            τA_BC := 1
            hPhi := correctedCkwMonogamyPhi_trivial m
            desc := "HO_freq_low_l" },
          [phaseGate (harmonicSlotShell0 L)],
          SkewIncrement.hoFrequencySkew 0 Φ φ ((k : ℝ) * δt)⟩ : HQIVEvolutionStep L)
      else
        (⟨{
            shell := m
            slot := some (harmonicSlotShell1 L hL)
            τAB := 0
            τAC := 0
            τA_BC := 1
            hPhi := correctedCkwMonogamyPhi_trivial m
            desc := "HO_freq_high_l" },
          [phaseGate (harmonicSlotShell1 L hL)],
          SkewIncrement.hoFrequencySkew 1 Φ φ ((k : ℝ) * δt)⟩ : HQIVEvolutionStep L))

/--
**Two-body sequential interaction:** apply a local `π` phase on slot `ijA`, then on slot `ijB`,
with **distinct** monogamy metadata on the second tick (`correctedCkwMonogamyPhi_quarter_pair`).
This is the minimal “sequentialize a two-site term” pattern—**not** a simultaneous two-body gate.
-/
noncomputable def twoBodySequentialSlots (ijA ijB : HarmonicIndex L) (mA mB : ℕ) :
    SequentialHQIVEvolution L where
  steps :=
    [⟨{
        shell := mA
        slot := some ijA
        τAB := 0
        τAC := 0
        τA_BC := 1
        hPhi := correctedCkwMonogamyPhi_trivial mA
        desc := "two_body_slot_A_first"
      }, [phaseGate ijA], SkewIncrement.minkowski⟩,
      ⟨{
        shell := mB
        slot := some ijB
        τAB := 1 / 4
        τAC := 1 / 4
        τA_BC := 1
        hPhi := correctedCkwMonogamyPhi_quarter_pair mB
        desc := "two_body_slot_B_second"
      }, [phaseGate ijB], SkewIncrement.minkowski⟩]

/-- **Truncated harmonic oscillator (digital analogue):** sequential `π` phases on a
fixed ladder slot emulate discrete phase kicks; ladder hopping as a true HO requires
additional swap/tensor structure (**out of scope** for this first file). -/
noncomputable def hoTruncatedSequential (ij : HarmonicIndex L) (m : ℕ) (n : ℕ) :
    SequentialHQIVEvolution L where
  steps :=
    (List.replicate n (⟨{
        shell := m
        slot := some ij
        τAB := 0
        τAC := 0
        τA_BC := 1
        hPhi := correctedCkwMonogamyPhi_trivial m
        desc := "HO_trunc_phase"
      }, [phaseGate ij], SkewIncrement.minkowski⟩ : HQIVEvolutionStep L))

/-- **Spin-½ in a Zeeman field (two-level proxy):** one angular slot, sequential `π`
pulses (digital Pauli-`Z` analogue at the available gate set). -/
noncomputable def spinHalfZeemanSequential (ij : HarmonicIndex L) (m : ℕ) (n : ℕ) :
    SequentialHQIVEvolution L where
  steps :=
    (List.replicate n (⟨{
        shell := m
        slot := some ij
        τAB := 0
        τAC := 0
        τA_BC := 1
        hPhi := correctedCkwMonogamyPhi_trivial m
        desc := "PauliZ_digital_pi"
      }, [phaseGate ij], SkewIncrement.minkowski⟩ : HQIVEvolutionStep L))

/-- **Two-level Rabi / dipole drive:** modeled here as the same sequential `π` channel as the
Zeeman stub. Angle-resolved Rabi scheduling should use the two-level local-mix witness from
`DigitalGates` rather than this legacy phase-only stub. -/
noncomputable def twoLevelRabiSequential (ij : HarmonicIndex L) (m : ℕ) (n : ℕ) :
    SequentialHQIVEvolution L where
  steps :=
    (List.replicate n (⟨{
        shell := m
        slot := some ij
        τAB := 0
        τAC := 0
        τA_BC := 1
        hPhi := correctedCkwMonogamyPhi_trivial m
        desc := "Rabi_digital_pi_stub"
      }, [phaseGate ij], SkewIncrement.minkowski⟩ : HQIVEvolutionStep L))

/--
**Single-particle potential / smeared field tick:** use a **Dirac shell smearing** of
`phi_of_shell` (`smearedAuxField_dirac_shell`) as the scalar mediator at `shell`, and a
local `π` phase on `ij` as the digital kick.

This is only a **proof-of-concept linkage** between `AuxiliaryFieldSmeared` and the gate
list; continuum potential flow is **out of scope**.
-/
noncomputable def potentialSmearedFieldSequential (ij : HarmonicIndex L) (m : ℕ) :
    SequentialHQIVEvolution L where
  steps :=
    [⟨{
        shell := m
        slot := some ij
        τAB := 0
        τAC := 0
        τA_BC := 1
        hPhi := correctedCkwMonogamyPhi_trivial m
        desc := "V_smear_dirac_shell"
      }, [phaseGate ij], {
        s := 1
        theta := 0
        lapse := 1 + smearedAuxField (fun k => if k = m then (1 : ℝ) else 0) {m}
      }⟩]

/-! ## Example theorems -/

theorem hoTruncated_respects_monogamy (ij : HarmonicIndex L) (m n : ℕ) :
    EvolutionRespectsMonogamyPhi (hoTruncatedSequential ij m n).steps := by
  intro p _
  exact p.1.hPhi

theorem hoTruncated_norm_preserving (ij : HarmonicIndex L) (m n : ℕ) (f : DiscreteState L) :
    discreteNormSq ((hoTruncatedSequential ij m n).toEquiv f) = discreteNormSq f :=
  SequentialHQIVEvolution_preserves_discreteNormSq _ f

theorem potentialSmearedFieldSequential_lapse_eq (ij : HarmonicIndex L) (m : ℕ) :
    ((potentialSmearedFieldSequential ij m).steps.head?).map (fun p => p.2.2.lapse) =
      some (1 + phi_of_shell m) := by
  simp [potentialSmearedFieldSequential, List.head?, smearedAuxField_dirac_shell]

theorem hoFrequency_respects_monogamy (hL : 0 < L) (Φ φ δt : ℝ) (m n : ℕ) :
    EvolutionRespectsMonogamyPhi (hoFrequencyBeatingSequential hL Φ φ δt m n).steps := by
  intro p _
  exact p.1.hPhi

theorem twoBodySequential_respects_monogamy (ijA ijB : HarmonicIndex L) (mA mB : ℕ) :
    EvolutionRespectsMonogamyPhi (twoBodySequentialSlots ijA ijB mA mB).steps := by
  intro p hp
  simp only [twoBodySequentialSlots, List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
  rcases hp with (h₁ | h₂)
  · subst h₁; exact correctedCkwMonogamyPhi_trivial mA
  · subst h₂; exact correctedCkwMonogamyPhi_quarter_pair mB

#print SequentialHQIVEvolution
#print hoTruncatedSequential
#print spinHalfZeemanSequential
#print twoLevelRabiSequential
#print potentialSmearedFieldSequential
#print SequentialHQIVEvolution_preserves_discreteIp
#print hoTruncated_respects_monogamy

end Hqiv.QuantumComputing

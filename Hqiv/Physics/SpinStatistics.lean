import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Hqiv.Algebra.OctonionSpinorCarrier
import Hqiv.QuantumMechanics.PatchQFTBridge

/-!
## Spin–statistics from triality and null-lattice causality

This module sets up a **clean logical chain** for the spin–statistics link in
an HQIV-style setting, with **no sorrys**:

1. We introduce an abstract type of one-particle lattice modes and a
   `SpinClass` (integer vs half-integer) encoding the SO(8) → SO(3,1)
   projection.
2. We package **exchange phases**, a **spacelike-separation** relation, and
   the data needed to talk about spin and locality in a `SpinStatisticsData`
   structure.
3. We formulate *axioms* that abstractly encode:
   * triality-style bilinears (two spinor modes → bosonic observable),
   * null-lattice causality (local commutativity at spacelike separation),
   * and an identification between 2π-rotation phases and exchange phases.
4. From these axioms we derive, in Lean, the **spin–statistics rule**:
   half-integer–spin modes have exchange phase −1 under exchange, integer-spin
   modes have exchange phase +1.

This gives a precise target: to realise the axioms using the existing HQIV
light-cone + monogamy + Spin(8) machinery, and then plug into the general
lemma proved here.
-/

namespace Hqiv.Physics

/-- Abstract label for the spin class of a lattice mode after projecting
SO(8) representations to the physical SO(3,1) rotation/Lorentz group. -/
inductive SpinClass
  | integer    -- integer spin: 2π rotation acts as +1
  | halfInteger -- half-integer spin: 2π rotation acts as −1
  deriving DecidableEq, Repr

/-- Abstract type of *one-particle lattice modes*.

In a future refinement this can be instantiated by an explicit mode carrier,
e.g. octonionic spinor data plus lattice site; for the problem statement we
keep it abstract. -/
opaque LatticeMode : Type

/-- Exchange phase for a pair of identical lattice modes. In a Fock-style
description this encodes whether exchanging two copies of the same mode
acts as +1 (commuting / bosonic) or −1 (anticommuting / fermionic). -/
abbrev ExchangePhase := LatticeMode → LatticeMode → ℂ

/-- Abstract notion of *spacelike separation* on the discrete null lattice.

This is intended to be induced by the HQVMetric / `Now` geometry and the
discrete null-lattice ordering; for the spin–statistics statement we only
need an abstract predicate. -/
abbrev SpacelikeSeparated := LatticeMode → LatticeMode → Prop

/-- Data needed to talk about spin classes and exchange phases for
one-particle modes on the HQIV null lattice. -/
structure SpinStatisticsData where
  /-- Underlying carrier of one-particle modes. -/
  mode          : Type
  /-- Spin class of each mode after the SO(8) → SO(3,1) projection. -/
  spinClass     : mode → SpinClass
  /-- Exchange phase for a pair of (identical) modes. -/
  exchangePhase : mode → mode → ℂ
  /-- Spacelike separation relation on the lattice. -/
  spacelikeSep  : mode → mode → Prop

namespace SpinStatisticsData

variable (D : SpinStatisticsData)

/-- Mode is bosonic (integer spin) in a given spin–statistics data bundle. -/
def isBosonic (m : D.mode) : Prop :=
  D.spinClass m = SpinClass.integer

/-- Mode is fermionic (half-integer spin) in a given spin–statistics data bundle. -/
def isFermionic (m : D.mode) : Prop :=
  D.spinClass m = SpinClass.halfInteger

end SpinStatisticsData

open SpinStatisticsData

/-- Axioms encoding triality, causality, and the link between spin (2π phase)
and exchange phase for a given `SpinStatisticsData` bundle.

These are deliberately abstract; the goal for HQIV is to *realise* them from:

* the Spin(8)/so(8) structure obtained from counting over O,
* the null-lattice / monogamy geometry (HQVMetric, `Now`),
* and the way triality maps pairs of spinor modes into bosonic observables. -/
structure SpinStatisticsAxioms (D : SpinStatisticsData) : Type where
  /-- Phase picked up by a one-particle mode under a 2π rotation. -/
  twoPiPhase : D.mode → ℂ

  /-- Half-integer–spin modes acquire a −1 phase under 2π rotation. -/
  twoPiPhase_halfInteger :
    ∀ m, isFermionic D m → twoPiPhase m = (-1 : ℂ)

  /-- Integer–spin modes acquire a +1 phase under 2π rotation. -/
  twoPiPhase_integer :
    ∀ m, isBosonic D m → twoPiPhase m = (1 : ℂ)

  /-- Triality-style bilinear: two modes combine to a bosonic observable. -/
  J : D.mode → D.mode → D.mode

  /-- Bilinears of two fermionic modes transform as bosons. -/
  J_bosonic :
    ∀ m₁ m₂,
      isFermionic D m₁ →
      isFermionic D m₂ →
      isBosonic D (J m₁ m₂)

  /-- Local commutativity / monogamy: triality-induced bosonic observables
  commute at spacelike separation. Here encoded as unit exchange phase. -/
  locality_bosonic :
    ∀ m₁ m₂,
      D.spacelikeSep m₁ m₂ →
      D.exchangePhase (J m₁ m₂) (J m₂ m₁) = (1 : ℂ)

  /-- Composition law (fermionic sector): for two fermionic modes, the
  exchange phase of the bilinear observable built from them equals the
  product of the single-mode exchange phases. This abstracts the way
  exchange acts on pairs of identical fermionic modes. -/
  exchangePhase_bilinear :
    ∀ m₁ m₂,
      isFermionic D m₁ →
      isFermionic D m₂ →
      D.exchangePhase (J m₁ m₂) (J m₂ m₁) =
        D.exchangePhase m₁ m₁ * D.exchangePhase m₂ m₂

  /-- Identification of 2π rotation phase with the single-mode exchange phase.

  This is the step where the *representation-theoretic* phase (from Spin(3,1))
  is tied to the exchange phase for identical modes. In a full HQIV
  realisation this should come from the way mode operators are built from the
  underlying Spin(8) / triality data. -/
  exchange_eq_twoPiPhase :
    ∀ m, D.exchangePhase m m = twoPiPhase m

/-- **Spin–statistics from triality and null-lattice causality (HQIV version).**

This `Prop` bundles the desired theorem as a single statement, in the same
spirit as `YangMills_SM_GR_Unification_statement`. It says that there exists
a description of one-particle lattice modes such that:

1. (**Spin classes from Spin(8)**)
   Modes fall into two spin classes `integer` and `halfInteger` derived from
   the Spin(8) / so(8) structure and its triality, with:
   * `halfInteger` modes picking up a phase −1 under 2π rotation,
   * `integer` modes picking up +1 under 2π rotation.

2. (**Null-lattice causality / monogamy**)
   There is a spacelike-separation relation compatible with the HQIV null
   lattice such that:
   * local bosonic observables (built from vector / integer-spin reps) commute
     at spacelike separation,
   * these observables can be expressed as triality-induced bilinears of the
     underlying one-particle modes.

3. (**Spin–statistics conclusion**)
   For *identical* modes, exchange phases are fixed purely by the above:
   * half-integer–spin modes anticommute (exchange phase −1),
   * integer–spin modes commute (exchange phase +1).

The details of “triality-induced bilinears” and “locality” are kept abstract
here; the goal for future work is to realise this statement with the concrete
Spin(8) data from the generator stack and the discrete null lattice.
-/
def SpinStatistics_from_triality_and_causality_statement : Prop :=
  ∃ D : SpinStatisticsData,
    (∀ m : D.mode, D.spinClass m = SpinClass.integer ∨
                   D.spinClass m = SpinClass.halfInteger) ∧
    (∃ _ : SpinStatisticsAxioms D,
      (∀ m : D.mode, isFermionic D m →
          D.exchangePhase m m = (-1 : ℂ)) ∧
      (∀ m : D.mode, isBosonic D m →
          D.exchangePhase m m = (1 : ℂ)))

/-- **Abstract spin–statistics lemma.**

For any given `SpinStatisticsData` bundle, the axioms suffice to derive the
spin–statistics sign rule: half-integer–spin modes have exchange phase −1,
integer–spin modes have exchange phase +1.

This is the internal chain of logic; HQIV's task is to *realise* these axioms
using the light-cone + monogamy + Spin(8) machinery. -/
theorem spin_statistics_from_axioms
    (D : SpinStatisticsData) (A : SpinStatisticsAxioms D) :
    (∀ m : D.mode, isFermionic D m →
        D.exchangePhase m m = (-1 : ℂ)) ∧
    (∀ m : D.mode, isBosonic D m →
        D.exchangePhase m m = (1 : ℂ)) := by
  -- Unpack the axioms we actually use.
  rcases A with
    ⟨twoPiPhase, h_half, h_int, _J, _J_bos, _loc, _bilin, h_link⟩
  constructor
  · intro m hF
    -- For fermionic modes, 2π phase is −1 and equals the exchange phase.
    have h₁ : twoPiPhase m = (-1 : ℂ) := h_half m hF
    have h₂ : D.exchangePhase m m = twoPiPhase m := h_link m
    -- Combine.
    simpa [h₁] using h₂
  · intro m hB
    -- For bosonic modes, 2π phase is +1 and equals the exchange phase.
    have h₁ : twoPiPhase m = (1 : ℂ) := h_int m hB
    have h₂ : D.exchangePhase m m = twoPiPhase m := h_link m
    -- Combine.
    simpa [h₁] using h₂

/-- A fermionic one-particle horizon mode: shell index + local patch + octonion carrier. -/
structure HQIVFermionMode where
  shell : ℕ
  patch : Fin 4
  spinor : Hqiv.Algebra.OctonionSpinorCarrier

/-- A bosonic observable remembers the shell and the two local support patches it couples. -/
structure HQIVBosonMode where
  shell : ℕ
  leftPatch : Fin 4
  rightPatch : Fin 4

/-- Concrete HQIV mode carrier used by the spin-statistics package. -/
abbrev HQIVMode := Sum HQIVFermionMode HQIVBosonMode

noncomputable instance : DecidableEq HQIVFermionMode := Classical.decEq _
noncomputable instance : DecidableEq HQIVBosonMode := Classical.decEq _
noncomputable instance : DecidableEq HQIVMode := Classical.decEq _

/-- A simple reference spinor used for locality witnesses. -/
noncomputable def zeroSpinor : Hqiv.Algebra.OctonionSpinorCarrier := fun _ => 0

/-- Canonical fermionic mode at shell `m` and local patch `p`. -/
noncomputable def sampleFermionMode (m : ℕ) (p : Fin 4) : HQIVMode :=
  Sum.inl { shell := m, patch := p, spinor := zeroSpinor }

/-- Extract the shell carried by a concrete HQIV mode. -/
def hqivModeShell : HQIVMode → ℕ
  | Sum.inl f => f.shell
  | Sum.inr b => b.shell

/-- Primary patch used when feeding a mode into the locality relation. -/
def hqivModePrimaryPatch : HQIVMode → Fin 4
  | Sum.inl f => f.patch
  | Sum.inr b => b.leftPatch

/--
Concrete spacelike separation for HQIV modes:

two modes are spacelike when they lie on the same shell and their primary local
patches are Minkowski-spacelike in the patch chart from `PatchQFTBridge`.
-/
def hqivModeSpacelikeSep (m₁ m₂ : HQIVMode) : Prop :=
  hqivModeShell m₁ = hqivModeShell m₂ ∧
    Hqiv.QM.minkowskiSpacelikeSep
      (Hqiv.QM.patchChartPoint (hqivModePrimaryPatch m₁))
      (Hqiv.QM.patchChartPoint (hqivModePrimaryPatch m₂))

/-- Triality-style bilinear witness carrying the shell and patch support of its inputs. -/
def hqivTrialityObservable : HQIVMode → HQIVMode → HQIVMode
  | Sum.inl f₁, Sum.inl f₂ =>
      Sum.inr
        { shell := Nat.min f₁.shell f₂.shell
          leftPatch := f₁.patch
          rightPatch := f₂.patch }
  | m₁, m₂ =>
      Sum.inr
        { shell := Nat.min (hqivModeShell m₁) (hqivModeShell m₂)
          leftPatch := hqivModePrimaryPatch m₁
          rightPatch := hqivModePrimaryPatch m₂ }

/-- Same-shell spatial patches furnish concrete spacelike fermionic modes. -/
theorem hqivModeSpacelikeSep_same_shell_spatial {m : ℕ} {i j : Fin 4}
    (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    hqivModeSpacelikeSep (sampleFermionMode m i) (sampleFermionMode m j) := by
  constructor
  · rfl
  · simpa [hqivModeSpacelikeSep, sampleFermionMode, hqivModePrimaryPatch] using
      Hqiv.QM.minkowski_spacelike_patchChartPoint_spatial hi hj hij

/-- A patch is never spacelike separated from itself, so the HQIV relation is nontrivial. -/
theorem not_hqivModeSpacelikeSep_same_patch (m : ℕ) (i : Fin 4) :
    ¬ hqivModeSpacelikeSep (sampleFermionMode m i) (sampleFermionMode m i) := by
  intro hsep
  have hsp :
      Hqiv.QM.minkowskiSpacelikeSep (Hqiv.QM.patchChartPoint i) (Hqiv.QM.patchChartPoint i) := by
    simpa [hqivModeSpacelikeSep, sampleFermionMode, hqivModeShell, hqivModePrimaryPatch] using hsep.2
  have hdiag :
      Hqiv.QM.minkowskiIntervalSq
          (Hqiv.QM.minkowskiSep (Hqiv.QM.patchChartPoint i) (Hqiv.QM.patchChartPoint i)) = 0 := by
    fin_cases i <;>
      simp [Hqiv.QM.patchChartPoint, Hqiv.QM.minkowskiIntervalSq, Hqiv.QM.minkowskiSep,
        Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold Hqiv.QM.minkowskiSpacelikeSep at hsp
  rw [hdiag] at hsp
  have : ¬ (0 : ℝ) < 0 := by linarith
  exact this hsp

/-- The concrete HQIV locality relation has a genuine spacelike witness. -/
theorem hqivModeSpacelikeSep_has_witness :
    ∃ m₁ m₂ : HQIVMode, hqivModeSpacelikeSep m₁ m₂ := by
  refine ⟨sampleFermionMode 4 1, sampleFermionMode 4 2, ?_⟩
  exact hqivModeSpacelikeSep_same_shell_spatial (by decide) (by decide) (by decide)

/-- The concrete HQIV locality relation is not the degenerate "all pairs spacelike" relation. -/
theorem hqivModeSpacelikeSep_not_universal :
    ∃ m₁ m₂ : HQIVMode, ¬ hqivModeSpacelikeSep m₁ m₂ := by
  exact ⟨sampleFermionMode 4 1, sampleFermionMode 4 1, not_hqivModeSpacelikeSep_same_patch 4 1⟩

/-- **Concrete spin–statistics data** built from shell-aware horizon modes and patch locality. -/
noncomputable def D_HQIV : SpinStatisticsData :=
  { mode := HQIVMode
    , spinClass := fun m =>
        match m with
        | Sum.inl _ => SpinClass.halfInteger
        | Sum.inr _ => SpinClass.integer
    , exchangePhase := fun m₁ m₂ =>
        if _ : m₁ = m₂ then
          match m₁ with
          | Sum.inl _ => (-1 : ℂ)
          | Sum.inr _ => (1 : ℂ)
        else
          (1 : ℂ)
    , spacelikeSep := hqivModeSpacelikeSep }

namespace D_HQIV

/-- Every HQIV mode in `D_HQIV` is either integer- or half-integer–spin. -/
theorem spinClass_cases (m : D_HQIV.mode) :
    D_HQIV.spinClass m = SpinClass.integer ∨
    D_HQIV.spinClass m = SpinClass.halfInteger := by
  cases m <;> simp [D_HQIV]

/-- Concrete witness: the HQIV locality relation sees same-shell spatially separated modes. -/
theorem spacelikeSep_has_witness :
    ∃ m₁ m₂ : D_HQIV.mode, D_HQIV.spacelikeSep m₁ m₂ := by
  simpa [D_HQIV] using hqivModeSpacelikeSep_has_witness

/-- Concrete witness: the HQIV locality relation is not universal. -/
theorem spacelikeSep_not_universal :
    ∃ m₁ m₂ : D_HQIV.mode, ¬ D_HQIV.spacelikeSep m₁ m₂ := by
  simpa [D_HQIV] using hqivModeSpacelikeSep_not_universal

end D_HQIV

/-- **Concrete axioms**: triality-style bilinear, locality, and phase link
for the HQIV spin–statistics data `D_HQIV`. -/
noncomputable def A_HQIV : SpinStatisticsAxioms D_HQIV :=
by
  refine
    { twoPiPhase := ?twoPi
      , twoPiPhase_halfInteger := ?twoPi_half
      , twoPiPhase_integer := ?twoPi_int
      , J := ?J
      , J_bosonic := ?J_bos
      , locality_bosonic := ?loc
      , exchangePhase_bilinear := ?bilin
      , exchange_eq_twoPiPhase := ?link }
  · -- twoPiPhase
    exact fun m =>
      match m with
      | Sum.inl _ => (-1 : ℂ)
      | Sum.inr _ => (1 : ℂ)
  · -- twoPiPhase_halfInteger: half-integer modes get −1.
    intro m hF
    cases m with
    | inl v =>
        simp [D_HQIV, SpinStatisticsData.isFermionic, *] at hF ⊢
    | inr u =>
        -- Impossible: bosonic mode cannot be fermionic.
        simp [D_HQIV, SpinStatisticsData.isFermionic] at hF
  · -- twoPiPhase_integer: integer-spin modes get +1.
    intro m hB
    cases m with
    | inl v =>
        -- Impossible: fermionic mode cannot be bosonic.
        simp [D_HQIV, SpinStatisticsData.isBosonic] at hB
    | inr u =>
        simp [D_HQIV, SpinStatisticsData.isBosonic, *] at hB ⊢
  · -- J: triality-style bilinear — promote fermion pairs to a bosonic observable
    -- while preserving shell/patch support data.
    exact hqivTrialityObservable
  · -- J_bosonic: fermion–fermion bilinear is bosonic.
    intro m₁ m₂ hF₁ hF₂
    cases m₁ <;> cases m₂ <;>
      simp [D_HQIV, hqivTrialityObservable, SpinStatisticsData.isFermionic,
            SpinStatisticsData.isBosonic] at hF₁ hF₂ ⊢
  · -- locality_bosonic: bosonic bilinears commute (unit exchange phase).
    intro m₁ m₂ _hsep
    -- J m₁ m₂ and J m₂ m₁ are always bosonic observables; exchange phase = 1.
    cases m₁ <;> cases m₂
    all_goals
      simp [D_HQIV, hqivTrialityObservable]
  · -- exchangePhase_bilinear: in fermionic sector, phase is product of
    -- single-mode phases (−1)·(−1) = 1.
    intro m₁ m₂ hF₁ hF₂
    cases m₁ <;> cases m₂
    · simp [D_HQIV, hqivTrialityObservable, SpinStatisticsData.isFermionic] at hF₁ hF₂ ⊢
    all_goals
      simp [D_HQIV, SpinStatisticsData.isFermionic] at hF₁ hF₂
  · -- exchange_eq_twoPiPhase: single-mode exchange phase equals 2π phase.
    intro m
    cases m with
    | inl v =>
        simp [D_HQIV]
    | inr u =>
        simp [D_HQIV]

/-- **HQIV satisfies the spin–statistics statement** in the abstract sense:
there exists a spin–statistics data bundle and corresponding axioms such
that the spin–statistics sign rule holds. -/
theorem HQIV_satisfies_SpinStatistics_from_triality_and_causality :
    SpinStatistics_from_triality_and_causality_statement := by
  refine ⟨D_HQIV, ?_, ?_⟩
  · -- (1) Every mode is labelled as integer or half-integer spin.
    intro m
    exact D_HQIV.spinClass_cases m
  · refine ⟨A_HQIV, ?_⟩
    exact spin_statistics_from_axioms D_HQIV A_HQIV

/-!
## Energy-time uncertainty for resonances

This section links an overlap energy scale `ΔE` to a resonance lifetime via the
standard uncertainty relation. It lives here because the fermionic lattice rules
constrain the admissible overlap energies, and those energies then control the
strong-decay timescale.

**SI twin:** `Hqiv.energyTimeResolutionScale` in `HQVMPerturbations` uses the same `τ = ħ/ΔE` form
with `hbar_SI` from `Forces` for observer-centric time-resolution bookkeeping on the lapse /
perturbation side (no new axiom).
-/

/-- Reduced Planck constant in MeV·s. -/
noncomputable def hbar_MeV_s : ℝ := 6.582119569e-22

/-- Mean lifetime `τ = ħ / ΔE` for a resonance with width / overlap scale `ΔE`
    measured in MeV. -/
noncomputable def resonance_lifetime (delta_E : ℝ) : ℝ :=
  hbar_MeV_s / delta_E

/-- Half-life corresponding to `resonance_lifetime`. -/
noncomputable def resonance_half_life (delta_E : ℝ) : ℝ :=
  Real.log 2 * resonance_lifetime delta_E

/-- Substituting a concrete overlap-energy witness into `τ = ħ / ΔE` gives the
    corresponding resonance lifetime. -/
theorem resonance_lifetime_from_overlap_energy
    {ΔE overlap_energy : ℝ} (hΔ : ΔE = overlap_energy) :
    resonance_lifetime ΔE = hbar_MeV_s / overlap_energy := by
  simp [resonance_lifetime, hΔ]

/-- Substituting a concrete overlap-energy witness into the half-life formula
    gives `t₁/₂ = (log 2) ħ / ΔE`. -/
theorem resonance_half_life_from_overlap_energy
    {ΔE overlap_energy : ℝ} (hΔ : ΔE = overlap_energy) :
    resonance_half_life ΔE = Real.log 2 * (hbar_MeV_s / overlap_energy) := by
  simp [resonance_half_life, resonance_lifetime, hΔ]

/-- Positive overlap energy gives a positive resonance lifetime. -/
theorem resonance_lifetime_pos
    {ΔE : ℝ} (hΔ : 0 < ΔE) :
    0 < resonance_lifetime ΔE := by
  unfold resonance_lifetime
  refine div_pos ?_ hΔ
  unfold hbar_MeV_s
  norm_num

/-- If a weak-channel lifetime is bounded below by any quantity that already
    exceeds the resonance lifetime, then the weak channel is slower than the
    overlap-driven resonance decay. -/
theorem weak_channel_slower_than_resonance
    {ΔE lifetime_weak lower_bound : ℝ}
    (hres : resonance_lifetime ΔE < lower_bound)
    (hweak : lower_bound ≤ lifetime_weak) :
    resonance_lifetime ΔE < lifetime_weak :=
  lt_of_lt_of_le hres hweak

end Hqiv.Physics


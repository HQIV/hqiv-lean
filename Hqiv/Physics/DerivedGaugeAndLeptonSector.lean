import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Physics.BaryogenesisCore
import Hqiv.Algebra.OctonionAxisAngles
import Hqiv.Geometry.UniverseAge
import Hqiv.Physics.ModalFrequencyHorizon
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

open scoped ArithmeticFunction.Omega
open ArithmeticFunction

namespace Hqiv.Physics

/-!
This module must remain light-weight: it defines only the outer-horizon
closure witnesses needed for JSON export and avoids importing `Triality`,
which pulls in heavier algebra (and `So8CoordMatrix`).

It now also serves as the lightweight outer-horizon modal/horizon readout package for the lepton/gauge
closure side: shells remain bookkeeping, while quarter-period / surface readouts are exposed through
`ModalFrequencyHorizonSpec`.
-/

def trialityOrder : ℕ := 3

-- Generation index for SM export: `So8RepIndex` (`Hqiv.Algebra`, defeq to `Fin 3`).

/-!
Pure-derived outer-horizon closure sector:
all scales in this file are generated from the lock-in shell `referenceM`,
the temperature ladder, triality count, and the monogamy split `alpha + gamma = 1`.
There are no charged-lepton shell placeholders and no external mass inputs here.

**Boson-mass witnesses.**
One radial step beyond lock-in, `T_lockin` multiplies the outer-horizon surface
at `referenceM + 1` to form the geometric base `vacuumExpectationValue`.
**EW gauge** masses use `vacuumExpectationValueGauge`: the same **quantum-number
budget** ingredients as the nucleon constituent layer — `latticeSimplexCount` at
lock-in, triality fold, and the charged-lepton **isospin doublet** (two
independent SM quantum numbers). **Z** uses the same outer closure line as **W**,
with effective coupling `g_SU2 + g_U1` on the lifted vev (both from triality and
`gammaDerived`). Weak mixing and PDG `sin²θ_W` are **not** imported here: **β decay** is packaged
like `NuclearAndAtomicSpectra.beta_decay_rate` + `Forces.weak_is_electric_tipping`
(horizon tipping / `G_F_from_beta`), not as an on-shell boson line in this file.
**Neutrino oscillation** is packaged **below** with masses from this ladder; the
effective mixing angle is **`Hqiv.Algebra.intrinsicShellAxisAngle` at `referenceM`**
(Fano-plane / `Ω`–axis assignment from `OctonionAxisAngles`, not a PMNS import). A
**CP-odd rapidity skew** uses the same monogamy coefficient as the Rindler layer
(`γ/2` in lock-in units, cf. `FanoResonance.c_rindler_shared` / `GlobalDetuning`).
`neutrinoSurvivalProb_twoFlavor` keeps a generic `θ` for the same schematic role as
the nuclear `ℳ` placeholder in `beta_decay_rate`.
**Higgs** uses `vacuumExpectationValueScalar` with scalar lift
`trialityOrder + chargedLeptonSmDoubletCount` (weak doublet tied to the triality
stack), and `m_H_derived = 2 * vev_scalar` as the minimal portal normalization.

**Carrier Gram certificate (downstream import).** The Pauli-plane Gram matrix,
its trace/determinant spectral identities, the factor-`8` bridge to `M_W_derived²`,
and a single packaged certificate `ew_carrier_gram_mass_certificate` tying these
to `boson_witness_M_W` / `boson_witness_m_H` live in
`Hqiv/Physics/WeakDoubletCarrierGaugeQuadratic.lean` (that module imports this file;
do not import it here to avoid a cycle).

**Neutrino witnesses.**
The same outer-horizon story continues one shell farther out:
`outerHorizonNeutrinoSuppression` uses `outerHorizonSurface (referenceM + 2)`,
so `m_nu_e_derived` is an adjacent-surface witness built from the same closure
ingredients. **Oscillation:** splittings `neutrinoDeltaMSquared_*_derived`; mixing uses
**Fano-plane axis angles** at lock-in (`neutrinoMixingAngle_fanoPlane_lockin`); optional
**rapidity CP** shift `neutrinoCPPhase_skew_from_rapidity`. Generic `θ` remains in
`neutrinoSurvivalProb_twoFlavor` for nuclear-style `ℳ` flexibility. Spin-only neutral
bookkeeping (`ConservedContentMassBridge`) matches the narrative of **no charge/color
well** between generations. Charged-lepton shell selection stays in other modules.
-/

/-- Outer-horizon surface from lattice stars-and-bars leading term. -/
noncomputable def outerHorizonSurface (m : ℕ) : ℝ :=
  ((m + 1 : ℝ) * (m + 2 : ℝ))

/-- Inner meta-horizon surface uses the same shell geometry. -/
noncomputable def innerMetaHorizonSurface (m : ℕ) : ℝ :=
  ((m + 1 : ℝ) * (m + 2 : ℝ))

/-- Resonance step is the geometric surface ratio between shells. -/
noncomputable def resonanceStepK (m_from m_to : ℕ) : ℝ :=
  outerHorizonSurface m_to / outerHorizonSurface m_from

/-- Boson closure shell chosen one radial step beyond lock-in. -/
def bosonClosureShell : ℕ := referenceM + 1

/-- Canonical outer-horizon closure shell: one radial step beyond `referenceM`. -/
def outerClosureShell : ℕ := bosonClosureShell

/-- Modal-frequency / horizon wrapper for the boson/outer-closure shell. -/
noncomputable def outerClosureModalFrequencySpec : ModalFrequencyHorizonSpec :=
  modalFrequencyHorizonFromShellNominal outerClosureShell

/-- Modal-frequency / horizon wrapper for the next outer neutrino suppression shell. -/
noncomputable def neutrinoSuppressionModalFrequencySpec : ModalFrequencyHorizonSpec :=
  modalFrequencyHorizonFromShellNominal (referenceM + 2)

/-- Monogamy coefficient derived from the HQIV lattice split α+γ=1. -/
def gammaDerived : ℝ := 1 - alpha

/-- Monogamy lift multiplying the outer-horizon closure scale. -/
def outerClosureMonogamyLift : ℝ := 1 + gammaDerived

/-- Geometric vev from horizon temperature/area coupling at the boson closure shell. -/
noncomputable def vacuumExpectationValue : ℝ :=
  T_lockin * outerHorizonSurface bosonClosureShell * outerClosureMonogamyLift

/-- Charged-lepton weak-isospin doublet dimension (= `chargedLeptonContentCount` in lepton modules). -/
def chargedLeptonSmDoubletCount : ℕ := 2

/--
EW **gauge** quantum lift: simplex mode count at lock-in, triality fold, and the
charged-lepton doublet — parallel to the nucleon `quarkConstituentDress` bookkeeping.
-/
noncomputable def ewGaugeSectorQuantumLift : ℝ :=
  (latticeSimplexCount referenceM : ℝ) / (trialityOrder : ℝ) *
    (chargedLeptonSmDoubletCount : ℝ)

/-- Scalar / Higgs vev lift: triality stack plus weak-isospin doublet (3 + 2). -/
noncomputable def ewScalarSectorQuantumLift : ℝ :=
  (trialityOrder + chargedLeptonSmDoubletCount : ℝ)

noncomputable def vacuumExpectationValueGauge : ℝ :=
  vacuumExpectationValue * ewGaugeSectorQuantumLift

noncomputable def vacuumExpectationValueScalar : ℝ :=
  vacuumExpectationValue * ewScalarSectorQuantumLift

/-- Canonical outer-horizon **gauge** closure scale (includes EW quantum lift). -/
noncomputable def outerClosureScale : ℝ := vacuumExpectationValueGauge

/-- Minimal gauge closure couplings from triality count and monogamy split. -/
noncomputable def su2CouplingDerived : ℝ := 1 / (trialityOrder : ℝ)
noncomputable def u1CouplingDerived : ℝ := gammaDerived / (trialityOrder : ℝ)

/-- Generic boson mass from the **base** geometric vev (legacy hook; prefer `gaugeBosonMassFromVevGauge`). -/
noncomputable def gaugeBosonMassFromVev (gEff : ℝ) : ℝ :=
  gEff * vacuumExpectationValue

noncomputable def gaugeBosonMassFromVevGauge (gEff : ℝ) : ℝ :=
  gEff * vacuumExpectationValueGauge

noncomputable def M_W_derived : ℝ :=
  gaugeBosonMassFromVevGauge su2CouplingDerived

/-- Neutral vector from the same lifted vev with `g_SU2 + g_U1` (no weak-mixing import). -/
noncomputable def M_Z_derived : ℝ :=
  gaugeBosonMassFromVevGauge (su2CouplingDerived + u1CouplingDerived)

noncomputable def m_H_derived : ℝ :=
  2 * vacuumExpectationValueScalar

theorem M_Z_derived_eq_W_times_one_plus_gamma : M_Z_derived = (1 + gammaDerived) * M_W_derived := by
  unfold M_Z_derived M_W_derived gaugeBosonMassFromVevGauge su2CouplingDerived u1CouplingDerived
  ring

/-- Charged outer-horizon closure witness. -/
noncomputable def chargedClosureWitness : ℝ := M_W_derived

/-- Neutral outer-horizon closure witness. -/
noncomputable def neutralClosureWitness : ℝ := M_Z_derived

/-- Scalar outer-horizon closure witness. -/
noncomputable def scalarClosureWitness : ℝ := m_H_derived

/-- Small ν mass factor: `γ` over the next outer-horizon surface (`referenceM + 2`). -/
noncomputable def outerHorizonNeutrinoSuppression : ℝ :=
  gammaDerived / outerHorizonSurface (referenceM + 2)

noncomputable def m_nu_tree : ℝ := 0
noncomputable def m_nu_e_derived : ℝ := outerHorizonNeutrinoSuppression * M_Z_derived
noncomputable def m_nu_mu_derived : ℝ := outerHorizonNeutrinoSuppression * m_nu_e_derived
noncomputable def m_nu_tau_derived : ℝ := outerHorizonNeutrinoSuppression * m_nu_mu_derived

/-- Closed form for the outer-horizon ν suppression factor at the current lock-in / surface stack. -/
theorem outerHorizonNeutrinoSuppression_eq_inv_140 :
    outerHorizonNeutrinoSuppression = (1 : ℝ) / 140 := by
  unfold outerHorizonNeutrinoSuppression
  simp [gammaDerived, referenceM, qcdShell, stepsFromQCDToLockin, latticeStepCount, outerHorizonSurface,
    alpha]
  norm_num

/-- T13 coarse-graining on the canonical outer-shell witness agrees with the derived ν suppression. -/
theorem outerHorizonNeutrinoSuppression_eq_T13_fluctuationCoarseGrained :
    outerHorizonNeutrinoSuppression =
      fluctuationCoarseGrainedSuppression outerShellNeutrinoFluctuationWitness :=
  Eq.trans outerHorizonNeutrinoSuppression_eq_inv_140 canonical_T13_witness_recovers_exact_neutrino_suppression.symm

theorem outerHorizonNeutrinoSuppression_pos : 0 < outerHorizonNeutrinoSuppression := by
  rw [outerHorizonNeutrinoSuppression_eq_inv_140]
  norm_num

theorem outerHorizonNeutrinoSuppression_lt_one : outerHorizonNeutrinoSuppression < 1 := by
  rw [outerHorizonNeutrinoSuppression_eq_inv_140]
  norm_num

/-!
Neutrino layer split:
- `*_derived` stays the horizon-closure **witness** ladder.
- `*_observable κ` is an optional uniform readout map for external comparison.
  This keeps witness semantics and observable normalization separate.
-/
noncomputable def m_nu_e_observable (κ : ℝ) : ℝ := κ * m_nu_e_derived
noncomputable def m_nu_mu_observable (κ : ℝ) : ℝ := κ * m_nu_mu_derived
noncomputable def m_nu_tau_observable (κ : ℝ) : ℝ := κ * m_nu_tau_derived

theorem higgs_mass_from_outer_resonance :
    m_H_derived = 2 * vacuumExpectationValueScalar := rfl

theorem w_and_z_masses_from_gauge_closure :
    M_W_derived = gaugeBosonMassFromVevGauge su2CouplingDerived ∧
      M_Z_derived = gaugeBosonMassFromVevGauge (su2CouplingDerived + u1CouplingDerived) := by
  exact ⟨rfl, rfl⟩

theorem outer_closure_witnesses_from_scale :
    chargedClosureWitness = gaugeBosonMassFromVevGauge su2CouplingDerived ∧
      neutralClosureWitness = M_Z_derived ∧
      scalarClosureWitness = 2 * vacuumExpectationValueScalar := by
  exact ⟨rfl, rfl, rfl⟩

/-- Raw local boson closure layer: `M_W` and `M_Z` from `outerClosureScale` with derived `g` factors; Higgs from scalar vev. -/
theorem raw_local_boson_layers_from_outerClosureScale :
    M_W_derived = su2CouplingDerived * outerClosureScale ∧
      M_Z_derived = (su2CouplingDerived + u1CouplingDerived) * outerClosureScale ∧
      m_H_derived = 2 * vacuumExpectationValueScalar := by
  exact ⟨rfl, rfl, rfl⟩

theorem neutrino_masses_from_outer_horizon :
    m_nu_tree = 0 ∧
    m_nu_e_derived = outerHorizonNeutrinoSuppression * M_Z_derived ∧
    m_nu_mu_derived = outerHorizonNeutrinoSuppression * m_nu_e_derived ∧
    m_nu_tau_derived = outerHorizonNeutrinoSuppression * m_nu_mu_derived := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem neutrino_observable_eq_scale_times_witness (κ : ℝ) :
    m_nu_e_observable κ = κ * m_nu_e_derived ∧
      m_nu_mu_observable κ = κ * m_nu_mu_derived ∧
      m_nu_tau_observable κ = κ * m_nu_tau_derived := by
  exact ⟨rfl, rfl, rfl⟩

theorem neutrino_observable_at_unity_eq_witness :
    m_nu_e_observable 1 = m_nu_e_derived ∧
      m_nu_mu_observable 1 = m_nu_mu_derived ∧
      m_nu_tau_observable 1 = m_nu_tau_derived := by
  simp [m_nu_e_observable, m_nu_mu_observable, m_nu_tau_observable]

theorem neutrino_observable_at_zero_eq_zero :
    m_nu_e_observable 0 = 0 ∧
      m_nu_mu_observable 0 = 0 ∧
      m_nu_tau_observable 0 = 0 := by
  simp [m_nu_e_observable, m_nu_mu_observable, m_nu_tau_observable]

theorem neutrino_observable_ladder_from_neutralClosureWitness (κ : ℝ) :
    m_nu_e_observable κ = κ * outerHorizonNeutrinoSuppression * neutralClosureWitness ∧
      m_nu_mu_observable κ = κ * outerHorizonNeutrinoSuppression ^ 2 * neutralClosureWitness ∧
      m_nu_tau_observable κ = κ * outerHorizonNeutrinoSuppression ^ 3 * neutralClosureWitness := by
  constructor
  · unfold m_nu_e_observable m_nu_e_derived neutralClosureWitness
    ring
  constructor
  · unfold m_nu_mu_observable m_nu_mu_derived
    unfold m_nu_e_derived neutralClosureWitness
    ring
  · unfold m_nu_tau_observable m_nu_tau_derived m_nu_mu_derived
    unfold m_nu_e_derived neutralClosureWitness
    ring

theorem bosonClosureShell_eq_succ_reference : bosonClosureShell = referenceM + 1 := rfl

theorem outerClosureShell_eq_succ_reference : outerClosureShell = referenceM + 1 := by
  rfl

/-- Lock-in temperature is the ladder value at `referenceM` (`m_lockin = referenceM`). -/
theorem T_lockin_eq_T_referenceM : T_lockin = T referenceM := by
  rw [T_lockin_eq_ladder, m_lockin_eq_referenceM]

theorem vacuumExpectationValue_eq_T_lockin_outer_surface :
    vacuumExpectationValue =
      T_lockin * outerHorizonSurface (referenceM + 1) * (1 + gammaDerived) := by
  simp [vacuumExpectationValue, bosonClosureShell, outerClosureMonogamyLift]

theorem outerClosureScale_eq_reference_step :
    outerClosureScale =
      T_lockin * outerHorizonSurface (referenceM + 1) * outerClosureMonogamyLift *
        ewGaugeSectorQuantumLift := by
  simp [outerClosureScale, vacuumExpectationValueGauge, vacuumExpectationValue, bosonClosureShell,
    outerClosureMonogamyLift, ewGaugeSectorQuantumLift]

theorem outerClosureModalFrequencySpec_quarterPhase_eq_horizonQuarter :
    outerClosureModalFrequencySpec.nominalOmega *
        outerClosureModalFrequencySpec.interactionQuarterPeriod =
      Hqiv.horizonQuarterPeriod := by
  simpa [outerClosureModalFrequencySpec] using
    (modalFrequencyHorizonFromShellNominal outerClosureShell).quarterPhase_eq_horizonQuarter

theorem outerClosureModal_detunedSurfaceReadout :
    outerClosureModalFrequencySpec.detunedSurfaceReadout outerClosureShell =
      detunedShellSurface outerClosureShell := by
  rw [show outerClosureModalFrequencySpec = modalFrequencyHorizonFromShellNominal outerClosureShell by rfl]
  rw [detunedSurfaceReadout_fromShellNominal]

theorem neutrinoSuppressionModal_quarterPhase_eq_horizonQuarter :
    neutrinoSuppressionModalFrequencySpec.nominalOmega *
        neutrinoSuppressionModalFrequencySpec.interactionQuarterPeriod =
      Hqiv.horizonQuarterPeriod := by
  simpa [neutrinoSuppressionModalFrequencySpec] using
    (modalFrequencyHorizonFromShellNominal (referenceM + 2)).quarterPhase_eq_horizonQuarter

/-- Two adjacent resonance steps telescope to a surface ratio two shells out. -/
theorem resonance_two_step_outer_surface_ratio (m : ℕ) :
    resonanceStepK m (m + 1) * resonanceStepK (m + 1) (m + 2) =
      outerHorizonSurface (m + 2) / outerHorizonSurface m := by
  simp [resonanceStepK, outerHorizonSurface]
  field_simp

/--
Electron neutrino mass witness: explicit product of `T_lockin`, outer areas at
`referenceM + 1` and `referenceM + 2`, and the derived gauge couplings — no separate
mass-table input.
-/
theorem m_nu_e_derived_eq_suppression_times_M_Z :
    m_nu_e_derived = outerHorizonNeutrinoSuppression * M_Z_derived := rfl

theorem outer_horizon_neutrino_witness_from_adjacent_surfaces :
    m_nu_e_derived =
      (gammaDerived / outerHorizonSurface (referenceM + 2)) * M_Z_derived := by
  unfold m_nu_e_derived outerHorizonNeutrinoSuppression
  rfl

/-!
### Neutrino oscillation (parallel to `NuclearAndAtomicSpectra.beta_decay_rate`)

`NuclearAndAtomicSpectra.beta_decay_rate` uses `G_F_from_beta` (`Forces`) and a
placeholder `ℳ`. Here, **mixing angles come from the Fano-plane / Ω axis-angle map**
(`OctonionAxisAngles.intrinsicShellAxisAngle` at `referenceM`), aligned with the
same lock-in readout row as the heavy sector—not a PDG PMNS row. **CP violation** enters as a small
phase skew from the monogamy / rapidity side (`neutrinoCPPhase_skew_from_rapidity`,
cf. `GlobalDetuning` cumulative rapidity). `neutrinoSurvivalProb_twoFlavor θ …` keeps
a free `θ` for the same schematic flexibility as `ℳ`. Splittings are tied to
`m_nu_*_derived`. Use `E ≠ 0` in `neutrinoOscillationPhase` for a finite phase.
-/

noncomputable def neutrinoDeltaMSquared_mu_e_derived : ℝ :=
  m_nu_mu_derived ^ 2 - m_nu_e_derived ^ 2

noncomputable def neutrinoDeltaMSquared_tau_mu_derived : ℝ :=
  m_nu_tau_derived ^ 2 - m_nu_mu_derived ^ 2

noncomputable def neutrinoDeltaMSquared_tau_e_derived : ℝ :=
  m_nu_tau_derived ^ 2 - m_nu_e_derived ^ 2

theorem neutrinoDeltaMSquared_mu_e_derived_eq :
    neutrinoDeltaMSquared_mu_e_derived =
      outerHorizonNeutrinoSuppression ^ 2 * (outerHorizonNeutrinoSuppression ^ 2 - 1) *
        M_Z_derived ^ 2 := by
  unfold neutrinoDeltaMSquared_mu_e_derived m_nu_mu_derived
  rw [m_nu_e_derived_eq_suppression_times_M_Z]
  ring

theorem neutrinoDeltaMSquared_tau_mu_derived_eq :
    neutrinoDeltaMSquared_tau_mu_derived =
      outerHorizonNeutrinoSuppression ^ 4 * (outerHorizonNeutrinoSuppression ^ 2 - 1) *
        M_Z_derived ^ 2 := by
  unfold neutrinoDeltaMSquared_tau_mu_derived m_nu_tau_derived m_nu_mu_derived
  rw [m_nu_e_derived_eq_suppression_times_M_Z]
  ring

theorem neutrinoDeltaMSquared_tau_e_derived_eq :
    neutrinoDeltaMSquared_tau_e_derived =
      outerHorizonNeutrinoSuppression ^ 2 * (outerHorizonNeutrinoSuppression ^ 4 - 1) *
        M_Z_derived ^ 2 := by
  unfold neutrinoDeltaMSquared_tau_e_derived m_nu_tau_derived m_nu_mu_derived
  rw [m_nu_e_derived_eq_suppression_times_M_Z]
  ring

/-- Vacuum two-flavor oscillation phase `Δm² L / (4 E)` in natural units (`c = ħ = 1`). -/
noncomputable def neutrinoOscillationPhase (L E ΔmSq : ℝ) : ℝ := ΔmSq * L / (4 * E)

/--
Two-flavor ν\_e **survival** probability `P_{ee} = 1 - sin²(2θ) sin²(phase)`.
(Schematic 2-flavor; `θ` is an effective angle—not a PDG PMNS slot.)
-/
noncomputable def neutrinoSurvivalProb_twoFlavor (θ L E ΔmSq : ℝ) : ℝ :=
  1 - Real.sin (2 * θ) ^ 2 * Real.sin (neutrinoOscillationPhase L E ΔmSq) ^ 2

theorem neutrinoOscillationPhase_eq (L E ΔmSq : ℝ) :
    neutrinoOscillationPhase L E ΔmSq = ΔmSq * L / (4 * E) := rfl

theorem neutrinoSurvivalProb_twoFlavor_eq (θ L E ΔmSq : ℝ) :
    neutrinoSurvivalProb_twoFlavor θ L E ΔmSq =
      1 - Real.sin (2 * θ) ^ 2 * Real.sin (neutrinoOscillationPhase L E ΔmSq) ^ 2 := rfl

theorem one_lt_referenceM : 1 < referenceM := by
  unfold referenceM qcdShell stepsFromQCDToLockin latticeStepCount
  norm_num

theorem Omega_referenceM_eq_two : Ω referenceM = 2 := by
  unfold referenceM qcdShell stepsFromQCDToLockin latticeStepCount
  native_decide

/-- Two-flavor mixing angle from the **Fano / Ω intrinsic axis** at lock-in (`referenceM`). -/
noncomputable def neutrinoMixingAngle_fanoPlane_lockin : ℝ :=
  Hqiv.Algebra.intrinsicShellAxisAngle referenceM one_lt_referenceM

theorem neutrinoMixingAngle_fanoPlane_lockin_eq :
    neutrinoMixingAngle_fanoPlane_lockin = Real.pi / 4 := by
  unfold neutrinoMixingAngle_fanoPlane_lockin
  exact Hqiv.Algebra.intrinsicShellAxisAngle_of_Omega_two one_lt_referenceM Omega_referenceM_eq_two

/--
CP-odd increment on the oscillation phase from **monogamy / rapidity** normalization
(`(1-α)/2 · π` = `γ/2 · π` in lattice units at lock-in). Same coefficient class as
`FanoResonance.c_rindler_shared`; pairs with cumulative rapidity in `GlobalDetuning`.
-/
noncomputable def neutrinoCPPhase_skew_from_rapidity : ℝ :=
  (gammaDerived / 2) * Real.pi

theorem neutrinoCPPhase_skew_from_rapidity_eq :
    neutrinoCPPhase_skew_from_rapidity = Real.pi / 5 := by
  unfold neutrinoCPPhase_skew_from_rapidity gammaDerived alpha
  ring

/-- Two-flavor survival with mixing angle fixed to `neutrinoMixingAngle_fanoPlane_lockin`. -/
noncomputable def neutrinoSurvivalProb_fanoLockin_twoFlavor (L E ΔmSq : ℝ) : ℝ :=
  neutrinoSurvivalProb_twoFlavor neutrinoMixingAngle_fanoPlane_lockin L E ΔmSq

/-- Same, but the oscillation sine sees a **rapidity / CP** phase shift. -/
noncomputable def neutrinoSurvivalProb_fanoLockin_twoFlavor_withRapidityCP (L E ΔmSq : ℝ) : ℝ :=
  1 - Real.sin (2 * neutrinoMixingAngle_fanoPlane_lockin) ^ 2 *
    Real.sin (neutrinoOscillationPhase L E ΔmSq + neutrinoCPPhase_skew_from_rapidity) ^ 2

theorem neutrinoSurvivalProb_fanoLockin_twoFlavor_eq (L E ΔmSq : ℝ) :
    neutrinoSurvivalProb_fanoLockin_twoFlavor L E ΔmSq =
      neutrinoSurvivalProb_twoFlavor neutrinoMixingAngle_fanoPlane_lockin L E ΔmSq := rfl

theorem neutrinoSurvivalProb_fanoLockin_twoFlavor_withRapidityCP_eq (L E ΔmSq : ℝ) :
    neutrinoSurvivalProb_fanoLockin_twoFlavor_withRapidityCP L E ΔmSq =
      (1 - Real.sin (2 * neutrinoMixingAngle_fanoPlane_lockin) ^ 2 *
        Real.sin (neutrinoOscillationPhase L E ΔmSq + neutrinoCPPhase_skew_from_rapidity) ^ 2) := rfl

/-! ### PDG comparison and age-ratio correction -/

/-!
The paper-level informational-energy relation is

`E_tot = m c^2 + ħ c / Δx`, with `Δx ≤ Θ_local`.

In natural units `c = ħ = 1`, this becomes `E_tot = m + 1 / Δx`. The inequality
`Δx ≤ Θ_local` implies a **lower bound** on the localization contribution:

`1 / Θ_local ≤ 1 / Δx`.

**EW note.** After the electroweak quantum-number lifts, raw `W`/`Z`/`H` witnesses
sit at the tens–hundreds of GeV scale. The published apparent-age ratio
(`ageMassCorrection ≈ 3.7`) was informative when the *pre-lift* closure masses
were \(\mathcal O(1\text{–}10)\) GeV; multiplying \(\sim 80\) GeV by that factor
overshoots PDG entirely. The age/localization **definitions** below remain for
cross-module reuse and for the additive/multiplicative layer identities; we do
not claim they tighten PDG comparison at electroweak scale.
-/

/-- PDG central value for the W boson mass, in GeV. -/
def M_W_PDG : ℝ := 80.377

/-- PDG central value for the Z boson mass, in GeV. -/
def M_Z_PDG : ℝ := 91.1876

/-- PDG central value for the Higgs mass, in GeV. -/
def m_H_PDG : ℝ := 125.11

/-- PDG central pole mass for the muon, in GeV (same listing convention as other PDG centrals here). -/
def m_mu_PDG : ℝ := 105.6583755e-3

/-- PDG central pole mass for the electron, in GeV. -/
def m_e_PDG : ℝ := 0.510998950e-3

/-- Absolute gap between the raw W witness and the PDG central value. -/
noncomputable def M_W_gap_to_PDG : ℝ := |M_W_PDG - M_W_derived|

/-- Absolute gap between the raw Z witness and the PDG central value. -/
noncomputable def M_Z_gap_to_PDG : ℝ := |M_Z_PDG - M_Z_derived|

/-- Absolute gap between the raw scalar witness and the PDG central value. -/
noncomputable def m_H_gap_to_PDG : ℝ := |m_H_PDG - m_H_derived|

/-- Published wall-clock/apparent-age factor used as an optional multiplicative correction. -/
noncomputable def ageMassCorrection : ℝ := age_ratio_paper

/-- Multiply a local mass witness by the published age ratio. -/
noncomputable def ageAdjustedMass (mass : ℝ) : ℝ := ageMassCorrection * mass

/-- Boson-shell local horizon length from the auxiliary-field relation `φ = 2 / Θ_local`. -/
noncomputable def bosonClosureThetaLocal : ℝ :=
  phiTemperatureCoeff / phi_of_shell bosonClosureShell

/-- Minimal localization-energy correction allowed by `Δx ≤ Θ_local`. -/
noncomputable def bosonLocalizationEnergyLowerBound : ℝ :=
  1 / bosonClosureThetaLocal

/-- Horizon-localized boson witness: raw closure mass plus the minimal `1 / Θ_local` term. -/
noncomputable def horizonLocalizedBosonMass (mass : ℝ) : ℝ :=
  mass + bosonLocalizationEnergyLowerBound

/-- Age + horizon coupling applied together: same shell controls both the local energy term and age rescaling. -/
noncomputable def ageAndHorizonAdjustedMass (mass : ℝ) : ℝ :=
  ageMassCorrection * horizonLocalizedBosonMass mass

noncomputable def M_W_ageAdjusted : ℝ := ageAdjustedMass M_W_derived
noncomputable def M_Z_ageAdjusted : ℝ := ageAdjustedMass M_Z_derived
noncomputable def m_H_ageAdjusted : ℝ := ageAdjustedMass m_H_derived

noncomputable def M_W_horizonLocalized : ℝ := horizonLocalizedBosonMass M_W_derived
noncomputable def M_Z_horizonLocalized : ℝ := horizonLocalizedBosonMass M_Z_derived
noncomputable def m_H_horizonLocalized : ℝ := horizonLocalizedBosonMass m_H_derived

noncomputable def M_W_ageAndHorizonAdjusted : ℝ := ageAndHorizonAdjustedMass M_W_derived
noncomputable def M_Z_ageAndHorizonAdjusted : ℝ := ageAndHorizonAdjustedMass M_Z_derived
noncomputable def m_H_ageAndHorizonAdjusted : ℝ := ageAndHorizonAdjustedMass m_H_derived

/-- Absolute gap after multiplying by the published age ratio. -/
noncomputable def M_W_ageAdjusted_gap_to_PDG : ℝ := |M_W_PDG - M_W_ageAdjusted|
noncomputable def M_Z_ageAdjusted_gap_to_PDG : ℝ := |M_Z_PDG - M_Z_ageAdjusted|
noncomputable def m_H_ageAdjusted_gap_to_PDG : ℝ := |m_H_PDG - m_H_ageAdjusted|

/-- Absolute gap after adding the minimal horizon-localization term and then applying age compression. -/
noncomputable def M_W_ageAndHorizonAdjusted_gap_to_PDG : ℝ := |M_W_PDG - M_W_ageAndHorizonAdjusted|
noncomputable def M_Z_ageAndHorizonAdjusted_gap_to_PDG : ℝ := |M_Z_PDG - M_Z_ageAndHorizonAdjusted|
noncomputable def m_H_ageAndHorizonAdjusted_gap_to_PDG : ℝ := |m_H_PDG - m_H_ageAndHorizonAdjusted|

/-- Required multiplicative factor to hit the W central value exactly. -/
noncomputable def M_W_required_factor_to_PDG : ℝ := M_W_PDG / M_W_derived

/-- Required multiplicative factor to hit the Z central value exactly. -/
noncomputable def M_Z_required_factor_to_PDG : ℝ := M_Z_PDG / M_Z_derived

/-- Required multiplicative factor to hit the scalar central value exactly. -/
noncomputable def m_H_required_factor_to_PDG : ℝ := m_H_PDG / m_H_derived

theorem boson_witness_M_W : M_W_derived = (392 : ℝ) / 5 := by
  unfold M_W_derived gaugeBosonMassFromVevGauge su2CouplingDerived vacuumExpectationValueGauge
    vacuumExpectationValue bosonClosureShell ewGaugeSectorQuantumLift outerClosureMonogamyLift
    gammaDerived trialityOrder chargedLeptonSmDoubletCount
  rw [T_lockin_eq_T_referenceM, T_eq]
  simp only [referenceM, qcdShell, stepsFromQCDToLockin, latticeStepCount, outerHorizonSurface,
    latticeSimplexCount_eq, alpha]
  norm_num

theorem boson_witness_m_H : m_H_derived = (588 : ℝ) / 5 := by
  unfold m_H_derived vacuumExpectationValueScalar ewScalarSectorQuantumLift vacuumExpectationValue
    bosonClosureShell outerClosureMonogamyLift gammaDerived trialityOrder chargedLeptonSmDoubletCount
  rw [T_lockin_eq_T_referenceM, T_eq]
  simp only [referenceM, qcdShell, stepsFromQCDToLockin, latticeStepCount, outerHorizonSurface, alpha]
  norm_num

theorem boson_witness_M_Z : M_Z_derived = (2744 : ℝ) / 25 := by
  rw [M_Z_derived_eq_W_times_one_plus_gamma, boson_witness_M_W]
  simp [gammaDerived, alpha]
  norm_num

theorem boson_witness_values :
    M_W_derived = (392 : ℝ) / 5 ∧
      M_Z_derived = (2744 : ℝ) / 25 ∧
      m_H_derived = (588 : ℝ) / 5 :=
  ⟨boson_witness_M_W, boson_witness_M_Z, boson_witness_m_H⟩

theorem M_W_derived_pos : 0 < M_W_derived := by
  rw [boson_witness_M_W]
  norm_num

theorem M_Z_derived_pos : 0 < M_Z_derived := by
  rw [boson_witness_M_Z]
  norm_num

theorem M_W_derived_lt_M_Z_derived : M_W_derived < M_Z_derived := by
  rw [M_Z_derived_eq_W_times_one_plus_gamma]
  have hγ : 0 < gammaDerived := by
    unfold gammaDerived alpha
    norm_num
  have hone : 1 < 1 + gammaDerived := lt_add_of_pos_right 1 hγ
  have hW : 0 < M_W_derived := M_W_derived_pos
  have hmul : (1 : ℝ) * M_W_derived < (1 + gammaDerived) * M_W_derived :=
    mul_lt_mul_of_pos_right hone hW
  simpa using hmul

theorem m_nu_e_derived_lt_M_Z_derived : m_nu_e_derived < M_Z_derived := by
  rw [m_nu_e_derived_eq_suppression_times_M_Z, outerHorizonNeutrinoSuppression_eq_inv_140]
  have hZ : 0 < M_Z_derived := M_Z_derived_pos
  have hone : (1 : ℝ) / 140 < 1 := by norm_num
  have hmul : (1 / 140 : ℝ) * M_Z_derived < 1 * M_Z_derived := mul_lt_mul_of_pos_right hone hZ
  simpa using hmul

theorem m_nu_mu_derived_lt_m_nu_e_derived : m_nu_mu_derived < m_nu_e_derived := by
  unfold m_nu_mu_derived
  have hν : 0 < m_nu_e_derived := by
    rw [m_nu_e_derived_eq_suppression_times_M_Z]
    exact mul_pos outerHorizonNeutrinoSuppression_pos M_Z_derived_pos
  simpa [one_mul] using mul_lt_mul_of_pos_right outerHorizonNeutrinoSuppression_lt_one hν

theorem m_nu_tau_derived_lt_m_nu_mu_derived : m_nu_tau_derived < m_nu_mu_derived := by
  unfold m_nu_tau_derived
  have hμ : 0 < m_nu_mu_derived := by
    unfold m_nu_mu_derived
    rw [m_nu_e_derived_eq_suppression_times_M_Z]
    refine mul_pos outerHorizonNeutrinoSuppression_pos ?_
    exact mul_pos outerHorizonNeutrinoSuppression_pos M_Z_derived_pos
  simpa [one_mul] using mul_lt_mul_of_pos_right outerHorizonNeutrinoSuppression_lt_one hμ

/-- Strict generation order on the **derived** ν ladder from repeated `outerHorizonNeutrinoSuppression`. -/
theorem neutrino_derived_mass_ladder_strict :
    m_nu_tau_derived < m_nu_mu_derived ∧ m_nu_mu_derived < m_nu_e_derived :=
  ⟨m_nu_tau_derived_lt_m_nu_mu_derived, m_nu_mu_derived_lt_m_nu_e_derived⟩

theorem M_Z_derived_lt_one_twenty : M_Z_derived < 120 := by
  rw [boson_witness_M_Z]
  norm_num

/-- `W` and Higgs sit below PDG centrals; neutral closure without weak mixing sits **above** `M_Z` PDG. -/
theorem raw_ew_boson_W_H_below_PDG_Z_above :
    M_W_derived < M_W_PDG ∧ M_Z_PDG < M_Z_derived ∧ m_H_derived < m_H_PDG := by
  refine And.intro ?_ (And.intro ?_ ?_)
  · rw [boson_witness_M_W]; unfold M_W_PDG; norm_num
  · rw [boson_witness_M_Z]; unfold M_Z_PDG; norm_num
  · rw [boson_witness_m_H]; unfold m_H_PDG; norm_num

theorem ageMassCorrection_value :
    ageMassCorrection = 51.2 / 13.8 := by
  rfl

theorem bosonClosureThetaLocal_value :
    bosonClosureThetaLocal = 1 / 6 := by
  unfold bosonClosureThetaLocal
  rw [phi_of_shell_closed_form]
  norm_num [phiTemperatureCoeff, bosonClosureShell, referenceM, qcdShell, stepsFromQCDToLockin,
    latticeStepCount]

theorem bosonLocalizationEnergyLowerBound_value :
    bosonLocalizationEnergyLowerBound = 6 := by
  unfold bosonLocalizationEnergyLowerBound
  rw [bosonClosureThetaLocal_value]
  norm_num

theorem ageMassCorrection_gt_one : 1 < ageMassCorrection := by
  unfold ageMassCorrection age_ratio_paper age_wall_clock_Gyr_paper age_apparent_Gyr_paper
  norm_num

theorem bosonLocalizationEnergyLowerBound_pos : 0 < bosonLocalizationEnergyLowerBound := by
  rw [bosonLocalizationEnergyLowerBound_value]
  norm_num

/-- Published-age comparison layer is exactly multiplicative on the raw local witness. -/
theorem published_age_layer_eq_mul_raw (mass : ℝ) :
    ageAdjustedMass mass = ageMassCorrection * mass := rfl

/-- Horizon-localization comparison layer is exactly additive on the raw local witness. -/
theorem horizon_localization_layer_eq_add_raw (mass : ℝ) :
    horizonLocalizedBosonMass mass = mass + bosonLocalizationEnergyLowerBound := rfl

/-- Combined comparison layer: apply the published age ratio after the local horizon term is added. -/
theorem age_and_horizon_layer_eq_age_of_horizon_localized (mass : ℝ) :
    ageAndHorizonAdjustedMass mass = ageMassCorrection * (mass + bosonLocalizationEnergyLowerBound) := rfl

/-- Same combined layer written as the age-adjusted raw mass plus the age-adjusted localization term. -/
theorem age_and_horizon_layer_eq_age_plus_localization (mass : ℝ) :
    ageAndHorizonAdjustedMass mass =
      ageAdjustedMass mass + ageMassCorrection * bosonLocalizationEnergyLowerBound := by
  unfold ageAndHorizonAdjustedMass ageAdjustedMass horizonLocalizedBosonMass
  ring

/-- For positive raw local witnesses, the published-age layer is strictly above the raw local layer. -/
theorem ageAdjustedMass_gt_raw {mass : ℝ} (hmass : 0 < mass) :
    mass < ageAdjustedMass mass := by
  rw [published_age_layer_eq_mul_raw]
  have hfac : 1 < ageMassCorrection := ageMassCorrection_gt_one
  nlinarith

/-- For positive raw local witnesses, adding the local horizon term strictly raises the witness. -/
theorem horizonLocalizedBosonMass_gt_raw {mass : ℝ} :
    mass < horizonLocalizedBosonMass mass := by
  rw [horizon_localization_layer_eq_add_raw]
  have hloc : 0 < bosonLocalizationEnergyLowerBound := bosonLocalizationEnergyLowerBound_pos
  linarith

/-- For positive raw local witnesses, the age+horizon layer is strictly above the age-only layer. -/
theorem ageAndHorizonAdjustedMass_gt_ageAdjusted {mass : ℝ} :
    ageAdjustedMass mass < ageAndHorizonAdjustedMass mass := by
  rw [published_age_layer_eq_mul_raw, age_and_horizon_layer_eq_age_of_horizon_localized]
  have hfac : 0 < ageMassCorrection := by linarith [ageMassCorrection_gt_one]
  have hloc : 0 < bosonLocalizationEnergyLowerBound := bosonLocalizationEnergyLowerBound_pos
  nlinarith

theorem M_Z_derived_gt_hundred : (100 : ℝ) < M_Z_derived := by
  rw [boson_witness_M_Z]
  norm_num

theorem M_Z_derived_gt_eighty_nine : (89 : ℝ) < M_Z_derived := by
  linarith [M_Z_derived_gt_hundred]

theorem age_adjusted_boson_witness_values :
    M_W_ageAdjusted = (392 : ℝ) / 5 * ageMassCorrection ∧
      M_Z_ageAdjusted = M_Z_derived * ageMassCorrection ∧
      m_H_ageAdjusted = (588 : ℝ) / 5 * ageMassCorrection := by
  refine And.intro ?_ (And.intro ?_ ?_)
  · unfold M_W_ageAdjusted ageAdjustedMass; rw [boson_witness_M_W]; ring
  · unfold M_Z_ageAdjusted ageAdjustedMass; ring
  · unfold m_H_ageAdjusted ageAdjustedMass; rw [boson_witness_m_H]; ring

theorem horizon_localized_boson_witness_values :
    M_W_horizonLocalized = (392 : ℝ) / 5 + bosonLocalizationEnergyLowerBound ∧
      M_Z_horizonLocalized = M_Z_derived + bosonLocalizationEnergyLowerBound ∧
      m_H_horizonLocalized = (588 : ℝ) / 5 + bosonLocalizationEnergyLowerBound := by
  refine And.intro ?_ (And.intro ?_ ?_)
  · simp [M_W_horizonLocalized, horizonLocalizedBosonMass, boson_witness_M_W]
  · simp [M_Z_horizonLocalized, horizonLocalizedBosonMass]
  · simp [m_H_horizonLocalized, horizonLocalizedBosonMass, boson_witness_m_H]

theorem age_and_horizon_adjusted_boson_witness_values :
    M_W_ageAndHorizonAdjusted =
        ageMassCorrection * ((392 : ℝ) / 5 + bosonLocalizationEnergyLowerBound) ∧
      M_Z_ageAndHorizonAdjusted =
        ageMassCorrection * (M_Z_derived + bosonLocalizationEnergyLowerBound) ∧
      m_H_ageAndHorizonAdjusted =
        ageMassCorrection * ((588 : ℝ) / 5 + bosonLocalizationEnergyLowerBound) := by
  refine And.intro ?_ (And.intro ?_ ?_)
  · simp [M_W_ageAndHorizonAdjusted, ageAndHorizonAdjustedMass, horizonLocalizedBosonMass,
      boson_witness_M_W, bosonLocalizationEnergyLowerBound_value]
  · simp [M_Z_ageAndHorizonAdjusted, ageAndHorizonAdjustedMass, horizonLocalizedBosonMass,
      bosonLocalizationEnergyLowerBound_value]
  · simp [m_H_ageAndHorizonAdjusted, ageAndHorizonAdjustedMass, horizonLocalizedBosonMass,
      boson_witness_m_H, bosonLocalizationEnergyLowerBound_value]

/-- The three comparison layers are strictly ordered on the W witness:
raw local closure < published age compression < age+horizon comparison. -/
theorem M_W_raw_lt_age_lt_ageAndHorizon :
    M_W_derived < M_W_ageAdjusted ∧ M_W_ageAdjusted < M_W_ageAndHorizonAdjusted := by
  refine And.intro ?_ ?_
  · exact ageAdjustedMass_gt_raw (by rw [boson_witness_M_W]; norm_num)
  · exact ageAndHorizonAdjustedMass_gt_ageAdjusted

/-- The three comparison layers are strictly ordered on the Z witness. -/
theorem M_Z_raw_lt_age_lt_ageAndHorizon :
    M_Z_derived < M_Z_ageAdjusted ∧ M_Z_ageAdjusted < M_Z_ageAndHorizonAdjusted := by
  refine And.intro ?_ ?_
  · exact ageAdjustedMass_gt_raw (by linarith [M_Z_derived_gt_eighty_nine])
  · exact ageAndHorizonAdjustedMass_gt_ageAdjusted

/-- The three comparison layers are strictly ordered on the Higgs witness. -/
theorem m_H_raw_lt_age_lt_ageAndHorizon :
    m_H_derived < m_H_ageAdjusted ∧ m_H_ageAdjusted < m_H_ageAndHorizonAdjusted := by
  refine And.intro ?_ ?_
  · exact ageAdjustedMass_gt_raw (by rw [boson_witness_m_H]; norm_num)
  · exact ageAndHorizonAdjustedMass_gt_ageAdjusted

/-- After EW-scale quantum lifts, multiplying by the published age ratio overshoots PDG centrals. -/
theorem age_adjusted_boson_masses_exceed_PDG_centrals :
    M_W_PDG < M_W_ageAdjusted ∧ M_Z_PDG < M_Z_ageAdjusted ∧ m_H_PDG < m_H_ageAdjusted := by
  refine And.intro ?_ (And.intro ?_ ?_)
  · unfold M_W_ageAdjusted ageAdjustedMass ageMassCorrection age_ratio_paper M_W_PDG
    rw [boson_witness_M_W]
    norm_num [age_wall_clock_Gyr_paper, age_apparent_Gyr_paper]
  · unfold M_Z_ageAdjusted ageAdjustedMass M_Z_PDG
    have hage_pos : 0 < ageMassCorrection := by linarith [ageMassCorrection_gt_one]
    have hub : M_Z_PDG < (100 : ℝ) * ageMassCorrection := by
      unfold ageMassCorrection age_ratio_paper M_Z_PDG
      norm_num [age_wall_clock_Gyr_paper, age_apparent_Gyr_paper]
    have hcmp : (100 : ℝ) * ageMassCorrection < ageMassCorrection * M_Z_derived := by
      simpa [mul_comm] using mul_lt_mul_of_pos_right M_Z_derived_gt_hundred hage_pos
    exact lt_trans hub hcmp
  · unfold m_H_ageAdjusted ageAdjustedMass ageMassCorrection age_ratio_paper m_H_PDG
    rw [boson_witness_m_H]
    norm_num [age_wall_clock_Gyr_paper, age_apparent_Gyr_paper]

theorem published_age_ratio_exceeds_multiplicative_PDG_closure_for_W :
    M_W_required_factor_to_PDG < ageMassCorrection := by
  unfold M_W_required_factor_to_PDG ageMassCorrection age_ratio_paper M_W_PDG
  rw [boson_witness_M_W]
  norm_num [age_wall_clock_Gyr_paper, age_apparent_Gyr_paper]
end Hqiv.Physics

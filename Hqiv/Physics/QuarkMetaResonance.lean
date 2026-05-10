import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.Fin.Basic
import Hqiv.Physics.FanoResonance
import Hqiv.Physics.ChargedLeptonResonance
import Hqiv.Physics.BoundStates
import Hqiv.Physics.ModalFrequencyHorizon
import Hqiv.Physics.QuarterPeriodRelaxation
import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.BaryogenesisCore
import Hqiv.Geometry.HQVMetric
import Hqiv.Physics.GRFromMaxwell

namespace Hqiv.Physics

/-!
# Quark meta-horizon resonance ladder

**Core physics story:** SM fermions occupy **three generation slots** because the octonionic /
**Spin(8)** packaging and **triality** identify `Fin 3` with `Hqiv.Algebra.So8RepIndex` (`SMEmbedding`,
`AnomalyCancellation`). **This repository** proves the **three-representation / So8RepIndex** strain
inside the formalized **SO(8) / octonion** stack, not a larger exceptional Lie closure beyond what
those modules import. **Resonance** is driven by **horizon-area readouts** (`shellSurface`, detuned
variants) and geometric ratios; natural indices are **readout coordinates** for evaluating those
functionals, not a claim that wave support is pointlike on one row.

This module keeps the internal three-harmonic ladder for quarks, but exports the nucleon mass story
through a **single HQIV spine**:

* evaluations at the lock-in **representative index** `referenceM` (currently `qcdShell + 3`),
* `alphaEffAtShell referenceM` and `latticeSimplexCount referenceM`,
* an explicit multi-channel 8×8 composite-trace witness,
* constituent masses only for the proton/neutron outputs.

The light/heavy **readout anchors** (`m_quark_up_*`, `m_quark_down_*`) remain explicit calibration inputs,
but hadron exports no longer depend on PDG-closeness lemmas. The proton is read bottom-up from the same
quark ladder plus composite-trace binding spine, rather than being held fixed by a numeral-as-physics
boundary condition.

**Geometry-first quark track (separate import cone):** `Hqiv.Physics.QuarkResonanceMassFunctional` packages
the τ-resonance assignment `m_tau_Pl * (1 / resonanceProduct ρ)` on `So8RepIndex` — the same template as
`SM_GR_Unification.smMassFromGeometry` / quark labels there, without the GeV anchors of *this* file.
`Hqiv.Physics.QuarkSectorFromEWGauge` is the parallel **blank slate** using `vacuumExpectationValueGauge`
instead of `m_tau_Pl`, with the same resonance ratios and a proved contact `heavy slot × su2 = M_W`.
Wiring nucleon **constituent** MeV sums to that track plus an EW-derived unit conversion is not done here.

**Witness honesty:** GeV anchors such as `m_top_GeV` (and legacy `m_bottom_GeV` on the down branch) and
the natural-number **readout triples** `m_quark_up_*` / `m_quark_down_*` are **inputs** to the ratio
machinery. The formalism reuses the **same** `geometricResonanceStep` / `detunedShellSurface` layer as
charged leptons; uniqueness of those anchors or a first-principles replacement is **out of scope**
here—present this module as **one consistent ladder**, not as a uniqueness theorem for the tables.

This module encodes a single three-harmonic internal ladder for quarks (generation index `Fin 3`,
defeq to `Hqiv.Algebra.So8RepIndex` used in `ChargedLeptonResonance` / `SM_GR_Unification`):

* **Lock-in narrative:** the top quark birth readout is pinned at `referenceM` (`m_top_at_lockin`),
  aligned with baryogenesis lock-in (`T_lockin`).
* **Geometric steps (same as charged leptons):** the two internal octave factors are
  **ratios of detuned horizon-area readouts** `geometricResonanceStep m_heavy m_lighter`
  (`FanoResonance.detunedShellSurface`), not mass-table ratios.
* **Readout triples:** explicit `m_quark_up_*` and `m_quark_down_*` supply the internal resonance
  ordering used by the generation ladder.

Up/down split: hypercharge sign metadata on the Fano axes (`upResonanceAxis` / `downResonanceAxis`).

Lepton-side lock-in alignment lives in `ChargedLeptonResonance` / `SM_GR_Unification`; ν from
`DerivedGaugeAndLeptonSector`.

**Integration (plasma / inertia):** collective plasmas and lapse- or φ-modified inertia are
not modeled here; they enter through shared EM/O-Maxwell and metric sectors.

**Proved structural link to O-Maxwell / monogamy:** `QuarkOMaxwellBridge.lean` packages Fano vertex
placement for the canonical quark axes, factorizes internal steps as `geometricResonanceStep`, and
records that Rindler detuning uses `γ/2` while the O-Maxwell EL `a = 0` slot uses `α`, with `α+γ=1`.

This file now also exposes modal-frequency / interaction-horizon readout wrappers so the public quark
and color-composed ladders can be viewed as downstream readouts from the **modal-first** layer in
`ModalFrequencyHorizon`.

**Sphere-split relaxation:** `topRelaxedQuarterSpec` / `bottomRelaxedQuarterSpec` use the legacy `S⁷`
weight; `topRelaxedQuarterSpecS4` / `bottomRelaxedQuarterSpecS4` and the `*_relaxedQuarterS4_*`
mass/compression API mirror the same readout anchors with the `S⁴` Laplace bridge from
`QuarterPeriodRelaxation`.
-/

/-- Internal meta-horizon surface area from the leading horizon-area term (`shellSurface`). -/
def internalSurfaceArea (m : ℕ) : ℝ :=
  shellSurface m

/-- Top birth shell is fixed at lock-in (`referenceM`). -/
def m_top_at_lockin : ℕ := referenceM

/-- Allowed resonance bands on the color-composed rung. The public resonance ladder is now exposed
heavy/mid/light first; SM flavor labels remain secondary metadata. -/
inductive AllowedColorResonanceBand
  | light
  | mid
  | heavy
  deriving DecidableEq, Repr

/-- Internal residual channels carried by the octonion-loop bookkeeping. -/
inductive ResidualChargeChannel
  | upLike
  | downLike
  deriving DecidableEq, Repr

/-- Convert the public heavy/mid/light resonance band to the existing generation index. -/
def AllowedColorResonanceBand.toGenerationIndex : AllowedColorResonanceBand → Fin 3
  | .light => ⟨0, by decide⟩
  | .mid => ⟨1, by decide⟩
  | .heavy => ⟨2, by decide⟩

/-- Integer loop multiplicity left by the simple octonionic residual loop on each channel.
`upLike` carries two positive quanta, while `downLike` carries one negative quantum. -/
def ResidualChargeChannel.loopMultiplicity : ResidualChargeChannel → Int
  | .upLike => 2
  | .downLike => -1

/-- Shared denominator for quark residuals: the color-composed rung carries three active channels. -/
def colorComposedResidualDenominator : ℚ := 3

/-- Fractional residual metadata derived from simple loop multiplicity over the color-composed
denominator rather than postulated directly. -/
def ResidualChargeChannel.toRat : ResidualChargeChannel → ℚ
  | q => q.loopMultiplicity / colorComposedResidualDenominator

/-!
### Up-type readout triple (heavy > mid > light)

Explicit **ℕ** readout coordinates fed into `geometricResonanceStep` for the up-type ladder. They
determine `resonanceK_internal` and hence **charm/up masses given** `m_top_GeV`. They are **calibration
witnesses**, not unique minimizers proved from the null lattice in this module.
-/

def m_quark_up_top_shell : ℕ := 31382
def m_quark_up_charm_shell : ℕ := 233
def m_quark_up_light_shell : ℕ := 0

/-!
### Down-type readout triple

Same role as the up-type triple for `resonanceK_internal_down`. Together with `m_bottom_GeV` (legacy
heavy anchor on this branch) they fix strange/down **ratios**.
-/

def m_quark_down_bottom_shell : ℕ := 5329
def m_quark_down_strange_shell : ℕ := 123
def m_quark_down_light_shell : ℕ := 7

/--
**Heavy up-type mass anchor (GeV).** PDG-style central pole mass for the top quark, used as the **absolute
scale** for the up-type resonance ladder in this file.

**Downstream (same module):** `m_charm_GeV := m_top_GeV / resonanceK_internal 0`,
`m_up_GeV := m_charm_GeV / resonanceK_internal 1`, with each `resonanceK_internal _` a
`geometricResonanceStep` ratio between the readout triple above. The **machinery** is the same
detuned-surface formalism as charged leptons; the **numeral** is an external SM calibration witness.
-/
def m_top_GeV : ℝ := 172.57

/--
**Heavy down-type GeV witness** for the bottom of the down ladder (PDG-style listing; MS-bar vs pole
as in the paper alignment for this repo—not re-derived here).

**Role:** fixes `m_strange_GeV`, `m_down_GeV` through `resonanceK_internal_down` on the down shell
triple. The public color-resonance API also **cross-detunes** the heavy down band from the top-anchored
up channel; this literal remains the **down-branch absolute normalization** unless replaced by a new
closure theorem.
-/
def m_bottom_GeV : ℝ := 4.18

/-- Two internal octave drops for the up-type side (top→charm, charm→up), from detuned surfaces. -/
noncomputable def resonanceK_internal (step : Fin 2) : ℝ :=
  match step with
  | ⟨0, _⟩ => geometricResonanceStep m_quark_up_top_shell m_quark_up_charm_shell
  | ⟨1, _⟩ => geometricResonanceStep m_quark_up_charm_shell m_quark_up_light_shell

/-- Two internal octave drops for the down-type side (bottom→strange, strange→down). -/
noncomputable def resonanceK_internal_down (step : Fin 2) : ℝ :=
  match step with
  | ⟨0, _⟩ => geometricResonanceStep m_quark_down_bottom_shell m_quark_down_strange_shell
  | ⟨1, _⟩ => geometricResonanceStep m_quark_down_strange_shell m_quark_down_light_shell

/-- Three-jet up-side internal drops (top→charm, charm→up) from `detunedShellSurfaceThreeJet`. -/
noncomputable def resonanceK_internal_threeJet (step : Fin 2) : ℝ :=
  match step with
  | ⟨0, _⟩ => geometricResonanceStepThreeJet m_quark_up_top_shell m_quark_up_charm_shell
  | ⟨1, _⟩ => geometricResonanceStepThreeJet m_quark_up_charm_shell m_quark_up_light_shell

/-- Three-jet down-side internal drops (bottom→strange, strange→down). -/
noncomputable def resonanceK_internal_down_threeJet (step : Fin 2) : ℝ :=
  match step with
  | ⟨0, _⟩ => geometricResonanceStepThreeJet m_quark_down_bottom_shell m_quark_down_strange_shell
  | ⟨1, _⟩ => geometricResonanceStepThreeJet m_quark_down_strange_shell m_quark_down_light_shell

/-- Relaxed quarter-period spec for the heavy up-like lock-in channel (cubic + `S⁷` mode). -/
noncomputable def topRelaxedQuarterSpec : RelaxedQuarterModalSpec :=
  relaxedQuarterModalFromShellNominal Hqiv.Algebra.rep8SPlus 2 m_quark_up_top_shell

/-- Relaxed quarter-period spec for the heavy down-like channel. -/
noncomputable def bottomRelaxedQuarterSpec : RelaxedQuarterModalSpec :=
  relaxedQuarterModalFromShellNominal Hqiv.Algebra.rep8V 2 m_quark_down_bottom_shell

/-- Heavy up-like channel with **`S⁴`** Laplace weight (O-extension shell beyond quaternion `S³`). -/
noncomputable def topRelaxedQuarterSpecS4 : RelaxedQuarterModalSpec :=
  relaxedQuarterModalFromShellNominalS4 Hqiv.Algebra.rep8SPlus 2 m_quark_up_top_shell

/-- Heavy down-like channel with **`S⁴`** weight. -/
noncomputable def bottomRelaxedQuarterSpecS4 : RelaxedQuarterModalSpec :=
  relaxedQuarterModalFromShellNominalS4 Hqiv.Algebra.rep8V 2 m_quark_down_bottom_shell

/-- Relaxed-quarter up-side internal drops (top→charm, charm→up). -/
noncomputable def resonanceK_internal_relaxedQuarter (step : Fin 2) : ℝ :=
  match step with
  | ⟨0, _⟩ =>
      topRelaxedQuarterSpec.relaxedGeometricStepReadout m_quark_up_top_shell m_quark_up_charm_shell
  | ⟨1, _⟩ =>
      topRelaxedQuarterSpec.relaxedGeometricStepReadout m_quark_up_charm_shell m_quark_up_light_shell

/-- Relaxed-quarter down-side internal drops (bottom→strange, strange→down). -/
noncomputable def resonanceK_internal_down_relaxedQuarter (step : Fin 2) : ℝ :=
  match step with
  | ⟨0, _⟩ =>
      bottomRelaxedQuarterSpec.relaxedGeometricStepReadout
        m_quark_down_bottom_shell m_quark_down_strange_shell
  | ⟨1, _⟩ =>
      bottomRelaxedQuarterSpec.relaxedGeometricStepReadout
        m_quark_down_strange_shell m_quark_down_light_shell

/-- Relaxed-quarter up-side internal drops with **`S⁴`** spectral weight. -/
noncomputable def resonanceK_internal_relaxedQuarterS4 (step : Fin 2) : ℝ :=
  match step with
  | ⟨0, _⟩ =>
      topRelaxedQuarterSpecS4.relaxedGeometricStepReadout m_quark_up_top_shell m_quark_up_charm_shell
  | ⟨1, _⟩ =>
      topRelaxedQuarterSpecS4.relaxedGeometricStepReadout m_quark_up_charm_shell m_quark_up_light_shell

/-- Relaxed-quarter down-side internal drops with **`S⁴`** weight. -/
noncomputable def resonanceK_internal_down_relaxedQuarterS4 (step : Fin 2) : ℝ :=
  match step with
  | ⟨0, _⟩ =>
      bottomRelaxedQuarterSpecS4.relaxedGeometricStepReadout
        m_quark_down_bottom_shell m_quark_down_strange_shell
  | ⟨1, _⟩ =>
      bottomRelaxedQuarterSpecS4.relaxedGeometricStepReadout
        m_quark_down_strange_shell m_quark_down_light_shell

/-- Derived charm mass (GeV) from top anchor and first geometric step. -/
noncomputable def m_charm_GeV : ℝ := m_top_GeV / resonanceK_internal ⟨0, by decide⟩

/-- Derived up mass (GeV). -/
noncomputable def m_up_GeV : ℝ := m_charm_GeV / resonanceK_internal ⟨1, by decide⟩

/-- Derived strange mass (GeV). -/
noncomputable def m_strange_GeV : ℝ := m_bottom_GeV / resonanceK_internal_down ⟨0, by decide⟩

/-- Derived down mass (GeV). -/
noncomputable def m_down_GeV : ℝ := m_strange_GeV / resonanceK_internal_down ⟨1, by decide⟩

/-- Three-jet charm candidate from the top anchor. -/
noncomputable def m_charm_threeJet_GeV : ℝ := m_top_GeV / resonanceK_internal_threeJet ⟨0, by decide⟩

/-- Three-jet up candidate from the three-jet charm value. -/
noncomputable def m_up_threeJet_GeV : ℝ :=
  m_charm_threeJet_GeV / resonanceK_internal_threeJet ⟨1, by decide⟩

/-- Three-jet strange candidate from the bottom witness. -/
noncomputable def m_strange_threeJet_GeV : ℝ :=
  m_bottom_GeV / resonanceK_internal_down_threeJet ⟨0, by decide⟩

/-- Three-jet down candidate from the three-jet strange value. -/
noncomputable def m_down_threeJet_GeV : ℝ :=
  m_strange_threeJet_GeV / resonanceK_internal_down_threeJet ⟨1, by decide⟩

/-- Relaxed-quarter charm candidate from the top anchor. -/
noncomputable def m_charm_relaxedQuarter_GeV : ℝ :=
  m_top_GeV / resonanceK_internal_relaxedQuarter ⟨0, by decide⟩

/-- Relaxed-quarter up candidate from the relaxed-quarter charm value. -/
noncomputable def m_up_relaxedQuarter_GeV : ℝ :=
  m_charm_relaxedQuarter_GeV / resonanceK_internal_relaxedQuarter ⟨1, by decide⟩

/-- Relaxed-quarter strange candidate from the bottom witness. -/
noncomputable def m_strange_relaxedQuarter_GeV : ℝ :=
  m_bottom_GeV / resonanceK_internal_down_relaxedQuarter ⟨0, by decide⟩

/-- Relaxed-quarter down candidate from the relaxed-quarter strange value. -/
noncomputable def m_down_relaxedQuarter_GeV : ℝ :=
  m_strange_relaxedQuarter_GeV / resonanceK_internal_down_relaxedQuarter ⟨1, by decide⟩

/-- Relaxed-quarter charm candidate (`S⁴` weight) from the top anchor. -/
noncomputable def m_charm_relaxedQuarterS4_GeV : ℝ :=
  m_top_GeV / resonanceK_internal_relaxedQuarterS4 ⟨0, by decide⟩

/-- Relaxed-quarter up candidate (`S⁴` weight). -/
noncomputable def m_up_relaxedQuarterS4_GeV : ℝ :=
  m_charm_relaxedQuarterS4_GeV / resonanceK_internal_relaxedQuarterS4 ⟨1, by decide⟩

/-- Relaxed-quarter strange candidate (`S⁴` weight) from the bottom witness. -/
noncomputable def m_strange_relaxedQuarterS4_GeV : ℝ :=
  m_bottom_GeV / resonanceK_internal_down_relaxedQuarterS4 ⟨0, by decide⟩

/-- Relaxed-quarter down candidate (`S⁴` weight). -/
noncomputable def m_down_relaxedQuarterS4_GeV : ℝ :=
  m_strange_relaxedQuarterS4_GeV / resonanceK_internal_down_relaxedQuarterS4 ⟨1, by decide⟩

lemma topRelaxedQuarterSpec_base_detuning_ne_zero (m : ℕ) :
    topRelaxedQuarterSpec.base.detuning1Jet m ≠ 0 := by
  unfold topRelaxedQuarterSpec relaxedQuarterModalFromShellNominal
    RelaxedQuarterModalSpec.fromBaseTagged modalFrequencyHorizonFromShellNominal
  change rindlerDetuningShared (m : ℝ) ≠ 0
  have hm : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
  have hpos : 0 < rindlerDetuningShared (m : ℝ) := by
    unfold rindlerDetuningShared c_rindler_shared
    rw [gamma_eq_2_5]
    nlinarith
  exact ne_of_gt hpos

theorem resonanceK_internal_relaxedQuarter_top_charm_abs_le_kinetic_control
    (κ : ℝ) (hκ : 0 ≤ κ) (A : Fin 8 → Fin 4 → ℝ) (x : ℝ)
    (hctrl :
      topRelaxedQuarterSpec.relaxationLoad m_quark_up_charm_shell ≤
        κ * (∑ a : Fin 8, ∑ i : Fin 4, ((Hqiv.Physics.linearEnd (F_from_A A a i (i + 1))) x - x) ^ 2)) :
    |resonanceK_internal_relaxedQuarter ⟨0, by decide⟩| ≤
      |resonanceK_internal ⟨0, by decide⟩| * (1 + κ * ((-4 : ℝ) * L_O_kinetic A)) := by
  have hbase :
      topRelaxedQuarterSpec.base.geometricStepReadout m_quark_up_top_shell m_quark_up_charm_shell =
        resonanceK_internal ⟨0, by decide⟩ := by
    unfold topRelaxedQuarterSpec relaxedQuarterModalFromShellNominal
      RelaxedQuarterModalSpec.fromBaseTagged resonanceK_internal
    rw [geometricStepReadout_fromShellNominal]
  have hdet_top : topRelaxedQuarterSpec.base.detuning1Jet m_quark_up_top_shell ≠ 0 :=
    topRelaxedQuarterSpec_base_detuning_ne_zero m_quark_up_top_shell
  have hdet_charm : topRelaxedQuarterSpec.base.detuning1Jet m_quark_up_charm_shell ≠ 0 :=
    topRelaxedQuarterSpec_base_detuning_ne_zero m_quark_up_charm_shell
  have hmain := RelaxedQuarterModalSpec.abs_relaxedGeometricStepReadout_le_kinetic_control
      (spec := topRelaxedQuarterSpec) m_quark_up_top_shell m_quark_up_charm_shell
      hdet_top hdet_charm κ hκ A x hctrl
  have hmain' :
      |resonanceK_internal_relaxedQuarter ⟨0, by decide⟩| ≤
        |topRelaxedQuarterSpec.base.geometricStepReadout
          m_quark_up_top_shell m_quark_up_charm_shell| *
          (1 + κ * ((-4 : ℝ) * L_O_kinetic A)) := by
    simpa [resonanceK_internal_relaxedQuarter] using hmain
  simpa [hbase] using hmain'

theorem top_over_charm_relaxedQuarter_abs_le_kinetic_control
    (κ : ℝ) (hκ : 0 ≤ κ) (A : Fin 8 → Fin 4 → ℝ) (x : ℝ)
    (hctrl :
      topRelaxedQuarterSpec.relaxationLoad m_quark_up_charm_shell ≤
        κ * (∑ a : Fin 8, ∑ i : Fin 4, ((Hqiv.Physics.linearEnd (F_from_A A a i (i + 1))) x - x) ^ 2)) :
    |m_top_GeV / m_charm_relaxedQuarter_GeV| ≤
      |resonanceK_internal ⟨0, by decide⟩| * (1 + κ * ((-4 : ℝ) * L_O_kinetic A)) := by
  have hratio : m_top_GeV / m_charm_relaxedQuarter_GeV = resonanceK_internal_relaxedQuarter ⟨0, by decide⟩ := by
    unfold m_charm_relaxedQuarter_GeV
    have htop : m_top_GeV ≠ 0 := by norm_num [m_top_GeV]
    field_simp [htop]
  rw [hratio]
  exact resonanceK_internal_relaxedQuarter_top_charm_abs_le_kinetic_control κ hκ A x hctrl

theorem resonanceK_internal_relaxedQuarter_top_charm_abs_ge_kinetic_control
    (κ : ℝ) (hκ : 0 ≤ κ) (A : Fin 8 → Fin 4 → ℝ) (x : ℝ)
    (hctrl_top :
      topRelaxedQuarterSpec.relaxationLoad m_quark_up_top_shell ≤
        κ * (∑ a : Fin 8, ∑ i : Fin 4, ((Hqiv.Physics.linearEnd (F_from_A A a i (i + 1))) x - x) ^ 2)) :
    |resonanceK_internal ⟨0, by decide⟩| / (1 + κ * ((-4 : ℝ) * L_O_kinetic A)) ≤
      |resonanceK_internal_relaxedQuarter ⟨0, by decide⟩| := by
  have hbase :
      topRelaxedQuarterSpec.base.geometricStepReadout m_quark_up_top_shell m_quark_up_charm_shell =
        resonanceK_internal ⟨0, by decide⟩ := by
    unfold topRelaxedQuarterSpec relaxedQuarterModalFromShellNominal
      RelaxedQuarterModalSpec.fromBaseTagged resonanceK_internal
    rw [geometricStepReadout_fromShellNominal]
  have hdet_top : topRelaxedQuarterSpec.base.detuning1Jet m_quark_up_top_shell ≠ 0 :=
    topRelaxedQuarterSpec_base_detuning_ne_zero m_quark_up_top_shell
  have hdet_charm : topRelaxedQuarterSpec.base.detuning1Jet m_quark_up_charm_shell ≠ 0 :=
    topRelaxedQuarterSpec_base_detuning_ne_zero m_quark_up_charm_shell
  have hkrel :
      resonanceK_internal_relaxedQuarter ⟨0, by decide⟩ =
        topRelaxedQuarterSpec.base.geometricStepReadout m_quark_up_top_shell m_quark_up_charm_shell *
          ((1 + topRelaxedQuarterSpec.relaxationLoad m_quark_up_charm_shell) /
            (1 + topRelaxedQuarterSpec.relaxationLoad m_quark_up_top_shell)) := by
    simpa [resonanceK_internal_relaxedQuarter] using
      (RelaxedQuarterModalSpec.relaxedGeometricStepReadout_eq_base_mul_loadRatio
        (spec := topRelaxedQuarterSpec) m_quark_up_top_shell m_quark_up_charm_shell hdet_top hdet_charm)
  have hratio_nonneg :
      0 ≤ (1 + topRelaxedQuarterSpec.relaxationLoad m_quark_up_charm_shell) /
            (1 + topRelaxedQuarterSpec.relaxationLoad m_quark_up_top_shell) := by
    have hnum : 0 ≤ 1 + topRelaxedQuarterSpec.relaxationLoad m_quark_up_charm_shell := by
      linarith [topRelaxedQuarterSpec.relaxationLoad_nonneg m_quark_up_charm_shell]
    have hden : 0 ≤ 1 + topRelaxedQuarterSpec.relaxationLoad m_quark_up_top_shell := by
      linarith [topRelaxedQuarterSpec.relaxationLoad_nonneg m_quark_up_top_shell]
    exact div_nonneg hnum hden
  have hratio_ge :
      (1 / (1 + topRelaxedQuarterSpec.relaxationLoad m_quark_up_top_shell)) ≤
        ((1 + topRelaxedQuarterSpec.relaxationLoad m_quark_up_charm_shell) /
          (1 + topRelaxedQuarterSpec.relaxationLoad m_quark_up_top_shell)) := by
    have hden_pos : 0 < 1 + topRelaxedQuarterSpec.relaxationLoad m_quark_up_top_shell := by
      linarith [topRelaxedQuarterSpec.relaxationLoad_nonneg m_quark_up_top_shell]
    have hnum_ge : (1 : ℝ) ≤ 1 + topRelaxedQuarterSpec.relaxationLoad m_quark_up_charm_shell := by
      linarith [topRelaxedQuarterSpec.relaxationLoad_nonneg m_quark_up_charm_shell]
    exact (le_div_iff₀ hden_pos).2 (by simpa [hden_pos.ne'] using hnum_ge)
  have hbudget : (∑ a : Fin 8, ∑ i : Fin 4, ((Hqiv.Physics.linearEnd (F_from_A A a i (i + 1))) x - x) ^ 2) ≤
      ((-4 : ℝ) * L_O_kinetic A) := (Hqiv.Physics.cyclic_wilson_defect_sum_bounds_from_kinetic A x).2
  have hload_top_le :
      topRelaxedQuarterSpec.relaxationLoad m_quark_up_top_shell ≤ κ * ((-4 : ℝ) * L_O_kinetic A) := by
    exact le_trans hctrl_top (mul_le_mul_of_nonneg_left hbudget hκ)
  have hsum_nonneg :
      0 ≤ ∑ a : Fin 8, ∑ i : Fin 4, ((Hqiv.Physics.linearEnd (F_from_A A a i (i + 1))) x - x) ^ 2 := by
    refine Finset.sum_nonneg ?_
    intro a ha
    refine Finset.sum_nonneg ?_
    intro i hi
    exact sq_nonneg _
  have hM_nonneg : 0 ≤ κ * ((-4 : ℝ) * L_O_kinetic A) := by
    have hκsum : 0 ≤ κ *
        (∑ a : Fin 8, ∑ i : Fin 4, ((Hqiv.Physics.linearEnd (F_from_A A a i (i + 1))) x - x) ^ 2) :=
      mul_nonneg hκ hsum_nonneg
    have hκbudget :
        κ * (∑ a : Fin 8, ∑ i : Fin 4, ((Hqiv.Physics.linearEnd (F_from_A A a i (i + 1))) x - x) ^ 2) ≤
          κ * ((-4 : ℝ) * L_O_kinetic A) := mul_le_mul_of_nonneg_left hbudget hκ
    exact le_trans hκsum hκbudget
  have hD_pos : 0 < 1 + topRelaxedQuarterSpec.relaxationLoad m_quark_up_top_shell := by
    linarith [topRelaxedQuarterSpec.relaxationLoad_nonneg m_quark_up_top_shell]
  have hM_pos : 0 < 1 + κ * ((-4 : ℝ) * L_O_kinetic A) := by linarith
  have hrecip :
      (1 / (1 + κ * ((-4 : ℝ) * L_O_kinetic A))) ≤
        (1 / (1 + topRelaxedQuarterSpec.relaxationLoad m_quark_up_top_shell)) := by
    simpa [one_div] using (inv_le_inv₀ hM_pos hD_pos).2 (by linarith [hload_top_le])
  have hbase_nonneg : 0 ≤ |resonanceK_internal ⟨0, by decide⟩| := abs_nonneg _
  have hmul1 :
      |resonanceK_internal ⟨0, by decide⟩| * (1 / (1 + κ * ((-4 : ℝ) * L_O_kinetic A))) ≤
        |resonanceK_internal ⟨0, by decide⟩| * (1 / (1 + topRelaxedQuarterSpec.relaxationLoad m_quark_up_top_shell)) :=
    mul_le_mul_of_nonneg_left hrecip hbase_nonneg
  have hmul2 :
      |resonanceK_internal ⟨0, by decide⟩| * (1 / (1 + topRelaxedQuarterSpec.relaxationLoad m_quark_up_top_shell)) ≤
        |resonanceK_internal ⟨0, by decide⟩| *
          ((1 + topRelaxedQuarterSpec.relaxationLoad m_quark_up_charm_shell) /
            (1 + topRelaxedQuarterSpec.relaxationLoad m_quark_up_top_shell)) :=
    mul_le_mul_of_nonneg_left hratio_ge hbase_nonneg
  have hEqAbs :
      |resonanceK_internal_relaxedQuarter ⟨0, by decide⟩| =
        |resonanceK_internal ⟨0, by decide⟩| *
          ((1 + topRelaxedQuarterSpec.relaxationLoad m_quark_up_charm_shell) /
            (1 + topRelaxedQuarterSpec.relaxationLoad m_quark_up_top_shell)) := by
    rw [hkrel, hbase, abs_mul, abs_of_nonneg hratio_nonneg]
  calc
    |resonanceK_internal ⟨0, by decide⟩| / (1 + κ * ((-4 : ℝ) * L_O_kinetic A))
        = |resonanceK_internal ⟨0, by decide⟩| * (1 / (1 + κ * ((-4 : ℝ) * L_O_kinetic A))) := by
          ring
    _ ≤ |resonanceK_internal ⟨0, by decide⟩| * (1 / (1 + topRelaxedQuarterSpec.relaxationLoad m_quark_up_top_shell)) := hmul1
    _ ≤ |resonanceK_internal ⟨0, by decide⟩| *
          ((1 + topRelaxedQuarterSpec.relaxationLoad m_quark_up_charm_shell) /
            (1 + topRelaxedQuarterSpec.relaxationLoad m_quark_up_top_shell)) := hmul2
    _ = |resonanceK_internal_relaxedQuarter ⟨0, by decide⟩| := by
          rw [hEqAbs]

theorem charm_over_top_relaxedQuarter_abs_two_sided_envelope
    (κ : ℝ) (hκ : 0 ≤ κ) (A : Fin 8 → Fin 4 → ℝ) (x : ℝ)
    (hctrl_charm :
      topRelaxedQuarterSpec.relaxationLoad m_quark_up_charm_shell ≤
        κ * (∑ a : Fin 8, ∑ i : Fin 4, ((Hqiv.Physics.linearEnd (F_from_A A a i (i + 1))) x - x) ^ 2))
    (hctrl_top :
      topRelaxedQuarterSpec.relaxationLoad m_quark_up_top_shell ≤
        κ * (∑ a : Fin 8, ∑ i : Fin 4, ((Hqiv.Physics.linearEnd (F_from_A A a i (i + 1))) x - x) ^ 2)) :
    (|resonanceK_internal ⟨0, by decide⟩| * (1 + κ * ((-4 : ℝ) * L_O_kinetic A)))⁻¹ ≤
      |m_charm_relaxedQuarter_GeV / m_top_GeV| ∧
      |m_charm_relaxedQuarter_GeV / m_top_GeV| ≤
        (|resonanceK_internal ⟨0, by decide⟩| / (1 + κ * ((-4 : ℝ) * L_O_kinetic A)))⁻¹ := by
  have hktop_ub := resonanceK_internal_relaxedQuarter_top_charm_abs_le_kinetic_control κ hκ A x hctrl_charm
  have hkrel_lb := resonanceK_internal_relaxedQuarter_top_charm_abs_ge_kinetic_control κ hκ A x hctrl_top
  have hratio :
      |m_charm_relaxedQuarter_GeV / m_top_GeV| =
        (|resonanceK_internal_relaxedQuarter ⟨0, by decide⟩|)⁻¹ := by
    have htop : m_top_GeV ≠ 0 := by norm_num [m_top_GeV]
    calc
      |m_charm_relaxedQuarter_GeV / m_top_GeV|
          = |(m_top_GeV / resonanceK_internal_relaxedQuarter ⟨0, by decide⟩) / m_top_GeV| := by
              simp [m_charm_relaxedQuarter_GeV]
      _ = |(resonanceK_internal_relaxedQuarter ⟨0, by decide⟩)⁻¹| := by
              field_simp [htop]
      _ = (|resonanceK_internal_relaxedQuarter ⟨0, by decide⟩|)⁻¹ := by
              rw [abs_inv]
  have hkbase_pos : 0 < |resonanceK_internal ⟨0, by decide⟩| := by
    have hkpos : 0 < resonanceK_internal ⟨0, by decide⟩ := by
      unfold resonanceK_internal
      simpa using geometricResonanceStep_pos m_quark_up_top_shell m_quark_up_charm_shell
    exact abs_pos.2 (ne_of_gt hkpos)
  have hM_nonneg : 0 ≤ κ * ((-4 : ℝ) * L_O_kinetic A) := by
    have hbudget : (∑ a : Fin 8, ∑ i : Fin 4, ((Hqiv.Physics.linearEnd (F_from_A A a i (i + 1))) x - x) ^ 2) ≤
        ((-4 : ℝ) * L_O_kinetic A) := (Hqiv.Physics.cyclic_wilson_defect_sum_bounds_from_kinetic A x).2
    have hsum_nonneg :
        0 ≤ ∑ a : Fin 8, ∑ i : Fin 4, ((Hqiv.Physics.linearEnd (F_from_A A a i (i + 1))) x - x) ^ 2 := by
      refine Finset.sum_nonneg ?_
      intro a ha
      refine Finset.sum_nonneg ?_
      intro i hi
      exact sq_nonneg _
    exact mul_nonneg hκ (le_trans hsum_nonneg hbudget)
  have hG_pos : 0 < 1 + κ * ((-4 : ℝ) * L_O_kinetic A) := by linarith
  have hkrel_pos : 0 < |resonanceK_internal_relaxedQuarter ⟨0, by decide⟩| := by
    have hlt : |resonanceK_internal ⟨0, by decide⟩| / (1 + κ * ((-4 : ℝ) * L_O_kinetic A)) > 0 := by
      exact div_pos hkbase_pos hG_pos
    exact lt_of_lt_of_le hlt hkrel_lb
  constructor
  · rw [hratio]
    exact (inv_le_inv₀ (mul_pos hkbase_pos hG_pos) hkrel_pos).2 hktop_ub
  · rw [hratio]
    exact (inv_le_inv₀ hkrel_pos (div_pos hkbase_pos hG_pos)).2 hkrel_lb

/-- Canonical up-quark internal ladder axis (first up-line Fano vertex). -/
def upResonanceAxis : ResonanceAxis := upQuarkAxis ⟨0, by decide⟩ m_quark_up_top_shell

/-- Canonical down-quark internal ladder axis (first down-line Fano vertex). -/
def downResonanceAxis : ResonanceAxis := downQuarkAxis ⟨0, by decide⟩ m_quark_down_bottom_shell

noncomputable def upResonanceProduct (gen : Fin 3) : ℝ :=
  resonanceProductFromSteps
    (resonanceK_internal ⟨0, by decide⟩)
    (resonanceK_internal ⟨1, by decide⟩) gen

noncomputable def downResonanceProduct (gen : Fin 3) : ℝ :=
  resonanceProductFromSteps
    (resonanceK_internal_down ⟨0, by decide⟩)
    (resonanceK_internal_down ⟨1, by decide⟩) gen

/-- Up-type quark mass by generation index (`.two=.top`, `.one=.charm`, `.zero=.up`). -/
noncomputable def quarkMass (gen : Fin 3) : ℝ :=
  match gen with
  | ⟨2, _⟩ => m_top_GeV
  | ⟨1, _⟩ => m_top_GeV / upResonanceProduct ⟨1, by decide⟩
  | ⟨0, _⟩ => m_top_GeV / upResonanceProduct ⟨0, by decide⟩

/-- Down-type ladder (`.two=.bottom`, `.one=.strange`, `.zero=.down`). -/
noncomputable def quarkMassDown (gen : Fin 3) : ℝ :=
  match gen with
  | ⟨2, _⟩ => m_bottom_GeV
  | ⟨1, _⟩ => m_bottom_GeV / downResonanceProduct ⟨1, by decide⟩
  | ⟨0, _⟩ => m_bottom_GeV / downResonanceProduct ⟨0, by decide⟩

/-- Positive loop weight used to detune the heavy top-anchored band into channel-specific heavy
visible states. -/
def ResidualChargeChannel.heavyMassWeight : ResidualChargeChannel → ℕ
  | .upLike => 2
  | .downLike => 1

/-- The public color-composed ladder is normalized from the top-at-lockin heavy channel. -/
def topLockinColorResonanceAnchorMass : ℝ := m_top_GeV

/-- Cross-channel detuning between the heavy up-like and down-like shell witnesses. This is the
shell-geometry part of the down-like visibility compression. -/
noncomputable def crossChannelHeavyShellDetuning : ℝ :=
  geometricResonanceStep m_quark_up_top_shell m_quark_down_bottom_shell

/-- Three-jet heavy cross-channel detuning candidate. -/
noncomputable def crossChannelHeavyShellDetuning_threeJet : ℝ :=
  geometricResonanceStepThreeJet m_quark_up_top_shell m_quark_down_bottom_shell

/-- Relaxed-quarter heavy cross-channel detuning candidate. -/
noncomputable def crossChannelHeavyShellDetuning_relaxedQuarter : ℝ :=
  topRelaxedQuarterSpec.relaxedGeometricStepReadout m_quark_up_top_shell m_quark_down_bottom_shell

/-- Relaxed-quarter heavy cross-channel detuning with **`S⁴`** weight. -/
noncomputable def crossChannelHeavyShellDetuning_relaxedQuarterS4 : ℝ :=
  topRelaxedQuarterSpecS4.relaxedGeometricStepReadout m_quark_up_top_shell m_quark_down_bottom_shell

/-- Visible-state bookkeeping budget for the down-like branch: two signed charge states carried
across the three color-composed axes. -/
def downChannelVisibleBudgetCount : ℕ := chargedLeptonContentCount * cubeAxes

/-- Fraction of the shared heavy spin/color energy that remains visible in a given residual
channel after shell detuning and visible-state compression. The down-like branch keeps the full
spin/color state-space, but its observed mass is compressed by the heavy-shell detuning and the
`2 × 3` visible-state budget. -/
noncomputable def channelVisibleMassCompression : ResidualChargeChannel → ℝ
  | .upLike => 1
  | .downLike => 1 / (crossChannelHeavyShellDetuning * (downChannelVisibleBudgetCount : ℝ))

/-- Three-jet visible-state compression candidate. -/
noncomputable def channelVisibleMassCompression_threeJet : ResidualChargeChannel → ℝ
  | .upLike => 1
  | .downLike => 1 / (crossChannelHeavyShellDetuning_threeJet * (downChannelVisibleBudgetCount : ℝ))

/-- Relaxed-quarter visible-state compression candidate. -/
noncomputable def channelVisibleMassCompression_relaxedQuarter : ResidualChargeChannel → ℝ
  | .upLike => 1
  | .downLike => 1 / (crossChannelHeavyShellDetuning_relaxedQuarter * (downChannelVisibleBudgetCount : ℝ))

/-- Relaxed-quarter visible-state compression candidate (`S⁴` cross-channel detuning). -/
noncomputable def channelVisibleMassCompression_relaxedQuarterS4 : ResidualChargeChannel → ℝ
  | .upLike => 1
  | .downLike => 1 / (crossChannelHeavyShellDetuning_relaxedQuarterS4 * (downChannelVisibleBudgetCount : ℝ))

/-- Heavy visible-band normalization for each residual channel. Both channels start from the same
top lock-in spin/color energy budget; the down-like branch is then compressed by the heavy-shell
detuning and visible-state bookkeeping rather than by a naive loop fraction. -/
noncomputable def channelHeavyColorResonanceMass
    (channel : ResidualChargeChannel) : ℝ :=
  topLockinColorResonanceAnchorMass * channelVisibleMassCompression channel

/-- Three-jet heavy visible-band normalization candidate. -/
noncomputable def channelHeavyColorResonanceMass_threeJet
    (channel : ResidualChargeChannel) : ℝ :=
  topLockinColorResonanceAnchorMass * channelVisibleMassCompression_threeJet channel

/-- Relaxed-quarter heavy visible-band normalization candidate. -/
noncomputable def channelHeavyColorResonanceMass_relaxedQuarter
    (channel : ResidualChargeChannel) : ℝ :=
  topLockinColorResonanceAnchorMass * channelVisibleMassCompression_relaxedQuarter channel

/-- Relaxed-quarter heavy visible-band normalization candidate (`S⁴` compression). -/
noncomputable def channelHeavyColorResonanceMass_relaxedQuarterS4
    (channel : ResidualChargeChannel) : ℝ :=
  topLockinColorResonanceAnchorMass * channelVisibleMassCompression_relaxedQuarterS4 channel

/-- Public resonance-product interface for the color-composed ladder. -/
noncomputable def colorResonanceProduct
    (channel : ResidualChargeChannel) (band : AllowedColorResonanceBand) : ℝ :=
  match channel with
  | .upLike => upResonanceProduct band.toGenerationIndex
  | .downLike => downResonanceProduct band.toGenerationIndex

/-- Public mass API for the color-composed resonance ladder: choose a heavy/mid/light band, then a
residual internal channel (`upLike` / `downLike`). -/
noncomputable def allowedColorResonanceMass
    (channel : ResidualChargeChannel) (band : AllowedColorResonanceBand) : ℝ :=
  channelHeavyColorResonanceMass channel / colorResonanceProduct channel band

/-- Three-jet public mass API candidate on the same resonance products. -/
noncomputable def allowedColorResonanceMass_threeJet
    (channel : ResidualChargeChannel) (band : AllowedColorResonanceBand) : ℝ :=
  channelHeavyColorResonanceMass_threeJet channel / colorResonanceProduct channel band

/-- Relaxed-quarter public mass API candidate on the same resonance products. -/
noncomputable def allowedColorResonanceMass_relaxedQuarter
    (channel : ResidualChargeChannel) (band : AllowedColorResonanceBand) : ℝ :=
  channelHeavyColorResonanceMass_relaxedQuarter channel / colorResonanceProduct channel band

/-- Relaxed-quarter public mass API candidate with **`S⁴`** spectral weight in the compression line. -/
noncomputable def allowedColorResonanceMass_relaxedQuarterS4
    (channel : ResidualChargeChannel) (band : AllowedColorResonanceBand) : ℝ :=
  channelHeavyColorResonanceMass_relaxedQuarterS4 channel / colorResonanceProduct channel band

/-- Shell witness attached to the public resonance-band API. -/
def allowedColorResonanceShell
    (channel : ResidualChargeChannel) (band : AllowedColorResonanceBand) : ℕ :=
  match channel, band with
  | .upLike, .light => m_quark_up_light_shell
  | .upLike, .mid => m_quark_up_charm_shell
  | .upLike, .heavy => m_quark_up_top_shell
  | .downLike, .light => m_quark_down_light_shell
  | .downLike, .mid => m_quark_down_strange_shell
  | .downLike, .heavy => m_quark_down_bottom_shell

/-- Modal-frequency / horizon wrapper for one public color-composed shell readout. -/
noncomputable def allowedColorResonanceModalFrequencySpec
    (channel : ResidualChargeChannel) (band : AllowedColorResonanceBand) : ModalFrequencyHorizonSpec :=
  modalFrequencyHorizonFromShellNominal (allowedColorResonanceShell channel band)

/-- Lock-in modal-frequency / horizon wrapper for the heavy up-like channel. -/
noncomputable def topModalFrequencySpec : ModalFrequencyHorizonSpec :=
  allowedColorResonanceModalFrequencySpec .upLike .heavy

/-- Heavy down-branch modal-frequency / horizon wrapper. -/
noncomputable def bottomModalFrequencySpec : ModalFrequencyHorizonSpec :=
  allowedColorResonanceModalFrequencySpec .downLike .heavy

theorem allowedColorResonanceModal_detunedSurfaceReadout
    (channel : ResidualChargeChannel) (band : AllowedColorResonanceBand) :
    (allowedColorResonanceModalFrequencySpec channel band).detunedSurfaceReadout
        (allowedColorResonanceShell channel band) =
      detunedShellSurface (allowedColorResonanceShell channel band) := by
  rw [show allowedColorResonanceModalFrequencySpec channel band =
        modalFrequencyHorizonFromShellNominal (allowedColorResonanceShell channel band) by rfl]
  rw [detunedSurfaceReadout_fromShellNominal]

theorem resonanceK_internal_top_charm_eq_modal_readout :
    resonanceK_internal ⟨0, by decide⟩ =
      ModalFrequencyHorizonSpec.geometricStepReadout
        topModalFrequencySpec m_quark_up_top_shell m_quark_up_charm_shell := by
  rw [show topModalFrequencySpec = modalFrequencyHorizonFromShellNominal m_quark_up_top_shell by rfl]
  rw [geometricStepReadout_fromShellNominal]
  rfl

theorem resonanceK_internal_charm_up_eq_modal_readout :
    resonanceK_internal ⟨1, by decide⟩ =
      ModalFrequencyHorizonSpec.geometricStepReadout
        topModalFrequencySpec m_quark_up_charm_shell m_quark_up_light_shell := by
  rw [show topModalFrequencySpec = modalFrequencyHorizonFromShellNominal m_quark_up_top_shell by rfl]
  rw [geometricStepReadout_fromShellNominal]
  rfl

theorem resonanceK_internal_down_bottom_strange_eq_modal_readout :
    resonanceK_internal_down ⟨0, by decide⟩ =
      ModalFrequencyHorizonSpec.geometricStepReadout bottomModalFrequencySpec
        m_quark_down_bottom_shell m_quark_down_strange_shell := by
  rw [show bottomModalFrequencySpec = modalFrequencyHorizonFromShellNominal m_quark_down_bottom_shell by rfl]
  rw [geometricStepReadout_fromShellNominal]
  rfl

theorem resonanceK_internal_down_strange_down_eq_modal_readout :
    resonanceK_internal_down ⟨1, by decide⟩ =
      ModalFrequencyHorizonSpec.geometricStepReadout bottomModalFrequencySpec
        m_quark_down_strange_shell m_quark_down_light_shell := by
  rw [show bottomModalFrequencySpec = modalFrequencyHorizonFromShellNominal m_quark_down_bottom_shell by rfl]
  rw [geometricStepReadout_fromShellNominal]
  rfl

theorem m_charm_GeV_eq_top_over_modal_readout :
    m_charm_GeV =
      m_top_GeV /
        ModalFrequencyHorizonSpec.geometricStepReadout
          topModalFrequencySpec m_quark_up_top_shell m_quark_up_charm_shell := by
  rw [m_charm_GeV, resonanceK_internal_top_charm_eq_modal_readout]

theorem m_up_GeV_eq_charm_over_modal_readout :
    m_up_GeV =
      m_charm_GeV /
        ModalFrequencyHorizonSpec.geometricStepReadout
          topModalFrequencySpec m_quark_up_charm_shell m_quark_up_light_shell := by
  rw [m_up_GeV, resonanceK_internal_charm_up_eq_modal_readout]

theorem m_strange_GeV_eq_bottom_over_modal_readout :
    m_strange_GeV =
      m_bottom_GeV /
        ModalFrequencyHorizonSpec.geometricStepReadout
          bottomModalFrequencySpec m_quark_down_bottom_shell m_quark_down_strange_shell := by
  rw [m_strange_GeV, resonanceK_internal_down_bottom_strange_eq_modal_readout]

theorem m_down_GeV_eq_strange_over_modal_readout :
    m_down_GeV =
      m_strange_GeV /
        ModalFrequencyHorizonSpec.geometricStepReadout
          bottomModalFrequencySpec m_quark_down_strange_shell m_quark_down_light_shell := by
  rw [m_down_GeV, resonanceK_internal_down_strange_down_eq_modal_readout]

/-- Hypercharge sign-flip witness in the 8×8 block language (+1 for up, -1 for down). -/
def hyperchargeSignUp : ℝ := (upResonanceAxis.hyperchargeSign : ℝ)
def hyperchargeSignDown : ℝ := (downResonanceAxis.hyperchargeSign : ℝ)

/-- Legacy proton comparison value retained for reference only; no longer fed back into the
hadron constituent definitions. -/
def protonAnchorMass_MeV : ℝ := 938.272

/-- First active generator slot used by the nucleon composite trace witness. -/
def nucleonTraceGeneratorIndex0 : So8Index := ⟨0, by decide⟩

/-- First active carrier slot used by the nucleon composite trace witness. -/
def nucleonTraceCarrierIndex0 : Fin 8 := ⟨0, by decide⟩

/-- Second active carrier slot used by the nucleon composite trace witness. -/
def nucleonTraceCarrierIndex1 : Fin 8 := ⟨1, by decide⟩

/-- Third active carrier slot used by the nucleon composite trace witness. -/
def nucleonTraceCarrierIndex2 : Fin 8 := ⟨2, by decide⟩

/-- Number of active channels in the composite nucleon witness. -/
def nucleonTraceChannelCount : ℕ := 3

/-- A triadic 8×8 state witness spread across three carrier slots. -/
def nucleonTraceState : OctonionState :=
  fun i =>
    if i = nucleonTraceCarrierIndex0 ∨ i = nucleonTraceCarrierIndex1 ∨ i = nucleonTraceCarrierIndex2
    then 1
    else 0

/-- A triadic diagonal trace witness selecting three carrier channels on one generator family. -/
def nucleonTraceDiagonal : So8TraceDiagonal :=
  fun k i =>
    if k = nucleonTraceGeneratorIndex0 ∧
        (i = nucleonTraceCarrierIndex0 ∨ i = nucleonTraceCarrierIndex1 ∨ i = nucleonTraceCarrierIndex2)
    then 1
    else 0

/-- Shared QCD binding at `referenceM`, derived from the lattice mode count and
effective coupling through the explicit composite-trace witness. -/
noncomputable def nucleonSharedBinding_MeV : ℝ :=
  E_bind_from_composite_trace referenceM nucleonTraceDiagonal nucleonTraceState

/-- Internal isospin splitting from the hypercharge sign flip on the two Fano axes. -/
noncomputable def nucleonIsospinGap_MeV : ℝ :=
  (hyperchargeSignUp - hyperchargeSignDown) / 2

/-- Shared constituent baseline from the same network binding spine; split equally across the
three color-composed channels before adding quark-ladder dressing. -/
noncomputable def quarkConstituentBaseLift_MeV : ℝ :=
  (nucleonSharedBinding_MeV + nucleonIsospinGap_MeV) / 3

/-- Common quark-to-constituent dressing scale from the lock-in shell's lattice multiplicity and
the two visible charge states on the light rung. This replaces the old proton anchor feedback. -/
noncomputable def quarkConstituentDress_MeV : ℝ :=
  (1000 : ℝ) * (latticeSimplexCount referenceM : ℝ) * (1 + gamma_HQIV) *
    (chargedLeptonContentCount : ℝ)

/-- Residual constituent dressing on the light rung: a smaller channel-splitting correction driven
by the same shell coupling, but only at the effective-coupling strength. -/
noncomputable def quarkResidualDetuningDress_MeV : ℝ :=
  (1000 : ℝ) * (latticeSimplexCount referenceM : ℝ) * alphaEffAtShell referenceM * (1 + gamma_HQIV)

/-- Active light up-like visible mass used by the nucleon ladder. -/
noncomputable def activeUpLightQuarkMass_GeV : ℝ :=
  allowedColorResonanceMass .upLike .light

/-- Active light down-like visible mass used by the nucleon ladder. -/
noncomputable def activeDownLightQuarkMass_GeV : ℝ :=
  allowedColorResonanceMass .downLike .light

/-- Shared light-rung state-space mass carried by both active quark channels before residual
detuning is applied. -/
noncomputable def activeLightQuarkAverageMass_GeV : ℝ :=
  (activeUpLightQuarkMass_GeV + activeDownLightQuarkMass_GeV) / 2

/-- Residual light-rung offset from the shared state-space mass. -/
noncomputable def activeLightQuarkResidualOffset_GeV : ResidualChargeChannel → ℝ
  | .upLike => activeUpLightQuarkMass_GeV - activeLightQuarkAverageMass_GeV
  | .downLike => activeDownLightQuarkMass_GeV - activeLightQuarkAverageMass_GeV

/-- Up constituent mass from the common constituent baseline plus the shared light-rung dressing
and a smaller residual detuning correction. -/
noncomputable def upConstituentMass_MeV : ℝ :=
  quarkConstituentBaseLift_MeV +
    quarkConstituentDress_MeV * activeLightQuarkAverageMass_GeV +
    quarkResidualDetuningDress_MeV * activeLightQuarkResidualOffset_GeV .upLike

/-- Down constituent mass from the same shared light-rung budget plus the down-like residual
detuning correction. -/
noncomputable def downConstituentMass_MeV : ℝ :=
  quarkConstituentBaseLift_MeV +
    quarkConstituentDress_MeV * activeLightQuarkAverageMass_GeV +
    quarkResidualDetuningDress_MeV * activeLightQuarkResidualOffset_GeV .downLike

/-- Proton constituent sum (`uud`) in MeV. -/
noncomputable def protonConstituentMass_MeV : ℝ :=
  2 * upConstituentMass_MeV + downConstituentMass_MeV

/-- Neutron constituent sum (`udd`) in MeV. -/
noncomputable def neutronConstituentMass_MeV : ℝ :=
  upConstituentMass_MeV + 2 * downConstituentMass_MeV

/-- Proton mass from constituent masses minus the shared network binding. -/
noncomputable def protonMassFromMetaHarmonics_MeV : ℝ :=
  protonConstituentMass_MeV - nucleonSharedBinding_MeV

/-- Neutron mass from constituent masses minus the shared network binding. -/
noncomputable def neutronMassFromMetaHarmonics_MeV : ℝ :=
  neutronConstituentMass_MeV - nucleonSharedBinding_MeV

/-! ### Controlled HQVM lapse wiring for resonance/binding readouts -/

/-- Lock-in auxiliary field value used by the nucleon readout shell. -/
noncomputable def lockinAuxPhi : ℝ := phi_of_shell referenceM

/-- HQVM lapse evaluated on the lock-in auxiliary field. -/
noncomputable def lockinHQVMLapse (Φ t : ℝ) : ℝ := HQVM_lapse Φ lockinAuxPhi t

/-- Controlled lapse application to a MeV readout. -/
noncomputable def applyHQVMLapseCorrection (massMeV lapse : ℝ) : ℝ := massMeV / lapse

/-- Lapse-corrected shared binding. -/
noncomputable def nucleonSharedBinding_lapseCorrected_MeV (Φ t : ℝ) : ℝ :=
  applyHQVMLapseCorrection nucleonSharedBinding_MeV (lockinHQVMLapse Φ t)

/-- Lapse-corrected proton constituent sum. -/
noncomputable def protonConstituentMass_lapseCorrected_MeV (Φ t : ℝ) : ℝ :=
  applyHQVMLapseCorrection protonConstituentMass_MeV (lockinHQVMLapse Φ t)

/-- Lapse-corrected neutron constituent sum. -/
noncomputable def neutronConstituentMass_lapseCorrected_MeV (Φ t : ℝ) : ℝ :=
  applyHQVMLapseCorrection neutronConstituentMass_MeV (lockinHQVMLapse Φ t)

/-- Lapse-corrected proton mass from the same constituent-minus-shared-binding pattern. -/
noncomputable def protonMassFromMetaHarmonics_lapseCorrected_MeV (Φ t : ℝ) : ℝ :=
  protonConstituentMass_lapseCorrected_MeV Φ t - nucleonSharedBinding_lapseCorrected_MeV Φ t

/-- Lapse-corrected neutron mass from the same constituent-minus-shared-binding pattern. -/
noncomputable def neutronMassFromMetaHarmonics_lapseCorrected_MeV (Φ t : ℝ) : ℝ :=
  neutronConstituentMass_lapseCorrected_MeV Φ t - nucleonSharedBinding_lapseCorrected_MeV Φ t

theorem lockinHQVMLapse_eq_timeAngle (Φ t : ℝ) :
    lockinHQVMLapse Φ t = 1 + Φ + timeAngle lockinAuxPhi t := by
  unfold lockinHQVMLapse
  exact HQVM_lapse_eq_timeAngle Φ lockinAuxPhi t

theorem lockinHQVMLapse_eq_one_add_phi_t (Φ t : ℝ) :
    lockinHQVMLapse Φ t = 1 + Φ + lockinAuxPhi * t := by
  unfold lockinHQVMLapse lockinAuxPhi
  rcases same_phi_in_O_Maxwell_and_HQVM (phi_of_shell referenceM) t with ⟨hangle, _⟩
  rw [HQVM_lapse_eq_timeAngle, hangle]

theorem protonMassFromMetaHarmonics_lapseCorrected_eq_raw_div_lapse (Φ t : ℝ) :
    protonMassFromMetaHarmonics_lapseCorrected_MeV Φ t =
      protonMassFromMetaHarmonics_MeV / lockinHQVMLapse Φ t := by
  unfold protonMassFromMetaHarmonics_lapseCorrected_MeV
    protonConstituentMass_lapseCorrected_MeV
    nucleonSharedBinding_lapseCorrected_MeV
    applyHQVMLapseCorrection protonMassFromMetaHarmonics_MeV
    protonConstituentMass_MeV nucleonSharedBinding_MeV
  ring_nf

theorem neutronMassFromMetaHarmonics_lapseCorrected_eq_raw_div_lapse (Φ t : ℝ) :
    neutronMassFromMetaHarmonics_lapseCorrected_MeV Φ t =
      neutronMassFromMetaHarmonics_MeV / lockinHQVMLapse Φ t := by
  unfold neutronMassFromMetaHarmonics_lapseCorrected_MeV
    neutronConstituentMass_lapseCorrected_MeV
    nucleonSharedBinding_lapseCorrected_MeV
    applyHQVMLapseCorrection neutronMassFromMetaHarmonics_MeV
    neutronConstituentMass_MeV nucleonSharedBinding_MeV
  ring_nf

/-- Lock-in auxiliary $\varphi$ is strictly positive on every shell (`phi_of_shell_pos`). -/
theorem lockinAuxPhi_pos : 0 < lockinAuxPhi := by
  simpa [lockinAuxPhi] using phi_of_shell_pos referenceM

/-- Forward-time, weak-field regime: the lock-in lapse is strictly positive. -/
theorem lockinHQVMLapse_pos (Φ t : ℝ) (h₁ : 0 < 1 + Φ) (ht : 0 ≤ t) :
    0 < lockinHQVMLapse Φ t := by
  unfold lockinHQVMLapse
  exact HQVM_lapse_pos Φ lockinAuxPhi t h₁ (le_of_lt lockinAuxPhi_pos) ht

/-- With nonnegative Newtonian potential and positive coordinate time, the lock-in lapse exceeds
Minkowski ($N>1$) because $\varphi(\texttt{referenceM})>0$. -/
theorem lockinHQVMLapse_gt_one (Φ t : ℝ) (hΦ : 0 ≤ Φ) (ht : 0 < t) :
    1 < lockinHQVMLapse Φ t := by
  unfold lockinHQVMLapse
  exact HQVM_lapse_gt_one Φ lockinAuxPhi t hΦ lockinAuxPhi_pos ht

/-- **Monotonicity (mass readout):** when $N>1$, lapse-corrected proton mass is strictly below the
raw meta-harmonic mass (same algebraic sign as ``blueshift vs.\ divisor'' in the HQVM chart). -/
theorem protonMassFromMetaHarmonics_lapseCorrected_lt_raw_of_lapse_gt_one
    (Φ t : ℝ) (hN : 1 < lockinHQVMLapse Φ t) (hraw : 0 < protonMassFromMetaHarmonics_MeV)
    (_hlapse : 0 < lockinHQVMLapse Φ t) :
    protonMassFromMetaHarmonics_lapseCorrected_MeV Φ t < protonMassFromMetaHarmonics_MeV := by
  rw [protonMassFromMetaHarmonics_lapseCorrected_eq_raw_div_lapse, div_eq_mul_inv]
  have hinv : (lockinHQVMLapse Φ t)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hN
  convert mul_lt_mul_of_pos_right hinv hraw using 1
  · rw [mul_comm]
  · rw [one_mul]

theorem resonanceK_internal_pos (step : Fin 2) : 0 < resonanceK_internal step := by
  fin_cases step
  · exact geometricResonanceStep_pos m_quark_up_top_shell m_quark_up_charm_shell
  · exact geometricResonanceStep_pos m_quark_up_charm_shell m_quark_up_light_shell

theorem resonanceK_internal_down_pos (step : Fin 2) : 0 < resonanceK_internal_down step := by
  fin_cases step
  · exact geometricResonanceStep_pos m_quark_down_bottom_shell m_quark_down_strange_shell
  · exact geometricResonanceStep_pos m_quark_down_strange_shell m_quark_down_light_shell

theorem top_at_T_lockin_now :
    m_top_at_lockin = referenceM ∧ quarkMass ⟨2, by decide⟩ = 172.57 := by
  constructor
  · rfl
  · norm_num [quarkMass, m_top_GeV]

theorem two_octave_drops_to_light_quarks :
    quarkMass ⟨1, by decide⟩ = m_charm_GeV ∧
    quarkMass ⟨0, by decide⟩ = m_up_GeV ∧
    quarkMassDown ⟨1, by decide⟩ = m_strange_GeV ∧
    quarkMassDown ⟨0, by decide⟩ = m_down_GeV := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [quarkMass, m_charm_GeV, upResonanceProduct, resonanceProductFromSteps, resonanceK_internal]
  ·
    simp [quarkMass, m_up_GeV, m_charm_GeV, upResonanceProduct, resonanceProductFromSteps,
      resonanceK_internal]
    field_simp
  · simp [quarkMassDown, m_strange_GeV, downResonanceProduct, resonanceProductFromSteps,
      resonanceK_internal_down]
  ·
    simp [quarkMassDown, m_down_GeV, m_strange_GeV, downResonanceProduct, resonanceProductFromSteps,
      resonanceK_internal_down]
    field_simp

theorem allowedColorResonanceBand_heavy_at_lockin :
    m_top_at_lockin = referenceM ∧
      AllowedColorResonanceBand.toGenerationIndex .heavy = ⟨2, by decide⟩ := by
  exact ⟨rfl, rfl⟩

theorem residualChargeChannel_heavyMassWeight_values :
    ResidualChargeChannel.heavyMassWeight .upLike = 2 ∧
      ResidualChargeChannel.heavyMassWeight .downLike = 1 := by
  exact ⟨rfl, rfl⟩

theorem residualChargeChannel_heavyMassWeight_eq_loopMultiplicity_natAbs
    (channel : ResidualChargeChannel) :
    channel.heavyMassWeight = Int.natAbs channel.loopMultiplicity := by
  cases channel <;> rfl

theorem topLockinColorResonanceAnchorMass_value :
    topLockinColorResonanceAnchorMass = 172.57 := by
  norm_num [topLockinColorResonanceAnchorMass, m_top_GeV]

theorem crossChannelHeavyShellDetuning_pos : 0 < crossChannelHeavyShellDetuning := by
  unfold crossChannelHeavyShellDetuning
  exact geometricResonanceStep_pos _ _

theorem downChannelVisibleBudgetCount_eq_six :
    downChannelVisibleBudgetCount = 6 := by
  norm_num [downChannelVisibleBudgetCount, chargedLeptonContentCount, cubeAxes]

theorem channelHeavyColorResonanceMass_upLike_eq_top_lockin_anchor :
    channelHeavyColorResonanceMass .upLike = topLockinColorResonanceAnchorMass := by
  simp [channelHeavyColorResonanceMass, channelVisibleMassCompression, topLockinColorResonanceAnchorMass]

theorem channelHeavyColorResonanceMass_downLike_eq_top_over_detuning_and_visible_budget :
    channelHeavyColorResonanceMass .downLike =
      topLockinColorResonanceAnchorMass /
        (crossChannelHeavyShellDetuning * (downChannelVisibleBudgetCount : ℝ)) := by
  unfold channelHeavyColorResonanceMass channelVisibleMassCompression
  field_simp

theorem channelHeavyColorResonanceMass_downLike_eq_upLike_over_detuning_and_visible_budget :
    channelHeavyColorResonanceMass .downLike =
      channelHeavyColorResonanceMass .upLike /
        (crossChannelHeavyShellDetuning * (downChannelVisibleBudgetCount : ℝ)) := by
  rw [channelHeavyColorResonanceMass_upLike_eq_top_lockin_anchor,
    channelHeavyColorResonanceMass_downLike_eq_top_over_detuning_and_visible_budget]

theorem colorResonanceProduct_upLike_heavy :
    colorResonanceProduct .upLike .heavy = 1 := by
  simp [colorResonanceProduct, upResonanceProduct, resonanceProductFromSteps,
    AllowedColorResonanceBand.toGenerationIndex]

theorem colorResonanceProduct_downLike_heavy :
    colorResonanceProduct .downLike .heavy = 1 := by
  simp [colorResonanceProduct, downResonanceProduct, resonanceProductFromSteps,
    AllowedColorResonanceBand.toGenerationIndex]

theorem allowedColorResonanceMass_eq_shared_heavy_band_over_product
    (channel : ResidualChargeChannel) (band : AllowedColorResonanceBand) :
    allowedColorResonanceMass channel band =
      channelHeavyColorResonanceMass channel / colorResonanceProduct channel band := by
  rfl

theorem allowedColorResonanceMass_upLike_heavy_eq_top_lockin_anchor :
    allowedColorResonanceMass .upLike .heavy = topLockinColorResonanceAnchorMass := by
  rw [allowedColorResonanceMass_eq_shared_heavy_band_over_product,
    colorResonanceProduct_upLike_heavy, channelHeavyColorResonanceMass_upLike_eq_top_lockin_anchor]
  ring

theorem allowedColorResonanceMass_downLike_heavy_eq_top_over_detuning_and_visible_budget :
    allowedColorResonanceMass .downLike .heavy =
      topLockinColorResonanceAnchorMass /
        (crossChannelHeavyShellDetuning * (downChannelVisibleBudgetCount : ℝ)) := by
  rw [allowedColorResonanceMass_eq_shared_heavy_band_over_product,
    colorResonanceProduct_downLike_heavy,
    channelHeavyColorResonanceMass_downLike_eq_top_over_detuning_and_visible_budget]
  ring

theorem allowedColorResonanceMass_downLike_heavy_eq_upLike_over_detuning_and_visible_budget :
    allowedColorResonanceMass .downLike .heavy =
      allowedColorResonanceMass .upLike .heavy /
        (crossChannelHeavyShellDetuning * (downChannelVisibleBudgetCount : ℝ)) := by
  rw [allowedColorResonanceMass_upLike_heavy_eq_top_lockin_anchor,
    allowedColorResonanceMass_downLike_heavy_eq_top_over_detuning_and_visible_budget]

theorem allowedColorResonanceMass_upLike_mid_eq_heavy_over_resonance :
    allowedColorResonanceMass .upLike .mid =
      topLockinColorResonanceAnchorMass / upResonanceProduct ⟨1, by decide⟩ := by
  rw [allowedColorResonanceMass_eq_shared_heavy_band_over_product,
    channelHeavyColorResonanceMass_upLike_eq_top_lockin_anchor]
  rfl

theorem allowedColorResonanceMass_upLike_mid_eq_heavy_over_modal_readout :
    allowedColorResonanceMass .upLike .mid =
      topLockinColorResonanceAnchorMass /
        ModalFrequencyHorizonSpec.geometricStepReadout
          topModalFrequencySpec m_quark_up_top_shell m_quark_up_charm_shell := by
  rw [allowedColorResonanceMass_upLike_mid_eq_heavy_over_resonance]
  change topLockinColorResonanceAnchorMass / resonanceK_internal ⟨0, by decide⟩ =
    topLockinColorResonanceAnchorMass /
      ModalFrequencyHorizonSpec.geometricStepReadout
        topModalFrequencySpec m_quark_up_top_shell m_quark_up_charm_shell
  rw [resonanceK_internal_top_charm_eq_modal_readout]

theorem allowedColorResonanceMass_downLike_mid_eq_heavy_over_resonance :
    allowedColorResonanceMass .downLike .mid =
      (topLockinColorResonanceAnchorMass /
        (crossChannelHeavyShellDetuning * (downChannelVisibleBudgetCount : ℝ))) /
          downResonanceProduct ⟨1, by decide⟩ := by
  rw [allowedColorResonanceMass_eq_shared_heavy_band_over_product,
    channelHeavyColorResonanceMass_downLike_eq_top_over_detuning_and_visible_budget]
  rfl

theorem allowedColorResonanceMass_downLike_mid_eq_heavy_over_modal_readout :
    allowedColorResonanceMass .downLike .mid =
      (topLockinColorResonanceAnchorMass /
        (crossChannelHeavyShellDetuning * (downChannelVisibleBudgetCount : ℝ))) /
          ModalFrequencyHorizonSpec.geometricStepReadout bottomModalFrequencySpec
            m_quark_down_bottom_shell m_quark_down_strange_shell := by
  rw [allowedColorResonanceMass_downLike_mid_eq_heavy_over_resonance]
  change (topLockinColorResonanceAnchorMass /
      (crossChannelHeavyShellDetuning * (downChannelVisibleBudgetCount : ℝ))) /
        resonanceK_internal_down ⟨0, by decide⟩ =
      (topLockinColorResonanceAnchorMass /
        (crossChannelHeavyShellDetuning * (downChannelVisibleBudgetCount : ℝ))) /
          ModalFrequencyHorizonSpec.geometricStepReadout bottomModalFrequencySpec
            m_quark_down_bottom_shell m_quark_down_strange_shell
  rw [resonanceK_internal_down_bottom_strange_eq_modal_readout]

theorem allowedColorResonanceMass_upLike_light_eq_heavy_over_resonanceProduct :
    allowedColorResonanceMass .upLike .light =
      topLockinColorResonanceAnchorMass / upResonanceProduct ⟨0, by decide⟩ := by
  rw [allowedColorResonanceMass_eq_shared_heavy_band_over_product,
    channelHeavyColorResonanceMass_upLike_eq_top_lockin_anchor]
  rfl

theorem allowedColorResonanceMass_downLike_light_eq_heavy_over_resonanceProduct :
    allowedColorResonanceMass .downLike .light =
      (topLockinColorResonanceAnchorMass /
        (crossChannelHeavyShellDetuning * (downChannelVisibleBudgetCount : ℝ))) /
          downResonanceProduct ⟨0, by decide⟩ := by
  rw [allowedColorResonanceMass_eq_shared_heavy_band_over_product,
    channelHeavyColorResonanceMass_downLike_eq_top_over_detuning_and_visible_budget]
  rfl

theorem allowedColorResonanceShell_upLike_heavy :
    allowedColorResonanceShell .upLike .heavy = m_quark_up_top_shell := by
  rfl

theorem allowedColorResonanceShell_downLike_heavy :
    allowedColorResonanceShell .downLike .heavy = m_quark_down_bottom_shell := by
  rfl

theorem residualChargeChannel_is_fractional_bookkeeping :
    ResidualChargeChannel.toRat .upLike = 2 / 3 ∧
      ResidualChargeChannel.toRat .downLike = -1 / 3 := by
  norm_num [ResidualChargeChannel.toRat, ResidualChargeChannel.loopMultiplicity,
    colorComposedResidualDenominator]

theorem residualChargeChannel_loopMultiplicity_values :
    ResidualChargeChannel.loopMultiplicity .upLike = 2 ∧
      ResidualChargeChannel.loopMultiplicity .downLike = -1 := by
  exact ⟨rfl, rfl⟩

theorem upLike_loopMultiplicity_is_double_downLike_magnitude :
    ResidualChargeChannel.loopMultiplicity .upLike =
      2 * Int.natAbs (ResidualChargeChannel.loopMultiplicity .downLike) := by
  norm_num [ResidualChargeChannel.loopMultiplicity]

theorem residualChargeChannel_toRat_eq_loopMultiplicity_over_color_denominator
    (q : ResidualChargeChannel) :
    q.toRat = q.loopMultiplicity / colorComposedResidualDenominator := by
  cases q <;> rfl

theorem upLike_residual_is_double_downLike_magnitude :
    ResidualChargeChannel.toRat .upLike =
      2 * |ResidualChargeChannel.toRat .downLike| := by
  norm_num [ResidualChargeChannel.toRat, ResidualChargeChannel.loopMultiplicity,
    colorComposedResidualDenominator]

theorem allowedColorResonanceMass_upLike_heavy_eq_top_GeV :
    allowedColorResonanceMass .upLike .heavy = m_top_GeV := by
  rw [allowedColorResonanceMass_upLike_heavy_eq_top_lockin_anchor]
  rfl

theorem allowedColorResonanceMass_downLike_heavy_eq_top_GeV_over_detuning_and_visible_budget :
    allowedColorResonanceMass .downLike .heavy =
      m_top_GeV / (crossChannelHeavyShellDetuning * (downChannelVisibleBudgetCount : ℝ)) := by
  rw [allowedColorResonanceMass_downLike_heavy_eq_top_over_detuning_and_visible_budget]
  rfl

theorem nucleonSharedBinding_from_composite_trace :
    nucleonSharedBinding_MeV =
      E_bind_from_network referenceM
        (networkWeightFromCompositeTrace nucleonTraceDiagonal nucleonTraceState) := by
  rfl

theorem nucleonTraceChannelCount_eq_three : nucleonTraceChannelCount = 3 := by
  rfl

theorem nucleonIsospinGap_eq_one : nucleonIsospinGap_MeV = 1 := by
  norm_num [nucleonIsospinGap_MeV, hyperchargeSignUp, hyperchargeSignDown,
    upResonanceAxis, downResonanceAxis, upQuarkAxis, downQuarkAxis]

theorem resonanceK_internal_nonzero (step : Fin 2) : resonanceK_internal step ≠ 0 :=
  ne_of_gt (resonanceK_internal_pos step)

theorem resonanceK_internal_down_nonzero (step : Fin 2) : resonanceK_internal_down step ≠ 0 :=
  ne_of_gt (resonanceK_internal_down_pos step)

theorem m_charm_GeV_pos : 0 < m_charm_GeV := by
  unfold m_charm_GeV
  exact div_pos (by norm_num [m_top_GeV]) (resonanceK_internal_pos ⟨0, by decide⟩)

theorem m_up_GeV_pos : 0 < m_up_GeV := by
  unfold m_up_GeV
  exact div_pos m_charm_GeV_pos (resonanceK_internal_pos ⟨1, by decide⟩)

theorem m_strange_GeV_pos : 0 < m_strange_GeV := by
  unfold m_strange_GeV
  exact div_pos (by norm_num [m_bottom_GeV]) (resonanceK_internal_down_pos ⟨0, by decide⟩)

theorem m_down_GeV_pos : 0 < m_down_GeV := by
  unfold m_down_GeV
  exact div_pos m_strange_GeV_pos (resonanceK_internal_down_pos ⟨1, by decide⟩)

theorem activeUpLightQuarkMass_GeV_pos : 0 < activeUpLightQuarkMass_GeV := by
  unfold activeUpLightQuarkMass_GeV
  rw [allowedColorResonanceMass_upLike_light_eq_heavy_over_resonanceProduct,
    topLockinColorResonanceAnchorMass_value]
  apply div_pos
  · norm_num
  ·
    unfold upResonanceProduct resonanceProductFromSteps
    have hk21 := resonanceK_internal_pos ⟨0, by decide⟩
    have hk10 := resonanceK_internal_pos ⟨1, by decide⟩
    nlinarith

theorem activeDownLightQuarkMass_GeV_pos : 0 < activeDownLightQuarkMass_GeV := by
  unfold activeDownLightQuarkMass_GeV
  rw [allowedColorResonanceMass_downLike_light_eq_heavy_over_resonanceProduct]
  apply div_pos
  ·
    apply div_pos
    · rw [topLockinColorResonanceAnchorMass_value]; norm_num
    ·
      apply mul_pos crossChannelHeavyShellDetuning_pos
      norm_num [downChannelVisibleBudgetCount_eq_six]
  ·
    unfold downResonanceProduct resonanceProductFromSteps
    have hk21 := resonanceK_internal_down_pos ⟨0, by decide⟩
    have hk10 := resonanceK_internal_down_pos ⟨1, by decide⟩
    nlinarith

theorem activeLightQuarkAverageMass_GeV_pos : 0 < activeLightQuarkAverageMass_GeV := by
  unfold activeLightQuarkAverageMass_GeV
  nlinarith [activeUpLightQuarkMass_GeV_pos, activeDownLightQuarkMass_GeV_pos]

theorem activeLightQuarkResidualOffset_up_add_average :
    activeLightQuarkAverageMass_GeV + activeLightQuarkResidualOffset_GeV .upLike =
      activeUpLightQuarkMass_GeV := by
  unfold activeLightQuarkResidualOffset_GeV
  ring

theorem activeLightQuarkResidualOffset_down_add_average :
    activeLightQuarkAverageMass_GeV + activeLightQuarkResidualOffset_GeV .downLike =
      activeDownLightQuarkMass_GeV := by
  unfold activeLightQuarkResidualOffset_GeV
  ring

theorem activeLightQuarkResidualOffsets_sum_to_zero :
    activeLightQuarkResidualOffset_GeV .upLike +
      activeLightQuarkResidualOffset_GeV .downLike = 0 := by
  unfold activeLightQuarkResidualOffset_GeV activeLightQuarkAverageMass_GeV
  ring

theorem quarkConstituentDress_MeV_pos : 0 < quarkConstituentDress_MeV := by
  unfold quarkConstituentDress_MeV
  have h1000 : 0 < (1000 : ℝ) := by norm_num
  have href : referenceM = 4 := by
    unfold referenceM qcdShell stepsFromQCDToLockin latticeStepCount
    norm_num
  have hlat : 0 < (latticeSimplexCount referenceM : ℝ) := by
    rw [href]
    norm_num [latticeSimplexCount]
  have hmono : 0 < 1 + gamma_HQIV := by
    rw [gamma_eq_2_5]
    norm_num
  have hcount : 0 < (chargedLeptonContentCount : ℝ) := by
    norm_num [chargedLeptonContentCount]
  exact mul_pos (mul_pos (mul_pos h1000 hlat) hmono) hcount

theorem alphaEffAtShell_referenceM_lt_one : alphaEffAtShell referenceM < 1 := by
  unfold alphaEffAtShell
  have hgt : 1 < oneOverAlphaEffAtShell referenceM := by
    unfold oneOverAlphaEffAtShell oneOverAlphaBare
    have hlog : 0 ≤ Real.log (phi_of_shell referenceM + 1) := by
      apply Real.log_nonneg
      have hphi : 1 ≤ phi_of_shell referenceM + 1 := by
        have hphi2 : (2 : ℝ) ≤ phi_of_shell referenceM := phi_of_shell_ge_two referenceM
        nlinarith
      linarith
    have halpha : 0 ≤ alpha := by
      rw [alpha_eq_3_5]
      positivity
    have hfac : 1 ≤ 1 + alpha * Real.log (phi_of_shell referenceM + 1) := by
      nlinarith
    nlinarith
  exact inv_lt_one_of_one_lt₀ hgt

theorem quarkResidualDetuningDress_MeV_pos : 0 < quarkResidualDetuningDress_MeV := by
  unfold quarkResidualDetuningDress_MeV
  have h1000 : 0 < (1000 : ℝ) := by norm_num
  have href : referenceM = 4 := by
    unfold referenceM qcdShell stepsFromQCDToLockin latticeStepCount
    norm_num
  have hlat : 0 < (latticeSimplexCount referenceM : ℝ) := by
    rw [href]
    norm_num [latticeSimplexCount]
  have hden : 0 < oneOverAlphaEffAtShell referenceM := by
    unfold oneOverAlphaEffAtShell oneOverAlphaBare
    have hlog : 0 ≤ Real.log (phi_of_shell referenceM + 1) := by
      apply Real.log_nonneg
      have hphi : 1 ≤ phi_of_shell referenceM + 1 := by
        have hphi2 : (2 : ℝ) ≤ phi_of_shell referenceM := phi_of_shell_ge_two referenceM
        nlinarith
      linarith
    have halpha : 0 ≤ alpha := by
      rw [alpha_eq_3_5]
      positivity
    nlinarith
  have ha : 0 < alphaEffAtShell referenceM := by
    unfold alphaEffAtShell
    exact inv_pos.mpr hden
  have hmono : 0 < 1 + gamma_HQIV := by
    rw [gamma_eq_2_5]
    norm_num
  exact mul_pos (mul_pos (mul_pos h1000 hlat) ha) hmono

theorem quarkConstituentDress_MeV_gt_quarkResidualDetuningDress_MeV :
    quarkResidualDetuningDress_MeV < quarkConstituentDress_MeV := by
  have hα : alphaEffAtShell referenceM < (chargedLeptonContentCount : ℝ) := by
    have hlt := alphaEffAtShell_referenceM_lt_one
    have : alphaEffAtShell referenceM < (2 : ℝ) := by linarith
    simpa [chargedLeptonContentCount] using this
  let common : ℝ := (1000 : ℝ) * (latticeSimplexCount referenceM : ℝ) * (1 + gamma_HQIV)
  have hcommon : 0 < common := by
    have hlat : 0 < (latticeSimplexCount referenceM : ℝ) := by
      have href : referenceM = 4 := by
        unfold referenceM qcdShell stepsFromQCDToLockin latticeStepCount
        norm_num
      rw [href]
      norm_num [latticeSimplexCount]
    have hmono : 0 < 1 + gamma_HQIV := by
      rw [gamma_eq_2_5]
      norm_num
    nlinarith
  have hmul : common * alphaEffAtShell referenceM < common * (chargedLeptonContentCount : ℝ) :=
    mul_lt_mul_of_pos_left hα hcommon
  simpa [common, quarkConstituentDress_MeV, quarkResidualDetuningDress_MeV, mul_assoc, mul_left_comm, mul_comm]
    using hmul

theorem activeLightQuarkResidualOffset_up_gt_neg_average :
    -activeLightQuarkAverageMass_GeV < activeLightQuarkResidualOffset_GeV .upLike := by
  have hup : 0 < activeUpLightQuarkMass_GeV := activeUpLightQuarkMass_GeV_pos
  rw [← activeLightQuarkResidualOffset_up_add_average] at hup
  nlinarith

theorem activeLightQuarkResidualOffset_down_gt_neg_average :
    -activeLightQuarkAverageMass_GeV < activeLightQuarkResidualOffset_GeV .downLike := by
  have hdown : 0 < activeDownLightQuarkMass_GeV := activeDownLightQuarkMass_GeV_pos
  rw [← activeLightQuarkResidualOffset_down_add_average] at hdown
  nlinarith

theorem protonMassFromMetaHarmonics_eq_quantum_number_energy_budget :
    protonMassFromMetaHarmonics_MeV =
      quarkConstituentDress_MeV * ((3 : ℝ) * activeLightQuarkAverageMass_GeV) +
        quarkResidualDetuningDress_MeV * activeLightQuarkResidualOffset_GeV .upLike +
        nucleonIsospinGap_MeV := by
  unfold protonMassFromMetaHarmonics_MeV protonConstituentMass_MeV downConstituentMass_MeV
    upConstituentMass_MeV quarkConstituentBaseLift_MeV quarkResidualDetuningDress_MeV
    activeLightQuarkAverageMass_GeV activeLightQuarkResidualOffset_GeV
    quarkConstituentDress_MeV activeUpLightQuarkMass_GeV activeDownLightQuarkMass_GeV
  rw [nucleonIsospinGap_eq_one]
  set u : ℝ := allowedColorResonanceMass .upLike .light
  set d : ℝ := allowedColorResonanceMass .downLike .light
  set q : ℝ := (1000 : ℝ) * (latticeSimplexCount referenceM : ℝ) * (1 + gamma_HQIV) *
    (chargedLeptonContentCount : ℝ)
  set r : ℝ := (1000 : ℝ) * (latticeSimplexCount referenceM : ℝ) * alphaEffAtShell referenceM *
    (1 + gamma_HQIV)
  have hu : activeUpLightQuarkMass_GeV = u := by rfl
  have hd : activeDownLightQuarkMass_GeV = d := by rfl
  simp [activeLightQuarkAverageMass_GeV, hu, hd]
  change 2 * (((nucleonSharedBinding_MeV + 1) / 3) + q * ((u + d) / 2) + r * (u - (u + d) / 2)) +
      (((nucleonSharedBinding_MeV + 1) / 3) + q * ((u + d) / 2) + r * (d - (u + d) / 2)) -
      nucleonSharedBinding_MeV =
    q * (3 * ((u + d) / 2)) + r * (u - (u + d) / 2) + 1
  ring

theorem neutronMassFromMetaHarmonics_eq_quantum_number_energy_budget :
    neutronMassFromMetaHarmonics_MeV =
      quarkConstituentDress_MeV * ((3 : ℝ) * activeLightQuarkAverageMass_GeV) +
        quarkResidualDetuningDress_MeV * activeLightQuarkResidualOffset_GeV .downLike +
        nucleonIsospinGap_MeV := by
  unfold neutronMassFromMetaHarmonics_MeV neutronConstituentMass_MeV downConstituentMass_MeV
    upConstituentMass_MeV quarkConstituentBaseLift_MeV quarkResidualDetuningDress_MeV
    activeLightQuarkAverageMass_GeV activeLightQuarkResidualOffset_GeV
    quarkConstituentDress_MeV activeUpLightQuarkMass_GeV activeDownLightQuarkMass_GeV
  rw [nucleonIsospinGap_eq_one]
  set u : ℝ := allowedColorResonanceMass .upLike .light
  set d : ℝ := allowedColorResonanceMass .downLike .light
  set q : ℝ := (1000 : ℝ) * (latticeSimplexCount referenceM : ℝ) * (1 + gamma_HQIV) *
    (chargedLeptonContentCount : ℝ)
  set r : ℝ := (1000 : ℝ) * (latticeSimplexCount referenceM : ℝ) * alphaEffAtShell referenceM *
    (1 + gamma_HQIV)
  have hu : activeUpLightQuarkMass_GeV = u := by rfl
  have hd : activeDownLightQuarkMass_GeV = d := by rfl
  simp [activeLightQuarkAverageMass_GeV, hu, hd]
  change (((nucleonSharedBinding_MeV + 1) / 3) + q * ((u + d) / 2) + r * (u - (u + d) / 2)) +
      2 * (((nucleonSharedBinding_MeV + 1) / 3) + q * ((u + d) / 2) + r * (d - (u + d) / 2)) -
      nucleonSharedBinding_MeV =
    q * (3 * ((u + d) / 2)) + r * (d - (u + d) / 2) + 1
  ring

theorem protonMassFromMetaHarmonics_pos : 0 < protonMassFromMetaHarmonics_MeV := by
  rw [protonMassFromMetaHarmonics_eq_quantum_number_energy_budget, nucleonIsospinGap_eq_one]
  have hshared : 0 < quarkConstituentDress_MeV := quarkConstituentDress_MeV_pos
  have havg : 0 < activeLightQuarkAverageMass_GeV := activeLightQuarkAverageMass_GeV_pos
  have hres : 0 < quarkResidualDetuningDress_MeV := quarkResidualDetuningDress_MeV_pos
  have hgt : quarkResidualDetuningDress_MeV < quarkConstituentDress_MeV :=
    quarkConstituentDress_MeV_gt_quarkResidualDetuningDress_MeV
  have hoff : -activeLightQuarkAverageMass_GeV < activeLightQuarkResidualOffset_GeV .upLike :=
    activeLightQuarkResidualOffset_up_gt_neg_average
  have hmain :
      0 < quarkConstituentDress_MeV * ((3 : ℝ) * activeLightQuarkAverageMass_GeV) +
        quarkResidualDetuningDress_MeV * activeLightQuarkResidualOffset_GeV .upLike := by
    nlinarith
  nlinarith

theorem neutronMassFromMetaHarmonics_pos : 0 < neutronMassFromMetaHarmonics_MeV := by
  rw [neutronMassFromMetaHarmonics_eq_quantum_number_energy_budget, nucleonIsospinGap_eq_one]
  have hshared : 0 < quarkConstituentDress_MeV := quarkConstituentDress_MeV_pos
  have havg : 0 < activeLightQuarkAverageMass_GeV := activeLightQuarkAverageMass_GeV_pos
  have hres : 0 < quarkResidualDetuningDress_MeV := quarkResidualDetuningDress_MeV_pos
  have hgt : quarkResidualDetuningDress_MeV < quarkConstituentDress_MeV :=
    quarkConstituentDress_MeV_gt_quarkResidualDetuningDress_MeV
  have hoff : -activeLightQuarkAverageMass_GeV < activeLightQuarkResidualOffset_GeV .downLike :=
    activeLightQuarkResidualOffset_down_gt_neg_average
  have hmain :
      0 < quarkConstituentDress_MeV * ((3 : ℝ) * activeLightQuarkAverageMass_GeV) +
        quarkResidualDetuningDress_MeV * activeLightQuarkResidualOffset_GeV .downLike := by
    nlinarith
  nlinarith

theorem proton_neutron_split_from_dressed_light_quarks :
    neutronMassFromMetaHarmonics_MeV - protonMassFromMetaHarmonics_MeV =
      quarkResidualDetuningDress_MeV *
        (activeDownLightQuarkMass_GeV - activeUpLightQuarkMass_GeV) := by
  rw [protonMassFromMetaHarmonics_eq_quantum_number_energy_budget,
    neutronMassFromMetaHarmonics_eq_quantum_number_energy_budget,
    ← activeLightQuarkResidualOffset_up_add_average,
    ← activeLightQuarkResidualOffset_down_add_average]
  ring

theorem up_down_matrix_almost_identical :
    hyperchargeSignUp + hyperchargeSignDown = 0 := by
  norm_num [hyperchargeSignUp, hyperchargeSignDown, upResonanceAxis, downResonanceAxis,
    upQuarkAxis, downQuarkAxis]

theorem exactly_three_harmonics_only :
    ∃ k3 : ℕ,
      internalSurfaceArea (m_top_at_lockin + k3) < internalSurfaceArea m_top_at_lockin + 1 ∧
      ¬ ∃ fourthGen : Fin 3,
        fourthGen ≠ ⟨0, by decide⟩ ∧
          fourthGen ≠ ⟨1, by decide⟩ ∧
          fourthGen ≠ ⟨2, by decide⟩ := by
  refine ⟨0, ?_, ?_⟩
  · simp [m_top_at_lockin]
  · intro h
    rcases h with ⟨g, hg⟩
    fin_cases g
    · simp at hg
    · simp at hg
    · simp at hg

end Hqiv.Physics

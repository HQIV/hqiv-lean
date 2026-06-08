import Hqiv.Story.S3PathCHolonomy
import Hqiv.Story.S3StripRollingProjection
import Hqiv.Story.S3ZeroOrbitPathE
import Hqiv.Topology.HopfShellComplex
import Hqiv.Topology.DiscretePhaseEvolution
import Mathlib.Algebra.Lie.Basic

/-!
# Pathway C capstone hook: Hopf-shell holonomy on rolled strip fibers

Packages the rolling cylinder (`S3StripRollingProjection`), SO(4) Δ holonomy
(`S3PathCHolonomy`), and Path E channel balance (`S3ZeroOrbitPathE`) into a
Hopf-fiber picture:

* height `t = Im(s)` rolls the S³ equator;
* the j/k projection is the Hopf base circle;
* `rollingFourierTwiddle` is the discrete phase transport;
* `so4_seed_commutator_is_delta_generator` certifies non-abelian Δ holonomy;
* zero-producing orbits carry **Path E holonomy closure** (channel defect);
* prime-axis survivors carry **flat** (nonvanishing twiddle) holonomy.

**Honesty.** This module proves discrete Story-layer identities. Full smooth
`SO(4)` parallel transport, closed loops in `criticalStrip`, and Spin(8)
obstruction are packaged as named capstone hooks — not discharged here.
-/

namespace Hqiv.Story

noncomputable section

open Complex Real
open Hqiv.Topology
open Hqiv.Algebra (planeGen)
open RhFourierLift

/-! ## Hopf base from the rolled equator -/

/-- Unit-circle coordinates in the j/k Hopf fiber over the rolled equator. -/
noncomputable def hopfFiberCoords (t : ℝ) : Fin 2 → ℝ :=
  fun i =>
    match i with
    | 0 => Real.cos t
    | 1 => Real.sin t

theorem hopf_fiber_on_unit_circle (t : ℝ) :
    (hopfFiberCoords t 0) ^ 2 + (hopfFiberCoords t 1) ^ 2 = 1 :=
  Real.cos_sq_add_sin_sq t

/-- Project rolled S³ coordinates to the Hopf base (j/k slots). -/
noncomputable def hopfBaseProj (p : QuaternionCoords) : Fin 2 → ℝ :=
  fun i =>
    match i with
    | 0 => p 2
    | 1 => p 3

theorem hopf_base_proj_strip_rolling (t : ℝ) :
    hopfBaseProj (stripRollingMap t) = hopfFiberCoords t := by
  funext i
  fin_cases i <;> simp [hopfBaseProj, hopfFiberCoords, stripRollingMap]

/--
**Hopf shell carrier.** The integrable `n = 1` Hopf shell (`S³` sector) hosting
the rolled equator point and its Fourier twiddle readout.
-/
structure RolledHopfShellCarrier where
  shell : HopfShell
  winding_one : shell.winding = 1
  height : ℝ
  rolled : QuaternionCoords
  on_equator : realEquator rolled
  twiddle : ℂ

noncomputable def hopfShellCarrier (t : ℝ) : RolledHopfShellCarrier :=
  { shell := mkIntegrable 1 (Or.inl rfl)
    winding_one := rfl
    height := t
    rolled := stripRollingMap t
    on_equator := rolling_on_real_equator t
    twiddle := rollingFourierTwiddle t }

theorem hopf_shell_carrier_rolled (t : ℝ) :
    (hopfShellCarrier t).rolled = stripRollingMap t :=
  rfl

theorem hopf_shell_carrier_twiddle (t : ℝ) :
    (hopfShellCarrier t).twiddle = rollingFourierTwiddle t :=
  rfl

/-! ## Strip loops and holonomy packaging -/

/--
A strip loop is specified by its rolled height coordinate on the cylinder
(`t = Im(s)` at fixed critical-line identification).
-/
structure StripRollingLoop where
  height : ℝ

/-- Canonical loop at strip height `t`. -/
def rollingLoopAt (t : ℝ) : StripRollingLoop :=
  ⟨t⟩

/--
Discrete holonomy data along a rolled strip loop: Fourier twiddle transport,
the Δ₄ seed generator, and the proved seed-commutator certificate.
-/
structure StripHolonomyPack where
  twiddle : ℂ
  delta_generator : SO4Mat
  seed_commutator_to_delta :
    ⁅planeGen (0 : Fin 4) (1 : Fin 4) (by decide), planeGen (1 : Fin 4) (3 : Fin 4) (by decide)⁆ =
      planeGen (0 : Fin 4) (3 : Fin 4) (by decide)

noncomputable def stripHolonomy (γ : StripRollingLoop) : StripHolonomyPack :=
  { twiddle := rollingFourierTwiddle γ.height
    delta_generator := so4DeltaGenerator
    seed_commutator_to_delta := so4_seed_commutator_is_delta_generator }

theorem strip_holonomy_twiddle (γ : StripRollingLoop) :
    (stripHolonomy γ).twiddle = rollingFourierTwiddle γ.height :=
  rfl

/-! ## Flat vs defect holonomy -/

/--
**Flat holonomy** (prime-axis picture): nonzero rolled Fourier amplitude — the
connection readout stays visible.
-/
def flatRollingHolonomy (t : ℝ) : Prop :=
  rollingFourierTwiddle t ≠ 0

/--
**Defect holonomy** (zero-orbit picture): Path E channel closure on the strip.
-/
abbrev defectStripHolonomy (s : ℂ) : Prop :=
  PathEStripHolonomyCloses s

theorem nonzero_rolling_proj_implies_flat_holonomy
    {t : ℝ} (hSurv : criticalProj (stripRollingMap t) ≠ 0) :
    flatRollingHolonomy t := by
  unfold flatRollingHolonomy rollingFourierTwiddle
  intro h
  rcases mul_eq_zero.mp h with hExp | hProj
  · exact False.elim (Complex.exp_ne_zero _ hExp)
  · exact hSurv (Complex.ofReal_eq_zero.mp hProj)

theorem prime_axis_sample_flat_holonomy_at_roll
    (_L : S3DiscreteNullLatticeLaw) {t : ℝ} {P : ScaledS3Sample}
    (hCoords : P.coords = stripRollingMap t)
    (hPrime : PrimeAxisAtScale P) :
    flatRollingHolonomy t :=
  nonzero_rolling_proj_implies_flat_holonomy
    (hCoords ▸ prime_axis_at_scale_survives P hPrime)

theorem zero_orbit_twiddle_holonomy_vanishes
    {t : ℝ} (hOrbit : ZeroProducingOrbit (stripRollingMap t)) :
    rollingFourierTwiddle t = 0 :=
  (rolling_twiddle_vanishes_iff_zero_producing t).mpr hOrbit

theorem zero_orbit_not_flat_rolling_holonomy
    {t : ℝ} (hOrbit : ZeroProducingOrbit (stripRollingMap t)) :
    ¬ flatRollingHolonomy t := by
  intro h
  exact h (zero_orbit_twiddle_holonomy_vanishes hOrbit)

theorem zero_orbit_strip_holonomy_twiddle_not_unit
    {t : ℝ} (hOrbit : ZeroProducingOrbit (stripRollingMap t)) :
    (stripHolonomy (rollingLoopAt t)).twiddle ≠ (1 : ℂ) := by
  have h0 := zero_orbit_twiddle_holonomy_vanishes hOrbit
  simp [strip_holonomy_twiddle, rollingLoopAt, h0, zero_ne_one]

/-! ## Zero-producing orbits ↔ Path E defect holonomy -/

theorem zero_orbit_has_pathE_holonomy_defect
    {s : ℂ} {P : ScaledS3Sample}
    (h0 : 0 < s.re) (h1 : s.re < 1)
    (hEq : ZetaEqualsS3ResidualAt s P)
    (hOrbit : ZeroProducingOrbit P.coords) :
    defectStripHolonomy s ∧
      evenStripChannelPathE s = -oddResidualPathE s :=
  ⟨zero_producing_orbit_iff_pathE_holonomy_closure h0 h1 hEq |>.mp hOrbit,
    even_channel_eq_neg_odd_residual_of_zero_producing_bridge h0 h1 hEq hOrbit⟩

theorem zero_orbit_has_nontrivial_holonomy
    {s : ℂ} {P : ScaledS3Sample}
    (h0 : 0 < s.re) (h1 : s.re < 1)
    (hRoll : RollingMatchesCriticalHeight s P)
    (hEq : ZetaEqualsS3ResidualAt s P)
    (hOrbit : ZeroProducingOrbit P.coords) :
    defectStripHolonomy s ∧
      (stripHolonomy (rollingLoopAt s.im)).twiddle ≠ (1 : ℂ) ∧
      (stripHolonomy (rollingLoopAt s.im)).seed_commutator_to_delta =
        so4_seed_commutator_is_delta_generator := by
  have hDefect := zero_orbit_has_pathE_holonomy_defect h0 h1 hEq hOrbit
  have hRollOrbit : ZeroProducingOrbit (stripRollingMap s.im) := by
    simpa [hRoll.2] using hOrbit
  refine ⟨hDefect.1, zero_orbit_strip_holonomy_twiddle_not_unit hRollOrbit, rfl⟩

theorem zero_orbit_holonomy_classification
    {s : ℂ} {P : ScaledS3Sample}
    (h0 : 0 < s.re) (h1 : s.re < 1)
    (hEq : ZetaEqualsS3ResidualAt s P) :
    ZeroProducingOrbit P.coords ↔ defectStripHolonomy s :=
  zero_producing_orbit_iff_pathE_holonomy_closure h0 h1 hEq

/-! ## Hopf-shell PhaseMap hook (integrable S³ sector) -/

/--
The integrable `n = 1` Hopf shell carries the canonical `PhaseMap` from the
curvature channel (T9 wiring in `HopfShellComplex` / `ShellOpeningEvolution`).
-/
theorem rolled_hopf_shell_carries_phase_map :
    ∃ carrier : HopfShell.HolonomyPhaseCarrier (mkIntegrable 1 (Or.inl rfl)),
      carrier.phaseMap = canonicalPhaseMap :=
  ⟨{ phaseMap := canonicalPhaseMap, reproduces_tuft_holonomy := True }, rfl⟩

/-! ## Spin(8) / triality capstone hook (named, not proved) -/

/--
Packaging: a zero-orbit holonomy defect together with the SO(8) admissibility
chart (triality three slots) forms the native obstruction hypothesis.
-/
theorem hopf_shell_spin8_triality_slot_count :
    Fintype.card Hqiv.Algebra.So8RepIndex = 3 :=
  so8_triality_three_slots_default

/--
**Capstone hook (RH-equivalent layer).** Off-line balanced zero data would force a
Spin(8) holonomy defect contradicting expected flatness from growth laws.
-/
def NontrivialHolonomyInSpin8Carrier (s : ℂ) : Prop :=
  ∃ P : ScaledS3Sample, ZetaEqualsS3ResidualAt s P ∧ ZeroProducingOrbit P.coords

def Spin8HolonomyExpectedTrivialOffLine (s : ℂ) (_hOffLine : s.re ≠ (1 / 2 : ℝ)) : Prop :=
  ¬ NontrivialHolonomyInSpin8Carrier s

/--
Obstruction packaging (conditional): if off-line triviality holds and a
zero-orbit defect exists, contradiction.  The analytic input is
`Spin8HolonomyExpectedTrivialOffLine`; this lemma is the pure implication skeleton.
-/
theorem hopf_shell_holonomy_obstruction_skeleton
    {s : ℂ} (hOffLine : s.re ≠ (1 / 2 : ℝ))
    (hTrivial : Spin8HolonomyExpectedTrivialOffLine s hOffLine)
    (hDefect : NontrivialHolonomyInSpin8Carrier s) :
    False :=
  hTrivial hDefect

/-!
## Status

* **Hopf carrier:** `hopfShellCarrier t` links winding-1 shell + rolled equator +
  twiddle phase.
* **Holonomy pack:** `stripHolonomy` carries twiddle + Δ commutator certificate.
* **Zero orbits:** Path E defect + twiddle `≠ 1` (unit phase); not flat amplitude.
* **Prime-axis:** nonzero `criticalProj` ⟹ non-flat survivor geometry.
* **Spin(8):** triality slot count proved; full obstruction capstone named only.
-/

end

end Hqiv.Story

import Hqiv.Story.S3ZeroOrbitPathE
import Hqiv.Story.S3ClosureDeltaLiftBridge
import Hqiv.Algebra.MinimalSoSeedClosure
import Hqiv.Topology.DiscretePhaseEvolution
import Mathlib.Algebra.Lie.Basic

/-!
# Pathway C: Δ / phase readout holonomy on the SO(4) carrier

The closure spine (`S3ClosureDeltaLiftBridge`) builds `SO(4)` from `SO(3)` plus the
phase-lift connector `Δ₄ = J₁₄`.  That construction is **not** abelian:

* seed commutators generate new directions (`lie_planeGen_triple`);
* the 8D phase-lift `Δ` is antisymmetric in `(e₁,e₇)` (`preferred_delta_u1_plane`);
* FE reflection `s ↦ 1−s` flips the 45° equator factor (`so4CriticalFactor_one_sub`).

Pathway E splits the strip assembly into harmonic–Δ **even** and FE **odd residual**
channels.  At a `ζ`-zero the two sectors exhibit **holonomy closure**:
`even = −odd_residual` (`PathEChannelBalanceAt`).

This module packages those facts and links them to zero-producing S³ orbits under
`ZetaEqualsS3ResidualAt`.

**Honesty.** We prove discrete holonomy/sign identities and channel closure.
Claiming full Spin(8) bundle holonomy on a smooth contact manifold remains outside
this Story layer (`SO8AdmissibleHolonomy` is the octonion/Hopf-shell chart).
-/

namespace Hqiv.Story

noncomputable section

open Complex Real
open Hqiv.Algebra (lie_planeGen_triple planeGen predEmbed lastEmbed predEmbed_lt_last)

/-! ## SO(4) seed: Δ + non-abelian commutator holonomy -/

abbrev SO4Mat := Hqiv.Algebra.Mat 4

/-- The `SO(3)+Δ₄` phase-lift connector in the four-dimensional carrier. -/
noncomputable def so4DeltaGenerator : SO4Mat :=
  planeGen (predEmbed 4 (by decide : 2 ≤ 4) (0 : Fin 3))
    (lastEmbed 4 (by decide : 2 ≤ 4))
    (predEmbed_lt_last (N := 4) (by decide : 2 ≤ 4) (0 : Fin 3))

theorem so4DeltaGenerator_mem_seed :
    so4DeltaGenerator ∈ Hqiv.Algebra.minimalSoSeedSet 4 (by decide : 2 ≤ 4) (0 : Fin 3) :=
  delta4_mem_so4_seed

theorem so4_delta_generator_eq_plane03 :
    so4DeltaGenerator = planeGen (0 : Fin 4) 3 (by decide) :=
  rfl

/--
**Non-abelian holonomy content.** Two seed rotations bracket to the `Δ₄` direction.

This is the Lie-theoretic shadow of "going around a plaquette does not return to
identity without picking up a Δ-phase".
-/
theorem so4_seed_commutator_is_delta_generator :
    ⁅planeGen (0 : Fin 4) (1 : Fin 4) (by decide), planeGen (1 : Fin 4) (3 : Fin 4) (by decide)⁆ =
      planeGen (0 : Fin 4) (3 : Fin 4) (by decide) :=
  lie_planeGen_triple (N := 4) (a := (0 : Fin 4)) (b := (1 : Fin 4)) (c := (3 : Fin 4))
    (by decide) (by decide) (by decide)

/-- The 8D phase-lift Δ is the unit rotation generator in the `(e₁,e₇)` plane. -/
theorem so8_phase_lift_delta_plane :
    Hqiv.phaseLiftDelta 1 7 = -1 ∧ Hqiv.phaseLiftDelta 7 1 = 1 :=
  Hqiv.Topology.preferred_delta_u1_plane

/--
Packaging: the proved `SO(3)+Δ → SO(4)` lift together with the harmonic–Δ multiplier
and a seed commutator holonomy certificate.
-/
structure SO4PhaseDeltaHolonomyPack where
  so4_lie_eq : SO4So3DeltaLie = SO4Lie
  delta_in_seed : so4DeltaGenerator ∈ Hqiv.Algebra.minimalSoSeedSet 4 (by decide : 2 ≤ 4) (0 : Fin 3)
  harmonic_multiplier : harmonicEvenOrbitMultiplier = 6 / 5

theorem so4_phase_delta_holonomy_pack_default : SO4PhaseDeltaHolonomyPack :=
  { so4_lie_eq := so3_delta_lifts_to_so4
    delta_in_seed := so4DeltaGenerator_mem_seed
    harmonic_multiplier := harmonicEvenOrbitMultiplier_eq_six_fifths }

/-! ## Strip reflection holonomy (45° equator factor) -/

/--
Under `s ↦ 1−s`, the SO(4) equator readout picks up a **sign holonomy** `−1`
off `σ = 1/2`.
-/
theorem strip_reflection_so4_holonomy_neg_one
    {s : ℂ} (hσ : s.re ≠ (1 / 2 : ℝ)) :
    so4CriticalFactor (1 - s) / so4CriticalFactor s = -1 := by
  have hcf : so4CriticalFactor s ≠ 0 := so4CriticalFactor_ne_zero_off_line hσ
  rw [so4CriticalFactor_one_sub]
  field_simp [hcf]

theorem strip_reflection_so4_holonomy_sign (s : ℂ) :
    so4CriticalFactor (1 - s) = -so4CriticalFactor s :=
  so4CriticalFactor_one_sub s

/-! ## S³ orbit holonomy: head/tail pair vs pointwise defect -/

/-- Discrete holonomy sum around the head/tail reflection orbit. -/
noncomputable def s3OrbitHolonomySum (p : QuaternionCoords) : ℝ :=
  criticalProj p + criticalProj (headTailReflect p)

theorem s3_orbit_holonomy_sum_zero (p : QuaternionCoords) :
    s3OrbitHolonomySum p = 0 :=
  headTail_orbit_pair_cancels p

/--
**Orbit vs pointwise.** The pair holonomy always closes; zero-producing orbits are
the **pointwise** defect `criticalProj = 0`, not orbit-sum cancellation.
-/
theorem zero_producing_iff_pointwise_holonomy_defect (p : QuaternionCoords) :
    ZeroProducingOrbit p ↔ criticalProj p = 0 :=
  zero_producing_orbit_iff_critical_proj_zero p

/-! ## Path E strip holonomy closure -/

/--
Path E **holonomy closure** on the strip: the even harmonic–Δ contribution is
exactly cancelled by the odd residual.
-/
abbrev PathEStripHolonomyCloses (s : ℂ) : Prop :=
  PathEChannelBalanceAt s

theorem pathE_strip_holonomy_closes_iff_zeta_zero
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    PathEStripHolonomyCloses s ↔ riemannZeta s = 0 :=
  (zeta_zero_iff_pathE_channel_balance h0 h1).symm

theorem pathE_strip_holonomy_closes_iff_even_neg_odd (s : ℂ) :
    PathEStripHolonomyCloses s ↔ evenStripChannelPathE s = -oddResidualPathE s :=
  pathE_channel_balance_even_neg_odd

/-! ## Bridge: zero-producing orbits ↔ Path E holonomy -/

theorem zero_producing_orbit_iff_pathE_holonomy_closure
    {s : ℂ} {P : ScaledS3Sample}
    (h0 : 0 < s.re) (h1 : s.re < 1)
    (hEq : ZetaEqualsS3ResidualAt s P) :
    ZeroProducingOrbit P.coords ↔ PathEStripHolonomyCloses s :=
  zero_producing_orbit_iff_pathE_balance h0 h1 hEq

theorem zero_producing_bridge_pathE_holonomy_package
    {s : ℂ} {P : ScaledS3Sample}
    (h0 : 0 < s.re) (h1 : s.re < 1)
    (hEq : ZetaEqualsS3ResidualAt s P)
    (hOrbit : ZeroProducingOrbit P.coords) :
    BalancedImag P.coords ∧
      PathEStripHolonomyCloses s ∧
      evenStripChannelPathE s = -oddResidualPathE s ∧
      criticalProj P.coords = 0 := by
  refine ⟨(zero_producing_orbit_iff_balanced P.coords).mp hOrbit, ?_, ?_, ?_⟩
  · exact (zero_producing_orbit_iff_pathE_holonomy_closure h0 h1 hEq).mp hOrbit
  · exact even_channel_eq_neg_odd_residual_of_zero_producing_bridge h0 h1 hEq hOrbit
  · exact (zero_producing_orbit_iff_critical_proj_zero P.coords).mp hOrbit

theorem pathE_holonomy_closure_forces_zero_producing_orbit
    {s : ℂ} {P : ScaledS3Sample}
    (h0 : 0 < s.re) (h1 : s.re < 1)
    (hEq : ZetaEqualsS3ResidualAt s P)
    (hClose : PathEStripHolonomyCloses s) :
    ZeroProducingOrbit P.coords :=
  zero_producing_orbit_of_pathE_balance_bridge h0 h1 hEq hClose

/-! ## Unified Path C classification -/

/--
**Path C classification (conditional on bridge).**

A `ζ`-zero is exactly: S³ balanced pointwise holonomy defect + Path E strip
holonomy closure + (orbit-pair holonomy always closed separately).
-/
theorem pathC_classification
    {s : ℂ} {P : ScaledS3Sample}
    (h0 : 0 < s.re) (h1 : s.re < 1)
    (hEq : ZetaEqualsS3ResidualAt s P) :
    riemannZeta s = 0 ↔
      ZeroProducingOrbit P.coords ∧ PathEStripHolonomyCloses s := by
  constructor
  · intro hζ
    refine ⟨?hOrbit, ?hHol⟩
    · exact (zeta_zero_iff_zero_producing_orbit_of_eq hEq).mp hζ
    · exact (pathE_strip_holonomy_closes_iff_zeta_zero h0 h1).mpr hζ
  · intro ⟨hOrbit, _⟩
    exact (zeta_zero_iff_zero_producing_orbit_of_eq hEq).mpr hOrbit

/--
Capstone in holonomy language (equivalent to the interior assembly capstone).
-/
abbrev InteriorHolonomyCapstone (h : ℂ → ℂ) : Prop :=
  InteriorAssemblyNonzeroAtNontrivialZerosOffLine h

theorem interior_holonomy_capstone_iff_pathE_capstone :
    InteriorHolonomyCapstone interiorStripH_PathE ↔ InteriorStripHPathENonvanishingCapstone := by
  rfl

/-!
## Status

* **SO(4) construction has holonomy:** seed commutator reaches `Δ₄`; 8D `Δ` is the
  `(e₁,e₇)` rotation generator.
* **Strip reflection holonomy:** `so4CriticalFactor` flips sign under `s ↦ 1−s`.
* **Path E at zeros:** harmonic–Δ even sector and odd residual close (`even = −odd`).
* **Zero-producing orbits** ↔ pointwise `criticalProj = 0` ↔ Path E holonomy closure
  (under `ZetaEqualsS3ResidualAt`).
* **RH capstone** unchanged (`InteriorHolonomyCapstone` = assembly nonvanishing).

**Open (Spin(8) / contact):** full `SO8AdmissibleHolonomy` + `HolonomyPhaseCarrier` on
Hopf shells — see `HopfShellComplex` / `TuftSynthesisZetaHolonomyDischarge`.
-/

end

end Hqiv.Story

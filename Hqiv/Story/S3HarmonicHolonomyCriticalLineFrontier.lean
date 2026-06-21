import Hqiv.Geometry.AlphaGammaForcedByLattice
import Hqiv.Story.S3HarmonicMulModCubeLieTransportBridge
import Hqiv.Story.S3DiophantineTransformer
import Hqiv.Story.S3LogPhaseZetaCouplingFrontier
import Hqiv.Story.S3ZetaGoldbachTailBandCrossChannelBridge
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Diagonal

/-!
# Harmonic holonomy → Hilbert–Pólya frontier (named, honest)

Three research routes toward RH-from-axioms, packaged without circular discharge
(plus a fourth **associator perturbation** route in
`S3HarmonicHolonomyAssociatorPerturb`):

1. **Lie-promoted holonomy operator.**  The structured cascade prefix
   `{6,5,11,13,…}` indexes an explicit **normal diagonal operator**
   `harmonicCascadeHolonomyTransformer`.  Its FE-reflected adjoint pins
   `Re s = 1/2` entrywise; at nontrivial zeros, RH ⟺ adjoint-across-FE
   (`RH_iff_holonomy_cascade_adjoint_at_zeros`).

2. **Tail-band phase readout.**  The closed `ζ(2)−ζ(3)` band is **positive**
   and literal; the critical-line phase carrier `tailBandCriticalLinePhase`
   satisfies a conjugation law (unit-circle reflection) and packages the
   trace/FE harmonic backbone shared with the Diophantine transformer.

3. **HQIV axioms → σ–t coupling witness.**  Once the geometric stack
   (`HarmonicCascadeTailBandFrontier` + forced `(α,γ)`) is in place,
   every nontrivial zero carries `SigmaTPhaseCouplingAt` unconditionally.
   **Forcing** the line from coupling alone remains RH-equivalent — the axiom
   stack supplies witnesses, not the millennium discharge.

4. **Associator perturbation (route 4).**  See `S3HarmonicHolonomyAssociatorPerturb`:
   anti-Hermitian `octAssociatorChannel` sheet on `(6,5,11)`, diagonal adjoint preserved on
   the line, explicit defect `M(1-s)−M(s)ᴴ = P(1-s)+P(s)`, and machine-checkable non-normality.
-/

namespace Hqiv.Story

open Hqiv Hqiv.Geometry Complex Real Matrix Filter

noncomputable section

/-! ## Route 1 — cascade-indexed holonomy operator -/

/--
**Cascade holonomy transformer.**  Diagonal operator on `ℂ^N` whose entries are
the spectral lines of the harmonic prefix trials (Lie-promoted cascade slots),
not the contiguous indices `1,…,N`.
-/
noncomputable def harmonicCascadeHolonomyTransformer (N : ℕ) (_hN : 2 ≤ N) (s : ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun i => so4SpectralLine (harmonicCascadeTrial (i : ℕ)) s

private theorem harmonic_cascade_trial_ge_two (i : ℕ) : 2 ≤ harmonicCascadeTrial i := by
  unfold harmonicCascadeTrial
  split <;> decide

theorem harmonic_cascade_holonomy_transformer_mul_comm (N : ℕ) (hN : 2 ≤ N) (s s' : ℂ) :
    harmonicCascadeHolonomyTransformer N hN s * harmonicCascadeHolonomyTransformer N hN s' =
      harmonicCascadeHolonomyTransformer N hN s' * harmonicCascadeHolonomyTransformer N hN s := by
  unfold harmonicCascadeHolonomyTransformer
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem harmonic_cascade_holonomy_transformer_normal (N : ℕ) (hN : 2 ≤ N) (s : ℂ) :
    harmonicCascadeHolonomyTransformer N hN s * (harmonicCascadeHolonomyTransformer N hN s)ᴴ =
      (harmonicCascadeHolonomyTransformer N hN s)ᴴ * harmonicCascadeHolonomyTransformer N hN s := by
  unfold harmonicCascadeHolonomyTransformer
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

/--
**Adjoint law on cascade slots:** FE reflection equals the conjugate-transpose
exactly on the critical line — the cascade-indexed Hilbert–Pólya face.
-/
theorem harmonic_cascade_holonomy_transformer_adjoint_iff {N : ℕ} (hN : 2 ≤ N) {s : ℂ} :
    harmonicCascadeHolonomyTransformer N hN (1 - s) =
      (harmonicCascadeHolonomyTransformer N hN s)ᴴ ↔
        s.re = (1 / 2 : ℝ) := by
  unfold harmonicCascadeHolonomyTransformer
  rw [Matrix.diagonal_conjTranspose]
  constructor
  · intro h
    have := congrArg (fun M => M ⟨1, by omega⟩ ⟨1, by omega⟩) h
    simp only [Matrix.diagonal_apply_eq, Pi.star_apply] at this
    exact (transformer_entry_adjoint_iff (harmonic_cascade_trial_ge_two 1)).mp this
  · intro hσ
    congr 1
    funext i
    simp only [Pi.star_apply]
    exact (transformer_entry_adjoint_iff (harmonic_cascade_trial_ge_two (i : ℕ))).mpr hσ

/--
**Structured Lie promotion bundles the cascade multiplier** used to build the
holonomy chart transport; on obstruction shells it equals the first coprime
prefix transition.
-/
structure HolonomyChartLiePromotionOperatorBundle (n : ℕ) (hn : 0 < n) where
  chart : Mod7CubeHolonomyChart
  promotion : SO4StructuredCascadeLiePromotion n hn
  chart_eq_default : chart = mod7CubeHolonomyChart_default
  promotion_eq_structured : promotion = so4LiePromotion_structured n hn

noncomputable def holonomyChartLiePromotionOperatorBundle_default (n : ℕ) (hn : 0 < n) :
    HolonomyChartLiePromotionOperatorBundle n hn where
  chart := mod7CubeHolonomyChart_default
  promotion := so4LiePromotion_structured n hn
  chart_eq_default := rfl
  promotion_eq_structured := rfl

theorem holonomy_chart_bundle_multiplier_eq (n : ℕ) (hn : 0 < n)
    (B : HolonomyChartLiePromotionOperatorBundle n hn) :
    B.promotion.multiplier = harmonicStructuredCascadeMultiplier n hn := by
  rw [B.promotion_eq_structured, (so4LiePromotion_structured n hn).multiplier_eq]

theorem holonomy_chart_bundle_transition_on_obstruction (n : ℕ) (hn : 0 < n)
    (B : HolonomyChartLiePromotionOperatorBundle n hn)
    (hncop : ¬ HarmonicMulModMultiplierCoprimeObstruction n) :
    B.promotion.multiplier =
      structuredCascadeTransition n hn (harmonicFirstCoprimeCascadeIndex n hn) := by
  rw [B.promotion_eq_structured]
  exact (so4LiePromotion_structured n hn).transition_eq hncop

/--
**RH in cascade holonomy language:** at every nontrivial zero the FE-reflected
cascade transformer is the adjoint — parallel to
`RH_iff_transformer_adjoint_at_zeros` on contiguous indices.
-/
theorem RH_iff_holonomy_cascade_adjoint_at_zeros {N : ℕ} (hN : 2 ≤ N) :
    RiemannHypothesis ↔
      ∀ ρ : ℂ, IsNontrivialZetaZero ρ →
        harmonicCascadeHolonomyTransformer N hN (1 - ρ) =
          (harmonicCascadeHolonomyTransformer N hN ρ)ᴴ := by
  constructor
  · intro hRH ρ hz
    exact (harmonic_cascade_holonomy_transformer_adjoint_iff hN).mpr
      (hRH ρ hz.1 hz.2.1 hz.2.2)
  · intro hA ρ hz hnt h1
    exact (harmonic_cascade_holonomy_transformer_adjoint_iff hN).mp
      (hA ρ ⟨hz, hnt, h1⟩)

/-! ## Route 2 — tail-band phase / positivity / FE backbone -/

/--
**Critical-line phase carrier** for the closed tail-band height.  Modulus is the
proved positive band width; imaginary argument tracks the height variable `t`.
This is the honest σ–t split: the band height is σ-blind, the unit phase is
t-dependent.
-/
noncomputable def tailBandCriticalLinePhase (t : ℝ) : ℂ :=
  Complex.exp ((Real.pi * t : ℂ) * Complex.I) * (goldbachAnnulusZetaTailBandWidth : ℂ)

theorem tailBandCriticalLinePhase_modulus (t : ℝ) :
    ‖tailBandCriticalLinePhase t‖ = goldbachAnnulusZetaTailBandWidth := by
  have hpos : 0 < goldbachAnnulusZetaTailBandWidth := goldbach_annulus_zeta_tail_band_width_pos
  have hunit : ‖Complex.exp ((Real.pi * t : ℂ) * Complex.I)‖ = 1 := by
    simpa [Complex.ofReal_mul] using Complex.norm_exp_ofReal_mul_I (Real.pi * t)
  simp [tailBandCriticalLinePhase, Complex.norm_mul, hunit, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hpos.le]

theorem tailBandCriticalLinePhase_pos (t : ℝ) :
    0 < ‖tailBandCriticalLinePhase t‖ := by
  rw [tailBandCriticalLinePhase_modulus t]
  exact goldbach_annulus_zeta_tail_band_width_pos

theorem tailBandCriticalLinePhase_conj (t : ℝ) :
    star (tailBandCriticalLinePhase t) = tailBandCriticalLinePhase (-t) := by
  apply Complex.ext
  · simp [tailBandCriticalLinePhase, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.exp_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, Complex.exp_im, neg_mul, Real.cos_neg,
      Real.sin_neg, mul_comm, mul_left_comm, mul_assoc]
  · simp [tailBandCriticalLinePhase, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.exp_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, Complex.exp_im, neg_mul, Real.cos_neg,
      Real.sin_neg, mul_comm, mul_left_comm, mul_assoc]

/--
**Regularized tail-band package** — positivity + literal Mathlib ζ identity +
Diophantine FE trace backbone (Connes / Hilbert–Pólya analog at the trace level).
-/
structure TailBandRegularizedPhaseCarrier where
  band_pos : 0 < goldbachAnnulusZetaTailBandWidth
  band_literal : ((goldbachAnnulusZetaTailBandWidth : ℝ) : ℂ) = riemannZeta 2 - riemannZeta 3
  fe_trace_backbone :
    ∀ (N : ℕ) (s : ℂ), 2 ≤ N →
      (diophantineTransformer N s * diophantineTransformer N (1 - s)).trace =
        ((harmonicPartialSum N : ℝ) : ℂ)

theorem tailBand_regularized_phase_carrier_default : TailBandRegularizedPhaseCarrier where
  band_pos := goldbach_annulus_zeta_tail_band_width_pos
  band_literal := zeta_goldbach_tail_band_is_literal_zeta_two_minus_zeta_three
  fe_trace_backbone := fun N s hN => feProduct_trace_eq_harmonic N s

/--
At `σ = 1/2` the cascade holonomy operator is a **scaled isometry** with
rational defect diagonal — the same FE-composition pattern as the contiguous
transformer, specialized to cascade slots.
-/
theorem harmonic_cascade_holonomy_fe_product {N : ℕ} (hN : 2 ≤ N) (s : ℂ) :
    harmonicCascadeHolonomyTransformer N hN s *
      harmonicCascadeHolonomyTransformer N hN (1 - s) =
      Matrix.diagonal fun i : Fin N =>
        ((harmonicCascadeTrial (i : ℕ) : ℂ))⁻¹ := by
  unfold harmonicCascadeHolonomyTransformer
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  unfold so4SpectralLine
  have hpos : 0 < harmonicCascadeTrial (i : ℕ) :=
    Nat.lt_of_lt_of_le (by decide : 0 < 2) (harmonic_cascade_trial_ge_two (i : ℕ))
  have hne : ((harmonicCascadeTrial (i : ℕ) : ℂ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr hpos.ne'
  push_cast
  rw [← cpow_add _ _ hne, show -s + -(1 - s) = (-1 : ℂ) by ring, cpow_neg_one]

theorem tail_band_phase_adjoint_pin_iff_critical_line {N : ℕ} (hN : 2 ≤ N) {s : ℂ} :
    harmonicCascadeHolonomyTransformer N hN (1 - s) =
      (harmonicCascadeHolonomyTransformer N hN s)ᴴ ↔
        s.re = (1 / 2 : ℝ) :=
  harmonic_cascade_holonomy_transformer_adjoint_iff hN

/-! ## Route 3 — HQIV axioms discharge σ–t coupling witnesses -/

/--
**HQIV geometric axiom stack** below millennium discharge: forced `(α,γ)` from
the discrete null lattice + monogamy split, together with the proved harmonic
cascade / tail-band / structured Lie promotion frontier.
-/
def HQIVGeometricAxiomStack : Prop :=
  (Hqiv.alpha = (3 / 5 : ℝ) ∧ Hqiv.gamma_HQIV = (2 / 5 : ℝ) ∧ Hqiv.alpha + Hqiv.gamma_HQIV = 1) ∧
    HarmonicCascadeTailBandFrontier

theorem hqiv_geometric_axiom_stack :
    HQIVGeometricAxiomStack :=
  ⟨Hqiv.alpha_gamma_forced_pair, harmonic_cascade_tail_band_frontier⟩

/--
Once the geometric stack is in place, **every nontrivial zero carries σ–t
coupling data** (log–Goldbach witness + global two-prime height pin).  This is
unconditional; it does not force `Re ρ = 1/2` without the global gate.
-/
theorem sigma_t_coupling_witness_from_hqiv_axiom_stack
    (_h : HQIVGeometricAxiomStack) {ρ : ℂ} (hζ : IsNontrivialZetaZero ρ) :
    SigmaTPhaseCouplingAt ρ :=
  sigma_t_coupling_at_every_nontrivial_zero hζ

theorem sigma_t_forcing_remains_rh_equivalent_with_axiom_stack
    (_h : HQIVGeometricAxiomStack) :
    SigmaTPhaseCouplingForcesCriticalLine ↔ RiemannHypothesis :=
  sigma_t_coupling_forces_critical_line_iff_RH

/--
**Named joint frontier** for the three routes: geometric axioms + cascade RH
axiom bundle + explicit holonomy adjoint law + tail-band phase carrier.
-/
def HarmonicHolonomyCriticalLineFrontier : Prop :=
  HQIVGeometricAxiomStack ∧
    HarmonicCascadeRhAxiomFrontier ∧
      TailBandRegularizedPhaseCarrier ∧
        (∀ (N : ℕ) (hN : 2 ≤ N) (s : ℂ),
          harmonicCascadeHolonomyTransformer N hN (1 - s) =
            (harmonicCascadeHolonomyTransformer N hN s)ᴴ ↔ s.re = (1 / 2 : ℝ))

theorem harmonic_holonomy_critical_line_frontier :
    HarmonicHolonomyCriticalLineFrontier := by
  refine ⟨hqiv_geometric_axiom_stack, ?_, tailBand_regularized_phase_carrier_default, ?_⟩
  · exact harmonic_cascade_rh_axiom_frontier
  · intro N hN s
    exact harmonic_cascade_holonomy_transformer_adjoint_iff hN

theorem RH_of_harmonic_holonomy_frontier_and_sigma_t_forcing
    (h : HarmonicHolonomyCriticalLineFrontier)
    (hForce : SigmaTPhaseCouplingForcesCriticalLine) :
    RiemannHypothesis :=
  RH_of_harmonic_cascade_axiom_frontier_and_coupling h.2.1 hForce

theorem harmonic_holonomy_frontier_plus_capstone_iff_millennium
    (W : TempLadderFiniteWindowConcrete) :
    HarmonicHolonomyCriticalLineFrontier ∧ ZetaGoldbachTailBandJointCapstone ↔
      RiemannHypothesis ∧ GoldbachParity := by
  constructor
  · intro ⟨hFront, hCap⟩
    exact zeta_goldbach_joint_capstone_iff_millennium.mp hCap
  · intro hMill
    exact ⟨harmonic_holonomy_critical_line_frontier,
      zeta_goldbach_joint_capstone_iff_millennium.mpr hMill⟩

end

end Hqiv.Story

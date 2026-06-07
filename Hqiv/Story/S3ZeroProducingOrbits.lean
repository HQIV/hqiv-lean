import Hqiv.Story.S3InteriorPathA
import Hqiv.Story.S3ZetaAxisRotationProjection
import Hqiv.Story.S3PoleZeroChannel
import Hqiv.Story.S3CenteredResidualModel

/-!
# Zero-producing orbits on the S³ shell (SO(4) 45° projection)

Geometric picture (story layer):

* **Prime-axis survivors** (`IsSingleAxis`, and at prime scale `PrimeAxisAtScale`)
  carry nonzero `criticalProj` — they are the visible, non-cancelling orbits.
* **Zero-producing orbits** are those where the 45° readout fully cancels:
  `criticalProj p = 0`, equivalently `BalancedImag p` (`imagSum p = 0`).

Head/tail reflection pairs always cancel as orbits; pointwise vanishing is exactly
the balanced imaginary hyperplane.  Single-axis points cannot balance
(`not_balanced_of_singleAxis`), so prime-axis poles never produce zeros.

This module packages that classification and links it to ζ only under the
explicit bridge `ZetaEqualsS3ResidualAt` (or a centered residual model).  It does
**not** identify ζ-zeros with interior-strip `h`-zeros without that bridge.

Pathway A (`S3InteriorPathA`) supplies the strip functional equation; this module
supplies the orbit geometry of the zero locus once the analytic identification is
assumed.
-/

namespace Hqiv.Story

/-! ## Zero-producing orbit classification -/

/--
Orbits on the S³ shell whose 45° critical projection vanishes.

`balancedMultiAxis` — balanced imaginary content and not a pure single-axis
survivor (trivial-imag or genuinely multi-axis cancellation).

`fullCancellation` — explicit vanishing of `criticalProj` (equivalent to balance).
-/
inductive ZeroProducingOrbit (p : QuaternionCoords) : Prop
  | balancedMultiAxis (hBal : BalancedImag p) (hNotSingle : ¬ IsSingleAxis p)
  | fullCancellation (hCancel : criticalProj p = 0)

theorem not_singleAxis_of_balanced (p : QuaternionCoords) (hBal : BalancedImag p) :
    ¬ IsSingleAxis p := by
  intro hSingle
  exact not_balanced_of_singleAxis p hSingle hBal

theorem zero_producing_orbit_iff_balanced (p : QuaternionCoords) :
    ZeroProducingOrbit p ↔ BalancedImag p := by
  constructor
  · rintro (⟨hBal, _⟩ | ⟨hCancel⟩)
    · exact hBal
    · exact (criticalProj_eq_zero_iff_balanced p).1 hCancel
  · intro hBal
    exact .balancedMultiAxis hBal (not_singleAxis_of_balanced p hBal)

theorem zero_producing_orbit_iff_critical_proj_zero (p : QuaternionCoords) :
    ZeroProducingOrbit p ↔ criticalProj p = 0 := by
  rw [zero_producing_orbit_iff_balanced, criticalProj_eq_zero_iff_balanced]

theorem not_zero_producing_of_singleAxis (p : QuaternionCoords) (hSingle : IsSingleAxis p) :
    ¬ ZeroProducingOrbit p := by
  intro hOrbit
  exact not_balanced_of_singleAxis p hSingle
    ((zero_producing_orbit_iff_balanced p).mp hOrbit)

theorem single_axis_critical_proj_nonzero (p : QuaternionCoords) (hSingle : IsSingleAxis p) :
    criticalProj p ≠ 0 :=
  criticalProj_ne_zero_of_singleAxis p hSingle

/-! ## Sample-level packaging -/

def SampleZeroProducingOrbit (P : ScaledS3Sample) : Prop :=
  ZeroProducingOrbit P.coords

theorem sample_zero_producing_iff_s3_pole_channel (P : ScaledS3Sample) :
    SampleZeroProducingOrbit P ↔ S3PoleChannel P := by
  dsimp [SampleZeroProducingOrbit, S3PoleChannel, S3ResidualZero]
  exact zero_producing_orbit_iff_critical_proj_zero P.coords

theorem sample_zero_producing_iff_balanced (P : ScaledS3Sample) :
    SampleZeroProducingOrbit P ↔ BalancedImag P.coords :=
  zero_producing_orbit_iff_balanced P.coords

/-! ## ζ bridge (conditional on identification) -/

theorem zeta_zero_iff_zero_producing_orbit_of_eq
    {s : ℂ} {P : ScaledS3Sample}
    (hEq : ZetaEqualsS3ResidualAt s P) :
    riemannZeta s = 0 ↔ ZeroProducingOrbit P.coords := by
  rw [zero_producing_orbit_iff_balanced P.coords]
  exact zeta_zero_iff_balanced_of_eq hEq

theorem zeta_zero_iff_sample_zero_producing_orbit_of_eq
    {s : ℂ} {P : ScaledS3Sample}
    (hEq : ZetaEqualsS3ResidualAt s P) :
    riemannZeta s = 0 ↔ SampleZeroProducingOrbit P := by
  dsimp [SampleZeroProducingOrbit]
  exact zeta_zero_iff_zero_producing_orbit_of_eq hEq

theorem zeta_nonzero_iff_prime_axis_survivor_of_eq_and_law
    (L : S3DiscreteNullLatticeLaw)
    {s : ℂ} {P : ScaledS3Sample}
    (hEq : ZetaEqualsS3ResidualAt s P) :
    riemannZeta s ≠ 0 ↔ PrimeAxisAtScale P :=
  zeta_nonzero_iff_primeAxisAtScale_of_eq_and_law L hEq

/--
Prime-axis-at-scale samples never lie in the zero-producing orbit class.
-/
theorem prime_axis_not_zero_producing (P : ScaledS3Sample) (hPrime : PrimeAxisAtScale P) :
    ¬ SampleZeroProducingOrbit P := by
  dsimp [SampleZeroProducingOrbit]
  intro hOrbit
  exact prime_axis_at_scale_survives P hPrime
    ((zero_producing_orbit_iff_critical_proj_zero P.coords).mp hOrbit)

theorem prime_axis_critical_proj_nonzero (P : ScaledS3Sample) (hPrime : PrimeAxisAtScale P) :
    criticalProj P.coords ≠ 0 :=
  prime_axis_at_scale_survives P hPrime

/-! ## Discrete null-lattice trichotomy -/

theorem zero_producing_orbit_classifies_non_prime_axis
    (L : S3DiscreteNullLatticeLaw) (P : ScaledS3Sample) :
    SampleZeroProducingOrbit P ↔ ¬ PrimeAxisAtScale P := by
  dsimp [SampleZeroProducingOrbit]
  rw [zero_producing_orbit_iff_balanced]
  constructor
  · intro hBal hPrime
    exact ((unbalanced_iff_prime_axis_at_scale L P).mpr hPrime) hBal
  · intro hNotPrime
    exact L.balanced_of_not_prime_axis P hNotPrime

theorem zero_producing_of_not_prime_axis
    (L : S3DiscreteNullLatticeLaw) (P : ScaledS3Sample)
    (hNotPrime : ¬ PrimeAxisAtScale P) :
    SampleZeroProducingOrbit P :=
  (zero_producing_orbit_classifies_non_prime_axis L P).2 hNotPrime

/--
Non-single-axis samples cancel under the discrete law; when cancellation occurs
the orbit is either trivial-imaginary or explicitly multi-axis balanced.
-/
theorem non_single_axis_zero_producing_classification
    (L : S3DiscreteNullLatticeLaw) (P : ScaledS3Sample)
    (hNotSingle : ¬ IsSingleAxis P.coords) :
    SampleZeroProducingOrbit P ∧
      (IsTrivialImag P.coords ∨ (IsTwoOrMoreAxis P.coords ∧ BalancedImag P.coords)) := by
  have hCancel : criticalProj P.coords = 0 :=
    non_single_axis_sample_cancels L P hNotSingle
  refine ⟨?hOrbit, non_single_axis_pointwise_cancel_restricted P.coords hNotSingle hCancel⟩
  exact (zero_producing_orbit_iff_critical_proj_zero P.coords).2 hCancel

/-! ## Multi-axis vs trivial zero channels -/

theorem trivial_imag_zero_producing (p : QuaternionCoords) (hTriv : IsTrivialImag p) :
    ZeroProducingOrbit p := by
  have hBal : BalancedImag p := by
    rcases hTriv with ⟨h1, h2, h3⟩
    simp [BalancedImag, imagSum, h1, h2, h3]
  exact .balancedMultiAxis hBal (not_singleAxis_of_balanced p hBal)

theorem two_or_more_axis_balanced_zero_producing
    (p : QuaternionCoords) (_hMulti : IsTwoOrMoreAxis p) (hBal : BalancedImag p) :
    ZeroProducingOrbit p :=
  .balancedMultiAxis hBal (not_singleAxis_of_balanced p hBal)

/-! ## j/k pole orbit examples (axis rotation sector) -/

theorem j_pole_pair_not_zero_producing :
    ¬ ZeroProducingOrbit poleJplus ∧ ¬ ZeroProducingOrbit poleJminus := by
  rcases six_poles_single_axis with ⟨_, _, hJplus, hJminus, _, _⟩
  exact ⟨not_zero_producing_of_singleAxis poleJplus hJplus,
    not_zero_producing_of_singleAxis poleJminus hJminus⟩

theorem k_pole_pair_not_zero_producing :
    ¬ ZeroProducingOrbit poleKplus ∧ ¬ ZeroProducingOrbit poleKminus := by
  rcases six_poles_single_axis with ⟨_, _, _, _, hKplus, hKminus⟩
  exact ⟨not_zero_producing_of_singleAxis poleKplus hKplus,
    not_zero_producing_of_singleAxis poleKminus hKminus⟩

/--
Antipodal j/k pairs cancel as **orbit sums**; individual poles are prime-axis
survivors, not zero-producing orbits.
-/
theorem axis_pole_orbit_cancellation_vs_pointwise_survival :
    jAxisProj poleJplus + jAxisProj poleJminus = 0 ∧
      kAxisProj poleKplus + kAxisProj poleKminus = 0 ∧
      ¬ ZeroProducingOrbit poleJplus ∧
      ¬ ZeroProducingOrbit poleKminus := by
  refine ⟨jAxis_orbit_cancels, kAxis_orbit_cancels, ?_, ?_⟩
  · exact j_pole_pair_not_zero_producing.1
  · exact k_pole_pair_not_zero_producing.2

/-! ## Centered model: zeros ↔ zero-producing sample ↔ critical line -/

theorem model_zeta_zero_iff_zero_producing_orbit
    (M : S3CenteredZetaResidualModel) (s : ℂ) :
    riemannZeta s = 0 ↔ ZeroProducingOrbit (M.sample s).coords := by
  rw [zero_producing_orbit_iff_balanced (M.sample s).coords]
  exact (model_zeta_zero_iff_pole_channel M s).trans (s3_pole_channel_iff_balanced (M.sample s))

theorem model_zeta_zero_iff_zero_producing_and_critical_line
    (M : S3CenteredZetaResidualModel) (s : ℂ) :
    riemannZeta s = 0 ↔
      SampleZeroProducingOrbit (M.sample s) ∧ s.re = (1 / 2 : ℝ) :=
  (model_zeta_zero_iff_pole_channel_and_re_eq_half M s).trans
    (by
      constructor
      · rintro ⟨hPole, hLine⟩
        exact ⟨(sample_zero_producing_iff_s3_pole_channel (M.sample s)).mpr hPole, hLine⟩
      · rintro ⟨hOrbit, hLine⟩
        exact ⟨(sample_zero_producing_iff_s3_pole_channel (M.sample s)).mp hOrbit, hLine⟩)

/--
RH packaging in orbit language (centered model): ζ-zeros coincide with
zero-producing samples on the critical line.
-/
theorem model_zeta_zero_on_critical_line
    (M : S3CenteredZetaResidualModel) (s : ℂ) (hz : riemannZeta s = 0) :
    SampleZeroProducingOrbit (M.sample s) ∧ s.re = (1 / 2 : ℝ) :=
  (model_zeta_zero_iff_zero_producing_and_critical_line M s).mp hz

/-!
## Pathway A link (honest)

Interior-strip factorization `ζ = h · so4CriticalFactor` is proved in
`S3InteriorStripHClosedForm`.  Zero-producing orbit geometry classifies the
**S³ residual bridge** layer, not `interiorStripH` directly: under
`ZetaEqualsS3ResidualAt`, ζ-zeros are balanced orbits; off that bridge, use
`interiorStripH_eq_zero_iff_zeta_eq_zero_on_strip` only after relating `h` to
`criticalProj`.
-/

theorem interior_h_zero_iff_zeta_zero_off_line
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ)) :
    interiorStripH s = 0 ↔ riemannZeta s = 0 :=
  interiorStripH_eq_zero_iff_zeta_eq_zero_on_strip h0 h1 hσ

end Hqiv.Story

import Hqiv.Story.S3EulerExplicitFormulaLocalization
import Hqiv.Story.S3InteriorPathE
import Hqiv.Story.S3ExplicitFormulaPrimePhaseCoincidence
import Hqiv.Story.S3HarmonicShellZeroCounting

/-!
# Rolling identification ↔ interior assembly on the critical line

On the open strip the interior assembly is a quotient off `σ ≠ 1/2`; on the
critical line the equator factor vanishes.  The correct objects are the Path E
numerator `even + odd_residual = ζ` and rolling identification
`ZetaEqualsS3ResidualAt`.
-/

namespace Hqiv.Story

open Complex Real

noncomputable section

theorem critical_line_point_strip_bounds (t : ℝ) :
    0 < (criticalLinePointAtHeight t).re ∧
      (criticalLinePointAtHeight t).re < 1 := by
  simp [criticalLinePointAtHeight]
  norm_num

theorem rolling_identification_pathE_numerator_eq_zeta
    (_hId : RollingZetaIdentificationAtCriticalLine) (t : ℝ) :
    let s := criticalLinePointAtHeight t
    evenStripChannelPathE s + oddStripChannelPathE s = riemannZeta s := by
  dsimp
  rcases critical_line_point_strip_bounds t with ⟨h0, h1⟩
  exact even_odd_pathE_assembles_to_zeta h0 h1

theorem rolling_identification_pathE_numerator_zero_iff_zeta_zero
    (_hId : RollingZetaIdentificationAtCriticalLine) (t : ℝ) :
    riemannZeta (criticalLinePointAtHeight t) = 0 ↔
      evenStripChannelPathE (criticalLinePointAtHeight t) +
        oddStripChannelPathE (criticalLinePointAtHeight t) = 0 := by
  rcases critical_line_point_strip_bounds t with ⟨h0, h1⟩
  simpa using (pathE_numerator_zero_iff_zeta_zero h0 h1).symm

theorem rolling_identification_residual_at_height
    (hId : RollingZetaIdentificationAtCriticalLine) (t : ℝ) :
    ∃ P : ScaledS3Sample, ZetaEqualsS3ResidualAt (criticalLinePointAtHeight t) P :=
  ⟨rolledSampleAtHeight t, hId t⟩

theorem rolling_identification_matched_zero_at_height
    (hId : RollingZetaIdentificationAtCriticalLine) (t : ℝ) :
    MatchedRollingZeroAt (criticalLinePointAtHeight t) (rolledSampleAtHeight t) :=
  matched_rolling_of_on_line_and_identification hId (by simp [criticalLinePointAtHeight])

theorem rolling_identification_zeta_zero_iff_shell_balance
    (hId : RollingZetaIdentificationAtCriticalLine) {n : ℕ} (hn : 0 < n) (k : Fin n) :
    riemannZeta (criticalLinePointAtHeight (shellSweepAngle hn k)) = 0 ↔
      HarmonicShellBalanceEvent hn k :=
  zeta_zero_iff_shell_slot_balance hId hn k

theorem rolling_identification_zeta_zero_iff_prime_twiddle_vanishes
    (hId : RollingZetaIdentificationAtCriticalLine) {n : ℕ} (hn : 0 < n) (k : Fin n) :
    riemannZeta (criticalLinePointAtHeight (shellSweepAngle hn k)) = 0 ↔
      (primeLogTwiddleAtAngle (shellSweepAngle hn k)).twiddle = 0 :=
  zeta_zero_iff_slot_prime_twiddle_vanishes hId hn k

theorem rolling_identification_cover_balance
    (hId : RollingZetaIdentificationAtCriticalLine) (t : ℝ) :
    riemannZeta (criticalLinePointAtHeight t) = 0 ↔
      criticalProj (stripRollingMap t) = 0 :=
  zeta_zero_iff_cover_balance hId t

end

end Hqiv.Story

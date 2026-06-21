import Hqiv.Story.S3HarmonicHolonomyAssociatorAdjointAttack
import Hqiv.Story.S3HopfJKEulerPrimeCircleCounting
import Hqiv.Story.S3LogPhaseEdge
import Hqiv.Story.S3ExplicitFormulaPrimePhaseCoincidence
import Hqiv.Story.S3LogExpTrigReadoutBridge
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# On-line spectral-product opposition ↔ discrete height ladder (proved)

On the critical line, the `(6,5)` cascade spectral-product lock

`star (d₆ d₅) = -(d₆ d₅)`

is exactly the log-30 phase ladder

`2 t log 30 = π + 2 k π`.

This discharges `OnLineSpectralProductOpposedIffHeightPhase` — the open pin behind
`SigmaTRotationVectorBridge` and the slot-budget height route.
-/

namespace Hqiv.Story

open Complex Real
open scoped ComplexConjugate

noncomputable section

/-! ## Critical-line product factorization -/

private theorem criticalLineModulus_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    criticalLineModulus a * criticalLineModulus b = criticalLineModulus (a * b) := by
  dsimp [criticalLineModulus]
  push_cast
  rw [← Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b) (z := -(1 / 2))]

private theorem criticalLineModulus_mul_cast {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ((criticalLineModulus a : ℂ) * (criticalLineModulus b : ℂ)) =
      (criticalLineModulus (a * b) : ℂ) := by
  norm_cast
  exact criticalLineModulus_mul ha hb

private theorem linePhase_ne_zero (n : ℕ) (_hn : 0 < n) (_t : ℝ) : linePhase n _t ≠ 0 :=
  Complex.exp_ne_zero _

theorem critical_line_spectral_product_six_five (t : ℝ) :
    so4SpectralLine 6 (criticalLinePointAtHeight t) * so4SpectralLine 5 (criticalLinePointAtHeight t) =
      (criticalLineModulus 30 : ℂ) * linePhase 30 t := by
  set ρ := criticalLinePointAtHeight t
  have h6 := critical_line_prime_power_polar (n := 6) (by decide) t
  have h5 := critical_line_prime_power_polar (n := 5) (by decide) t
  have hmul := linePhase_mul (p := 6) (q := 5) (by decide) (by decide) t
  have hcm := criticalLineModulus_mul_cast (by decide : 0 < 6) (by decide : 0 < 5)
  calc
    so4SpectralLine 6 ρ * so4SpectralLine 5 ρ =
        ((criticalLineModulus 6 : ℂ) * linePhase 6 t) *
          ((criticalLineModulus 5 : ℂ) * linePhase 5 t) := by rw [h6, h5]
    _ = ((criticalLineModulus 6 : ℂ) * (criticalLineModulus 5 : ℂ)) *
          (linePhase 6 t * linePhase 5 t) := by ring
    _ = (criticalLineModulus 30 : ℂ) * linePhase 30 t := by rw [hcm, hmul]

private theorem critical_line_modulus_thirty_pos : 0 < criticalLineModulus 30 :=
  critical_line_modulus_pos (n := 30) (by decide)

/-! ## Star spectral lock ↔ unit phase opposition -/

private theorem star_spectral_product_six_five (t : ℝ) :
    star (so4SpectralLine 6 (criticalLinePointAtHeight t)) *
        star (so4SpectralLine 5 (criticalLinePointAtHeight t)) =
      star (so4SpectralLine 6 (criticalLinePointAtHeight t) *
        so4SpectralLine 5 (criticalLinePointAtHeight t)) := by
  rw [← star_mul, mul_comm (so4SpectralLine 5 _) (so4SpectralLine 6 _)]

private theorem linePhase_conj (n : ℕ) (hn : 0 < n) (t : ℝ) :
    conj (linePhase n t) = Complex.exp (t * Real.log (n : ℝ) * Complex.I) := by
  rw [linePhase_conj_is_zero_oscillation hn t]
  dsimp [zeroOscillationUnitPhase, zeroOscillationPhase]
  simp [mul_comm I, Nat.cast_ofNat]

private theorem linePhase_star_exp (n : ℕ) (hn : 0 < n) (t : ℝ) :
    star (linePhase n t) =
      Complex.exp (t * Real.log (n : ℝ) * Complex.I) := by
  rw [Complex.star_def, linePhase_conj_is_zero_oscillation hn t]
  dsimp [zeroOscillationUnitPhase, zeroOscillationPhase]
  simp [mul_comm I, Nat.cast_ofNat]

private theorem linePhase_star_mul_self (n : ℕ) (hn : 0 < n) (t : ℝ) :
    star (linePhase n t) * linePhase n t = 1 := by
  rw [linePhase_star_exp n hn t]
  unfold linePhase
  rw [← Complex.exp_add]
  simp

theorem on_line_height_phase_lock_iff_linePhase_thirty_opposed (t : ℝ) :
    OnLineHeightPhaseLockAt t ↔
      star (linePhase 30 t) = -linePhase 30 t := by
  dsimp [OnLineHeightPhaseLockAt]
  simp only [starRingEnd_apply]
  rw [star_spectral_product_six_five t, critical_line_spectral_product_six_five t]
  have hcast :
      star ((criticalLineModulus 30 : ℂ) * linePhase 30 t) =
        ((criticalLineModulus 30 : ℝ) : ℂ) * star (linePhase 30 t) := by
    apply Complex.ext
    · simp [star, Complex.ofReal_mul]
    · simp [star, Complex.ofReal_mul]
  have hpos : 0 < (criticalLineModulus 30 : ℝ) := critical_line_modulus_thirty_pos
  have hne : ((criticalLineModulus 30 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  constructor
  · intro h
    rw [hcast] at h
    have hphase : star (linePhase 30 t) = -linePhase 30 t :=
      mul_left_cancel₀ hne (by simpa [neg_mul] using h)
    exact hphase
  · intro h
    rw [hcast, h]
    simp [neg_mul]

/-! ## Unit phase opposition ↔ `exp(2 i t log 30) = -1` -/

theorem linePhase_thirty_opposed_iff_exp_two_phase_neg_one (t : ℝ) :
    star (linePhase 30 t) = -linePhase 30 t ↔
      Complex.exp ((2 : ℝ) * t * Real.log 30 * Complex.I) = -1 := by
  have hstar := linePhase_star_exp 30 (by decide) t
  have hone := linePhase_star_mul_self 30 (by decide) t
  have hdouble_exp :
      star (linePhase 30 t) * star (linePhase 30 t) =
        Complex.exp ((2 : ℝ) * t * Real.log 30 * Complex.I) := by
    rw [hstar, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  constructor
  · intro h
    have hdouble : star (linePhase 30 t) * star (linePhase 30 t) = -1 := by
      calc
        star (linePhase 30 t) * star (linePhase 30 t) =
            star (linePhase 30 t) * -linePhase 30 t := by rw [h]
        _ = -(star (linePhase 30 t) * linePhase 30 t) := by ring
        _ = -1 := by rw [hone]
    rw [hdouble_exp] at hdouble
    exact hdouble
  · intro h
    have hstep := congrArg (fun z => z * linePhase 30 t) h
    rw [← hdouble_exp] at hstep
    simp at hstep
    have hleft :
        star (linePhase 30 t) * star (linePhase 30 t) * linePhase 30 t =
          star (linePhase 30 t) := by
      calc
        _ = star (linePhase 30 t) * (star (linePhase 30 t) * linePhase 30 t) := by ring
        _ = star (linePhase 30 t) * 1 := by rw [hone]
        _ = star (linePhase 30 t) := by ring
    have heq : star (linePhase 30 t) = -linePhase 30 t :=
      hleft.symm.trans hstep
    exact heq

/-! ## `exp(2 i t log 30) = -1` ↔ discrete height ladder -/

private theorem exp_I_mul_eq_neg_one_iff (x : ℝ) :
    Complex.exp (x * Complex.I) = -1 ↔ ∃ k : ℤ, x = Real.pi + 2 * Real.pi * k := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    rw [exp_ofReal_mul_I_re] at hre
    obtain ⟨k, hk⟩ := Real.cos_eq_neg_one_iff.mp hre
    exact ⟨k, by ring_nf at hk ⊢; exact hk.symm⟩
  · rintro ⟨k, hk⟩
    rw [hk]
    rw [show ((Real.pi + 2 * Real.pi * (k : ℝ)) : ℝ) * Complex.I =
        Real.pi * Complex.I + (2 * Real.pi * (k : ℝ)) * Complex.I by
      push_cast; exact add_mul _ _ _]
    rw [Complex.exp_add, Complex.exp_pi_mul_I]
    rw [show (2 * Real.pi * (k : ℝ)) * Complex.I = (k : ℂ) * (2 * Real.pi * Complex.I) by
      push_cast; ring]
    rw [Complex.exp_int_mul_two_pi_mul_I]
    simp

theorem exp_two_phase_neg_one_iff_height_ladder (t : ℝ) :
    Complex.exp ((2 : ℝ) * t * Real.log 30 * Complex.I) = -1 ↔
      ∃ k : ℤ, (2 : ℝ) * t * Real.log 30 = Real.pi + (2 : ℝ) * (k : ℝ) * Real.pi := by
  set x := (2 : ℝ) * t * Real.log 30
  have hexp : Complex.exp ((2 : ℝ) * t * Real.log 30 * Complex.I) = Complex.exp (x * Complex.I) := by
    dsimp [x]
    congr 1
    push_cast
    ring
  rw [hexp, exp_I_mul_eq_neg_one_iff x]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by dsimp [x] at hk ⊢; ring_nf at hk ⊢; exact hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by dsimp [x] at hk ⊢; ring_nf at hk ⊢; exact hk⟩

/-! ## Main ladder equivalence -/

theorem on_line_spectral_product_opposed_iff_height_phase :
    OnLineSpectralProductOpposedIffHeightPhase := by
  intro t
  exact (on_line_height_phase_lock_iff_linePhase_thirty_opposed t).trans
    ((linePhase_thirty_opposed_iff_exp_two_phase_neg_one t).trans
      (exp_two_phase_neg_one_iff_height_ladder t))

end

end Hqiv.Story

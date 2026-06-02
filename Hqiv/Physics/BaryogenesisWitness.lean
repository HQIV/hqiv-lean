import Hqiv.Physics.BaryogenesisCore
import Hqiv.Physics.BaryogenesisEtaPaper

namespace Hqiv

/-!
# Baryogenesis η witness (calibration to `eta_paper`)

**Imports `BaryogenesisEtaPaper`:** the only stack entry point for the literal `6.10×10⁻¹⁰`.
`eta_at_horizon` and all theorems that identify η with the paper value belong here, not in
`BaryogenesisCore`. Prefer importing `BaryogenesisCore` alone when proving results that should not
depend on the PDG-style anchor.
-/

/-- **Baryon asymmetry η at horizon N (evaluated at shell n).**
    Same normalization as Ω_k: η(n; N) = eta_paper × (curvature_integral n / curvature_integral N).
    When curvature_integral N ≤ 0 we fall back to eta_paper (no division). -/
noncomputable def eta_at_horizon (n N : Nat) : ℝ :=
  if curvature_integral N ≤ (0 : ℝ) then
    eta_paper
  else
    eta_paper * curvature_integral n / curvature_integral N

/-- **Equation for η at horizon N** when the horizon integral is positive. -/
theorem eta_at_horizon_eq (n N : Nat) (hN : 0 < curvature_integral N) :
    eta_at_horizon n N = eta_paper * curvature_integral n / curvature_integral N := by
  unfold eta_at_horizon
  split_ifs with h'
  · exfalso; linarith
  · rfl

/-- **η at the horizon itself:** η(N; N) = eta_paper. -/
theorem eta_at_horizon_self (N : Nat) (hN : 0 < curvature_integral N) :
    eta_at_horizon N N = eta_paper := by
  rw [eta_at_horizon_eq N N hN]
  simp only [mul_div_cancel_right₀ _ (ne_of_gt hN)]

/-- **Same normalization as Ω_k:** the ratio η(n; N) / Ω_k(n; N) = eta_paper (Ω_k is the
    curvature ratio, so η = eta_paper × ratio and Ω_k = ratio ⇒ η/Ω_k = eta_paper). -/
theorem eta_over_omega_k_constant (n N : Nat) (hN : 0 < curvature_integral N) (hn : curvature_integral n ≠ 0) :
    eta_at_horizon n N / omega_k_at_horizon n N = eta_paper := by
  rw [eta_at_horizon_eq n N hN, omega_k_at_horizon_eq n N hN]
  field_simp [hN.ne', hn]

/-- **Vital for the proof:** η at the lockin horizon (evaluated at the lockin shell) equals eta_paper.
    So the baryon asymmetry that locks in at T_lockin is the observed η. -/
theorem eta_lockin_calibration (h_lockin : 0 < curvature_integral m_lockin) :
    eta_at_horizon m_lockin m_lockin = eta_paper :=
  eta_at_horizon_self m_lockin h_lockin

/-- **Same normalization at lockin:** at the lockin horizon, η/Ω_k = eta_paper (Ω_k = 1 there). -/
theorem eta_over_omega_k_at_lockin (h_lockin : 0 < curvature_integral m_lockin) :
    eta_at_horizon m_lockin m_lockin / omega_k_at_horizon m_lockin m_lockin = eta_paper :=
  eta_over_omega_k_constant m_lockin m_lockin h_lockin (ne_of_gt h_lockin)

/-- **η at QCD shell with lockin horizon:** the baryon asymmetry evaluated at the QCD shell
    when the horizon is the lockin shell. Vital: this uses T_QCD (via m_QCD) and T_lockin (via m_lockin). -/
theorem eta_at_QCD_with_lockin_horizon (h_lockin : 0 < curvature_integral m_lockin) :
    eta_at_horizon m_QCD m_lockin = eta_paper * curvature_integral m_QCD / curvature_integral m_lockin :=
  eta_at_horizon_eq m_QCD m_lockin h_lockin

/-- **Baryogenesis proof uses T_QCD and T_lockin:** η at the lockin horizon equals eta_paper;
    the curvature imprint δE at the QCD shell and the integral at the lockin horizon fix both
    Ω_k and η. So T_QCD and T_lockin are vital for the proof. -/
theorem baryogenesis_vital_T_QCD_T_lockin :
    eta_at_horizon m_lockin m_lockin = eta_paper ∧
    omega_k_at_horizon m_lockin m_lockin = 1 ∧
    T_QCD = T m_QCD ∧ T_lockin = T m_lockin := by
  refine ⟨eta_lockin_calibration curvature_integral_m_lockin_pos,
          omega_k_lockin_calibration curvature_integral_m_lockin_pos,
          T_QCD_eq_ladder, T_lockin_eq_ladder⟩

/-- **η at reference horizon** equals eta_paper × curvature ratio (or fallback). -/
theorem eta_at_reference_horizon (n : Nat) :
    eta_at_horizon n referenceM = eta_paper * curvature_integral n / curvature_integral referenceM ∨
    curvature_integral referenceM ≤ 0 := by
  by_cases h : curvature_integral referenceM ≤ (0 : ℝ)
  · right; exact h
  · push_neg at h
    left
    exact eta_at_horizon_eq n referenceM h

/-- **Calibration at reference:** eta_at_horizon referenceM referenceM = eta_paper. -/
theorem eta_partial_at_reference :
    eta_at_horizon referenceM referenceM = eta_paper := by
  have hpos : 0 < curvature_integral referenceM := curvature_integral_ref_pos
  exact eta_at_horizon_self referenceM hpos

/-- **η partial** (η at horizon referenceM), mirroring omega_k_partial. -/
noncomputable def eta_partial (n : Nat) : ℝ := eta_at_horizon n referenceM

/-- **η partial at reference** equals eta_paper. -/
theorem eta_partial_at_reference' : eta_partial referenceM = eta_paper :=
  eta_partial_at_reference

/-- **η from curvature imprint δE:** per-shell imprint δE(m) = curvature_norm × shell_shape(m).
    The integrated imprint (curvature_integral) sets both Ω_k and η; so η at shell n
    relative to horizon N is determined by the ratio of integrals. -/
theorem eta_determined_by_curvature_integral (n N : Nat) (hN : 0 < curvature_integral N) :
    eta_at_horizon n N = eta_paper * curvature_integral n / curvature_integral N :=
  eta_at_horizon_eq n N hN

/-- **Monotonicity in readout shell:** same monotonicity as \(\Omega_k\), including the
    degenerate case `curvature_integral N ≤ 0` where both sides equal `eta_paper`. -/
theorem eta_at_horizon_mono (n1 n2 N : Nat) (h : n1 ≤ n2) :
    eta_at_horizon n1 N ≤ eta_at_horizon n2 N := by
  by_cases hNle : curvature_integral N ≤ (0 : ℝ)
  · simp [eta_at_horizon, hNle]
  · push_neg at hNle
    rw [eta_at_horizon_eq n1 N hNle, eta_at_horizon_eq n2 N hNle]
    have hden : curvature_integral N ≠ 0 := ne_of_gt hNle
    field_simp [hden]
    exact mul_le_mul_of_nonneg_left (curvature_integral_mono h) (le_of_lt eta_paper_pos)

/-- **Upper bound by the paper anchor** when the readout shell lies inside the horizon
    (`n ≤ N`): then \(I(n)\le I(N)\) so \(\eta(n;N)\le \eta_{\mathrm{paper}}\). -/
theorem eta_at_horizon_le_eta_paper (n N : Nat) (hN : 0 < curvature_integral N) (hn : n ≤ N) :
    eta_at_horizon n N ≤ eta_paper := by
  rw [eta_at_horizon_eq n N hN]
  have hquot : curvature_integral n / curvature_integral N ≤ 1 := by
    rw [div_le_one₀ hN]
    exact curvature_integral_mono hn
  calc
    eta_paper * curvature_integral n / curvature_integral N
        = eta_paper * (curvature_integral n / curvature_integral N) := by ring
    _ ≤ eta_paper * 1 := mul_le_mul_of_nonneg_left hquot (le_of_lt eta_paper_pos)
    _ = eta_paper := mul_one _

/-- **Strict increase in readout shell** when the horizon integral is positive. -/
theorem eta_at_horizon_strict_mono (n1 n2 N : Nat) (hN : 0 < curvature_integral N) (h : n1 < n2) :
    eta_at_horizon n1 N < eta_at_horizon n2 N := by
  rw [eta_at_horizon_eq n1 N hN, eta_at_horizon_eq n2 N hN]
  refine div_lt_div_of_pos_right ?_ hN
  exact mul_lt_mul_of_pos_left (curvature_integral_strict_mono h) eta_paper_pos

/-- **Positivity of η at horizon:** when both integrals are positive, η(n; N) > 0. -/
theorem eta_at_horizon_pos (n N : Nat) (hn : 0 < curvature_integral n)
    (hN : 0 < curvature_integral N) :
    0 < eta_at_horizon n N := by
  rw [eta_at_horizon_eq n N hN]
  apply div_pos
  · exact mul_pos eta_paper_pos hn
  · exact hN

/-- **Baryogenesis summary:** η = eta_paper × Ω_k (same curvature ratio; Ω_k dynamic). -/
theorem baryogenesis_same_normalization_as_omega_k (n N : Nat) (hN : 0 < curvature_integral N) :
    eta_at_horizon n N = eta_paper * omega_k_at_horizon n N := by
  rw [eta_at_horizon_eq n N hN, omega_k_at_horizon_eq n N hN]
  ring

/-!
## Optional bridge: curvature CP bias and η ratios

`TrialityRapidityWellEquivalence` uses `omega_k_at_horizon m m_lockin - 1` without importing this
file. The following theorem is the same identity in baryogenesis language, kept here so witness
importers are the only ones that need `eta_paper`.
-/

/-- With positive lockin integral, the Ω_k deviation at shell `m` (lockin horizon) equals
    the η-ratio to lockin-horizon calibration minus 1. -/
theorem omega_k_cp_bias_eq_eta_ratio_minus_one
    (m : ℕ) (h_lockin : 0 < curvature_integral m_lockin) :
    omega_k_at_horizon m m_lockin - 1
      = eta_at_horizon m m_lockin / eta_at_horizon m_lockin m_lockin - 1 := by
  have hηm : eta_at_horizon m m_lockin = eta_paper * omega_k_at_horizon m m_lockin := by
    simpa [m_lockin_eq_referenceM] using baryogenesis_same_normalization_as_omega_k m m_lockin h_lockin
  have hηlock : eta_at_horizon m_lockin m_lockin = eta_paper := by
    exact eta_lockin_calibration h_lockin
  have hηnz : eta_paper ≠ 0 := ne_of_gt eta_paper_pos
  rw [hηm, hηlock]
  field_simp [hηnz]

end Hqiv

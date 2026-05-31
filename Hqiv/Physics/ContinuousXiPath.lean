import Hqiv.Physics.ContinuousXiCoupling
import Hqiv.Physics.SM_GR_Unification
import Hqiv.QuantumChemistry.FiniteSiteQuantumChemistry

open Hqiv.QuantumChemistry

namespace Hqiv
namespace Physics
namespace ContinuousXiPath

/-!
# Continuous ξ path (adjacent to the discrete shell ladder)

The existing discrete backbone is unchanged:

* `T m`, `phi_of_shell m`, `shell_shape m` (`curvatureDensity (m+1)`);
* `curvature_integral` / `omega_k_at_horizon` / `omega_k_partial`;
* `one_over_alpha_EM_derived m c` from `SM_GR_Unification`.

This module installs a **parallel continuous chart** with horizon coordinate
\(\xi = m+1 = T_{\mathrm{Pl}}/T\). Integer shells are **chart samples**;
half-steps (e.g. \(\xi_G \approx 3.5\)) live on the same curve but off the
integer grid.

**Chart bridges** (proved here): \(\sigma\), \(\varphi\), \(T\), O–Maxwell
\(1/\alpha_{\mathrm{eff}}\), and finite-site chemistry energies agree on
\(\xi = \texttt{xiOfShell}\,m\).

**Ωₖ split** (honest): discrete ratios use `curvature_integral`; continuous
ratios use `continuousCurvaturePrimitive`. Both calibrate to \(1\) at lock-in
(\(\xi_{\mathrm{lock}} = 5\), `referenceM = 4`); identifying the two along the
full chart is a separate Riemann–integral program, not asserted here.
-/

/-! ## Continuous ladder (parallel API) -/

/-- Temperature ladder on the continuous horizon coordinate: \(T(\xi)=1/\xi\). -/
noncomputable def T_xi (ξ : ℝ) : ℝ := T_Pl / ξ

/-- Auxiliary field \(\varphi(\xi)=2/\Theta(\xi)\) with \(\Theta(\xi)=T(\xi)\). -/
noncomputable def phi_xi (ξ : ℝ) : ℝ := phi_of_T (T_xi ξ)

/-- Curvature-imprint density \(\sigma(\xi)=\texttt{curvatureDensity}(\xi)\). -/
noncomputable def sigma_xi (ξ : ℝ) : ℝ := sigmaXi ξ

/-- O–Maxwell log slot \(\alpha\log(\varphi(\xi)+1)\). -/
noncomputable def logPhi_xi (ξ : ℝ) : ℝ := logPhiXi ξ

/-- Effective inverse coupling on the continuous chart (same formula as discrete). -/
noncomputable def oneOverAlpha_xi (ξ c : ℝ) : ℝ := oneOverAlphaEffXi ξ c

/-- Continuous \(\Omega_k\) ratio against lock-in \(\xi_{\mathrm{lock}}=5\). -/
noncomputable def omegaK_xi (ξ : ℝ) : ℝ := omegaKContinuous ξ xiLockin

/-- Partial \(\Omega_k\) at the reference lock-in horizon (continuous chart). -/
noncomputable def omegaK_partial_xi (ξ : ℝ) : ℝ := omegaK_xi ξ

/-! ## Integer chart -/

/-- \(\xi\) lies on an integer shell sample \(m+1\). -/
def onIntegerChart (ξ : ℝ) : Prop := ∃ m : ℕ, ξ = xiOfShell m

theorem onIntegerChart_shell (m : ℕ) : onIntegerChart (xiOfShell m) := ⟨m, rfl⟩

theorem xiOfShell_succ (m : ℕ) : xiOfShell (m + 1) = xiOfShell m + 1 := by
  unfold xiOfShell
  push_cast
  ring

/-! ## Chart compatibility (discrete ↔ continuous) -/

theorem T_xi_chart (m : ℕ) : T_xi (xiOfShell m) = T m := by
  unfold T_xi xiOfShell T
  rfl

theorem xiOfShell_ne_zero (m : ℕ) : xiOfShell m ≠ 0 := by
  unfold xiOfShell
  positivity

theorem phi_xi_eq_phiOfXi (ξ : ℝ) (hξ : ξ ≠ 0) : phi_xi ξ = phiOfXi ξ := by
  unfold phi_xi phiOfXi phi_of_T T_xi T_Pl phiTemperatureCoeff
  field_simp [T_Pl_eq, hξ]
  norm_num

theorem phi_xi_eq_phiTemperatureCoeff_mul (ξ : ℝ) (hξ : ξ ≠ 0) :
    phi_xi ξ = phiTemperatureCoeff * ξ := by
  rw [phi_xi_eq_phiOfXi ξ hξ, phiOfXi]

theorem phi_xi_chart (m : ℕ) : phi_xi (xiOfShell m) = phi_of_shell m := by
  rw [phi_xi_eq_phiOfXi _ (xiOfShell_ne_zero m), phiOfXi_xiOfShell m]

theorem sigma_xi_chart (m : ℕ) : sigma_xi (xiOfShell m) = shell_shape m :=
  sigmaXi_xiOfShell m

theorem logPhi_xi_chart (m : ℕ) : logPhi_xi (xiOfShell m) = alpha * Real.log (phi_of_shell m + 1) := by
  unfold logPhi_xi logPhiXi
  rw [phiOfXi_xiOfShell]

theorem invAlphaGUT_eq_inv_alpha_GUT : invAlphaGUT = 1 / alpha_GUT := by
  rw [invAlphaGUT_eq_forty_two, one_over_alpha_bare_eq]

theorem oneOverAlpha_xi_eq_one_over_alpha_eff (ξ c : ℝ) :
    oneOverAlpha_xi ξ c = one_over_alpha_eff (phiOfXi ξ) c := by
  unfold oneOverAlpha_xi oneOverAlphaEffXi one_over_alpha_eff logPhiXi
  rw [invAlphaGUT_eq_inv_alpha_GUT]
  ring_nf

theorem one_over_alpha_EM_derived_eq_xi (m : ℕ) (c : ℝ) :
    one_over_alpha_EM_derived m c = oneOverAlpha_xi (xiOfShell m) c := by
  rw [oneOverAlpha_xi_eq_one_over_alpha_eff, one_over_alpha_EM_derived, phiOfXi_xiOfShell]

/-! ## Lock-in calibration (both paths → 1) -/

theorem omegaK_partial_xi_lockin : omegaK_partial_xi xiLockin = 1 :=
  omegaKContinuous_lockin

theorem xiLockin_eq_xiOfShell_referenceM :
    xiLockin = xiOfShell referenceM := by
  unfold xiLockin xiOfShell
  rfl

theorem omega_k_partial_at_reference_via_xi
    (hpos : 0 < curvature_integral referenceM) :
    omega_k_partial referenceM = omegaK_partial_xi xiLockin := by
  rw [omega_k_partial_at_reference hpos, omegaK_partial_xi_lockin]

/-- `omegaK_xi ξ > 0` for ξ > 1 (supporting the dynamic T → vev mapping).

Direct from the curvature primitive positivity (log + (α/2)log² > 0 for ξ > 1) and the
normalization at lock-in. The executable dynamic scale and physical-T mass spectrum
are the primary deliverables; this is the supporting analytic layer.
-/
theorem omegaK_xi_pos (ξ : ℝ) (h : 1 < ξ) : 0 < omegaK_xi ξ := by
  unfold omegaK_xi omegaKContinuous
  have hlock_gt_one : 1 < xiLockin := by
    rw [xiLockin_eq_five]
    norm_num
  have hden_pos : 0 < continuousCurvaturePrimitive xiLockin :=
    continuousCurvaturePrimitive_pos_for_gt_one xiLockin hlock_gt_one
  have hden_ne : continuousCurvaturePrimitive xiLockin ≠ 0 := ne_of_gt hden_pos
  simp [hden_ne, div_pos (continuousCurvaturePrimitive_pos_for_gt_one ξ h) hden_pos]

/-- `omegaK_xi` is strictly increasing for ξ > 5 (supporting the dynamic T → vev story).

Standard consequence of the curvature primitive being strictly increasing (its derivative
(1/x)(1 + α log x) > 0 on (1,∞)). The denominator is the positive lock-in
primitive at `xiLockin = 5`.
-/
theorem omegaK_xi_strictMono (ξ1 ξ2 : ℝ) (h1 : 5 ≤ ξ1) (h2 : ξ1 < ξ2) :
    omegaK_xi ξ1 < omegaK_xi ξ2 := by
  unfold omegaK_xi omegaKContinuous
  have hlock_gt_one : 1 < xiLockin := by
    rw [xiLockin_eq_five]
    norm_num
  have hden_pos : 0 < continuousCurvaturePrimitive xiLockin :=
    continuousCurvaturePrimitive_pos_for_gt_one xiLockin hlock_gt_one
  have hden_ne : continuousCurvaturePrimitive xiLockin ≠ 0 := ne_of_gt hden_pos
  have hξ1_gt_one : 1 < ξ1 := by linarith
  have hnum_lt : continuousCurvaturePrimitive ξ1 < continuousCurvaturePrimitive ξ2 :=
    continuousCurvaturePrimitive_strict_mono_gt_one ξ1 ξ2 hξ1_gt_one h2
  simp [hden_ne, div_lt_div_of_pos_right hnum_lt hden_pos]

/-! ## VEV on the temperature ladder (TUFT "only vev as input")

The vacuum expectation value / overall mass scale is **not independent of the
temperature ladder** and is no longer a fixed constant.

It emerges at every ξ from the inside/outside Casimir asymmetry on the carrier
(the symmetry-breaking mechanism):
- Inner contact surfaces (T12 witness shells + trapped Casimir) → binding, larger scale.
- Outer neutral surface (T13 fluctuations on the right-handed singlet extension) → suppression.

See `HopfShellBeltramiMassBridge.effective_casimir_scale_at_xi` (inner trapping(ωK_xi ξ) / outer suppression).

The lock-in point (ξ = xiLockin = 5, m_lockin = referenceM = 4) remains special:
this is where Ω_k = 1 and the legacy good ratios are recovered. But the scale
itself is now fully dynamic with universe age. "Dynamics all the way down."

In the TUFT claim ("mass spectrum on lock with only vev as input"), the vev at
any epoch is the instantaneous geometric balance read from the ladder + the
T12/T13 witnesses. The entire spectrum (absolute scale + ratios + T dependence)
follows from that.
-/

theorem vev_read_at_ladder_lockin :
    -- The vev that anchors the mass spectrum is the curvature calibration
    -- exactly where the ladder's Ω_k reaches 1 (xiLockin).
    omegaK_partial_xi xiLockin = 1 ∧
    xiLockin = xiOfShell referenceM := by
  exact ⟨omegaK_partial_xi_lockin, xiLockin_eq_xiOfShell_referenceM⟩

/-! ## Discrete-continuous Ωₖ bridge -/

/--
Bridge condition for reusing a continuous `ξ` path as a readout of the discrete
curvature ladder on integer samples.

The continuous chart (`omegaK_xi`) uses the analytic primitive from
`ContinuousXiCoupling`; the discrete ladder (`omega_k_partial`) uses the finite
null-lattice sum `curvature_integral`.  This predicate is the explicit slot that
must be supplied by any Riemann-sum / calibration argument before transporting
integer-step readout phases across the two APIs.
-/
def OmegaKIntegerBridge : Prop :=
  ∀ n : ℕ, omegaK_xi (xiOfShell n) = omega_k_partial n

theorem omegaK_xi_integer_bridge (hΩ : OmegaKIntegerBridge) (n : ℕ) :
    omegaK_xi (xiOfShell n) = omega_k_partial n :=
  hΩ n

theorem omegaK_xi_integer_increment_bridge (hΩ : OmegaKIntegerBridge) (n : ℕ) :
    omegaK_xi (xiOfShell (n + 1)) - omegaK_xi (xiOfShell n) =
      omega_k_partial (n + 1) - omega_k_partial n := by
  rw [omegaK_xi_integer_bridge hΩ (n + 1), omegaK_xi_integer_bridge hΩ n]

/-! ## Imprint readout on the continuous chart -/

/-- Density-weighted imprint factor at \(\xi\) (σ and φ slots aligned with the paper). -/
noncomputable def imprintReadoutDensity (ξ : ℝ) : ℝ :=
  alpha * Real.log (phi_xi ξ + 1) * sigma_xi ξ

theorem imprintReadoutDensity_chart (m : ℕ) :
    imprintReadoutDensity (xiOfShell m) =
      alpha * Real.log (phi_of_shell m + 1) * shell_shape m := by
  unfold imprintReadoutDensity
  rw [phi_xi_chart, sigma_xi_chart]

/-- Incremental imprint between two continuous coordinates (parallel to
`imprintWeightedReadoutPhase`, which steps by discrete shell index). -/
noncomputable def imprintWeightedReadoutPhase_xi (ξ ξNext : ℝ) : ℝ :=
  alpha * Real.log (phi_xi ξ + 1) * (omegaK_xi ξNext - omegaK_xi ξ)

theorem imprintWeightedReadoutPhase_xi_of_omega_eq (ξ ξNext : ℝ)
    (h : omegaK_xi ξNext = omegaK_xi ξ) :
    imprintWeightedReadoutPhase_xi ξ ξNext = 0 := by
  simp [imprintWeightedReadoutPhase_xi, h, sub_self, mul_zero]

/-! ## Finite-site chemistry on the continuous chart -/

/-- Single-site mode energy \(4(\xi+1)\xi^2\) with \(\xi=m+1\). -/
noncomputable def latticeFullModeEnergy_xi (ξ : ℝ) : ℝ := 4 * (ξ + 1) * ξ ^ 2

theorem latticeFullModeEnergy_xi_chart (m : ℕ) :
    latticeFullModeEnergy_xi (xiOfShell m) =
      Hqiv.ProteinResearch.latticeFullModeEnergy m := by
  rw [latticeFullModeEnergy_closed_form m, xiOfShell, latticeFullModeEnergy_xi]
  ring_nf

noncomputable def h2SiteEnergyTrace_xi (ξLeft ξRight : ℝ) : ℝ :=
  latticeFullModeEnergy_xi ξLeft + latticeFullModeEnergy_xi ξRight

theorem h2SiteEnergyTrace_xi_same (ξ : ℝ) :
    h2SiteEnergyTrace_xi ξ ξ = 2 * latticeFullModeEnergy_xi ξ := by
  unfold h2SiteEnergyTrace_xi
  ring

theorem h2SiteEnergyTrace_xi_chart (m : ℕ) :
    h2SiteEnergyTrace_xi (xiOfShell m) (xiOfShell m) =
      8 * (m + 2 : ℝ) * (m + 1 : ℝ) ^ 2 := by
  rw [h2SiteEnergyTrace_xi_same, latticeFullModeEnergy_xi_chart m]
  rw [latticeFullModeEnergy_closed_form m]
  ring

theorem referenceM_eq_four : referenceM = 4 := by
  unfold referenceM qcdShell stepsFromQCDToLockin latticeStepCount
  norm_num

theorem h2SiteEnergyTrace_xi_lockin :
    h2SiteEnergyTrace_xi xiLockin xiLockin = 1200 := by
  have h4 :
      h2SiteEnergyTrace_xi (xiOfShell 4) (xiOfShell 4) = 1200 := by
    rw [h2SiteEnergyTrace_xi_chart]
    norm_num
  simpa [xiLockin_eq_xiOfShell_referenceM, referenceM_eq_four] using h4

/-! ## Half-step off the integer chart -/

theorem two_mul_succ_ne_seven (m : ℕ) : 2 * (m + 1) ≠ 7 := by omega

theorem not_onIntegerChart_halfStep : ¬ onIntegerChart xiHalfStep := by
  rintro ⟨m, hm⟩
  unfold xiHalfStep xiOfShell at hm
  have h7 : xiOfShell m = 7 / 2 := by simpa [xiOfShell] using hm.symm
  have h5 : (2 : ℝ) * xiOfShell m = 7 := by
    rw [h7]
    norm_num
  have hNat : 2 * (m + 1) = 7 := by
    have hcast : (2 : ℝ) * xiOfShell m = (2 : ℝ) * ↑(m + 1) := by
      simp [xiOfShell]
    have hcast' : ((2 * (m + 1) : ℕ) : ℝ) = 7 := by
      push_cast
      linarith [h5, hcast]
    exact_mod_cast hcast'
  exact two_mul_succ_ne_seven m hNat

/-! ## Bundled adjacent-path witness -/

/-- Records that discrete and continuous APIs share the same lock-in anchor. -/
structure AdjacentPathLockinWitness where
  discreteShell : ℕ
  continuousXi : ℝ
  discrete_eq : discreteShell = referenceM
  continuous_eq : continuousXi = xiLockin
  omega_discrete : ℝ
  omega_continuous : ℝ
  omega_discrete_eq : omega_discrete = 1
  omega_continuous_eq : omega_continuous = 1

noncomputable def adjacentPathLockinWitness : AdjacentPathLockinWitness where
  discreteShell := referenceM
  continuousXi := xiLockin
  discrete_eq := rfl
  continuous_eq := rfl
  omega_discrete := omega_k_partial referenceM
  omega_continuous := omegaK_partial_xi xiLockin
  omega_discrete_eq := by
    have hpos : 0 < curvature_integral referenceM := curvature_integral_ref_pos
    exact omega_k_partial_at_reference hpos
  omega_continuous_eq := omegaK_partial_xi_lockin

end ContinuousXiPath
end Physics
end Hqiv

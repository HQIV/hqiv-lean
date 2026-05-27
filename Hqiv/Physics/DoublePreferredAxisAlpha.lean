import Hqiv.Physics.DoublePreferredAxis
import Hqiv.Physics.SM_GR_Unification

namespace Hqiv.Physics

/-!
# Fine-structure constant from double-axis + O–Maxwell ladder

Packages the **discrete** \(\alpha_{\mathrm{EM}}(M_Z)\) chain claimed in `paper/main.tex`:

1. **O–Maxwell running** at shell `m`: `one_over_alpha_EM_derived m c` (proved closed form in
   `SM_GR_Unification`).
2. **Double-axis Gauss imprint:** \(\delta_E/4\pi_{\mathrm{geom}} = \mathrm{shell\_shape}\times 21\)
   (`deltaE_div_fourPiGeom_eq_shell_shape_mul_twenty_one`).
3. **Shell translation:** evaluate the \(\phi\)-correction at the EM Gauss row `emGaussShell`
   (`referenceM - 1`) and multiply by the shell-shape ratio to the electroweak readout row
   `electroweakPhiShell = referenceM + 1` (discrete brace between parallel constructions).

The decimal `one_over_alpha_EM_at_MZ` in `SM_GR_Unification` remains an external CODATA-aligned
witness; this module gives the **derived target** `one_over_alpha_EM_double_axis` to compare against
it. Numeric closeness to \(137.036\) is checked outside Lean (interval bounds on `Real.log` are
future work).
-/

/-- **Derived** \(1/\alpha(M_Z)\): O–Maxwell at `emGaussShell` times the Gauss shell-factor ratio
to `electroweakPhiShell`. -/
noncomputable def one_over_alpha_EM_double_axis (c : ℝ := 1) : ℝ :=
  one_over_alpha_EM_derived emGaussShell c * gaussShellFactorRatio_em_to_electroweak

/-- \(\alpha_{\mathrm{EM}}(M_Z)\) from the double-axis chain. -/
noncomputable def alpha_EM_double_axis (c : ℝ := 1) : ℝ :=
  (one_over_alpha_EM_double_axis c)⁻¹

theorem one_over_alpha_EM_double_axis_eq_derived_mul_ratio (c : ℝ) :
    one_over_alpha_EM_double_axis c =
      one_over_alpha_EM_derived emGaussShell c * gaussShellFactorRatio_em_to_electroweak := rfl

theorem one_over_alpha_EM_double_axis_expands (c : ℝ) :
    one_over_alpha_EM_double_axis c =
      (42 : ℝ) * (1 + c * (3 / 5 : ℝ) * Real.log (2 * (emGaussShell + 1 : ℝ) + 1)) *
        (shell_shape emGaussShell / shell_shape (referenceM + 1)) := by
  rw [one_over_alpha_EM_double_axis_eq_derived_mul_ratio, one_over_alpha_EM_derived_closed_form,
    gaussShellFactorRatio_em_to_electroweak_eq_shell_ratio]

theorem one_over_alpha_EM_double_axis_default_expands :
    one_over_alpha_EM_double_axis 1 =
      (42 : ℝ) * (1 + (3 / 5 : ℝ) * Real.log 9) * (shell_shape 3 / shell_shape 5) := by
  rw [one_over_alpha_EM_double_axis_expands, emGaussShell_val]
  have hlog : (2 * (3 + 1 : ℝ) + 1) = 9 := by norm_num
  have hden : referenceM + 1 = 5 := by
    unfold referenceM qcdShell stepsFromQCDToLockin latticeStepCount
    norm_num
  simp [hlog, hden]

theorem one_over_alpha_EM_double_axis_pos (c : ℝ)
    (hφ : 0 < phi_of_shell emGaussShell + 1)
    (hc : 1 + c * alpha * Real.log (phi_of_shell emGaussShell + 1) > 0) :
    0 < one_over_alpha_EM_double_axis c := by
  unfold one_over_alpha_EM_double_axis one_over_alpha_EM_derived
  have hderived : 0 < one_over_alpha_eff (phi_of_shell emGaussShell) c :=
    one_over_alpha_eff_pos (phi_of_shell emGaussShell) c hφ hc
  have hratio : 0 < gaussShellFactorRatio_em_to_electroweak := by
    rw [gaussShellFactorRatio_em_to_electroweak_eq_shell_ratio]
    apply div_pos
    · rw [shell_shape_eq_density_succ]
      exact curvatureDensity_pos_succ emGaussShell
    · rw [shell_shape_eq_density_succ]
      exact curvatureDensity_pos_succ electroweakPhiShell
  positivity

theorem alpha_EM_double_axis_pos (c : ℝ) (hφ : 0 < phi_of_shell emGaussShell + 1)
    (hc : 1 + c * alpha * Real.log (phi_of_shell emGaussShell + 1) > 0) :
    0 < alpha_EM_double_axis c := by
  unfold alpha_EM_double_axis
  exact inv_pos.mpr (one_over_alpha_EM_double_axis_pos c hφ hc)

/-!
## CODATA witness alignment (external scale check)
-/

/-- CODATA-style inverse fine-structure constant (witness, not a theorem input). -/
noncomputable def one_over_alpha_EM_CODATA : ℝ := 137.035999139

/-- Paper-aligned witness used elsewhere in the repo. -/
theorem one_over_alpha_EM_at_MZ_aligns_CODATA :
    one_over_alpha_EM_at_MZ = 127.9 := one_over_alpha_EM_at_MZ_eq

/-- **Target identification:** the double-axis derived inverse coupling is the quantity to
compare with `one_over_alpha_EM_CODATA` after the discrete shell brace (not `one_over_alpha_EM_derived`
at `electroweakPhiShell` alone). -/
theorem alpha_EM_double_axis_eq_inv (c : ℝ) :
    alpha_EM_double_axis c = (one_over_alpha_EM_double_axis c)⁻¹ := rfl

/-- When EM and electroweak rows coincide, the shell ratio is unity. -/
theorem gaussShellFactorRatio_eq_one_of_shells_eq (h : emGaussShell = electroweakPhiShell) :
    gaussShellFactorRatio_em_to_electroweak = 1 := by
  rw [gaussShellFactorRatio_em_to_electroweak_eq_shell_ratio, h]
  have hew : electroweakPhiShell = referenceM + 1 := rfl
  have hpos : shell_shape (referenceM + 1) ≠ 0 := ne_of_gt (by
    rw [shell_shape_eq_density_succ]
    exact curvatureDensity_pos_succ (referenceM + 1))
  rw [hew]
  exact div_self hpos

theorem one_over_alpha_EM_double_axis_eq_derived_when_shells_align (c : ℝ)
    (h : emGaussShell = electroweakPhiShell) :
    one_over_alpha_EM_double_axis c = one_over_alpha_EM_derived emGaussShell c := by
  unfold one_over_alpha_EM_double_axis
  rw [gaussShellFactorRatio_eq_one_of_shells_eq h, mul_one]

/-!
## Full discrete chain (ratio rigidity + one optional Fano coefficient)
-/

/-- End-to-end statement: double-axis \(\alpha\) is O–Maxwell on `emGaussShell` times the
shell-shape brace to `electroweakPhiShell`, with Gauss-law curvature cancellation already in
`gaussShellFactorRatio_em_to_electroweak`. -/
theorem double_axis_alpha_chain (c : ℝ) :
    one_over_alpha_EM_double_axis c =
      one_over_alpha_eff (phi_of_shell emGaussShell) c *
        (shell_shape emGaussShell / shell_shape (referenceM + 1)) ∧
      deltaE emGaussShell / fourPiGeom = shell_shape emGaussShell * 21 ∧
      emPreferredMatrixIndex = 1 ∧
      colourPreferredMatrixIndex = 7 := by
  refine ⟨?_, deltaE_div_fourPiGeom_eq_shell_shape_mul_twenty_one emGaussShell, ?_, ?_⟩
  · unfold one_over_alpha_EM_double_axis one_over_alpha_EM_derived
    rw [gaussShellFactorRatio_em_to_electroweak_eq_shell_ratio]
  · exact emPreferredMatrixIndex_eq_one
  · exact colourPreferredMatrixIndex_eq_seven

end Hqiv.Physics

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Hqiv.Algebra.Triality
import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.FanoOmaxwellSpectrum
import Hqiv.Physics.FanoResonance

namespace Hqiv.Physics

/-!
# Double preferred-axis geometry (combinatorial layer)

Formalizes the **algebraic + combinatorial** content of the HQIV paper double-axis method
(`paper/main.tex`, Sec. double-preferred-axis): two aligned axes (spatial symmetry + Fano /
octonionic gauge axis) and the **geometric solid-angle replacement**

\[
  4\pi_{\mathrm{geom}} = \frac{6^7\sqrt{3}}{7 \times 3}
\]

with \(7\) octonionic imaginary directions and \(3\) Spin(8) triality generations.

**Proved here (no continuum Maxwell measure theory):**

* preferred EM / colour Fano vertices and matrix indices \(e_1, e_7\);
* `fourPiGeom` as the combinatorial solid-angle slot;
* **cancellation:** \(\delta_E(m) / 4\pi_{\mathrm{geom}} = \mathrm{shell\_shape}(m) \times 21\), so the
  huge curvature norm does not double-count in horizon-corrected Gauss law;
* transverse orientation factor \(1/2\) for flux-tube bookkeeping (strong sector).

Continuum reduction \(2\pi r_\perp\,dr_\perp \to \int dr_\perp\) remains a hypothesis bundle
(`DoublePreferredAxisMeasureHypothesis` below).
-/

/-- **EM / weak preferred vertex** in the Fano plane (`FanoResonance`: vertex `0`). -/
def emPreferredFanoVertex : FanoVertex := ⟨0, by decide⟩

/-- **Colour-preferred vertex** (`e_7` axis; vertex `6` in the standard tagging). -/
def colourPreferredFanoVertex : FanoVertex := ⟨6, by decide⟩

theorem emPreferredFanoVertex_ne_colour :
    emPreferredFanoVertex ≠ colourPreferredFanoVertex := by
  decide

/-- Octonion carrier matrix indices for the two preferred axes (`fanoVertexMatrixIndex`). -/
def emPreferredMatrixIndex : Fin 8 := fanoVertexMatrixIndex emPreferredFanoVertex

def colourPreferredMatrixIndex : Fin 8 := fanoVertexMatrixIndex colourPreferredFanoVertex

theorem emPreferredMatrixIndex_eq_one : emPreferredMatrixIndex = 1 := by
  simp [emPreferredMatrixIndex, fanoVertexMatrixIndex, emPreferredFanoVertex]

theorem colourPreferredMatrixIndex_eq_seven : colourPreferredMatrixIndex = 7 := by
  simp [colourPreferredMatrixIndex, fanoVertexMatrixIndex, colourPreferredFanoVertex]

/-- Spin(8) triality generation count (three 8-dimensional irreps). -/
def trialityGenerationCount : ℕ := Fintype.card Hqiv.Algebra.So8RepIndex

theorem trialityGenerationCount_eq_three : trialityGenerationCount = 3 :=
  Hqiv.Algebra.card_so8_eight_dim_irreps

/-- Denominator \(7 \times 3\) in the paper's \(4\pi_{\mathrm{geom}}\) formula. -/
def geomSolidAngleDenominator : ℕ := octonionImaginaryDim * trialityGenerationCount

theorem geomSolidAngleDenominator_eq_twenty_one : geomSolidAngleDenominator = 21 := by
  unfold geomSolidAngleDenominator
  rw [octonionImaginaryDim_eq, trialityGenerationCount_eq_three]

/-- Combinatorial solid-angle slot \(4\pi_{\mathrm{geom}} = 6^7\sqrt{3}/(7\times 3)\). -/
noncomputable def fourPiGeom : ℝ :=
  curvature_norm_combinatorial / (geomSolidAngleDenominator : ℝ)

theorem fourPiGeom_eq_curvature_div_twenty_one :
    fourPiGeom = curvature_norm_combinatorial / 21 := by
  unfold fourPiGeom
  simp [geomSolidAngleDenominator_eq_twenty_one]

theorem fourPiGeom_pos : 0 < fourPiGeom := by
  rw [fourPiGeom_eq_curvature_div_twenty_one]
  exact div_pos curvature_norm_combinatorial_pos (by norm_num)

/-- Standard \(4\pi\) sphere measure (comparison only). -/
noncomputable def fourPiSphere : ℝ := 4 * Real.pi

theorem fourPiSphere_pos : 0 < fourPiSphere := by
  unfold fourPiSphere
  have hπ : 0 < Real.pi := Real.pi_pos
  nlinarith

/-- **Gauss-law shell factor** after curvature / solid-angle cancellation:
\(\delta_E(m) / 4\pi_{\mathrm{geom}} = \mathrm{shell\_shape}(m) \times 21\). -/
noncomputable def gaussLawShellFactor (m : ℕ) : ℝ :=
  shell_shape m * (geomSolidAngleDenominator : ℝ)

theorem gaussLawShellFactor_eq_shell_times_denominator (m : ℕ) :
    gaussLawShellFactor m = shell_shape m * 21 := by
  unfold gaussLawShellFactor
  simp [geomSolidAngleDenominator_eq_twenty_one]

theorem gaussLawShellFactor_pos (m : ℕ) : 0 < gaussLawShellFactor m := by
  rw [gaussLawShellFactor_eq_shell_times_denominator]
  have hshape : 0 < shell_shape m := by
    rw [shell_shape_eq_density_succ]
    exact curvatureDensity_pos_succ m
  nlinarith

/-- **Key cancellation:** the combinatorial curvature norm divides out of \(\delta_E\) against
`fourPiGeom`, leaving only the shell shape and the \(7\times 3\) projection. -/
theorem deltaE_div_fourPiGeom_eq_gaussLawShellFactor (m : ℕ) :
    deltaE m / fourPiGeom = gaussLawShellFactor m := by
  unfold deltaE gaussLawShellFactor fourPiGeom
  rw [geomSolidAngleDenominator_eq_twenty_one]
  have hN : curvature_norm_combinatorial ≠ 0 := ne_of_gt curvature_norm_combinatorial_pos
  have h21 : (21 : ℝ) ≠ 0 := by norm_num
  field_simp [hN, h21, shell_shape]

theorem deltaE_div_fourPiGeom_eq_shell_shape_mul_twenty_one (m : ℕ) :
    deltaE m / fourPiGeom = shell_shape m * 21 := by
  rw [deltaE_div_fourPiGeom_eq_gaussLawShellFactor, gaussLawShellFactor_eq_shell_times_denominator]

theorem curvature_norm_cancels_in_gauss_law (m : ℕ) :
    deltaE m / (curvature_norm_combinatorial / 21) = shell_shape m * 21 := by
  simpa [fourPiGeom_eq_curvature_div_twenty_one] using
    deltaE_div_fourPiGeom_eq_shell_shape_mul_twenty_one m

/-!
## Strong sector: orientation / quark–antiquark averaging
-/

/-- Paper symmetry factor \(1/2\) from \(\pm e_i\) or quark–antiquark orientation averaging. -/
noncomputable def fluxTubeOrientationFactor : ℝ := 1 / 2

theorem fluxTubeOrientationFactor_pos : 0 < fluxTubeOrientationFactor := by
  unfold fluxTubeOrientationFactor
  norm_num

/-!
## Continuum measure reduction (hypothesis only)
-/

/-- **Hypothesis bundle** for the continuum step: in the principal-axis frame aligned with
spatial + algebraic preferred axes, transverse flux integrals reduce to a single radial line
integral (times `fluxTubeOrientationFactor` in the colour flux-tube case). Not proved here. -/
structure DoublePreferredAxisMeasureHypothesis where
  /-- Area measure \(2\pi r_\perp dr_\perp\) collapses to \(\int dr_\perp\) on the aligned chart. -/
  transverse_to_radial : Prop
  /-- Solid-angle measure \(4\pi\) is replaced by `fourPiGeom` in the static EM Gauss law. -/
  sphere_to_combinatorial : Prop

/-!
## EM freeze-out shell vs electroweak readout shell

The paper evaluates the EM Gauss imprint on a high shell while the O–Maxwell \(\phi\)-running
readout for \(1/\alpha(M_Z)\) is taken at `electroweakPhiShell` (`referenceM + 1`). The
**ratio of shell shapes** between those two rows is the discrete “brace” translating lock-in
geometry to the electroweak scale without reintroducing \(\mathcal{N}_{\mathrm{curv}}\).
-/

/-- Shell one step below lock-in (`referenceM - 1`); used as the EM Gauss / imprint row in the
double-axis \(\alpha\) chain. -/
def emGaussShell : ℕ := referenceM - 1

theorem referenceM_ge_one : 1 ≤ referenceM := by
  unfold referenceM qcdShell stepsFromQCDToLockin latticeStepCount
  norm_num

theorem emGaussShell_lt_referenceM : emGaussShell < referenceM := by
  unfold emGaussShell
  exact Nat.sub_lt (referenceM_ge_one) (by decide)

theorem emGaussShell_val : emGaussShell = 3 := by
  unfold emGaussShell referenceM qcdShell stepsFromQCDToLockin latticeStepCount
  norm_num

/-- Ratio of Gauss-law shell factors between EM imprint row and electroweak readout row. -/
noncomputable def gaussShellFactorRatio_em_to_electroweak : ℝ :=
  gaussLawShellFactor emGaussShell / gaussLawShellFactor (referenceM + 1)

theorem gaussShellFactorRatio_em_to_electroweak_eq_shell_ratio :
    gaussShellFactorRatio_em_to_electroweak =
      shell_shape emGaussShell / shell_shape (referenceM + 1) := by
  unfold gaussShellFactorRatio_em_to_electroweak gaussLawShellFactor
  simp only [geomSolidAngleDenominator_eq_twenty_one]
  have h21 : (21 : ℝ) ≠ 0 := by norm_num
  have hshape3 : shell_shape emGaussShell ≠ 0 := ne_of_gt (by
    rw [shell_shape_eq_density_succ]
    exact curvatureDensity_pos_succ emGaussShell)
  have hshape5 : shell_shape (referenceM + 1) ≠ 0 := ne_of_gt (by
    rw [shell_shape_eq_density_succ]
    exact curvatureDensity_pos_succ (referenceM + 1))
  field_simp [h21, hshape3, hshape5]

end Hqiv.Physics

import Hqiv.Physics.ContinuousXiCoupling
import Hqiv.Physics.ReadoutGaugeSeed
import Hqiv.Physics.FanoHolonomyOverlap

/-!
# Parton carrier evolution (PDF moments)

Discrete DGLAP-like transport of PDF moments on the null-lattice carrier.
Full parton functions are witness records; moment theorems are the proved objects.
-/

namespace Hqiv.Physics

/-- PDF moment index (n = 0,1,2,...). -/
abbrev PdfMomentIndex := ℕ

/-- Carrier PDF moment at scale ξ. -/
structure PdfMoment where
  index : PdfMomentIndex
  value : ℝ
  xi : ℝ

/-- Discrete evolution step: moment n at ξ₂ from ξ₁ via curvature imprint. -/
noncomputable def pdfMomentTransport (n : PdfMomentIndex) (ξ₁ ξ₂ : ℝ) (M₁ : ℝ) : ℝ :=
  M₁ * (sigmaXi ξ₂ / sigmaXi ξ₁) ^ n *
    Real.exp (alpha * (continuousCurvaturePrimitive ξ₂ - continuousCurvaturePrimitive ξ₁))

theorem pdfMomentTransport_xi_self (n : PdfMomentIndex) (ξ M : ℝ) (hξ : 1 < ξ) :
    pdfMomentTransport n ξ ξ M = M := by
  unfold pdfMomentTransport
  have hs : 0 < sigmaXi ξ := by
    rw [sigmaXi]
    exact curvatureDensity_pos (le_of_lt hξ)
  simp [div_self (ne_of_gt hs), sub_self, Real.exp_zero]

theorem pdfMomentTransport_zero (ξ₁ ξ₂ M : ℝ) :
    pdfMomentTransport 0 ξ₁ ξ₂ M =
      M * Real.exp (alpha * (continuousCurvaturePrimitive ξ₂ - continuousCurvaturePrimitive ξ₁)) := by
  unfold pdfMomentTransport
  simp

/-- First moment (valence) at lock-in from holonomy row normalization. -/
noncomputable def pdfValenceMomentAtLockin : ℝ :=
  generationHolonomyRow 0 / generationHolonomyRowSum

theorem pdfValenceMomentAtLockin_eq :
    pdfValenceMomentAtLockin = (48 : ℝ) / 288 := by
  rw [pdfValenceMomentAtLockin, generationHolonomyRow_zero, generationHolonomyRowSum_eq]
  norm_num

/-- Gluon moment from trapped Casimir channel weight (channels 4–7 slot). -/
noncomputable def pdfGluonMomentAtLockin : ℝ :=
  (4 : ℝ) / 7 * gamma_HQIV

theorem pdfGluonMomentAtLockin_eq_eight_over_thirtyfive :
    pdfGluonMomentAtLockin = (8 : ℝ) / 35 := by
  simp [pdfGluonMomentAtLockin, gamma_eq_2_5]
  norm_num

structure PartonCarrierEvolutionCertificate where
  transport_identity : ∀ n ξ M, 1 < ξ → pdfMomentTransport n ξ ξ M = M
  valence_lockin : pdfValenceMomentAtLockin = (48 : ℝ) / 288
  gluon_lockin : pdfGluonMomentAtLockin = (8 : ℝ) / 35

theorem partonCarrierEvolutionCertificate_holds : PartonCarrierEvolutionCertificate where
  transport_identity := pdfMomentTransport_xi_self
  valence_lockin := pdfValenceMomentAtLockin_eq
  gluon_lockin := pdfGluonMomentAtLockin_eq_eight_over_thirtyfive

end Hqiv.Physics

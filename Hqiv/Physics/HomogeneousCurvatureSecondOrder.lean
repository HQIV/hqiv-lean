import Hqiv.Physics.DynamicBBNBaryogenesis
import Hqiv.Physics.HopfShellBeltramiMassBridge
import Hqiv.QuantumChemistry.DynamicBindingChart

/-!
# Homogeneous-curvature second order with local defect feedback

**Program (not yet the default chart):**

1. Compute the **homogeneous** curvature budget `B_hom(ξ, ρ)` at bulk medium density ρ
   (unity at dilute limit, full `B_curv(ξ)` at ice-like ρ = 1).
2. Add a **local** perturbation `δB` from nucleation / defect sites (coordination spike above
   the homogeneous background) — same geometric role as BBN `bbn_binding_curvature_perturbation`.
3. Feed `B_eff = B_hom + δB` back into the binding / melt readout (κ₆ and outside `G_eff`).

Nucleation sites matter because they break homogeneity: a dust grain, surface defect, or
local H-bond template raises `δB` before the bulk phase is stable.

Python mirror: `scripts/hqiv_homogeneous_curvature_feedback.py`.

Phase geometry supplies ρ without atom counting: `Hqiv.QuantumChemistry.PhaseGeometryDensity`.
-/

namespace Hqiv.Physics

open Hqiv
open Hqiv.QuantumChemistry

/-- Medium density ρ ∈ [0,1]: intermolecular coordination vs ice tetrahedral reference. -/
def clampMediumDensity (ρ : ℝ) : ℝ := max 0 (min 1 ρ)

/-- κ(ξ) coupling slot used as homogeneous curvature budget proxy (chart spine). -/
noncomputable def curvatureBudgetAtXi (ξ : ℝ) : ℝ :=
  dynamicBindingCurvatureCouplingAtXi ξ

/-- Homogeneous bulk curvature budget: dilute → 1, fully condensed → `curvatureBudgetAtXi`. -/
noncomputable def homogeneousCurvatureBudgetAtXi (ξ ρ : ℝ) : ℝ :=
  let ρc := clampMediumDensity ρ
  1 + ρc * (curvatureBudgetAtXi ξ - 1)

/-- Local defect excess above homogeneous background (nucleation / surface site). -/
noncomputable def localCurvatureDefectExcess (δ_coord : ℝ) : ℝ :=
  gamma_HQIV * strongChannelFraction * max δ_coord 0

/-- Effective curvature budget entering second-order feedback. -/
noncomputable def effectiveCurvatureBudgetAtXi (ξ ρ δ_coord : ℝ) : ℝ :=
  homogeneousCurvatureBudgetAtXi ξ ρ + localCurvatureDefectExcess δ_coord

/--
Second-order binding feedback using **effective** homogeneous+local budget.

Replaces bare `dynamicBindingCurvatureFeedbackSecondOrderAtXi` once the homogeneous
medium and nucleation defect are supplied — κ couples to `(B_eff − 1)` not raw chart ξ alone.
-/
noncomputable def bindingCurvatureFeedbackSecondOrderHomogeneous
    (ξ ρ δ_coord : ℝ) : ℝ :=
  let bEff := effectiveCurvatureBudgetAtXi ξ ρ δ_coord
  let κ := gamma_HQIV * strongChannelFraction * bEff
  let cRel := clusterBindingContrastRelative
  let c2Ratio := tuftLapseConcentrationAtXi ξ 0 0 / tuftLapseConcentrationAtXi xiLockin 0 0
  (1 + κ * cRel) * c2Ratio

/-- Nucleation raises local curvature: defect coordination above homogeneous ρ. -/
noncomputable def nucleationCoordinationExcess (ρ_hom ρ_local : ℝ) : ℝ :=
  max (ρ_local - clampMediumDensity ρ_hom) 0

end Hqiv.Physics

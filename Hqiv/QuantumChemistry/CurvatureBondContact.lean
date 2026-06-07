import Hqiv.Geometry.HQVMetric
import Hqiv.Physics.ComptonIRWindow
import Hqiv.Physics.MetaHorizonTrappedPlanckMass
import Hqiv.Physics.BBNNetworkFromWeights

import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Inside / outside curvature contact (Lean structural layer)

**Primary physics target: nuclear binding** — see `Hqiv.Physics.NuclearCurvatureBinding`.
This QuantumChemistry copy packages the same `G_eff(θ)` contact primitive for bond-state
network bookkeeping; chemistry eV is a downstream projection, not the definition site.

* **Inside:** `metaHorizonTrappedInsideRatio` times the composite-trace binding spine.
* **Outside (contact):** geometry-near bonding via `G_eff(θ/θ₀)` on contact points,
  with lattice `α = 3/5` (`G_eff(η) = η^α`) and `θ₀ = phaseTheta`.

Python counterpart: `scripts/hqiv_curvature_bond_state.py`.
-/

namespace Hqiv.QuantumChemistry

open scoped BigOperators
open Finset
open Hqiv
open Hqiv.Physics

noncomputable section

/-- Normalized contact phase in the Compton IR window: `η = θ / phaseTheta`. -/
noncomputable def contactPhaseParticipation (θ : ℝ) : ℝ := θ / phaseTheta

/-- Outside contact coupling at phase `θ`: `G_eff(θ/θ₀)` with `θ₀ = phaseTheta`. -/
noncomputable def outsideContactCoupling (θ : ℝ) : ℝ :=
  G_eff (contactPhaseParticipation θ)

theorem outsideContactCoupling_eq_eta_pow
    (θ : ℝ) (hθ : 0 ≤ θ) (hθb : θ ≤ phaseTheta) :
    outsideContactCoupling θ = (contactPhaseParticipation θ) ^ alpha := by
  have hη : 0 ≤ contactPhaseParticipation θ := by
    unfold contactPhaseParticipation
    exact div_nonneg hθ (le_of_lt phaseTheta_pos)
  unfold outsideContactCoupling
  exact G_eff_eq (contactPhaseParticipation θ) hη

theorem outsideContactCoupling_nonneg
    (θ : ℝ) (hθ : 0 ≤ θ) (hθb : θ ≤ phaseTheta) :
    0 ≤ outsideContactCoupling θ := by
  rw [outsideContactCoupling_eq_eta_pow θ hθ hθb]
  have hη : 0 ≤ contactPhaseParticipation θ := by
    unfold contactPhaseParticipation
    exact div_nonneg hθ (le_of_lt phaseTheta_pos)
  exact Real.rpow_nonneg hη alpha

/-- Inside-curvature binding weight at shell `m` relative to reference shell `m_ref`. -/
noncomputable def insideCurvatureWeight (m m_ref : ℕ) : ℝ :=
  metaHorizonTrappedInsideRatio m m_ref

theorem insideCurvatureWeight_self (m : ℕ)
    (hcur : 0 < metaHorizonCurvatureVolumeThrough m)
    (hplanck : 0 < trappedPlanckCumulativeBudget m) :
    insideCurvatureWeight m m = 1 := by
  unfold insideCurvatureWeight
  exact metaHorizonTrappedInsideRatio_self m hcur hplanck

theorem insideCurvatureWeight_referenceM_ground :
    insideCurvatureWeight referenceM referenceM = 1 := by
  unfold insideCurvatureWeight
  exact metaHorizonTrappedInsideRatio_referenceM_ground

/-- Inside binding energy at shell `m` projected through the nucleon composite trace. -/
noncomputable def insideCurvatureBindingAtShell (m m_ref : ℕ) (c : ℝ := 1) : ℝ :=
  insideCurvatureWeight m m_ref * bbnNucleonTraceBinding m c

/-- Molecular binding surplus from inside curvature closure minus separated fragments. -/
noncomputable def insideCurvatureSurplusAtShell
    (m_joint : ℕ) (fragmentShells : List ℕ) (c : ℝ := 1) : ℝ :=
  insideCurvatureBindingAtShell m_joint m_joint c -
    (fragmentShells.map fun m => insideCurvatureBindingAtShell m m_joint c).sum

end

end Hqiv.QuantumChemistry

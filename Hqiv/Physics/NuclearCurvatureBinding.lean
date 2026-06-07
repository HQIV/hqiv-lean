import Hqiv.Geometry.HQVMetric
import Hqiv.Physics.ComptonIRWindow
import Hqiv.Physics.MetaHorizonTrappedPlanckMass
import Hqiv.Physics.BBNNetworkFromWeights
import Hqiv.Physics.HQIVNuclei

import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Nuclear binding from inside / outside curvature

**Nuclear binding energy** is read from the same curvature slot as the proton (or any
hadron):

* **Inside:** `metaHorizonTrappedInsideRatio` × nucleon composite trace at the cluster
  readout shell, minus the separated-nucleon inside contribution.
* **Outside:** isotope-valley **contact points** bonded via `G_eff(θ/θ₀) = (θ/θ₀)^α`
  (lattice α = 3/5), scaled by the nucleon trace at the binding shell.

Python counterpart: `scripts/hqiv_nuclear_inside_outside_binding.py`.
-/

namespace Hqiv.Physics

open scoped BigOperators
open Finset
open Hqiv

noncomputable section

/-- Normalized contact phase: `η = θ / phaseTheta`. -/
noncomputable def nuclearContactPhaseParticipation (θ : ℝ) : ℝ := θ / phaseTheta

/-- Outside nucleon–nucleon contact coupling: `G_eff(η)` with `η = θ/phaseTheta`. -/
noncomputable def nuclearOutsideContactCoupling (θ : ℝ) : ℝ :=
  G_eff (nuclearContactPhaseParticipation θ)

theorem nuclearOutsideContactCoupling_eq_eta_pow
    (θ : ℝ) (hθ : 0 ≤ θ) (hθb : θ ≤ phaseTheta) :
    nuclearOutsideContactCoupling θ = (nuclearContactPhaseParticipation θ) ^ alpha := by
  have hη : 0 ≤ nuclearContactPhaseParticipation θ := by
    unfold nuclearContactPhaseParticipation
    exact div_nonneg hθ (le_of_lt phaseTheta_pos)
  unfold nuclearOutsideContactCoupling
  exact G_eff_eq (nuclearContactPhaseParticipation θ) hη

/-- Inside-curvature weight at cluster shell `m` relative to lock-in reference. -/
noncomputable def nuclearInsideCurvatureWeight (m m_ref : ℕ) : ℝ :=
  metaHorizonTrappedInsideRatio m m_ref

/-- Inside nuclear binding at shell `m` for mass number `A` (MeV-scale witness units). -/
noncomputable def nuclearInsideBindingAtShell (m m_cluster : ℕ) (A : ℕ) (c : ℝ := 1) : ℝ :=
  (A : ℝ) * bbnNucleonTraceBinding m c *
    max 0 (nuclearInsideCurvatureWeight m_cluster referenceM -
      nuclearInsideCurvatureWeight m referenceM)

/-- Valley contact count on the constructive isotope ladder. -/
def nuclearValleyContactCount : ℕ → ℕ := bbnValleyCount

/-- Outside nuclear binding from valley contact points at phase `θ`. -/
noncomputable def nuclearOutsideBindingAtShell
    (m : ℕ) (A : ℕ) (θ : ℝ) (c : ℝ := 1) : ℝ :=
  (nuclearValleyContactCount A : ℝ) *
    nuclearOutsideContactCoupling θ * bbnNucleonTraceBinding m c

/-- Total nuclear cluster binding = inside + outside (structural split). -/
noncomputable def nuclearClusterBindingCurvature
    (m m_cluster : ℕ) (A : ℕ) (θ : ℝ) (c : ℝ := 1) : ℝ :=
  nuclearInsideBindingAtShell m m_cluster A c +
    nuclearOutsideBindingAtShell m A θ c

theorem nuclearClusterBindingCurvature_add
    (m m_cluster : ℕ) (A : ℕ) (θ : ℝ) (c : ℝ) :
    nuclearClusterBindingCurvature m m_cluster A θ c =
      nuclearInsideBindingAtShell m m_cluster A c +
        nuclearOutsideBindingAtShell m A θ c := rfl

theorem nuclearValleyContactCount_four :
    nuclearValleyContactCount 4 = 6 := bbnValleyCount_four

end

end Hqiv.Physics

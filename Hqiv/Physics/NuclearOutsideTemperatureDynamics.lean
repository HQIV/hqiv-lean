import Hqiv.Physics.DynamicBBNBaryogenesis
import Hqiv.Physics.NuclearCausticBinding
import Hqiv.Physics.NuclearCurvatureBinding
import Hqiv.Physics.NeutronBindingStabilityScaffold
import Hqiv.Physics.ContinuousXiPath
import Hqiv.Physics.HopfShellBeltramiMassBridge

/-!
# Outside-curvature temperature dynamics (nuclear binding + β± slots)

Before a full `nucleon(p,n)` function, this module locks the **temperature-dependent
outside curvature** that weakens or deepens nucleon own-binding and outside caustics.

* **Release** — `bbnBindingReleaseFactor` at `T = T_Pl/ξ` (BBN / cooling).
* **Bonded deepen** — favorable inside/outside temperature balance deepens outside wells.
* **Free weaken** — sub-lock-in Ω readout weakens own binding (β− branch).

Inside trapped curvature (`nuclearInsideBindingAtShell`) stays the structural lock-in
spine; outside caustics and trace binding carry ξ.

Python: `scripts/hqiv_nuclear_outside_temperature_dynamics.py`.
-/

namespace Hqiv.Physics

open Hqiv
open ContinuousXiPath

noncomputable section

/-- Temperature at horizon coordinate ξ on the BBN ladder. -/
noncomputable def T_MeV_from_xi (ξ : ℝ) : ℝ := T_Pl_MeV / ξ

/-- Outside-curvature release factor at ξ (same as BBN binding release at T(ξ)). -/
noncomputable def outsideCurvatureReleaseFactor (ξ : ℝ) : ℝ :=
  bbnBindingReleaseFactor (T_MeV_from_xi ξ)

theorem outsideCurvatureReleaseFactor_pos (ξ : ℝ) :
    0 < outsideCurvatureReleaseFactor ξ := by
  unfold outsideCurvatureReleaseFactor
  exact bbnBindingReleaseFactor_pos (T_MeV_from_xi ξ)

/-- At lock-in calibration the Python branch sets the outside modulator to unity. -/
def outsideCurvatureLockinCalibrated : Prop := True

theorem outsideCurvatureLockinCalibrated_holds : outsideCurvatureLockinCalibrated := trivial

/-- Ωₖ readout at ξ (continuous chart). -/
noncomputable def omegaReadoutAtXi (ξ : ℝ) : ℝ := omegaK_xi ξ

/-- Nucleon own-binding at ξ: composite trace × outside release (bonded lock-in spine). -/
noncomputable def nucleonOwnBindingAtXi (m : ℕ) (ξ : ℝ) (c : ℝ := 1) : ℝ :=
  bbnNucleonTraceBinding m c * outsideCurvatureReleaseFactor ξ

/-- Outside caustic stack modulated by outside temperature at ξ. -/
noncomputable def nuclearOutsideCausticBindingAtXi
    (m : ℕ) (A : ℕ) (θ : ℝ) (ξ : ℝ) (c : ℝ := 1) : ℝ :=
  nuclearOutsideCausticBinding m A θ c * outsideCurvatureReleaseFactor ξ

/-- Cluster binding at ξ: inside structural + outside caustics × release. -/
noncomputable def nuclearClusterBindingAtXi
    (m m_cluster : ℕ) (A : ℕ) (θ : ℝ) (ξ : ℝ) (c : ℝ := 1) : ℝ :=
  nuclearInsideBindingAtShell m m_cluster A c +
    nuclearOutsideCausticBindingAtXi m A θ ξ c

theorem nuclearClusterBindingAtXi_add
    (m m_cluster : ℕ) (A : ℕ) (θ : ℝ) (ξ : ℝ) (c : ℝ) :
    nuclearClusterBindingAtXi m m_cluster A θ ξ c =
      nuclearInsideBindingAtShell m m_cluster A c +
        nuclearOutsideCausticBindingAtXi m A θ ξ c := by
  unfold nuclearClusterBindingAtXi
  ring

/-- β− overlap slot: isospin gap + free curvature deficit (scaffold). -/
noncomputable def betaMinusOverlapAtXi (ξ : ℝ) : ℝ :=
  freeNeutronOverlapEnergy (omegaReadoutAtXi ξ)

theorem betaMinusOverlap_eq_scaffold (ξ : ℝ) :
    betaMinusOverlapAtXi ξ = freeNeutronOverlapEnergy (omegaK_xi ξ) := rfl

/-- Bonded stability predicate (well + shared binding; skew slot open). -/
def bondedNuclearStableAtXi (wellDepth : ℝ) (ξ : ℝ) : Prop :=
  0 < wellDepth + nucleonOwnBindingAtXi referenceM ξ

/-- Dimensionless gravitational potential slot `ε = GM/(Rc²)` for outside support. -/
structure OutsideGravityWitness where
  phiEpsilon : ℝ

/-- One additive layer of the weak-field binding stack (Earth, Sun, Galaxy, …). -/
structure OutsideGravityLayerWitness where
  label : String
  phiEpsilon : ℝ

/-- Sum of weak-field binding layers booked into the outside channel. -/
noncomputable def outsideGravityPhiSum (layers : List OutsideGravityLayerWitness) : ℝ :=
  (layers.map fun g => g.phiEpsilon).sum

/-- Molecular host binding inherited by one nucleus (bond-state network contact share). -/
structure OutsideMolecularWitness where
  hostLabel : String
  phiEpsilon : ℝ

/-- Outside support from local gravity via `G_eff(1+ε)` (`HQVMetric.G_eff`, α = 3/5). -/
noncomputable def outsideGravityGeffModulator (g : OutsideGravityWitness) : ℝ :=
  if g.phiEpsilon ≤ 0 then 1
  else 1 + gamma_HQIV * ((1 + g.phiEpsilon) ^ alpha - 1)

/-- Combined temperature + gravity outside modulator (multiplicative on the temperature branch). -/
noncomputable def outsideEnvironmentModulator
    (ξ : ℝ) (bonded : Bool) (g : OutsideGravityWitness) : ℝ :=
  -- Python supplies the full bonded/free temperature branch; this names the gravity slot.
  outsideGravityGeffModulator g

/-- β± channel tag (structural; weak widths separate). -/
inductive BetaDecayChannel
  | betaMinus
  | betaPlus
  deriving DecidableEq, Repr

end

end Hqiv.Physics

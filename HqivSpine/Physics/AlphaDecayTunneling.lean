import HqivSpine.Physics.Tunneling
import HqivSpine.Physics.NuclearCluster
import HqivSpine.Physics.NucleonLadder
import HqivSpine.Chemistry.Binding

/-!
# `HqivSpine.Physics.AlphaDecayTunneling` — curvature binding → Gamow law

Bridges `NuclearCluster` Q-values and outside contact barriers to the spine `Tunneling` toolkit,
mined from legacy `AlphaDecayCurvatureTunneling`. No PDG input, no fitted potential.

Honest scope: **Geiger–Nuttall monotonicity** and half-life positivity — not absolute α-decay
calibration without the MeV unit label.
-/

namespace HqivSpine.Physics.AlphaDecayTunneling

open HqivSpine.Physics
open HqivSpine.Physics.NuclearCluster

/-- α-particle reduced-mass scale in dimensionless ladder units (four nucleon masses). -/
def alphaTunnelingMassScale : ℝ := 4

theorem alphaTunnelingMassScale_pos : 0 < alphaTunnelingMassScale := by
  unfold alphaTunnelingMassScale; norm_num

/-- Resonance width shell radius `m + 1`. -/
noncomputable def resonanceShellRadius (m : ℕ) : ℝ := (m + 1 : ℝ)

theorem resonanceShellRadius_pos (m : ℕ) : 0 < resonanceShellRadius m := by
  unfold resonanceShellRadius; positivity

/-- **Q-value:** binding released when parent splits to daughter + α. -/
noncomputable def alphaDecayQ (m m_cluster A : ℕ) (θ c : ℝ) : ℝ :=
  clusterBinding m m_cluster (A - 4) θ c
    + clusterBinding m m_cluster 4 θ c
    - clusterBinding m m_cluster A θ c

/-- Curvature-Coulomb barrier from daughter outside coupling. -/
noncomputable def alphaCurvatureBarrier (m Z : ℕ) (θ : ℝ) : ℝ :=
  2 * max 0 ((Z : ℝ) - 2) * outsideContactCoupling θ / resonanceShellRadius m

/-- Interior Gamow rate `κ = √(2μ(V−Q))`. -/
noncomputable def alphaDecayKappa (m m_cluster A Z : ℕ) (θ c : ℝ) : ℝ :=
  kappaForbidden alphaTunnelingMassScale
    (alphaDecayQ m m_cluster A θ c)
    (alphaCurvatureBarrier m Z θ)

/-- α-decay half-life. -/
noncomputable def alphaDecayHalfLife (ν L : ℝ) (m m_cluster A Z : ℕ) (θ c : ℝ) : ℝ :=
  halfLife ν (alphaDecayKappa m m_cluster A Z θ c) L

theorem alphaDecayHalfLife_pos (ν L : ℝ) (hν : 0 < ν) (m m_cluster A Z : ℕ) (θ c : ℝ) :
    0 < alphaDecayHalfLife ν L m m_cluster A Z θ c :=
  halfLife_pos ν _ L hν

/-- **Geiger–Nuttall:** larger Q at fixed barrier gives shorter half-life. -/
theorem alphaHalfLife_antitone_Q (ν L V : ℝ) (hν : 0 < ν) (hL : 0 < L)
    {Q Q' : ℝ} (hQ : Q ≤ Q') (hQV : Q' < V) :
    halfLife ν (kappaForbidden alphaTunnelingMassScale Q' V) L
      ≤ halfLife ν (kappaForbidden alphaTunnelingMassScale Q V) L := by
  apply halfLife_monotone_kappa ν L hν hL
  exact kappaForbidden_antitone_E alphaTunnelingMassScale V alphaTunnelingMassScale_pos.le hQ hQV

/-- Taller barrier ⇒ longer half-life at fixed Q. -/
theorem alphaHalfLife_monotone_barrier (ν L Q : ℝ) (hν : 0 < ν) (hL : 0 < L)
    {V V' : ℝ} (hV : V ≤ V') :
    halfLife ν (kappaForbidden alphaTunnelingMassScale Q V) L
      ≤ halfLife ν (kappaForbidden alphaTunnelingMassScale Q V') L := by
  apply halfLife_monotone_kappa ν L hν hL
  exact kappaForbidden_monotone_V alphaTunnelingMassScale Q alphaTunnelingMassScale_pos.le hV

structure AlphaDecayTunnelingCertified : Prop where
  half_life_pos :
    ∀ ν L (_ : 0 < ν) m m_cluster A Z θ c,
      0 < alphaDecayHalfLife ν L m m_cluster A Z θ c
  geiger_nuttall :
    ∀ ν L V (_ : 0 < ν) (_ : 0 < L) Q Q', Q ≤ Q' → Q' < V →
      halfLife ν (kappaForbidden alphaTunnelingMassScale Q' V) L
        ≤ halfLife ν (kappaForbidden alphaTunnelingMassScale Q V) L

theorem alphaDecayTunnelingCertified : AlphaDecayTunnelingCertified where
  half_life_pos := fun ν L hν m m_cluster A Z θ c =>
    alphaDecayHalfLife_pos ν L hν m m_cluster A Z θ c
  geiger_nuttall := fun ν L V hν hL _ _ hQ hQV =>
    alphaHalfLife_antitone_Q ν L V hν hL hQ hQV

end HqivSpine.Physics.AlphaDecayTunneling

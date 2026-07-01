/-
# α-decay as curvature-barrier tunneling

This module bridges the HQIV nuclear curvature-binding ladder
(`Hqiv.Physics.NuclearCurvatureBinding`) to the 3D tunneling toolkit
(`Hqiv.QuantumMechanics.Tunneling`).

The two HQIV-derived inputs are:

* the **decay energy** `Q = B(daughter) + B(α) − B(parent)`, the curvature binding *released*
  when a parent nucleus emits an α-particle (α-decay is energetically favoured when `Q > 0`);
* the **curvature-Coulomb barrier** `V₀`, the outside contact coupling the α must climb to
  escape past the daughter shell.

Feeding these into the interior decay rate `κ = √(2μ(V₀−Q))/ħ` and the Gamow half-life
`t₁/₂ = ln2 / (ν · e^{−2κL})` reproduces the **Geiger–Nuttall law** with *zero* PDG input
and *no fitted potential*: half-life falls monotonically with the curvature decay energy `Q`
and rises monotonically with the curvature barrier height and width.
-/
import Hqiv.QuantumMechanics.Tunneling
import Hqiv.Physics.NuclearCurvatureBinding
import Hqiv.Physics.SM_GR_Unification
import Hqiv.Physics.DerivedNucleonMass

namespace Hqiv.Physics

-- The tunneling Gamow half-life `Hqiv.halfLife` is referenced fully qualified below to
-- disambiguate from the nucleus-indexed `Hqiv.Physics.halfLife` in this namespace.
open Hqiv

noncomputable section

/-- α-particle reduced-mass scale (≈ 4 nucleon masses, MeV-witness units of the binding ladder). -/
noncomputable def alphaTunnelingMass : ℝ := 4 * m_proton_MeV_central

theorem alphaTunnelingMass_pos : 0 < alphaTunnelingMass := by
  unfold alphaTunnelingMass m_proton_MeV_central
  have := derivedProtonMass_pos
  positivity

/-- **Q-value of α-decay** as the curvature-binding difference
`Q = B(daughter) + B(α) − B(parent)` (released energy; α-decay is favoured when `Q > 0`). -/
noncomputable def alphaDecayQ (m m_cluster A Z : ℕ) (θ c : ℝ) : ℝ :=
  nuclearClusterBindingNetworkCurvature m m_cluster (A - 4) (Z - 2) θ c
    + nuclearClusterBindingNetworkCurvature m m_cluster 4 2 θ c
    - nuclearClusterBindingNetworkCurvature m m_cluster A Z θ c

theorem alphaDecayQ_eq (m m_cluster A Z : ℕ) (θ c : ℝ) :
    alphaDecayQ m m_cluster A Z θ c
      = nuclearClusterBindingNetworkCurvature m m_cluster (A - 4) (Z - 2) θ c
        + nuclearClusterBindingNetworkCurvature m m_cluster 4 2 θ c
        - nuclearClusterBindingNetworkCurvature m m_cluster A Z θ c := rfl

/-- The α-decay condition `Q > 0` is precisely `B(daughter) + B(α) > B(parent)`. -/
theorem alphaDecayQ_pos_iff (m m_cluster A Z : ℕ) (θ c : ℝ) :
    0 < alphaDecayQ m m_cluster A Z θ c ↔
      nuclearClusterBindingNetworkCurvature m m_cluster A Z θ c <
        nuclearClusterBindingNetworkCurvature m m_cluster (A - 4) (Z - 2) θ c
          + nuclearClusterBindingNetworkCurvature m m_cluster 4 2 θ c := by
  unfold alphaDecayQ
  constructor <;> intro h <;> linarith

/-- **HQIV curvature-Coulomb barrier** the α tunnels through: the daughter's outside contact
coupling, weighted by the product of α and daughter charges `2(Z−2)`, over the shell radius
`resonanceWidthShellRadius m = m + 1`.  No external table or fitted potential enters. -/
noncomputable def alphaCurvatureBarrierHeight (m Z : ℕ) (θ : ℝ) : ℝ :=
  2 * ((Z : ℝ) - 2) * nuclearOutsideContactCoupling θ / resonanceWidthShellRadius m

/-- Interior tunneling decay rate `κ = √(2μ(V₀−Q))/ħ` for the α at decay energy `Q`. -/
noncomputable def alphaDecayKappa (m m_cluster A Z : ℕ) (θ c : ℝ) : ℝ :=
  kappaForbidden alphaTunnelingMass (alphaDecayQ m m_cluster A Z θ c)
    (alphaCurvatureBarrierHeight m Z θ)

/-- α-decay half-life through the HQIV curvature barrier (attempt frequency `ν`, width `L`). -/
noncomputable def alphaDecayHalfLife (ν L : ℝ) (m m_cluster A Z : ℕ) (θ c : ℝ) : ℝ :=
  Hqiv.halfLife ν (alphaDecayKappa m m_cluster A Z θ c) L

theorem alphaDecayHalfLife_pos (ν L : ℝ) (hν : 0 < ν) (m m_cluster A Z : ℕ) (θ c : ℝ) :
    0 < alphaDecayHalfLife ν L m m_cluster A Z θ c :=
  halfLife_pos ν _ L hν

/-! ## Geiger–Nuttall law (PDG-free, curvature-sourced) -/

/-- **Geiger–Nuttall energy law**: among α-emitters sharing a curvature barrier `V₀`, width `L`
and attempt frequency `ν`, a *larger* curvature decay energy `Q` gives a *shorter* half-life. -/
theorem alphaHalfLife_antitone_Q (ν L V₀ : ℝ) (hν : 0 < ν) (hL : 0 < L)
    {Q Q' : ℝ} (hQ : Q ≤ Q') (hQV : Q' < V₀) :
    Hqiv.halfLife ν (kappaForbidden alphaTunnelingMass Q' V₀) L
      ≤ Hqiv.halfLife ν (kappaForbidden alphaTunnelingMass Q V₀) L := by
  apply halfLife_monotone_kappa ν L hν hL
  exact kappaForbidden_antitone_E alphaTunnelingMass V₀ alphaTunnelingMass_pos.le hQ hQV

/-- **Taller barriers live longer**: at fixed decay energy `Q < V`, a higher curvature barrier
gives a longer half-life. -/
theorem alphaHalfLife_monotone_barrier (ν L Q : ℝ) (hν : 0 < ν) (hL : 0 < L)
    {V V' : ℝ} (hV : V ≤ V') :
    Hqiv.halfLife ν (kappaForbidden alphaTunnelingMass Q V) L
      ≤ Hqiv.halfLife ν (kappaForbidden alphaTunnelingMass Q V') L := by
  apply halfLife_monotone_kappa ν L hν hL
  exact kappaForbidden_monotone_V alphaTunnelingMass Q alphaTunnelingMass_pos.le hV

/-- **Wider barriers live longer**: at fixed positive interior rate `κ`, a thicker barrier gives
a longer half-life. -/
theorem alphaHalfLife_monotone_width (ν κ : ℝ) (hν : 0 < ν) (hκ : 0 < κ) {L L' : ℝ}
    (h : L ≤ L') : Hqiv.halfLife ν κ L ≤ Hqiv.halfLife ν κ L' :=
  halfLife_monotone_L ν κ hν hκ h

/-! ## Certificate bundle -/

/-- Bundles the curvature → tunneling α-decay bridge: positivity of the half-life, the
Geiger–Nuttall energy law, and barrier height/width monotonicity. -/
structure AlphaDecayCurvatureCertified : Prop where
  half_life_pos :
    ∀ ν L (_hν : 0 < ν) m m_cluster A Z θ c,
      0 < alphaDecayHalfLife ν L m m_cluster A Z θ c
  geiger_nuttall :
    ∀ ν L V₀ (_hν : 0 < ν) (_hL : 0 < L) (Q Q' : ℝ), Q ≤ Q' → Q' < V₀ →
      Hqiv.halfLife ν (kappaForbidden alphaTunnelingMass Q' V₀) L
        ≤ Hqiv.halfLife ν (kappaForbidden alphaTunnelingMass Q V₀) L
  taller_lives_longer :
    ∀ ν L Q (_hν : 0 < ν) (_hL : 0 < L) (V V' : ℝ), V ≤ V' →
      Hqiv.halfLife ν (kappaForbidden alphaTunnelingMass Q V) L
        ≤ Hqiv.halfLife ν (kappaForbidden alphaTunnelingMass Q V') L
  wider_lives_longer :
    ∀ ν κ (_hν : 0 < ν) (_hκ : 0 < κ) (L L' : ℝ), L ≤ L' →
      Hqiv.halfLife ν κ L ≤ Hqiv.halfLife ν κ L'

theorem alphaDecayCurvatureCertified : AlphaDecayCurvatureCertified where
  half_life_pos := fun ν L hν m m_cluster A Z θ c =>
    alphaDecayHalfLife_pos ν L hν m m_cluster A Z θ c
  geiger_nuttall := fun ν L V₀ hν hL _Q _Q' hQ hQV =>
    alphaHalfLife_antitone_Q ν L V₀ hν hL hQ hQV
  taller_lives_longer := fun ν L Q hν hL _V _V' hV =>
    alphaHalfLife_monotone_barrier ν L Q hν hL hV
  wider_lives_longer := fun ν κ hν hκ _L _L' h =>
    alphaHalfLife_monotone_width ν κ hν hκ h

end

end Hqiv.Physics

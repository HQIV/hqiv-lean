import Hqiv.Geometry.HQVMetric
import Hqiv.Physics.ComptonIRWindow
import Hqiv.Physics.MetaHorizonTrappedPlanckMass
import Hqiv.Physics.BBNNetworkFromWeights
import Hqiv.Physics.HQIVNuclei
import Hqiv.Physics.NuclearAndAtomicSpectra
import Hqiv.Physics.PostAlphaBindingGeometry

import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Nuclear binding from inside / outside curvature

**Nuclear binding energy** is read from the same curvature slot as the proton (or any
hadron):

* **Inside:** `metaHorizonTrappedInsideRatio` × nucleon composite trace at the cluster
  readout shell, minus the separated-nucleon inside contribution.
* **Outside:** isotope-valley **contact points** bonded via `G_eff(θ/θ₀) = (θ/θ₀)^α`
  (lattice α = 3/5), scaled by the nucleon trace at the binding shell.
* **Network (shared wells):** valley occupancy deepens wells; deepened sites interact
  via `γ`; barbell / tetra cooperative closure; post-α extension for `A > 4`.
* **Residual:** spin–statistics participation + magnetic dipole contrast
  (`μ_n μ_p / R_m`) — last few percent (see `nuclearSpinMagneticResidualParticipation`).

Python counterpart: `scripts/hqiv_curvature_binding_core.py`.
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

/-- Per-valley-contact well deepening increment: `(4/8) / constructiveValleyCap`. -/
noncomputable def nuclearDeepeningPerValleyContact : ℝ :=
  strongChannelFraction / (constructiveValleyCap : ℝ)

/-- Intrinsic well deepening from valley occupancy (constructive ladder). -/
noncomputable def nuclearIntrinsicWellDeepening (A : ℕ) : ℝ :=
  if nuclearValleyContactCount A ≤ 1 then 1
  else
    1 + nuclearDeepeningPerValleyContact *
      ((nuclearValleyContactCount A : ℝ) - 1)

/-- Mass-deficit deepening: each nucleon loses `B/A` into shared wells. -/
noncomputable def nuclearMassDeficitWellDeepening (bindingPerNucleon : ℝ) : ℝ :=
  if bindingPerNucleon ≤ 0 then 1
  else
    1 + gamma_HQIV * strongChannelFraction * bindingPerNucleon / m_proton_MeV_central

/-- Constructive valley ladder in `G_eff × trace` currency (`A ≤ 4` spine). -/
noncomputable def nuclearValleyLadderOutside (m : ℕ) (A : ℕ) (θ : ℝ) (c : ℝ := 1) : ℝ :=
  if A ≤ 1 then 0
  else
    (A : ℝ) * (1 + (nuclearValleyContactCount A : ℝ) / (constructiveValleyCap : ℝ)) *
      nuclearOutsideContactCoupling θ * bbnNucleonTraceBinding m c

/-- Barbell cooperative participation: `(vc − 2) / (cap − 2)`. -/
noncomputable def nuclearBarbellCooperativeParticipation (A : ℕ) : ℝ :=
  if nuclearValleyContactCount A ≤ 2 then 0
  else
    ((nuclearValleyContactCount A : ℝ) - 2) /
      ((constructiveValleyCap : ℝ) - 2)

/-- Barbell torus scale at shell `m` (matches `NuclearCausticBinding`). -/
noncomputable def nuclearBarbellTorusScale (m : ℕ) : ℝ :=
  gamma_HQIV * Hqiv.new_modes (m + 1) / R_m (m + 1)

/-- Tetrahedral closure scale two shells above binding drum `m`. -/
noncomputable def nuclearTetrahedralClosureScale (m : ℕ) : ℝ :=
  gamma_HQIV * modes (m + 2) / R_m (m + 2)

/-- Closed α tetra cooperative boost (⁴He shell completion). -/
noncomputable def alphaClosedCooperativeParticipation (A : ℕ) : ℝ :=
  if A = 4 then
    1 + gamma_HQIV * strongChannelFraction / (constructiveValleyCap : ℝ)
  else 1

/-- Proton Coulomb erosion on outside contacts: valley + EM repulsion for proton-rich nuclei. -/
noncomputable def protonCoulombOutsideErosion (m A Z : ℕ) (geff : ℝ) : ℝ :=
  if Z < 2 ∨ A = 0 then 0
  else
    let protonExcess := max 0 ((2 * Z - A : ℤ) : ℝ) / (A : ℝ)
    let vc := (nuclearValleyContactCount A : ℝ)
    let cap := (constructiveValleyCap : ℝ)
    let valleyPart := if cap = 0 then 0 else vc / cap
    let erosion :=
      protonExcess * geff * deuteronBindingScale m * strongChannelFraction * valleyPart
    if 4 < A ∧ 0 < vc then erosion * cap / vc else erosion

/-- γ-network on valley contacts (`vc > 2` only). -/
noncomputable def nuclearGammaNetworkOnValleyContacts
    (m : ℕ) (A : ℕ) (θ : ℝ) (c : ℝ := 1) : ℝ :=
  if A ≤ 1 ∨ nuclearValleyContactCount A ≤ 2 then 0
  else
    let deepen := nuclearIntrinsicWellDeepening A
    let coreVc := (min (nuclearValleyContactCount A) constructiveValleyCap : ℝ)
    gamma_HQIV * (deepen - 1) * coreVc *
      nuclearOutsideContactCoupling θ * bbnNucleonTraceBinding m c *
        deuteronBindingScale m * alphaClosedCooperativeParticipation A

/-- Outside shared-well network for constructive valley nuclei (`A ≤ 4`). -/
noncomputable def nuclearOutsideNetworkBindingAtShell
    (m : ℕ) (A : ℕ) (θ : ℝ) (c : ℝ := 1) : ℝ :=
  if A ≤ 1 then 0
  else if 4 < A then 0
  else
    let geff := nuclearOutsideContactCoupling θ
    let trace := bbnNucleonTraceBinding m c
    let intrinsic := nuclearIntrinsicWellDeepening A
    let ladder :=
      if A < 3 then
        (A : ℝ) * (1 + (nuclearValleyContactCount A : ℝ) / (constructiveValleyCap : ℝ)) *
          geff * trace
      else
        nuclearValleyLadderOutside m A θ c * intrinsic
    let network := nuclearGammaNetworkOnValleyContacts m A θ c
    let barbell :=
      nuclearBarbellCooperativeParticipation A *
        nuclearBarbellTorusScale m * geff * trace * intrinsic
    let tetra :=
      if A < 4 then 0
      else
        nuclearTetrahedralClosureScale m * geff * trace * intrinsic *
          alphaClosedCooperativeParticipation A
    ladder + network + barbell + tetra

/-- Spin–statistics + residual magnetic dipole participation (dimensionless). -/
noncomputable def nuclearSpinMagneticResidualParticipation (m A Z : ℕ) : ℝ :=
  let vc := (nuclearValleyContactCount A : ℝ)
  let cap := (constructiveValleyCap : ℝ)
  let r := (R_m m : ℝ)
  let muProduct := gamma_HQIV * gamma_HQIV
  let valleyPart := if cap = 0 then 0 else vc / cap
  let isospinAsym :=
    if A = 0 then 0
    else (Int.natAbs ((A : ℤ) - 2 * (Z : ℤ)) : ℝ) / (A : ℝ)
  gamma_HQIV * strongChannelFraction *
    (muProduct * valleyPart / r + spinStabilityParticipation A Z * isospinAsym * valleyPart)

/-- Spin-statistics completeness: `1` when every nucleon sits in a closed spin pair.

The deuteron (`A = 2, Z = 1`) is the unique odd-odd bound state — its proton and neutron lock
into a single spin-triplet `np` pair — so it counts as saturated.  Otherwise saturation is the
even-even condition (`Z` and `N = A − Z` both even and positive).  Odd-A nuclei carry one unpaired
nucleon and odd-odd valence nuclei two, so they are not saturated. -/
noncomputable def nuclearSpinSaturatedPairing (A Z : ℕ) : ℝ :=
  if A = 2 ∧ Z = 1 then 1
  else if Z % 2 = 0 ∧ (A - Z) % 2 = 0 ∧ 0 < Z ∧ 0 < A - Z then 1 else 0

/-- Free-surface spin-alignment boundary lift: the second geometric channel of the magnetic
coupling.  The spin–magnetic residual carries the dipole-product coupling `γ·(4/8)·γ²`
(`μ_n μ_p ~ γ²`) on the *valley-contact* geometry `vc/(cap·R_m)`; spin-saturated nucleons aligned
along the **free boundary** open the same coupling on a *surface* geometry `1/A^(1/3)` (boundary
nucleons per nucleon), weighted by `nuclearSpinSaturatedPairing`.  No new constant enters — only the
geometric factor (surface vs valley) differs:

  `γ · (4/8) · γ² · nuclearSpinSaturatedPairing A Z / A^(1/3)`. -/
noncomputable def nuclearSpinAlignmentBoundaryParticipation (A Z : ℕ) : ℝ :=
  if A ≤ 1 then 0
  else
    gamma_HQIV * strongChannelFraction * (gamma_HQIV * gamma_HQIV) *
      nuclearSpinSaturatedPairing A Z / (A : ℝ) ^ ((1 : ℝ) / 3)

/-- The boundary lift shares the spin–magnetic residual's `γ³·(4/8)` dipole coupling exactly:
its strength differs from the residual's `muProduct` channel only by the geometric factor
(`1/A^(1/3)` boundary vs `vc/(cap·R_m)` valley). -/
theorem nuclearSpinAlignmentBoundaryParticipation_coupling (A Z : ℕ) (hA : 2 ≤ A) :
    nuclearSpinAlignmentBoundaryParticipation A Z =
      gamma_HQIV * strongChannelFraction * (gamma_HQIV * gamma_HQIV) *
        nuclearSpinSaturatedPairing A Z / (A : ℝ) ^ ((1 : ℝ) / 3) := by
  unfold nuclearSpinAlignmentBoundaryParticipation
  have : ¬ A ≤ 1 := by omega
  simp [this]

/-- Unpaired (odd-A or odd-odd, non-deuteron) clusters receive no alignment boundary lift. -/
theorem nuclearSpinAlignmentBoundaryParticipation_unpaired (A Z : ℕ)
    (h : nuclearSpinSaturatedPairing A Z = 0) :
    nuclearSpinAlignmentBoundaryParticipation A Z = 0 := by
  unfold nuclearSpinAlignmentBoundaryParticipation
  split
  · rfl
  · rw [h]; ring

/-- Incremental facet/far geometry only (no α-cap duplication). -/
noncomputable def postAlphaIncrementalGeometricTouchEnergy (m A Z : ℕ) : ℝ :=
  if A ≤ 4 then 0
  else
    spinStabilityParticipation A Z *
      (protonFacetTouchContactSum (bbnProtonFacetTouches A Z) : ℝ) *
        sphereTouchContactEnergyUnit m +
      farNeutronWeightedContactSum A Z * sphereTouchContactEnergyUnit m

/-- Proton-excess tension: `max(0, Z − N) / (A − 4)` (not neutron-rich far-neutron). -/
noncomputable def postAlphaAlphaAdditionIsospinTension (A Z : ℕ) : ℝ :=
  if A ≤ 4 then 0
  else
    let n := A - Z
    max 0 ((Z : ℝ) - (n : ℝ)) / (A - 4 : ℝ)

/-- Barbell torus scale: `γ · new_modes(m+1) / R_{m+1}` (inter-α barbell links). -/
noncomputable def barbellTorusScale (m : ℕ) : ℝ :=
  gamma_HQIV * Hqiv.new_modes (m + 1) / R_m (m + 1)

/-- Closed α multiple count when `A = 4n` and `Z = A/2`. -/
noncomputable def closedAlphaClusterCount (A Z : ℕ) : Option ℕ :=
  if 8 ≤ A ∧ A % 4 = 0 ∧ Z = A / 2 then some (A / 4) else none

/-- Resonance-width denominator: discrete shell radius `R_m = m + 1` on the binding ladder. -/
noncomputable def resonanceWidthShellRadius (m : ℕ) : ℝ := (m + 1 : ℝ)

/-- Two-α resonance width (⁸Be): erodes over-tight double closure.

`B · γ · (4/8) · 2n / (cap · R_m)` for `n = 2` only; Python
`multi_alpha_resonance_width_mev`. -/
noncomputable def multiAlphaResonanceWidthMev (m : ℕ) (nAlpha : ℕ) (clusterTotal : ℝ) : ℝ :=
  if nAlpha ≠ 2 ∨ clusterTotal ≤ 0 then 0
  else
    clusterTotal * gamma_HQIV * strongChannelFraction * (2 * nAlpha : ℝ) /
      (constructiveValleyCap * resonanceWidthShellRadius m)

/-- Trimer resonance width (³He / ³H): saddle broadening on three-body valley closure.

Same lattice spine as `multiAlphaResonanceWidthMev` with constructive valley contacts
`bbnValleyCount A` in place of `2n` (`A = 3` only). Python `trimer_resonance_width_mev`. -/
noncomputable def trimerResonanceWidthMev (m : ℕ) (A : ℕ) (clusterTotal : ℝ) : ℝ :=
  if A ≠ 3 ∨ clusterTotal ≤ 0 then 0
  else
    clusterTotal * gamma_HQIV * strongChannelFraction * (bbnValleyCount A : ℝ) /
      (constructiveValleyCap * resonanceWidthShellRadius m)

theorem multiAlphaResonanceWidthMev_zero_of_not_two (m : ℕ) (nAlpha : ℕ) (clusterTotal : ℝ)
    (h : nAlpha ≠ 2) :
    multiAlphaResonanceWidthMev m nAlpha clusterTotal = 0 := by
  unfold multiAlphaResonanceWidthMev
  simp [h]

theorem trimerResonanceWidthMev_zero_of_not_three (m : ℕ) (A : ℕ) (clusterTotal : ℝ)
    (h : A ≠ 3) :
    trimerResonanceWidthMev m A clusterTotal = 0 := by
  unfold trimerResonanceWidthMev
  simp [h]

/-- Inter-α barbell / deuteron horizon coupling between closed α clusters. -/
noncomputable def interAlphaCoupling (m n : ℕ) (geff trace : ℝ) : ℝ :=
  if n < 2 ∨ n = 2 then 0
  else if 4 ≤ n then
    let link := geff * strongChannelFraction * gamma_HQIV *
      (deuteronBindingScale m) *
      (1 + gamma_HQIV * ((n - 3 : ℝ) / constructiveValleyCap))
    (n - 1 : ℝ) * link
  else
    (n - 1 : ℝ) * geff * trace * barbellTorusScale m *
      strongChannelFraction * gamma_HQIV

/-- Far-neutron curvature binding (shielded from proton-excess destabilization). -/
noncomputable def postAlphaFarNeutronCurvatureBinding (m A Z : ℕ) (geff : ℝ) : ℝ :=
  if A ≤ 4 then 0
  else
    (farNeutronWeightedContactSum A Z : ℝ) * geff *
      deuteronBindingScale m * strongChannelFraction

/-- α-core destabilization when extras mismatch closed-α isospin. -/
noncomputable def postAlphaCoreDestabilization
    (m A Z : ℕ) (alphaOutsidePerNucleon : ℝ) : ℝ :=
  if A ≤ 4 then 0
  else
    gamma_HQIV * strongChannelFraction * alphaOutsidePerNucleon *
      (A - 4 : ℝ) * postAlphaAlphaAdditionIsospinTension A Z

/-- Incremental post-α binding (geometry × deepen + network − relax). -/
noncomputable def postAlphaCoreIncrementalBinding (m A Z : ℕ) (c : ℝ := 1) : ℝ :=
  if A ≤ 4 then 0
  else
    postAlphaIncrementalGeometricTouchEnergy m A Z * geometryToMeVCoupling m c *
        postAlphaCoreWellDeepening A Z +
      postAlphaNetworkBindingEnergy m A Z c -
      postAlphaWellRelaxationEnergy m A Z c

/-- Outside binding with spin–magnetic residual (few-percent closure). -/
noncomputable def nuclearOutsideNetworkWithResidualAtShell
    (m : ℕ) (A : ℕ) (Z : ℕ) (θ : ℝ) (c : ℝ := 1) : ℝ :=
  if A ≤ 1 then 0
  else if 4 < A then
    let he4Out := nuclearOutsideNetworkBindingAtShell m 4 θ c *
      (1 + nuclearSpinMagneticResidualParticipation m 4 Z)
    let inc := postAlphaCoreIncrementalBinding m A Z c -
      postAlphaCoreDestabilization m A Z (he4Out / 4)
    (he4Out + inc * nuclearOutsideContactCoupling θ) *
      (1 + nuclearSpinMagneticResidualParticipation m A Z)
  else
    -- Standalone constructive regime: the cluster's outer shell is free, so the spin-alignment
    -- boundary lift applies (an α bonded inside a post-α lattice has no free surface and uses the
    -- post-α branch above instead).
    nuclearOutsideNetworkBindingAtShell m A θ c *
      (1 + nuclearSpinMagneticResidualParticipation m A Z) *
      (1 + nuclearSpinAlignmentBoundaryParticipation A Z)

/-- Total cluster binding: inside + networked outside + spin–magnetic residual. -/
noncomputable def nuclearClusterBindingNetworkCurvature
    (m m_cluster : ℕ) (A : ℕ) (Z : ℕ) (θ : ℝ) (c : ℝ := 1) : ℝ :=
  nuclearInsideBindingAtShell m m_cluster A c +
    nuclearOutsideNetworkWithResidualAtShell m A Z θ c

theorem nuclearClusterBindingNetworkCurvature_add
    (m m_cluster : ℕ) (A : ℕ) (Z : ℕ) (θ : ℝ) (c : ℝ) :
    nuclearClusterBindingNetworkCurvature m m_cluster A Z θ c =
      nuclearInsideBindingAtShell m m_cluster A c +
        nuclearOutsideNetworkWithResidualAtShell m A Z θ c := rfl

end

end Hqiv.Physics

import Hqiv.Physics.BoundStates
import Hqiv.Physics.HQIVNuclei
import Hqiv.Physics.QuarkMetaResonance
import Hqiv.Physics.NuclearAndAtomicSpectra

/-!
# Post-α binding geometry program (`A > 4`)

See `AGENTS/POST_ALPHA_BINDING_PROGRAM.md`.

## Network + relaxation (user mechanism)

Extra nucleons beyond ⁴He **lower the energy** of the α-core sites they touch (well deepening).
Those deepened wells **interact** on the contact graph (network term, `γ`).

The **added** nucleons are often **lighter** (partial facet contacts, far-neutron 4/8 weight):
the collective well **relaxes** slightly and the compound **loses a little binding per nucleon**
(`BE/A` trends down vs a naive `A × trace` ladder).
-/

namespace Hqiv.Physics

open Hqiv

/-- Nucleons beyond closed ⁴He. -/
def postAlphaExtraNucleonCount (A : ℕ) : ℕ :=
  if A ≤ 4 then 0 else A - 4

/-- Incremental effective contacts above the constructive α cap (6). -/
noncomputable def postAlphaIncrementalContactCount (A Z : ℕ) : ℝ :=
  if A ≤ 4 then 0
  else postAlphaOutsideValleyCountEffective A Z - (constructiveValleyCap : ℝ)

/-- Core well deepening: each post-α touch deepens the α facet wells already in the compound. -/
noncomputable def postAlphaCoreWellDeepening (A Z : ℕ) : ℝ :=
  if A ≤ 4 then 1
  else
    1 + strongChannelFraction * postAlphaIncrementalContactCount A Z /
      (constructiveValleyCap : ℝ)

/-- Fraction of incremental contact weight on light channels (partial facets + far neutrons). -/
noncomputable def postAlphaLightContactFraction (A Z : ℕ) : ℝ :=
  if A ≤ 4 then 0
  else
    let touches := bbnProtonFacetTouches A Z
    let facet := protonFacetTouchContactSum touches
    let facetPartial := protonFacetPartialContactSum touches
    let far := farNeutronWeightedContactSum A Z
    let total := (facet : ℝ) + far
    if total = 0 then 0 else (facetPartial + far) / total

/-- Total geometric touch energy for `A > 4` (α cap + facet + far contacts × `R_m²`). -/
noncomputable def postAlphaGeometricTouchEnergy (m A Z : ℕ) : ℝ :=
  if A ≤ 4 then 0
  else
    (constructiveValleyCap : ℝ) * sphereTouchContactEnergyUnit m +
      spinStabilityParticipation A Z *
        (protonFacetTouchContactSum (bbnProtonFacetTouches A Z) : ℝ) *
          sphereTouchContactEnergyUnit m +
      farNeutronWeightedContactSum A Z * sphereTouchContactEnergyUnit m

/-- α-core slice of geometric energy (constructive cap only). -/
noncomputable def postAlphaAlphaCoreGeometricEnergy (m A Z : ℕ) : ℝ :=
  if A ≤ 4 then 0 else (constructiveValleyCap : ℝ) * sphereTouchContactEnergyUnit m

theorem postAlphaGeometricTouchEnergy_be7 (m : ℕ) :
    postAlphaGeometricTouchEnergy m 7 4 = (17 : ℝ) / 2 * sphereTouchContactEnergyUnit m := by
  simp [postAlphaGeometricTouchEnergy, bbnProtonFacetTouches_be7, protonFacetTouchContactSum,
    constructiveValleyCap_eq_six, spinStabilityParticipation_be7_li7,
    farNeutronWeightedContactSum_be7_eq_half]
  ring

theorem postAlphaGeometricTouchEnergy_li7 (m : ℕ) :
    postAlphaGeometricTouchEnergy m 7 3 = 8 * sphereTouchContactEnergyUnit m := by
  simp [postAlphaGeometricTouchEnergy, bbnProtonFacetTouches_li7, protonFacetTouchContactSum,
    constructiveValleyCap_eq_six, spinStabilityParticipation_be7_li7,
    farNeutronWeightedContactSum_li7]
  ring

theorem postAlphaGeometricTouchEnergy_be7_gt_li7 (m : ℕ) :
    postAlphaGeometricTouchEnergy m 7 3 < postAlphaGeometricTouchEnergy m 7 4 := by
  rw [postAlphaGeometricTouchEnergy_li7, postAlphaGeometricTouchEnergy_be7]
  have hpos := sphereTouchContactEnergyUnit_pos m
  nlinarith

/-- Maps one `R_m²` contact unit to MeV via the nucleon composite trace at shell `m`. -/
noncomputable def geometryToMeVCoupling (m : ℕ) (c : ℝ := 1) : ℝ :=
  E_bind_from_composite_trace m nucleonTraceDiagonal nucleonTraceState c /
    sphereTouchContactEnergyUnit m

/-- Direct geometry binding (no network/back-reaction yet). -/
noncomputable def postAlphaClusterBindingFromGeometry (m A Z : ℕ) (c : ℝ := 1) : ℝ :=
  postAlphaGeometricTouchEnergy m A Z * geometryToMeVCoupling m c

/-- Network binding: deepened α-core wells interact (`γ ×` deepening excess × core energy). -/
noncomputable def postAlphaNetworkBindingEnergy (m A Z : ℕ) (c : ℝ := 1) : ℝ :=
  if A ≤ 4 then 0
  else
    gamma_HQIV * (postAlphaCoreWellDeepening A Z - 1) *
      postAlphaAlphaCoreGeometricEnergy m A Z * geometryToMeVCoupling m c

/-- Well relaxation: lighter additions let the compound well relax — small `BE/A` loss. -/
noncomputable def postAlphaWellRelaxationEnergy (m A Z : ℕ) (c : ℝ := 1) : ℝ :=
  if A ≤ 4 then 0
  else
    (postAlphaExtraNucleonCount A : ℝ) * postAlphaLightContactFraction A Z *
      strongChannelFraction * gamma_HQIV *
      E_bind_from_composite_trace m nucleonTraceDiagonal nucleonTraceState c

/-- Total post-α binding: deepen touched core + network − relaxation (lighter extras). -/
noncomputable def postAlphaClusterBindingWithNetwork (m A Z : ℕ) (c : ℝ := 1) : ℝ :=
  if A ≤ 4 then 0
  else
    postAlphaClusterBindingFromGeometry m A Z c * postAlphaCoreWellDeepening A Z +
      postAlphaNetworkBindingEnergy m A Z c -
      postAlphaWellRelaxationEnergy m A Z c

/-- Binding per nucleon (witness for the slight `BE/A` erosion). -/
noncomputable def postAlphaBindingPerNucleon (m A Z : ℕ) (c : ℝ := 1) : ℝ :=
  postAlphaClusterBindingWithNetwork m A Z c / (A : ℝ)

/-- Naive geometry binding per nucleon (no deepening / network / relaxation). -/
noncomputable def postAlphaBindingPerNucleonNaive (m A Z : ℕ) (c : ℝ := 1) : ℝ :=
  postAlphaClusterBindingFromGeometry m A Z c / (A : ℝ)

/-- Binding per nucleon after deepening + network, before well relaxation. -/
noncomputable def postAlphaBindingPerNucleonPreRelax (m A Z : ℕ) (c : ℝ := 1) : ℝ :=
  if A ≤ 4 then 0
  else
    (postAlphaClusterBindingFromGeometry m A Z c * postAlphaCoreWellDeepening A Z +
        postAlphaNetworkBindingEnergy m A Z c) /
      (A : ℝ)

theorem postAlphaIncrementalContactCount_be7 :
    postAlphaIncrementalContactCount 7 4 = (5 : ℝ) / 2 := by
  simp [postAlphaIncrementalContactCount, postAlphaOutsideValleyCountEffective_be7,
    constructiveValleyCap_eq_six]
  norm_num

theorem postAlphaIncrementalContactCount_li7 :
    postAlphaIncrementalContactCount 7 3 = 2 := by
  simp [postAlphaIncrementalContactCount, postAlphaOutsideValleyCountEffective_li7,
    constructiveValleyCap_eq_six]
  norm_num

theorem postAlphaCoreWellDeepening_li7 :
    postAlphaCoreWellDeepening 7 3 = 1 + strongChannelFraction * (1 : ℝ) / 3 := by
  simp [postAlphaCoreWellDeepening, postAlphaIncrementalContactCount_li7,
    constructiveValleyCap_eq_six, strongChannelFraction_eq_four_eighths]
  norm_num

theorem postAlphaCoreWellDeepening_be7 :
    postAlphaCoreWellDeepening 7 4 = 1 + strongChannelFraction * (5 : ℝ) / 12 := by
  simp [postAlphaCoreWellDeepening, postAlphaIncrementalContactCount_be7,
    constructiveValleyCap_eq_six, strongChannelFraction_eq_four_eighths]
  norm_num

end Hqiv.Physics

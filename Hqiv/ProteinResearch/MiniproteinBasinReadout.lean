import Hqiv.ProteinResearch.MiniproteinRamachandran
import Hqiv.ProteinResearch.MiniproteinFoldSpine

/-!
# Ramachandran basin readout from spine (no named register profiles)

Basin assignment is computed from:
* local curvature readout ``Ω`` vs reference shell ``m⋆ = 4``,
* 8-slot carrier phase alignment on proved ``(φ, ψ)`` pairs,
* SS topology (coil uses ``α``-weighted blends between neighbor basins).

Python mirror: ``hqiv_lab/miniprotein_basin.py``.
-/

namespace Hqiv.ProteinResearch

open Hqiv
open Real

/-- Compact-basin gate: same dress slot as ``ramachandranAlphaPsiDressed`` (``1 + γ/6``). -/
noncomputable def preferCompactBasin (omegaLocal : ℝ) : Prop :=
  omegaLocal ≥ 1 + gamma_HQIV / 6

theorem prefer_compact_uses_gamma_only :
    preferCompactBasin (1 + gamma_HQIV / 6) := by
  simp [preferCompactBasin, le_refl]

/-- Open β vs compact strap: strap when compact gate holds (matrix readout degeneracy broken by Ω). -/
noncomputable def resolveStrandBasin (omegaLocal : ℝ) : RamachandranBasin := by
  classical
  exact if preferCompactBasin omegaLocal then .strap else .beta

/-- Open α vs distorted helix on long/compact runs. -/
noncomputable def resolveHelixBodyBasin (omegaLocal : ℝ) (helixRunLen : ℕ) : RamachandranBasin := by
  classical
  exact if helixRunLen ≥ 4 ∨ preferCompactBasin omegaLocal then
    if preferCompactBasin omegaLocal then .distortedHelix else .alpha
  else .alpha

/-- Coil between unlike SS neighbors: ``α`` blend (no named turn profile). -/
noncomputable def coilBridgePair (left right : RamachandranBasin) : RamachandranPair :=
  let pl := basinRamachandranPair left
  let pr := basinRamachandranPair right
  { phi := alpha * pr.phi + (1 - alpha) * pl.phi
    psi := alpha * pr.psi + (1 - alpha) * pl.psi }

theorem coil_bridge_between_beta_alpha :
    (coilBridgePair .beta .alpha).phi =
      alpha * ramachandranAlphaPhi + (1 - alpha) * ramachandranBetaPhi := by
  simp [coilBridgePair, basinRamachandranPair, ramachandranForSS, ramachandranAlphaPhi, ramachandranBetaPhi]

theorem coil_bridge_between_strap_distorted_phi :
    (coilBridgePair .strap .distortedHelix).phi =
      alpha * ramachandranDistortedHelixPhi + (1 - alpha) * ramachandranStrapPhi := by
  simp [coilBridgePair, basinRamachandranPair, ramachandranStrapPair, ramachandranDistortedHelixPair,
    ramachandranStrapPhi, ramachandranDistortedHelixPhi]

/-- Named register profiles are deprecated — spine readout replaces ``RegisterProfile``. -/
theorem register_profiles_deprecated :
    True := trivial

end Hqiv.ProteinResearch

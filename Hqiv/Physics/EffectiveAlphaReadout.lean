import Hqiv.Physics.ContinuousXiCoupling
import Hqiv.Physics.ContinuousXiPath
import Hqiv.Physics.DoublePreferredAxisAlpha
import Hqiv.Physics.ScaleWitness
import Hqiv.Physics.SM_GR_Unification

namespace Hqiv.Physics

/-!
# Effective electromagnetic coupling readouts (scale-witness discipline)

HQIV derives α from the O–Maxwell φ-ladder and the double-axis Gauss→EW brace — **not**
from CODATA in the default `proton_lockin` pipeline.

| Readout | Lean name | Typical `1/α` | Role |
|---------|-----------|---------------|------|
| Double-axis brace (discrete shells) | `one_over_alpha_EM_double_axis` | ≈ 129 | **Primary** TUFT / sector-determinant EM slot |
| Lock-in continuous chart | `one_over_alpha_EM_braced_at_xi` | ≈ 116 @ ξ=5 | Continuous-chart alternative at lock-in |
| CODATA low-energy | `one_over_alpha_EM_CODATA` | ≈ 137 | Comparison layer only |
| Paper M_Z witness | `one_over_alpha_EM_at_MZ` | ≈ 127.9 | Legacy EW-scale witness (`SM_GR_Unification`) |

**Scale honesty:** `one_over_alpha_EM_double_axis` is the **electroweak-braced** O–Maxwell
prediction (between EM Gauss shell `referenceM−1` and EW shell `referenceM+1`). CODATA
`137.036` is the **Thomson / low-energy** comparison; it is not the same scale as α(M_Z)≈128.
Under `proton_lockin`, matching CODATA is a **prediction test**, not a solve input.

Python mirror: `scripts/hqiv_alpha_readout.py`.
-/

open ContinuousXiPath

/-- Which α readout tier to export (comparison tiers are never physical inputs). -/
inductive AlphaReadoutTier
  | primaryBraceMz
  | lockinContinuous
  | codataComparison
  | paperMzWitness
  deriving DecidableEq, Repr, Inhabited

def alphaReadoutTierToString : AlphaReadoutTier → String
  | .primaryBraceMz => "primary_brace_mz"
  | .lockinContinuous => "lockin_continuous"
  | .codataComparison => "codata_comparison"
  | .paperMzWitness => "paper_mz_witness"

/-- **Primary derived α** for sector determinants, g−2 spurions, and TUFT `exp(n α/6)` slots. -/
noncomputable def alpha_EM_primary (c : ℝ := 1) : ℝ :=
  alpha_EM_double_axis c

/-- Inverse coupling for the primary brace readout. -/
noncomputable def one_over_alpha_EM_primary (c : ℝ := 1) : ℝ :=
  one_over_alpha_EM_double_axis c

theorem alpha_EM_primary_eq_double_axis (c : ℝ) :
    alpha_EM_primary c = alpha_EM_double_axis c := rfl

theorem one_over_alpha_EM_primary_eq_double_axis (c : ℝ) :
    one_over_alpha_EM_primary c = one_over_alpha_EM_double_axis c := rfl

/-- Continuous-chart braced inverse α at horizon coordinates `(ξG, ξEW)`. -/
noncomputable def one_over_alpha_EM_braced_at_xi (ξG ξEW c : ℝ) : ℝ :=
  oneOverAlpha_xi ξG c * sigmaRatio ξG ξEW

noncomputable def alpha_EM_braced_at_xi (ξG ξEW c : ℝ) : ℝ :=
  (one_over_alpha_EM_braced_at_xi ξG ξEW c)⁻¹

/-- Lock-in braced readout at `ξ = xiLockin` with EW reference `electroweakPhiShell` chart sample. -/
noncomputable def one_over_alpha_EM_lockin_braced (c : ℝ := 1) : ℝ :=
  one_over_alpha_EM_braced_at_xi xiLockin (referenceM + 1 : ℝ) c

noncomputable def alpha_EM_lockin_braced (c : ℝ := 1) : ℝ :=
  (one_over_alpha_EM_lockin_braced c)⁻¹

/-- Resolve α for an active scale witness (comparison tiers excluded from `proton_lockin`). -/
noncomputable def alpha_EM_for_witness (w : ScaleWitness) (c : ℝ := 1) : ℝ :=
  match w with
  | .proton_lockin => alpha_EM_primary c
  | .cmb_now => alpha_EM_lockin_braced c
  | .codata_alpha => (one_over_alpha_EM_CODATA)⁻¹

theorem alpha_EM_proton_lockin_eq_primary (c : ℝ) :
    alpha_EM_for_witness .proton_lockin c = alpha_EM_primary c := rfl

/-- Proton lock-in uses the primary brace readout (not the CODATA comparison slot). -/
theorem alpha_EM_proton_lockin_uses_primary :
    alpha_EM_for_witness .proton_lockin 1 = alpha_EM_primary 1 := rfl

/- Numeric separation from CODATA is checked in `scripts/hqiv_alpha_readout.py` (transcendental). -/

/-- Tier selector (mirrors Python `resolve_alpha_em`). -/
noncomputable def alpha_EM_at_tier (tier : AlphaReadoutTier) (c : ℝ := 1) : ℝ :=
  match tier with
  | .primaryBraceMz => alpha_EM_primary c
  | .lockinContinuous => alpha_EM_lockin_braced c
  | .codataComparison => (one_over_alpha_EM_CODATA)⁻¹
  | .paperMzWitness => alpha_EM_at_MZ

/-- Default Fano coefficient for the primary readout (holonomy solve pins `c₀ ≈ 1` under proton_lockin). -/
def defaultFanoAlphaCoeff : ℝ := 1

/-- Alias used by TUFT sector-determinant exports. -/
noncomputable def tuftFineStructureAlphaDerived (c : ℝ := defaultFanoAlphaCoeff) : ℝ :=
  alpha_EM_primary c

/-- Primary EM coupling in TUFT readouts (proton_lockin default). -/
noncomputable def tuftFineStructureAlpha : ℝ := tuftFineStructureAlphaDerived defaultFanoAlphaCoeff

theorem tuftFineStructureAlpha_eq_primary_default :
    tuftFineStructureAlpha = alpha_EM_primary defaultFanoAlphaCoeff := rfl

end Hqiv.Physics

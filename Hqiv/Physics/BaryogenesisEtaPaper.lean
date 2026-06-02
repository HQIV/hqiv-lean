import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Hqiv

/-!
# Paper η anchor (quarantined)

**This module is the only place** the PDG / literature baryon-asymmetry value `6.10×10⁻¹⁰` appears
as a named constant. Core baryogenesis geometry (`m_QCD`, `m_lockin`, `T_*`, Ω_k integrals) lives
in `Hqiv.Physics.BaryogenesisCore`; the η *calibration* theorems that multiply curvature ratios
by this anchor live in `Hqiv.Physics.BaryogenesisWitness`.

`norm_num` handles equalities to rational divisions for this literal; tactic-only positivity on
the raw `e`-notation is brittle, so `eta_paper_pos` rewrites to `(610/10^12)` first.

Import this module directly **only** when you intentionally wire observational calibration;
otherwise prefer `BaryogenesisCore` (and optionally `BaryogenesisWitness` for packaged η theorems
without re-exporting the raw anchor through unrelated proofs).
-/

/-- **Observed baryon asymmetry parameter** (paper value). η ≈ 6.10×10⁻¹⁰. -/
def eta_paper : ℝ := 6.10e-10

/-- **η equals the paper constant.** -/
theorem eta_paper_eq : eta_paper = 6.10e-10 := rfl

/-- Same value as a division of natural casts (convenient for `norm_num` / `field_simp` steps). -/
theorem eta_paper_eq_div : eta_paper = (610 : ℝ) / 10^12 := by
  simp [eta_paper]
  norm_num

/-- **η is positive.** -/
theorem eta_paper_pos : 0 < eta_paper := by
  rw [eta_paper_eq_div]
  apply div_pos <;> norm_num

end Hqiv

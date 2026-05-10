/-
ARCHIVE / ABANDONED: legacy **“sterile neutrino”** naming for the same outer-horizon factor.
Not included in default `lake` targets; kept so old searches / prose still match Lean names.

Active API: `Hqiv.Physics.outerHorizonNeutrinoSuppression` and
`Hqiv.Physics.neutrino_masses_from_outer_horizon`.
-/

import Hqiv.Physics.DerivedGaugeAndLeptonSector

namespace Archive.Abandoned

open Hqiv Hqiv.Physics

/-- Deprecated alias (historical). Defeq to `outerHorizonNeutrinoSuppression`. -/
noncomputable abbrev sterileNeutrinoSuppression : ℝ := outerHorizonNeutrinoSuppression

theorem neutrino_masses_from_sterile_overlap :
    m_nu_tree = 0 ∧
    m_nu_e_derived = sterileNeutrinoSuppression * M_Z_derived ∧
    m_nu_mu_derived = sterileNeutrinoSuppression * m_nu_e_derived ∧
    m_nu_tau_derived = sterileNeutrinoSuppression * m_nu_mu_derived := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end Archive.Abandoned

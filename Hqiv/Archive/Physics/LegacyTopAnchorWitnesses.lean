import Mathlib.Data.Real.Basic
import Mathlib.Tactic

import Hqiv.Physics.ConservedContentMassBridge

/-!
**Archived:** legacy top-anchor witness chain for the old `ν < τ < top` comparison.

These lemmas remain mathematically valid, but they are no longer part of the
active visible-state story after the public color-resonance API was de-anchored
from `m_top_GeV` / `m_bottom_GeV`. The active hierarchy now runs through
`visible_state_hierarchy_ν_e_tau_colorHeavy` instead.
-/

namespace Hqiv.Physics

/-- **Archived:** τ resonance anchor is strictly below the legacy top GeV anchor. -/
theorem m_tau_from_resonance_lt_m_top_GeV : m_tau_from_resonance < m_top_GeV := by
  unfold m_tau_from_resonance m_top_GeV
  norm_num

/-- **Archived:** transitive hierarchy `ν_e derived < τ < top` from the old witness chain. -/
theorem observed_mass_hierarchy_ν_e_tau_top :
    m_nu_e_derived < m_tau_from_resonance ∧ m_tau_from_resonance < m_top_GeV :=
  ⟨m_nu_e_derived_lt_m_tau_from_resonance, m_tau_from_resonance_lt_m_top_GeV⟩

end Hqiv.Physics

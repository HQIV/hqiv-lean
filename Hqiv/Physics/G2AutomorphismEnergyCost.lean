import Hqiv.Algebra.PhaseLiftDelta

namespace Hqiv.Physics

/-!
# Phase-lift / “automorphism cost” scalar slot (shell `m`)

`Hqiv.Algebra.phaseLiftCoeff` is the proved HQIV scalar **φ(m)/6** used wherever the matrix
`phaseLiftDelta` is scaled to a shell (`PhaseLiftDelta` module doc).

External brane–bulk narratives sometimes describe a **G₂ automorphism energy cost**. This file
does **not** identify that story with Planck units, continuum Yang–Mills, or Clay `Δ`. It only
exposes the **existing** positive shell readout under a physics-facing name so later bridges can
cite one stable definition.
-/

open Hqiv.Algebra

/-- Positive scalar tied to phase-lift strength at shell `m` (definitionally `φ(m)/6`). -/
noncomputable abbrev automorphismEnergyCostAtShell (m : ℕ) : ℝ :=
  phaseLiftCoeff m

theorem automorphismEnergyCostAtShell_pos (m : ℕ) : 0 < automorphismEnergyCostAtShell m :=
  phaseLiftCoeff_pos m

theorem automorphismEnergyCostAtShell_eq_phi_div_six (m : ℕ) :
    automorphismEnergyCostAtShell m = Hqiv.phi_of_shell m / 6 :=
  rfl

end Hqiv.Physics

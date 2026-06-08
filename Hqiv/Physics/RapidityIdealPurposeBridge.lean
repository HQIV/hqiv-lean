import Hqiv.Algebra.PhaseLiftDelta
import Hqiv.Algebra.SMEmbedding
import Hqiv.Physics.RapidityZetaPhaseBridge

/-!
# Rapidity / zeta phase vs Furey minimal-left-ideal *purpose* (proved wiring)

Furey’s **minimal left ideals** in a Clifford picture are often used to **pick a
one-dimensional charge line** inside a larger spinor carrier: a canonical
submodule stable under the relevant left action, used to anchor hypercharge /
phase bookkeeping on a single generation.

HQIV does **not** formalize `Cl(6)` or minimal ideals here. What *can* be proved
today is that the **same mathematical slots** used in the SM embedding are wired
to the **rapidity / polar-angle / lattice-zeta** channel:

* the SM bookkeeping **hypercharge generator** is **definitionally** the unit
  **phase-lift Δ** matrix (`Hqiv.phaseLiftDelta`), i.e. the `(e₁,e₇)` rotation
  generator used throughout the phase-lift story;
* the **exponent** of `zetaHQIVTerm` is **exactly** `I *` the **rapidity polar
  angle** `polarAngleFromRapidity` (already in `RapidityZetaPhaseBridge`).

So the “carrier” that threads phase through shell rapidity is not an unrelated
scalar: it is the **same phase object** the zeta scaffold exponentiates, while
the **Lie-algebra hypercharge slot** is the **same Δ matrix** named explicitly
in algebra.  The Clifford + minimal-ideal refinement packaging is in
`Hqiv.Algebra.CliffordHQIVSlotRefinement` (together with `Hqiv.Algebra.CliffordMinimalIdeal`);
this module is the HQIV-side certificate that the **matrix and phase** slots are aligned
internally.
-/

namespace Hqiv.Physics

/-- SM hypercharge generator from `SMEmbedding` is definitionally the HQIV
phase-lift Δ (`GeneratorsFromAxioms.phaseLiftDelta`). -/
theorem sm_hyperchargeGenerator_eq_phaseLiftDelta :
    Hqiv.Algebra.hyperchargeGenerator = Hqiv.phaseLiftDelta :=
  rfl

/-- Same generator under the `PhaseLiftDelta` re-export name. -/
theorem sm_hyperchargeGenerator_eq_phaseLiftDeltaMatrix :
    Hqiv.Algebra.hyperchargeGenerator = Hqiv.Algebra.phaseLiftDeltaMatrix :=
  rfl

/-- The lattice-zeta phase uses exactly the rapidity polar-angle scaffold (same
statement as `zetaHQIVTerm_phase_arg_eq_polarAngleFromRapidity`, kept here as the
“ideal-purpose” packaging). -/
theorem rapidity_carrier_zeta_phase_arg_eq_polarAngle (φ t : ℝ) (m : ℕ) :
    Complex.I * φ * t * Hqiv.delta_theta_prime (m : ℝ) =
      Complex.I * (Hqiv.Geometry.polarAngleFromRapidity φ t m : ℂ) :=
  zetaHQIVTerm_phase_arg_eq_polarAngleFromRapidity φ t m

end Hqiv.Physics

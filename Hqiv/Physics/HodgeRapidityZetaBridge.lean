import Hqiv.Geometry.SpatialSliceRapidityScaffold
import Hqiv.Physics.RapidityZetaPhaseBridge

/-!
# Hodge **probe** ↔ rapidity ↔ lattice zeta (proved wiring, not the Hodge conjecture)

This file is the **same “distilled through Lean” step** as `RapidityZetaPhaseBridge`: it connects

* the **period / Hodge-class probe** scaffold (`FanoPeriodRapidityCoincidence`, `HodgeClassProbe`),
* the **polar-angle / zeta phase** identity (`zetaHQIVTerm_eq_effCorrected_mul_cexp_polarAngleFromRapidity`),

under explicit **parameter agreement** `φ = c.φ`, `t = c.t`.

**Still not claimed:** the classical **Hodge conjecture**, Chow groups, or that `HodgeClassProbe` is a Hodge
class on any complex projective variety. The reinforcement story is **internal to HQIV definitions**: once you
assume the Fano period coincidence, the **same** `(φ, t)` drive both the probe value and every shell’s
`zetaHQIVTerm` phase (via `polarAngleFromRapidity`).

**Algebra ↔ partition:** `Hqiv.Algebra.shellResidueFano_of_f_val_add_seven_mul` and
`fano_vertex_of_shell_f_val_add_seven_mul` align Fano-indexed zeta strands with the seven cycle tokens.

See `AGENTS/HODGE_HQIV_NARRATIVE.md` §5 for the human-readable stack.
-/

namespace Hqiv.Physics

open Complex
open Hqiv.Geometry

variable {M : Type u} [TopologicalSpace M]

/-- `HodgeClassProbe` is exactly lattice rapidity `φ·t` under the Fano period hypothesis. -/
theorem HodgeClassProbe_eq_mul_of_FanoPeriodRapidityCoincidence
    (c : FanoPeriodRapidityCoincidence M) :
    HodgeClassProbe c = c.φ * c.t :=
  (FanoPeriodRapidityCoincidence.phi_t_eq_hodgeClassProbe c).symm

/-- Same as `zetaHQIVTerm_eq_effCorrected_mul_cexp_polarAngleFromRapidity`, but forces `φ`,`t` to match a
    `FanoPeriodRapidityCoincidence` bundle (period = Hodge probe = rapidity parameters). -/
theorem zetaHQIVTerm_eq_eff_mul_cexp_polarAngle_of_coincident_rapidity
    (c : FanoPeriodRapidityCoincidence M) (δ : ℝ) (φ t : ℝ) (s : ℂ) (m : ℕ)
    (hφ : φ = c.φ) (ht : t = c.t) :
    zetaHQIVTerm δ φ t s m =
      (effCorrected δ m : ℂ) ^ (-s) * cexp (I * (polarAngleFromRapidity c.φ c.t m : ℂ)) := by
  subst hφ; subst ht
  exact zetaHQIVTerm_eq_effCorrected_mul_cexp_polarAngleFromRapidity δ c.φ c.t s m

end Hqiv.Physics

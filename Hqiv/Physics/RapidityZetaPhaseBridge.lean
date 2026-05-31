import Hqiv.Geometry.SpatialSliceRapidityScaffold
import Hqiv.Physics.OctonionicZeta

/-!
# Rapidity phase (`zetaHQIVTerm`) ↔ polar-angle scaffold (proved wiring)

Human narratives mix **π/2**, **2π**, and occasionally mistype **2/π**. Lean fixes the chain:

* **Horizon quarter scale:** `Hqiv.horizonQuarterPeriod = twoPi / 4 = π/2`
  (`ModifiedMaxwell.horizonQuarterPeriod_eq_pi_div_two`);
* **Tipping:** `delta_theta_prime E' = arctan(E') * (π/2)`
  (`ModifiedMaxwell.delta_theta_prime_eq_arctan_mul_pi_div_two`);
* **Lattice zeta phase:** `zetaHQIVTerm` uses `cexp (I * φ * t * delta_theta_prime (m : ℝ))`
  (`OctonionicZeta`);
* **Geometry polar angle:** `polarAngleFromRapidity φ t m = φ * t * delta_theta_prime (m : ℝ)`
  (`SpatialSliceRapidityScaffold`).

This module proves the **exponent** of `zetaHQIVTerm` is **exactly** `I *` the polar angle (as `ℂ`),
so the discrete `(r, θ)` spiral scaffold and the zeta phase channel are the **same** mathematical
object—not an analogy left implicit in comments.

**Still not claimed:** Peano/Hilbert-style space-filling, or that shell order induces a canonical
“next point” on a continuum curve without extra definitions.
-/

namespace Hqiv.Physics

open Complex

noncomputable section

open Hqiv.Geometry

/-- Exponent in `zetaHQIVTerm` agrees with `I * polarAngleFromRapidity` (coercions in `ℂ`). -/
theorem zetaHQIVTerm_phase_arg_eq_polarAngleFromRapidity (φ t : ℝ) (m : ℕ) :
    I * φ * t * delta_theta_prime (m : ℝ) = I * (polarAngleFromRapidity φ t m : ℂ) := by
  rw [polarAngleFromRapidity_eq]
  simp [mul_assoc]

theorem zetaHQIVTerm_cexp_eq_cexp_polarAngleFromRapidity (φ t : ℝ) (m : ℕ) :
    cexp (I * φ * t * delta_theta_prime (m : ℝ)) =
      cexp (I * (polarAngleFromRapidity φ t m : ℂ)) := by
  rw [zetaHQIVTerm_phase_arg_eq_polarAngleFromRapidity]

/-- Same shell term, with the phase written explicitly through `polarAngleFromRapidity`. -/
theorem zetaHQIVTerm_eq_effCorrected_mul_cexp_polarAngleFromRapidity (δ φ t : ℝ) (s : ℂ) (m : ℕ) :
    zetaHQIVTerm δ φ t s m =
      (effCorrected δ m : ℂ) ^ (-s) * cexp (I * (polarAngleFromRapidity φ t m : ℂ)) := by
  simp [zetaHQIVTerm, zetaHQIVTerm_cexp_eq_cexp_polarAngleFromRapidity]

end

end Hqiv.Physics

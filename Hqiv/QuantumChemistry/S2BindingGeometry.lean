import Hqiv.Geometry.SphericalHarmonicsBridge
import Hqiv.Physics.ComptonIRWindow
import Hqiv.Algebra.OctonionAxisAngles

/-!
# S² binding geometry (p-shell contacts)

Angular bookkeeping for covalent contacts on the curvature network:

* **S² degeneracy** — `2ℓ+1` modes per orbital ℓ (`SphericalHarmonicsBridge`).
* **Compton IR window** — contact phase `η = θ/θ₀` (`ComptonIRWindow.phaseParticipationEta`).
* **Dihedral budget** — attractive alignment favors `θ → 0` (`HQIVAtoms.allowed_binding_angles_minimize_budget`).
* **Axis ladder** — `π/(2k)` from shell rungs (`OctonionAxisAngles.axisAngle`).

Python witness: `scripts/hqiv_s2_binding_geometry.py`.
-/

namespace Hqiv.QuantumChemistry

open Hqiv
open Hqiv.Physics
open Hqiv.Algebra

/-- S² harmonic degeneracy `2ℓ+1`. -/
def s2Degeneracy (ℓ : ℕ) : ℕ := 2 * ℓ + 1

theorem s2Degeneracy_pShell : s2Degeneracy 1 = 3 := by
  native_decide

/-- Compton participation on a contact phase (normalized to `phaseTheta`). -/
noncomputable def contactEta (θ : ℝ) : ℝ := phaseParticipationEta θ

/-- Dihedral alignment weight: unity at θ = 0, zero at θ = π. -/
noncomputable def dihedralAlignmentWeight (θ : ℝ) : ℝ := (1 + Real.cos θ) / 2

theorem dihedralAlignmentWeight_zero : dihedralAlignmentWeight 0 = 1 := by
  simp [dihedralAlignmentWeight, Real.cos_zero]

/-- Valley alignment: deviation ``Δθ`` from native centre angle (minimum at ``Δθ = 0``). -/
noncomputable def valleyAlignmentWeight (bondAngle idealAngle : ℝ) : ℝ :=
  dihedralAlignmentWeight (bondAngle - idealAngle)

theorem valleyAlignmentWeight_at_ideal (θ : ℝ) :
    valleyAlignmentWeight θ θ = 1 := by
  simp [valleyAlignmentWeight, sub_self, dihedralAlignmentWeight_zero]

/-- p-shell active when a valence p index is present. -/
def pShellActive (mP : Option ℕ) : Bool := mP.isSome

end Hqiv.QuantumChemistry

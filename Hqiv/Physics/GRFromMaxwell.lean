import Hqiv.Physics.ModifiedMaxwell
import Hqiv.Geometry.HQVMetric
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Geometry.OctonionicLightCone

namespace Hqiv

/-!
# GR from Maxwell (Schuller-style): O-Maxwell / HQVM compatibility

**Schuller's derivation** (constructive gravity): Matter dynamics (e.g. Maxwell)
determine how spacetime can be foliated; requiring **causal consistency** between
matter and geometry yields the gravitational dynamics (Einstein–Hilbert action,
hence Einstein equations) as a compatibility condition rather than a separate
postulate.

**Our analogue:** We follow the same logic with **O-Maxwell** (emergent Maxwell
in the octonion algebra) and **HQVM-GR** (Horizon Quantized Vacuum Metric):

1. **O-Maxwell** is the matter/gauge dynamics (ModifiedMaxwell: emergent equation
   in O, reduction to classic Maxwell in H, 3D equations with one axis fixed).
2. **Compatible geometry** is the one that couples to the same horizon structure
   (φ, curvature) that appears in the O-Maxwell equation. In the current ladder the
   algebra-first Maxwell slot is primary, while `phi_of_T` is a later projection/readout.
   The informational-energy axiom fixes the lapse N = 1 + Φ + φ t (HQVMetric).
3. **HQVM-GR** (lapse, curvature from light-cone, G_eff, Friedmann) is the
   gravitational sector we compare against the same `φ`/`α` data used by
   O-Maxwell. In this file we prove only that compatibility packaging.

We formalise the **correspondence**: the same φ and α data that appear in the
O-Maxwell story, together with the later `phi_of_T` shell projection when chosen,
appear in the HQVM lapse, G_eff, and Friedmann equation. The full constructive
derivation (matter action → compatibility → gravitational action) is left as a
conceptual path only; here we prove the structural link and algebraic compatibility
statements.
-/

/-- **Same φ in O-Maxwell and HQVM.** The auxiliary field φ that feeds the optional
    shell projection on the O-Maxwell side is the same field that appears in the HQVM
    lapse as `timeAngle φ t` and in `G_eff(φ)`. The lattice defines φ
    (AuxiliaryField); both modules use it. -/
theorem same_phi_in_O_Maxwell_and_HQVM (φ t : ℝ) :
    timeAngle φ t = φ * t ∧ H_of_phi φ = φ := by
  unfold timeAngle H_of_phi
  exact ⟨rfl, rfl⟩

/-- **Same α in O-Maxwell and HQVM.** The lattice parameter α (OctonionicLightCone)
    that appears in the O-Maxwell φ-correction term also determines G_eff(φ) = φ^α
    and the Friedmann equation. So the gravitational coupling is fixed by the same
    structure that couples to the emergent O-Maxwell equation. -/
theorem same_alpha_in_O_Maxwell_and_HQVM :
    alpha = 3/5 :=
  alpha_eq_3_5

/-- **HQVM lapse is the compatible lapse.** The lapse N = 1 + Φ + φ t (informational-energy
    axiom) is the one that couples to the same φ that appears in the O-Maxwell equation.
    So the gravitational time evolution (lapse) is determined by the same horizon field. -/
theorem HQVM_lapse_uses_same_phi (Φ φ t : ℝ) :
    HQVM_lapse Φ φ t = 1 + Φ + timeAngle φ t :=
  HQVM_lapse_eq_timeAngle Φ φ t

/-- **O-Maxwell / HQVM compatibility (homogeneous limit).** In the homogeneous limit
    `(Φ = 0, H = φ)`, the HQVM Friedmann equation is equivalent to its explicit
    `(13/5)`-coefficient form. This is a compatibility theorem, not a derivation of
    gravitational dynamics from the Maxwell sector. -/
theorem O_Maxwell_compatible_with_HQVM_GR_homogeneous (φ rho_m rho_r : ℝ) (hφ : 0 ≤ φ) :
    HQVM_Friedmann_eq φ rho_m rho_r ↔
      (13/5 : ℝ) * φ ^ 2 = 8 * Real.pi * (φ ^ alpha) * (rho_m + rho_r) := by
  rw [HQVM_Friedmann_eq_power φ rho_m rho_r hφ]

/-- Legacy name kept for downstream imports; the theorem proves compatibility, not determination. -/
theorem O_Maxwell_determines_HQVM_GR_homogeneous (φ rho_m rho_r : ℝ) (hφ : 0 ≤ φ) :
    HQVM_Friedmann_eq φ rho_m rho_r ↔
      (13/5 : ℝ) * φ ^ 2 = 8 * Real.pi * (φ ^ alpha) * (rho_m + rho_r) :=
  O_Maxwell_compatible_with_HQVM_GR_homogeneous φ rho_m rho_r hφ

/-- **Minkowski limit.** When φ = 0 (no horizon coupling), the lapse is N = 1 and the
    O-Maxwell equation reduces to classic Maxwell (flat limit). So the "no gravity"
    limit of HQVM-GR coincides with the flat limit of O-Maxwell. -/
theorem Minkowski_limit_consistent (t : ℝ) :
    HQVM_lapse 0 0 t = 1 :=
  HQVM_lapse_Minkowski t

/-- **Summary: compatibility path.** The same `φ` and `α` data link the O-Maxwell side
    to the HQVM lapse / Friedmann side. This packages shared parameters and coefficients;
    it does not by itself produce a gravitational action from the Maxwell sector. -/
theorem compatibility_path_O_Maxwell_to_HQVM_GR (φ : ℝ) (hφ : 0 ≤ φ) :
    H_of_phi φ = φ ∧ G_eff φ = φ ^ alpha ∧ (3 : ℝ) - gamma_HQIV = 13/5 := by
  refine ⟨H_of_phi_eq φ, G_eff_eq φ hφ, three_minus_gamma_eq⟩

/-- Legacy summary name kept for downstream imports; the content is a compatibility package. -/
theorem derivation_path_O_Maxwell_to_HQVM_GR (φ : ℝ) (hφ : 0 ≤ φ) :
    H_of_phi φ = φ ∧ G_eff φ = φ ^ alpha ∧ (3 : ℝ) - gamma_HQIV = 13/5 :=
  compatibility_path_O_Maxwell_to_HQVM_GR φ hφ

end Hqiv

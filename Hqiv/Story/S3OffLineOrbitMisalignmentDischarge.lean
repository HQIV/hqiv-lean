import Hqiv.Story.S3HypercomplexResidualModel
import Hqiv.Story.S3DiscreteContinuumOffLineWeightBridge

/-!
# Off-line orbit misalignment discharge

This module formalizes the intended slogan:

> any nonzero displacement `δ = Re(s) - 1/2` breaks the fixed-locus orbit, so a
> zero cannot be absorbed off the critical line.

The unconditional geometric half is already proved: off `Re = 1/2`, the 45°
equator/free slot is nonzero, the SO(4) critical factor is nonzero, the tangent
is not unimodular, and the FE orbit does not collapse.

The remaining analytic principle is named here:
`OffLineOrbitMisalignmentForbidsInteriorCancellation`.  It says that this
misalignment prevents the interior channel `interiorStripH` from vanishing at a
nontrivial zero.  This is exactly the previously named interior nonvanishing
capstone, hence exactly RH.  The point of this file is to put the intuition in
the same formal slot as the hypercomplex continuation discharge.
-/

namespace Hqiv.Story

open Complex

noncomputable section

/-! ## Unconditional off-line misalignment -/

/-- Off-line points have a nonzero hypercomplex real displacement. -/
theorem off_line_hypercomplex_real_slot_ne_zero {s : ℂ}
    (hOff : s.re ≠ (1 / 2 : ℝ)) :
    hypercomplexResidualRealPart s ≠ 0 := by
  intro h0
  exact hOff ((hypercomplex_residual_real_part_vanishes_iff s).mp h0)

/-- Off-line points cannot lie on the SO(4) critical/equator fixed slot. -/
theorem off_line_so4_critical_factor_ne_zero {s : ℂ}
    (hOff : s.re ≠ (1 / 2 : ℝ)) :
    so4CriticalFactor s ≠ 0 :=
  so4CriticalFactor_ne_zero_off_line hOff

/-- Off-line open-strip points are not tangent-unimodular. -/
theorem off_line_tangent_misaligned {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hOff : s.re ≠ (1 / 2 : ℝ)) :
    Complex.normSq (projTangent s) ≠ 1 :=
  critical_strip_off_line_tangent_not_unimodular h0 h1 hOff

/-- Off-line open-strip points do not have FE orbit collapse in the tangent channel. -/
theorem off_line_tangent_orbit_not_collapsed {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hOff : s.re ≠ (1 / 2 : ℝ)) :
    (projTangent s)⁻¹ ≠ starRingEnd ℂ (projTangent s) :=
  critical_strip_off_line_quadruplet_does_not_collapse h0 h1 hOff

/--
Bundle of the four proved off-line misalignment certificates.  This is purely
geometric/orbit data and does not assume that `s` is a zero.
-/
structure OffLineOrbitMisalignmentAt (s : ℂ) : Prop where
  real_slot_ne_zero : hypercomplexResidualRealPart s ≠ 0
  critical_factor_ne_zero : so4CriticalFactor s ≠ 0
  tangent_not_unimodular :
    ∀ (_h0 : 0 < s.re) (_h1 : s.re < 1), Complex.normSq (projTangent s) ≠ 1
  tangent_orbit_not_collapsed :
    ∀ (_h0 : 0 < s.re) (_h1 : s.re < 1),
      (projTangent s)⁻¹ ≠ starRingEnd ℂ (projTangent s)

theorem off_line_orbit_misalignment_at {s : ℂ}
    (hOff : s.re ≠ (1 / 2 : ℝ)) :
    OffLineOrbitMisalignmentAt s where
  real_slot_ne_zero := off_line_hypercomplex_real_slot_ne_zero hOff
  critical_factor_ne_zero := off_line_so4_critical_factor_ne_zero hOff
  tangent_not_unimodular := fun h0 h1 => off_line_tangent_misaligned h0 h1 hOff
  tangent_orbit_not_collapsed := fun h0 h1 =>
    off_line_tangent_orbit_not_collapsed h0 h1 hOff

/-! ## Analytic discharge principle -/

/--
The analytic principle matching the user's intuition: when a nontrivial zero is
off the critical line, its off-line orbit misalignment forbids the interior
channel from absorbing the zero.

This is stated with the misalignment certificate as an explicit input, so the
result says exactly what the geometry must rule out.
-/
def OffLineOrbitMisalignmentForbidsInteriorCancellation : Prop :=
  ∀ ρ : ℂ, IsNontrivialZetaZero ρ → ρ.re ≠ (1 / 2 : ℝ) →
    OffLineOrbitMisalignmentAt ρ → interiorStripH ρ ≠ 0

/-- The misalignment principle is the interior nonvanishing capstone. -/
theorem off_line_orbit_misalignment_forbids_iff_interior_capstone :
    OffLineOrbitMisalignmentForbidsInteriorCancellation ↔
      InteriorStripHNonvanishingCapstone := by
  constructor
  · intro h ρ hζ hOff
    exact h ρ hζ hOff (off_line_orbit_misalignment_at hOff)
  · intro hCap ρ hζ hOff _hMis
    exact hCap ρ hζ hOff

/-- Therefore the misalignment principle is equivalent to RH. -/
theorem off_line_orbit_misalignment_forbids_iff_RH :
    OffLineOrbitMisalignmentForbidsInteriorCancellation ↔ RiemannHypothesis := by
  rw [off_line_orbit_misalignment_forbids_iff_interior_capstone,
    interior_capstone_iff_RiemannHypothesis]

/-- It is also equivalent to excluding off-line FE-partner cancellation. -/
theorem off_line_orbit_misalignment_forbids_iff_no_fe_partner_zero :
    OffLineOrbitMisalignmentForbidsInteriorCancellation ↔
      NoOfflineNontrivialFEPairedCancellation := by
  rw [off_line_orbit_misalignment_forbids_iff_interior_capstone,
    interior_capstone_iff_no_offline_fe_partner_zero]

/--
The desired theorem form: if the misalignment principle is supplied, then an
off-line nontrivial zero cannot occur because the off-line zero would force
`interiorStripH ρ = 0`, while misalignment forbids that.
-/
theorem off_line_orbit_misalignment_excludes_nontrivial_zero
    (hMis : OffLineOrbitMisalignmentForbidsInteriorCancellation)
    {ρ : ℂ} (hζ : IsNontrivialZetaZero ρ) (hOff : ρ.re ≠ (1 / 2 : ℝ)) :
    False := by
  have hDebt : interiorStripH ρ = 0 := offline_zero_forces_assembly_vanish hζ hOff
  have hNoDebt : interiorStripH ρ ≠ 0 :=
    hMis ρ hζ hOff (off_line_orbit_misalignment_at hOff)
  exact hNoDebt hDebt

/-- Misalignment-forbids-cancellation discharges RH. -/
theorem RiemannHypothesis_of_off_line_orbit_misalignment_forbids
    (hMis : OffLineOrbitMisalignmentForbidsInteriorCancellation) :
    RiemannHypothesis :=
  off_line_orbit_misalignment_forbids_iff_RH.mp hMis

/--
Misalignment-forbids-cancellation populates the hypercomplex continuation
discharge, hence all downstream SpecFrame and half-slope bridge hooks.
-/
noncomputable def hypercomplex_discharge_of_orbit_misalignment_forbids
    (hMis : OffLineOrbitMisalignmentForbidsInteriorCancellation) :
    HypercomplexZetaContinuationDischarge :=
  hypercomplex_discharge_of_interior_capstone
    (off_line_orbit_misalignment_forbids_iff_interior_capstone.mp hMis)

theorem off_line_orbit_misalignment_forbids_forces_specFrame_sieve_at_zeros
    (hMis : OffLineOrbitMisalignmentForbidsInteriorCancellation) :
    ∀ ρ : ℂ, IsNontrivialZetaZero ρ → ∀ N : ℕ, (hN : 2 ≤ N) →
      (specFrameSieveFunctor { N := N, hN := hN, s := ρ }).adjoint_fixed ∧
        (specFrameSieveFunctor { N := N, hN := hN, s := ρ }).radius =
          (specFrameSieveFunctor { N := N, hN := hN, s := ρ }).harmonic :=
  by
    intro ρ hζ N hN
    have hRH := RiemannHypothesis_of_off_line_orbit_misalignment_forbids hMis
    exact ⟨
      (specFrame_functor_adjoint_fixed_iff_line
        { N := N, hN := hN, s := ρ }).mpr (hRH ρ hζ.1 hζ.2.1 hζ.2.2),
      (specFrame_functor_harmonic_radius_iff_line
        { N := N, hN := hN, s := ρ }).mpr (hRH ρ hζ.1 hζ.2.1 hζ.2.2)⟩

/-!
## Status

* `OffLineOrbitMisalignmentAt s` is unconditional for `s.re ≠ 1/2`.
* `OffLineOrbitMisalignmentForbidsInteriorCancellation` is the analytic
  no-escape principle.
* That principle is equivalent to the existing interior capstone, to no off-line
  FE-partner cancellation, and to RH.
-/

end

end Hqiv.Story

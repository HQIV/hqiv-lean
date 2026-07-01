import Hqiv.Story.S3AnalyticStripLift
import Hqiv.Story.S3SO4ZetaProjectionClosedForm
import Hqiv.Story.S3SO4InteriorWitness
import Hqiv.Story.S3ComplexResidualModel
import Hqiv.Story.S3SpecFrameFunctorSieve
import Hqiv.Story.S3ExplicitFormulaDualitySlot
import Hqiv.Story.S3InteriorAssemblyNonvanishingAttack
import Hqiv.Story.S3HarmonicPrimeZetaPath
import Mathlib.Analysis.PSeriesComplex

/-!
# Hypercomplex residual centered on the critical line

This module defines a **hypercomplex residual chart** on the analytic strip cylinder
without presupposing any zero locations, proves **regional agreement with `ζ(s)`**
via the existing continuation closed forms, and extracts the **zero-lock** from
the proved off-line factorization through the real equator slot `σ − 1/2`.

## Geometric chart (unconditional)

* `HypercomplexResidualCoords` — `(σ, t)` cylinder coordinates;
* `hypercomplexResidualRealPart s = σ − 1/2` — vanishes iff `σ = 1/2`;
* `hypercomplexHopfAmplitude s` — `r(σ) · e^{it}` from `stripAnalyticLift`;
* `hypercomplexStripResidual s` — `(σ−1/2) + r(σ)e^{it}` as a complex carrier.

No zero set is assumed in these definitions.

## Regional continuation = `ζ` (proved, non-circular)

The continuation entries reuse the SO(4) regional closed forms already proved
against Mathlib:

| Region | Assembly | Agreement |
|--------|----------|-----------|
| `Re > 1` | `hypercomplexDirichletAssembly` | Dirichlet shell sum |
| open strip | `hypercomplexStripAssembly` | FE sin/cos–Γ–π (`oddStripChannel`) |
| even `2k ≥ 2` | `hypercomplexEvenPiAssembly` | Bernoulli/π sector |
| `−k` | `hypercomplexBernoulliAssembly` | Bernoulli slot |

These match `riemannZeta` on their regions by the existing regional theorems —
the discharge is **not** tautological because the assemblies are defined from
the hypercomplex/SO(4) spine first and identified with `ζ` afterward.

## Zero-lock (factorization route)

On the open strip off `Re = 1/2`, the proved identity

`ζ(s) = interiorStripH(s) · so4CriticalFactor(s)`

holds with `so4CriticalFactor(s) = 0 ↔ Re s = 1/2`.  The hypercomplex real slot
is exactly the critical-line deviation (up to the proved `√2` scaling).

Once `InteriorAssemblyNonzeroAtNontrivialZerosOffLine interiorStripH` is
supplied, RH follows — this is the single remaining analytic capstone, not hidden
inside the geometric definitions.

## Bridge wiring

A populated `HypercomplexZetaContinuationDischarge` yields
`S3ComplexResidualModel`, `HypercomplexResidualDischarge`, SpecFrame locators,
and (with twiddle coverage) the half-slope bridge.
-/

namespace Hqiv.Story

open Complex Real Filter Hqiv.Geometry

noncomputable section

/-! ## Geometric hypercomplex chart (no zero assumptions) -/

/--
Cylinder coordinates for the hypercomplex residual: real part `σ` and height `t`.
The fiber is the Hopf circle (`t` and `t + 2πn` identify the same S³ point).
-/
structure HypercomplexResidualCoords where
  sigma : ℝ
  height : ℝ

/-- Cylinder coordinates of a strip point `s = σ + it`. -/
def hypercomplexCoordsOfStrip (s : ℂ) : HypercomplexResidualCoords :=
  { sigma := s.re, height := s.im }

/--
**Real carrier:** critical-line deviation `σ − 1/2`.

Vanishes exactly on `Re s = 1/2`; this is the 45° equator factor in unscaled form.
-/
def hypercomplexResidualRealPart (s : ℂ) : ℝ :=
  criticalLineDeviation s

theorem hypercomplex_residual_real_part_eq_deviation (s : ℂ) :
    hypercomplexResidualRealPart s = s.re - (1 / 2 : ℝ) :=
  rfl

theorem hypercomplex_residual_real_part_vanishes_iff (s : ℂ) :
    hypercomplexResidualRealPart s = 0 ↔ s.re = (1 / 2 : ℝ) :=
  criticalLineDeviation_eq_zero_iff s

theorem hypercomplex_residual_real_part_eq_scaled_equator (s : ℂ) :
    (hypercomplexResidualRealPart s : ℂ) =
      (Real.sqrt 2 / 2 : ℂ) * so4CriticalFactor s := by
  have hR : criticalLineDeviation s =
      Real.sqrt 2 / 2 * exactTwiddleReadout s := by
    have h := so4CriticalFactor_eq_scaled_deviation s
    field_simp at h ⊢
    linarith
  rw [hypercomplexResidualRealPart, so4CriticalFactor, hR]
  push_cast
  ring

/-- Unit Hopf phase factor `e^{it}` from the strip height. -/
noncomputable def hypercomplexHopfPhaseFactor (s : ℂ) : ℂ :=
  Complex.exp (Complex.I * s.im)

theorem hypercomplex_hopf_phase_ne_zero (s : ℂ) :
    hypercomplexHopfPhaseFactor s ≠ 0 :=
  Complex.exp_ne_zero _

/--
**Imaginary carrier:** scaled Hopf amplitude `r(σ) · e^{it}` on the cylinder.

At `σ = 1/2` the radius is maximal (`r = 1`) and this is the rolling-map circle.
-/
noncomputable def hypercomplexHopfAmplitude (s : ℂ) : ℂ :=
  Complex.ofReal (stripHopfFiberRadius s.re) * hypercomplexHopfPhaseFactor s

/--
**Hypercomplex strip residual:** real slot `σ − 1/2`, imaginary slot the strip
height `t = Im s` (Hopf fiber coordinate on the cylinder).

The chart is **purely geometric** — it does not presuppose zero locations and is
not asserted to equal `ζ(s)` pointwise.
-/
noncomputable def hypercomplexStripResidual (s : ℂ) : ℂ :=
  Complex.mk (hypercomplexResidualRealPart s) s.im

theorem hypercomplex_strip_residual_real_part (s : ℂ) :
    (hypercomplexStripResidual s).re = hypercomplexResidualRealPart s := by
  simp [hypercomplexStripResidual, hypercomplexResidualRealPart]

theorem hypercomplex_strip_residual_imag_part (s : ℂ) :
    (hypercomplexStripResidual s).im = s.im := by
  simp [hypercomplexStripResidual]

theorem hypercomplex_strip_residual_vanishes_iff_line (s : ℂ) :
    hypercomplexStripResidual s = 0 ↔ s.re = (1 / 2 : ℝ) ∧ s.im = 0 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp [hypercomplexStripResidual, hypercomplexResidualRealPart] at hre him
    exact ⟨(criticalLineDeviation_eq_zero_iff s).mp hre, him⟩
  · intro ⟨hσ, ht⟩
    apply Complex.ext
    · simp [hypercomplexStripResidual, hypercomplexResidualRealPart,
        (criticalLineDeviation_eq_zero_iff s).mpr hσ]
    · simp [hypercomplexStripResidual, ht]

theorem hypercomplex_strip_residual_on_critical_line (s : ℂ)
    (hσ : s.re = (1 / 2 : ℝ)) :
    (hypercomplexStripResidual s).re = 0 := by
  rw [hypercomplex_strip_residual_real_part]
  exact (criticalLineDeviation_eq_zero_iff s).mpr hσ

theorem hypercomplex_hopf_amplitude_on_critical_line (s : ℂ)
    (hσ : s.re = (1 / 2 : ℝ)) :
    hypercomplexHopfAmplitude s =
      Complex.exp (Complex.I * s.im) := by
  have hr : stripHopfFiberRadius s.re = 1 := by rw [hσ]; exact strip_hopf_fiber_radius_at_half
  rw [hypercomplexHopfAmplitude, hr]
  simp [hypercomplexHopfPhaseFactor]

/-! ## Regional continuation assemblies (defined before identification) -/

/-- `Re > 1` entry: Dirichlet shell sum (even SO(4) channel). -/
noncomputable def hypercomplexDirichletAssembly (s : ℂ) : ℂ :=
  zetaEvenDirichletSO4 s

/-- Open-strip entry: FE sin/cos–Γ–π assembly (odd SO(4) channel). -/
noncomputable def hypercomplexStripAssembly (s : ℂ) : ℂ :=
  zetaFractionalSO4ClosedForm s

/-- Even π-sector entry at positive even integers `2k`, `k ≥ 1`. -/
noncomputable def hypercomplexEvenPiAssembly (k : ℕ) : ℂ :=
  zetaEvenSO4ClosedForm k

/-- Negative-integer Bernoulli entry at `−k`. -/
noncomputable def hypercomplexBernoulliAssembly (k : ℕ) : ℂ :=
  -bernoulli' (k + 1) / (k + 1)

/-! ## Regional agreement with `ζ` (non-circular discharge) -/

theorem hypercomplex_dirichlet_assembly_eq_zeta {s : ℂ} (hs : 1 < s.re) :
    hypercomplexDirichletAssembly s = riemannZeta s :=
  zeta_even_dirichlet_so4_eq_zeta hs

theorem hypercomplex_strip_assembly_eq_zeta {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    hypercomplexStripAssembly s = riemannZeta s :=
  zeta_fractional_so4_eq_zeta h0 h1

theorem hypercomplex_strip_assembly_eq_odd_channel (s : ℂ) :
    hypercomplexStripAssembly s = oddStripChannel s := rfl

theorem hypercomplex_strip_assembly_fe_closed_form {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    hypercomplexStripAssembly s =
      2 * (2 * (Real.pi : ℂ)) ^ (-(1 - s)) * Gamma (1 - s) * zetaSinCosFactor (1 - s) *
        riemannZeta (1 - s) := by
  rw [hypercomplex_strip_assembly_eq_zeta h0 h1]
  exact riemannZeta_open_strip_fe_closed_form s h0 h1

theorem hypercomplex_even_pi_assembly_eq_zeta {k : ℕ} (hk : k ≠ 0) :
    hypercomplexEvenPiAssembly k = riemannZeta (2 * k) := by
  unfold hypercomplexEvenPiAssembly
  exact (zeta_even_so4_closed_form hk).symm

theorem hypercomplex_bernoulli_assembly_eq_zeta (k : ℕ) :
    hypercomplexBernoulliAssembly k = riemannZeta (-k) := by
  unfold hypercomplexBernoulliAssembly
  exact (zeta_neg_so4_bernoulli k).symm

/-- Trace/ladder convergence: Dirichlet assemblies tend to `ζ` on `Re > 1`. -/
theorem hypercomplex_dirichlet_assembly_tendsto_zeta {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, 1 / (n + 1 : ℂ) ^ s) atTop
      (nhds (hypercomplexDirichletAssembly s)) := by
  rw [hypercomplex_dirichlet_assembly_eq_zeta hs]
  have hsum : Summable (fun n : ℕ => 1 / (n + 1 : ℂ) ^ s) := by
    have h0 : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
      Complex.summable_one_div_nat_cpow.mpr hs
    exact_mod_cast (summable_nat_add_iff 1).mpr h0
  have hHasSum : HasSum (fun n : ℕ => 1 / (n + 1 : ℂ) ^ s) (riemannZeta s) := by
    rw [shell_sum_eq_riemannZeta s hs]
    exact hsum.hasSum
  exact hHasSum.tendsto_sum_nat

/-! ## Continuation certificate -/

/--
Regional hypercomplex continuation certificate: records proved agreement with
`ζ` on the standard regions and the off-line factorization through the real
equator slot.  None of these fields presuppose zero locations.
-/
structure HypercomplexZetaContinuationCertificate where
  /-- Forces this bundle to live in `Type`, not `Prop`. -/
  tag : PUnit := .unit
  dirichlet_region :
    ∀ {s : ℂ}, 1 < s.re → hypercomplexDirichletAssembly s = riemannZeta s
  strip_region :
    ∀ {s : ℂ}, 0 < s.re → s.re < 1 → hypercomplexStripAssembly s = riemannZeta s
  strip_fe :
    ∀ {s : ℂ}, 0 < s.re → s.re < 1 →
      hypercomplexStripAssembly s =
        2 * (2 * (Real.pi : ℂ)) ^ (-(1 - s)) * Gamma (1 - s) * zetaSinCosFactor (1 - s) *
          riemannZeta (1 - s)
  even_pi_region :
    ∀ {k : ℕ}, k ≠ 0 → hypercomplexEvenPiAssembly k = riemannZeta (2 * k)
  bernoulli_region :
    ∀ k : ℕ, hypercomplexBernoulliAssembly k = riemannZeta (-k)
  off_line_factorization_exists :
    ∃ h : ℂ → ℂ,
      ∀ s, 0 < s.re → s.re < 1 → s.re ≠ (1 / 2 : ℝ) →
        riemannZeta s = h s * so4CriticalFactor s

/-- Unconditional regional certificate (factorization included). -/
noncomputable def hypercomplexZetaContinuationCertificate :
    HypercomplexZetaContinuationCertificate where
  tag := .unit
  dirichlet_region := fun hs => hypercomplex_dirichlet_assembly_eq_zeta hs
  strip_region := fun h0 h1 => hypercomplex_strip_assembly_eq_zeta h0 h1
  strip_fe := fun h0 h1 => hypercomplex_strip_assembly_fe_closed_form h0 h1
  even_pi_region := fun hk => hypercomplex_even_pi_assembly_eq_zeta hk
  bernoulli_region := hypercomplex_bernoulli_assembly_eq_zeta
  off_line_factorization_exists :=
    interiorStrip_off_line_factorization evenOddSO4Assembly_of_odd_channel

theorem hypercomplex_off_line_factorization_exists
    (_C : HypercomplexZetaContinuationCertificate) :
    ∃ h : ℂ → ℂ,
      ∀ s, 0 < s.re → s.re < 1 → s.re ≠ (1 / 2 : ℝ) →
        riemannZeta s = h s * so4CriticalFactor s :=
  _C.off_line_factorization_exists

theorem hypercomplex_off_line_factorization_interiorStripH :
    ∀ s, 0 < s.re → s.re < 1 → s.re ≠ (1 / 2 : ℝ) →
      riemannZeta s = interiorStripH s * so4CriticalFactor s := by
  intro s h0 h1 hσ
  have hcf : so4CriticalFactor s ≠ 0 := so4CriticalFactor_ne_zero_off_line hσ
  unfold interiorStripH
  rw [evenOddSO4Assembly_of_odd_channel s h0 h1 hσ, evenStripChannel,
    oddStripChannel_eq_zeta h0 h1]
  field_simp [hcf]

/-! ## Zero-lock from the real equator slot -/

/--
At any zero of `ζ` off the critical line, the hypercomplex real/equator slot
would have to vanish — contradicting `so4CriticalFactor ≠ 0` off the line.
This is the geometric zero-lock extracted from the factorization identity.
-/
theorem nontrivial_zero_forces_line_from_hypercomplex_factorization
    (_C : HypercomplexZetaContinuationCertificate)
    (hNz : InteriorAssemblyNonzeroAtNontrivialZerosOffLine interiorStripH) :
    RiemannHypothesis :=
  RiemannHypothesis_of_SO4_interior_witness hNz

theorem hypercomplex_equator_slot_vanishes_iff_line (s : ℂ) :
    so4CriticalFactor s = 0 ↔ s.re = (1 / 2 : ℝ) :=
  so4CriticalFactor_zero_iff s

theorem hypercomplex_real_slot_vanishes_iff_line (s : ℂ) :
    hypercomplexResidualRealPart s = 0 ↔ s.re = (1 / 2 : ℝ) :=
  hypercomplex_residual_real_part_vanishes_iff s

/--
If `ζ(ρ) = 0` with `ρ` off the line, the factorization
`ζ = interiorStripH · so4CriticalFactor` forces `so4CriticalFactor ρ = 0`.
Contradiction off the line — the real hypercomplex slot cannot vanish there.
-/
theorem off_line_zeta_zero_contradicts_hypercomplex_real_slot
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hσ : ρ.re ≠ (1 / 2 : ℝ))
    (hζ : riemannZeta ρ = 0) (hNz : interiorStripH ρ ≠ 0) : False := by
  have hfac := hypercomplex_off_line_factorization_interiorStripH ρ h0 h1 hσ
  have hcf : so4CriticalFactor ρ ≠ 0 := so4CriticalFactor_ne_zero_off_line hσ
  have hzero : interiorStripH ρ * so4CriticalFactor ρ = 0 := by rw [← hfac, hζ]
  have hcf0 : so4CriticalFactor ρ = 0 := by
    rcases mul_eq_zero.mp hzero with hh0 | hcf0
    · exact absurd hh0 hNz
    · exact hcf0
  exact hcf hcf0

/-! ## Full discharge and complex residual model -/

/--
Complete hypercomplex continuation discharge: regional certificate plus the
capstone nonvanishing of `interiorStripH` at off-line nontrivial zeros.
-/
structure HypercomplexZetaContinuationDischarge extends HypercomplexZetaContinuationCertificate where
  assembly_nonzero : InteriorAssemblyNonzeroAtNontrivialZerosOffLine interiorStripH

/--
Populate the hypercomplex continuation discharge from the existing interior
nonvanishing capstone.  This is the direct bridge from the older SO(4) interior
attack into the hypercomplex residual package.
-/
noncomputable def hypercomplex_discharge_of_interior_capstone
    (hCap : InteriorStripHNonvanishingCapstone) :
    HypercomplexZetaContinuationDischarge where
  toHypercomplexZetaContinuationCertificate := hypercomplexZetaContinuationCertificate
  assembly_nonzero := hCap

/--
The hypercomplex continuation discharge is exactly RH: the regional continuation
certificate is unconditional, and the only remaining field is the interior
nonvanishing capstone, already proved equivalent to RH elsewhere.
-/
theorem hypercomplex_continuation_discharge_iff_RH :
    Nonempty HypercomplexZetaContinuationDischarge ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨D⟩
    exact RiemannHypothesis_of_SO4_interior_witness D.assembly_nonzero
  · intro hRH
    exact ⟨hypercomplex_discharge_of_interior_capstone
      (interior_capstone_iff_RiemannHypothesis.mpr hRH)⟩

/--
Equivalent off-line FE-pair form of the hypercomplex discharge.  This imports the
zero-reduction audit: on the open strip off the line,
`interiorStripH ρ = 0 ↔ ζ(1-ρ)=0`.
-/
theorem hypercomplex_continuation_discharge_iff_no_offline_fe_partner_zero :
    Nonempty HypercomplexZetaContinuationDischarge ↔
      NoOfflineNontrivialFEPairedCancellation := by
  rw [hypercomplex_continuation_discharge_iff_RH,
    ← interior_capstone_iff_RiemannHypothesis,
    interior_capstone_iff_no_offline_fe_partner_zero]

theorem RiemannHypothesis_of_hypercomplex_continuation_discharge
    (D : HypercomplexZetaContinuationDischarge) :
    RiemannHypothesis :=
  RiemannHypothesis_of_SO4_interior_witness D.assembly_nonzero

/--
Build the sound complex residual model once continuation discharge is available.
The residual is `ζ` itself; zero-lock is inherited from RH.
-/
def s3ComplexResidualModel_of_hypercomplex_discharge
    (D : HypercomplexZetaContinuationDischarge) :
    S3ComplexResidualModel :=
  complexResidualModel_of_RiemannHypothesis
    (RiemannHypothesis_of_hypercomplex_continuation_discharge D)

theorem hypercomplex_continuation_discharge_implies_residual_discharge
    (D : HypercomplexZetaContinuationDischarge) :
    Nonempty S3ComplexResidualModel :=
  ⟨s3ComplexResidualModel_of_hypercomplex_discharge D⟩

def HypercomplexZetaContinuationDischarge.toResidualDischarge
    (D : HypercomplexZetaContinuationDischarge) :
    Nonempty S3ComplexResidualModel :=
  hypercomplex_continuation_discharge_implies_residual_discharge D

/-! ## SpecFrame and half-slope bridge wiring -/

private theorem hypercomplex_discharge_yields_RH
    (D : HypercomplexZetaContinuationDischarge) :
    RiemannHypothesis :=
  RiemannHypothesis_of_hypercomplex_continuation_discharge D

theorem hypercomplex_discharge_forces_specFrame_adjoint_at_zeros
    (D : HypercomplexZetaContinuationDischarge) :
    ∀ ρ : ℂ, IsNontrivialZetaZero ρ → ∀ N : ℕ, (hN : 2 ≤ N) →
      (specFrameSieveFunctor { N := N, hN := hN, s := ρ }).adjoint_fixed := by
  intro ρ hz N hN
  exact (specFrame_functor_adjoint_fixed_iff_line
    { N := N, hN := hN, s := ρ }).mpr
    (hypercomplex_discharge_yields_RH D ρ hz.1 hz.2.1 hz.2.2)

theorem hypercomplex_discharge_half_slope_bridge
    (D : HypercomplexZetaContinuationDischarge)
    (_hCover : ComplexifiedTwiddleZeroCoverage)
    (hMid : Hqiv.Geometry.SO4ZetaHolonomyForcesMidpointPairs 2) :
    SO8ProjectedHalfSlopeBridge 2 := by
  have hWeil : WeilPositivityForcesCriticalLine :=
    allNontrivialZerosOnLine_iff_RiemannHypothesis.mpr (hypercomplex_discharge_yields_RH D)
  exact {
    critical_line := hWeil
    midpoint_pairs := hMid
  }

theorem hypercomplex_discharge_forces_specFrame_sieve_at_zeros
    (D : HypercomplexZetaContinuationDischarge) :
    ∀ ρ : ℂ, IsNontrivialZetaZero ρ → ∀ N : ℕ, (hN : 2 ≤ N) →
      (specFrameSieveFunctor { N := N, hN := hN, s := ρ }).adjoint_fixed ∧
        (specFrameSieveFunctor { N := N, hN := hN, s := ρ }).radius =
          (specFrameSieveFunctor { N := N, hN := hN, s := ρ }).harmonic := by
  intro ρ hz N hN
  have hRH := hypercomplex_discharge_yields_RH D
  exact ⟨
    (specFrame_functor_adjoint_fixed_iff_line
      { N := N, hN := hN, s := ρ }).mpr (hRH ρ hz.1 hz.2.1 hz.2.2),
    (specFrame_functor_harmonic_radius_iff_line
      { N := N, hN := hN, s := ρ }).mpr (hRH ρ hz.1 hz.2.1 hz.2.2)⟩

/-!
## Status

* **Unconditional:** geometric chart, regional assemblies, regional = `ζ` theorems,
  FE strip formula, off-line factorization, real-slot locator.
* **RH-capstone:** `InteriorAssemblyNonzeroAtNontrivialZerosOffLine interiorStripH`
  packaged in `HypercomplexZetaContinuationDischarge`.
* **Bridge:** discharge ⇒ SpecFrame locators and (with twiddle coverage) half-slope.
-/

theorem hypercomplex_continuation_discharge_implies_residual_model
    (D : HypercomplexZetaContinuationDischarge) :
    Nonempty S3ComplexResidualModel :=
  D.toResidualDischarge

end

end Hqiv.Story

import Hqiv.Story.S3LogPhaseGoldbachHalfSlopeComparison
import Hqiv.Story.S3ExplicitFormulaPrimePhaseCoincidence

/-!
# Log-edge σ–t coupling frontier (named, honest)

`S3LogPhaseEdge` proves polar decoupling: modulus readouts cannot import additive
phase curvature into a σ-constraint.  This module **names** the coupling frontier
and proves what is unconditional vs RH-equivalent.
-/

namespace Hqiv.Story

open Complex Real Hqiv.Geometry

noncomputable section

/-! ## Coupling witness at a point -/

/--
**Log–Goldbach coupling data** at `ρ`: a nontrivial zero together with a concrete
half-slope spectral–additive package (slope `1/2`, phase-speed cap, gap = pair).
-/
structure LogPhaseGoldbachCouplingWitness (ρ : ℂ) where
  zero : IsNontrivialZetaZero ρ
  N : ℕ
  p : ℕ
  q : ℕ
  pair : GoldbachMidpointPair N p q
  package : HalfSlopeLogPhaseSpectralPackage N p q

def LogPhaseGoldbachZetaCouplingAt (ρ : ℂ) : Prop :=
  Nonempty (LogPhaseGoldbachCouplingWitness ρ)

theorem log_phase_goldbach_coupling_at_of_nontrivial_zero
    {ρ : ℂ} (h : IsNontrivialZetaZero ρ) :
    LogPhaseGoldbachZetaCouplingAt ρ := by
  let N := 2
  let p := 2
  let q := 2
  have hN : 0 < N := by decide
  have hPrime2 : Nat.Prime 2 := by decide
  have hPair : GoldbachMidpointPair N p q :=
    ⟨hPrime2, hPrime2, le_rfl, le_rfl, by decide⟩
  let P := halfSlope_log_phase_spectral_package_of_midpoint_pair hN hPair
  exact ⟨⟨h, N, p, q, hPair, P⟩⟩

/-! ## σ–t coupling frontier -/

/--
**σ–t phase coupling at `ρ`:** log–Goldbach package + global two-prime height pinning.
-/
def SigmaTPhaseCouplingAt (ρ : ℂ) : Prop :=
  LogPhaseGoldbachZetaCouplingAt ρ ∧
    (∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
      ∀ t₁ t₂ : ℝ,
        linePhase p t₁ = linePhase p t₂ → linePhase q t₁ = linePhase q t₂ → t₁ = t₂)

/--
**Coupling forces the critical line** — discharge is RH-equivalent.
-/
def SigmaTPhaseCouplingForcesCriticalLine : Prop :=
  ∀ ρ : ℂ, SigmaTPhaseCouplingAt ρ → ρ.re = (1 / 2 : ℝ)

theorem log_phase_coupling_at_every_nontrivial_zero
    {ρ : ℂ} (h : IsNontrivialZetaZero ρ) :
    LogPhaseGoldbachZetaCouplingAt ρ :=
  log_phase_goldbach_coupling_at_of_nontrivial_zero h

theorem sigma_t_coupling_at_every_nontrivial_zero
    {ρ : ℂ} (h : IsNontrivialZetaZero ρ) :
    SigmaTPhaseCouplingAt ρ :=
  ⟨log_phase_coupling_at_every_nontrivial_zero h,
    fun p q hp hq hne t₁ t₂ hp' hq' =>
      two_prime_phases_pin_height hp hq hne hp' hq'⟩

theorem sigma_t_coupling_forces_critical_line_iff_RH :
    SigmaTPhaseCouplingForcesCriticalLine ↔ RiemannHypothesis := by
  constructor
  · intro hCoupling ρ hzz hnt h1
    exact hCoupling ρ (sigma_t_coupling_at_every_nontrivial_zero ⟨hzz, hnt, h1⟩)
  · intro hRH ρ hCoupling
    rcases hCoupling with ⟨⟨hzz, _, _, _, _, _⟩, _⟩
    exact hRH ρ hzz.1 hzz.2.1 hzz.2.2

theorem RH_zero_determined_by_coupling
    (hRH : RiemannHypothesis) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    {ρ₁ ρ₂ : ℂ} (h₁ : IsNontrivialZetaZero ρ₁) (h₂ : IsNontrivialZetaZero ρ₂)
    (hph_p : linePhase p ρ₁.im = linePhase p ρ₂.im)
    (hph_q : linePhase q ρ₁.im = linePhase q ρ₂.im) :
    ρ₁ = ρ₂ :=
  RH_zero_determined_by_two_prime_phases hRH hp hq hne h₁ h₂ hph_p hph_q

end

end Hqiv.Story

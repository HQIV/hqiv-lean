import Hqiv.Story.S3ZetaClosedForm
import Hqiv.Story.S3RHDischarge
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# SO(4) interior witness: even π-sector + odd sin/cos channel

See `S3ZetaClosedForm` for the off-line factorization predicate and RH discharge.

The **odd channel** is the proved FE sin/cos–Γ–π assembly.  The **even channel** is the
π-sector continuation slot from `S3HarmonicPrimeZetaPath`.  Together they define
`interiorStripH`, the factorization witness off `Re = 1/2`.
-/

namespace Hqiv.Story

noncomputable section

open Complex Real

/-! ## Channel definitions -/

/-- Odd strip channel (proved closed form on the open strip). -/
noncomputable def oddStripChannel (s : ℂ) : ℂ :=
  2 * (2 * (Real.pi : ℂ)) ^ (-(1 - s)) * Gamma (1 - s) * zetaSinCosFactor (1 - s) *
    riemannZeta (1 - s)

theorem oddStripChannel_eq_zeta
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    oddStripChannel s = riemannZeta s := by
  unfold oddStripChannel
  exact (riemannZeta_open_strip_fe_closed_form s h0 h1).symm

/-- Even π-sector channel (continuation slot; zero placeholder until even split is proved). -/
noncomputable def evenStripChannel (_s : ℂ) : ℂ :=
  0

/-- Even + odd reassembles to `ζ` off the critical line. -/
def EvenOddSO4ChannelAssembly : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 / 2 : ℝ) →
    riemannZeta s = evenStripChannel s + oddStripChannel s

theorem evenOddSO4Assembly_of_odd_channel :
    EvenOddSO4ChannelAssembly := by
  intro s h0 h1 _
  simp [evenStripChannel, oddStripChannel_eq_zeta h0 h1]

/-- SO(4) assembly normalized by the 45° critical factor. -/
noncomputable def interiorStripH (s : ℂ) : ℂ :=
  (evenStripChannel s + oddStripChannel s) / so4CriticalFactor s

theorem interiorStripH_eq_zeta_div_critical_off_line
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ))
    (hAsm : EvenOddSO4ChannelAssembly) :
    interiorStripH s = riemannZeta s / so4CriticalFactor s := by
  unfold interiorStripH
  rw [hAsm s h0 h1 hσ, evenStripChannel, oddStripChannel_eq_zeta h0 h1]

/-! ## Witness -/

theorem interiorStrip_off_line_factorization
    (hAsm : EvenOddSO4ChannelAssembly) :
    ∃ h : ℂ → ℂ,
      ∀ s, 0 < s.re → s.re < 1 → s.re ≠ (1 / 2 : ℝ) →
        riemannZeta s = h s * so4CriticalFactor s := by
  refine ⟨interiorStripH, ?_⟩
  intro s h0 h1 hσ
  have hcf : so4CriticalFactor s ≠ 0 := so4CriticalFactor_ne_zero_off_line hσ
  unfold interiorStripH
  rw [hAsm s h0 h1 hσ, evenStripChannel, oddStripChannel_eq_zeta h0 h1]
  field_simp [hcf]

/--
**RH capstone (conditional).** Once the assembly is proved nonzero at nontrivial
zeros off the line, `RiemannHypothesis_of_interior_factorization` closes the chain.
The quotient witness `interiorStripH = ζ / (2σ−1)/√2` proves only the factorization
identity, not this nonvanishing lemma.
-/
theorem RiemannHypothesis_of_SO4_interior_witness
    (hNz : InteriorAssemblyNonzeroAtNontrivialZerosOffLine interiorStripH) :
    RiemannHypothesis :=
  RiemannHypothesis_of_interior_factorization
    ⟨interiorStripH,
      fun s h0 h1 hσ => by
        have hcf := so4CriticalFactor_ne_zero_off_line hσ
        unfold interiorStripH
        rw [evenOddSO4Assembly_of_odd_channel s h0 h1 hσ, evenStripChannel,
          oddStripChannel_eq_zeta h0 h1]
        field_simp [hcf],
      hNz⟩

/-!
The even channel is still a placeholder (`0`).  Replacing it with the harmonic–Δ
π-sector continuation and proving `InteriorAssemblyNonzeroAtNontrivialZerosOffLine
interiorStripH` is the remaining analytic step (not supplied by the quotient form).
-/

end

end Hqiv.Story

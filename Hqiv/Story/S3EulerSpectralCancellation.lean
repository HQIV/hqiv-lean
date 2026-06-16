import Hqiv.Story.S3TangentOrbitCriticalLine
import Hqiv.Story.S3DeltaOrbitOffStrip
import Hqiv.Story.S3HarmonicPrimeZetaPath

/-!
# Zeros as spectral cancellations of the Euler prime product

The conjecture this module makes precise: *the zeros in this construction are
exactly the spectral cancellations that give the Euler prime product*.  Three
faces of that statement are provable today; the module proves all three.

## 1. In the product region the prime phases provably cannot cancel

For `Re s > 1` the prime-phase product is a genuine convergent product of
**nonvanishing** factors (`euler_factor_ne_zero`: each
`(1 − p^{−s})⁻¹ ≠ 0`, since `‖p^{−s}‖ = p^{−Re s} < 1`), it *is* `ζ(s)`
(`riemannZeta_eulerProduct_hasProd`, Mathlib), and the value is nonzero
(`euler_product_region_no_cancellation`).  Cancellation can never *complete*
where the spectral product converges: a zero would contradict the product.

## 2. Zeros happen exactly where the spectral product breaks

Contrapositive packaging: a zero forces `Re s < 1`
(`zero_forces_product_breakdown`, even on the closed boundary `Re s = 1` via
Mathlib's nonvanishing), and the repo's strip confinement puts every
nontrivial zero in the open strip `0 < Re s < 1`
(`nontrivial_zero_open_strip`) — precisely the region where the prime
spectral series no longer converges absolutely.  The zero set lives on the
*breakdown locus* of the Euler product, nowhere else.

## 3. Each zero is a resonance pole of the inverse spectral response

On the product region the prime spectrum is tame: the von Mangoldt series
converges and equals the log-derivative
(`spectral_series_tame`: `L Λ(s) = −ζ′(s)/ζ(s)`).  The *inverse* spectral
response `1/ζ` — the un-inverted prime-phase product `∏(1−p^{−s})` continued
to the strip — **blows up at every zero**:
`inverse_spectral_response_blows_up_at_zero` proves
`‖ζ(s)⁻¹‖ → ∞` as `s → ρ` along the nonvanishing locus, unconditionally for
any zero `ρ ≠ 1`.  (For the punctured-neighbourhood version one needs that
zeros are isolated — classical, by the identity theorem; it is taken as an
explicit hypothesis in `inverse_spectral_response_blows_up_punctured` rather
than smuggled in.)

## Capstone

`spectral_cancellation_profile` packages the full profile of a nontrivial
zero: open-strip confinement (product breakdown region), impossibility in the
product region, the resonance blow-up of `1/ζ`, and the quadruplet tangent
orbit `{T, T⁻¹, conj T, (conj T)⁻¹}` of `S3TangentOrbitCriticalLine` — the
zero *is* a completed spectral cancellation, and it carries the full orbit
data of the factorization angle.

**Honest scope.**  "The zeros are exactly the spectral cancellations" is
proved in the directions available without RH: no cancellation in the product
region, zeros confined to the breakdown locus, resonance at every zero.  The
remaining classical content — that every such cancellation sits at
`‖tan(πs/2)‖ = 1` — is RH, already named by the capstone equivalences of the
neighbouring modules.
-/

namespace Hqiv.Story

open Complex Filter

noncomputable section

/-! ## 1. No cancellation in the product region -/

/-- Every Euler factor is **nonvanishing** in the product region:
`‖p^{−s}‖ = p^{−Re s} < 1`, so `1 − p^{−s} ≠ 0` and its inverse is nonzero.
The prime phases individually never cancel. -/
theorem euler_factor_ne_zero {s : ℂ} (hs : 1 < s.re) (p : Nat.Primes) :
    (1 - (p : ℂ) ^ (-s))⁻¹ ≠ 0 := by
  have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.prop.two_le
  have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  have hnorm : ‖(p : ℂ) ^ (-s)‖ = ((p : ℕ) : ℝ) ^ (-s).re := by
    rw [show ((p : ℂ)) = ((((p : ℕ) : ℝ)) : ℂ) by push_cast; rfl]
    exact Complex.norm_cpow_eq_rpow_re_of_pos hppos (-s)
  have hlt : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [hnorm, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  have hbase : (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := by
    intro h
    have : (p : ℂ) ^ (-s) = 1 := by linear_combination -h
    rw [this] at hlt
    simp at hlt
  exact inv_ne_zero hbase

/-- **No spectral cancellation in the product region**: for `Re s > 1` the
prime-phase product converges to `ζ(s)` *and* the value is nonzero.  Where
the Euler product holds, cancellation provably never completes. -/
theorem euler_product_region_no_cancellation {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => (1 - (p : ℂ) ^ (-s))⁻¹) (riemannZeta s) ∧
      riemannZeta s ≠ 0 :=
  ⟨riemannZeta_eulerProduct_hasProd hs, riemannZeta_ne_zero_of_one_lt_re hs⟩

/-! ## 2. Zeros live exactly on the breakdown locus -/

/-- **A zero forces product breakdown**: `ζ(s) = 0` is impossible anywhere
the Euler product region extends, including the closed boundary `Re s = 1`. -/
theorem zero_forces_product_breakdown {s : ℂ} (hz : riemannZeta s = 0) :
    s.re < 1 := by
  by_contra h
  push_neg at h
  exact riemannZeta_ne_zero_of_one_le_re h hz

/-- Nontrivial zeros are confined to the open strip — the exact region where
the prime spectral series no longer converges absolutely (re-export of the
repo strip confinement, framed as breakdown-locus confinement). -/
theorem spectral_cancellation_in_breakdown_locus (s : ℂ)
    (h : IsNontrivialZetaZero s) : 0 < s.re ∧ s.re < 1 :=
  nontrivial_zero_open_strip s h

/-! ## 3. The spectrum is tame in the product region; zeros are resonances -/

open scoped LSeries.notation in
/-- **The prime spectrum is tame in the product region**: the von Mangoldt
spectral series converges and equals the log-derivative `−ζ′/ζ`. -/
theorem spectral_series_tame {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable ↗ArithmeticFunction.vonMangoldt s ∧
      LSeries ↗ArithmeticFunction.vonMangoldt s =
        -deriv riemannZeta s / riemannZeta s :=
  ⟨ArithmeticFunction.LSeriesSummable_vonMangoldt hs,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs⟩

/-- Core resonance lemma: along any filter converging to a zero `ρ ≠ 1` on
which `ζ` is nonvanishing, the inverse spectral response `‖ζ⁻¹‖` tends to
infinity. -/
theorem inverse_spectral_response_core {ρ : ℂ} (hρ : ρ ≠ 1)
    (hz : riemannZeta ρ = 0) {l : Filter ℂ} (hl : l ≤ nhds ρ)
    (hne : ∀ᶠ s in l, riemannZeta s ≠ 0) :
    Tendsto (fun s => ‖(riemannZeta s)⁻¹‖) l atTop := by
  have hcont : ContinuousAt riemannZeta ρ :=
    (differentiableAt_riemannZeta hρ).continuousAt
  have h0 : Tendsto (fun s => ‖riemannZeta s‖) l (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hnorm : Tendsto (fun s => ‖riemannZeta s‖) (nhds ρ) (nhds ‖riemannZeta ρ‖) :=
        (hcont.norm).tendsto
      rw [hz, norm_zero] at hnorm
      exact hnorm.mono_left hl
    · filter_upwards [hne] with s hs
      exact norm_pos_iff.mpr hs
  have hinv : Tendsto (fun s => ‖riemannZeta s‖⁻¹) l atTop :=
    tendsto_inv_nhdsGT_zero.comp h0
  simpa [norm_inv] using hinv

/-- **Every zero is a resonance pole of the inverse spectral response**:
`‖ζ(s)⁻¹‖ → ∞` as `s → ρ` along the nonvanishing locus, for any zero
`ρ ≠ 1`.  The un-inverted prime-phase product `∏(1−p^{−s})`, which equals
`1/ζ` on the product region, diverges at every completed cancellation. -/
theorem inverse_spectral_response_blows_up_at_zero {ρ : ℂ} (hρ : ρ ≠ 1)
    (hz : riemannZeta ρ = 0) :
    Tendsto (fun s => ‖(riemannZeta s)⁻¹‖)
      (nhdsWithin ρ {s : ℂ | riemannZeta s ≠ 0}) atTop := by
  refine inverse_spectral_response_core hρ hz nhdsWithin_le_nhds ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact hs

/-- Punctured-neighbourhood resonance, given that the zero is isolated (the
classical fact, by the identity theorem; carried as an explicit hypothesis
rather than smuggled in). -/
theorem inverse_spectral_response_blows_up_punctured {ρ : ℂ} (hρ : ρ ≠ 1)
    (hz : riemannZeta ρ = 0)
    (hiso : ∀ᶠ s in nhdsWithin ρ {ρ}ᶜ, riemannZeta s ≠ 0) :
    Tendsto (fun s => ‖(riemannZeta s)⁻¹‖) (nhdsWithin ρ {ρ}ᶜ) atTop :=
  inverse_spectral_response_core hρ hz nhdsWithin_le_nhds hiso

/-! ## Capstone: the spectral-cancellation profile of a nontrivial zero -/

/--
**Spectral-cancellation profile.**  A nontrivial zero `ρ` is a completed
spectral cancellation of the Euler prime product, with the full provable
profile attached:

1. it lies in the open strip — the breakdown locus of the product;
2. it is impossible in the product region (`¬ 1 ≤ Re ρ` framing via strip);
3. the inverse spectral response `‖1/ζ‖` blows up at `ρ` (resonance pole);
4. its FE + Schwarz quadruplet carries the tangent orbit
   `{T, T⁻¹, conj T, (conj T)⁻¹}` of the factorization angle `πρ/2`.

What RH adds — and only RH — is that every such cancellation sits on the
unimodular-tangent locus `‖T‖ = 1`.
-/
theorem spectral_cancellation_profile (ρ : ℂ) (h : IsNontrivialZetaZero ρ) :
    (0 < ρ.re ∧ ρ.re < 1) ∧
      ρ.re < 1 ∧
      Tendsto (fun s => ‖(riemannZeta s)⁻¹‖)
        (nhdsWithin ρ {s : ℂ | riemannZeta s ≠ 0}) atTop ∧
      (projTangent (1 - ρ) = (projTangent ρ)⁻¹ ∧
        projTangent (schwarzReflect ρ) = starRingEnd ℂ (projTangent ρ) ∧
        projTangent (1 - schwarzReflect ρ) =
          (starRingEnd ℂ (projTangent ρ))⁻¹) :=
  ⟨nontrivial_zero_open_strip ρ h,
    zero_forces_product_breakdown h.1,
    inverse_spectral_response_blows_up_at_zero h.2.2 h.1,
    projTangent_quadruplet ρ⟩

end

end Hqiv.Story

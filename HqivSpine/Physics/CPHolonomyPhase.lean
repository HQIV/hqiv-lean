import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.Trigonometric

/-!
# `HqivSpine.Physics.CPHolonomyPhase` — CP violation as a holonomy phase

`MixingAngles` and `CabibboInterference` derived the mixing **angles** from the masses, but they are
purely **real** rotations — no CP phase. The missing physics (the `CKM_PMNS_FANO_OVERLAP` checklist
item 4) is the **CP-odd phase from fibre holonomy**, which only exists once transport is
**complexified**. This is the U(1) complexification of `Physics.WilsonLoop`:

* **Complex link / U(1) transport.** `link θ = e^{iθ}` is a unit parallel transport; products add
  phases (`link_mul`), conjugation reverses them (`conj_link`).
* **Abelian Wilson loop carries a flux.** A plaquette's holonomy is `e^{iΦ}` with net flux
  `Φ = θ₁+θ₂−θ₃−θ₄` (`u1Holonomy_eq_link_flux`); it is trivial **iff** the flux is a multiple of
  `2π` (`u1Holonomy_eq_one_iff`) — the complex analogue of `WilsonLoop`'s flat-iff, now with a
  genuine phase (`u1Holonomy_nontrivial`: `Φ = π ↦ −1`).
* **The CP phase is physical (rephasing-invariant).** The **Jarlskog invariant**
  `J = Im(V_us V_cb V*_ub V*_cs)` is the imaginary part of a closed quartet loop in flavour space.
  It is **invariant under rephasing** of the quark fields (`jarlskog_rephasing`): the CP phase cannot
  be rotated away. A purely real CKM matrix has `J = 0` (`jarlskog_real`, CP conserved), while a
  single holonomy phase `δ` gives `J = (∏|V|)·sin δ` (`jarlskog_phase`) — nonzero **iff** `sin δ ≠ 0`
  (`jarlskog_phase_ne_zero`). CP violation **is** a non-trivial fibre holonomy.

**Honest scope.** This is the *CP-phase / holonomy-invariant* layer. It does **not** derive a full
`3×3` unitary CKM matrix from Fano overlaps (still open); it isolates the one structural fact those
real modules could not see — that a non-zero loop holonomy is what makes CP violation physical.

Mathlib-only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.CPHolonomyPhase

open Complex ComplexConjugate

/-! ## Complex U(1) link: a unit parallel transport -/

/-- **U(1) parallel transport** `link θ = e^{iθ}` — a unit complex number. -/
noncomputable def link (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

@[simp] theorem link_zero : link 0 = 1 := by simp [link]

theorem link_mul (a b : ℝ) : link a * link b = link (a + b) := by
  unfold link
  rw [← Complex.exp_add]
  congr 1
  push_cast; ring

@[simp] theorem conj_link (θ : ℝ) : conj (link θ) = link (-θ) := by
  unfold link
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

@[simp] theorem link_im (θ : ℝ) : (link θ).im = Real.sin θ :=
  Complex.exp_ofReal_mul_I_im θ

@[simp] theorem link_re (θ : ℝ) : (link θ).re = Real.cos θ :=
  Complex.exp_ofReal_mul_I_re θ

/-- Inverse phase cancels: `e^{iθ}·e^{−iθ} = 1`. -/
theorem link_mul_neg (θ : ℝ) : link θ * link (-θ) = 1 := by
  rw [link_mul, add_neg_cancel, link_zero]

/-- A half-turn flux gives `−1`: `e^{iπ} = −1`. -/
theorem link_pi : link Real.pi = -1 := by
  apply Complex.ext
  · rw [link_re, Real.cos_pi]; norm_num
  · rw [link_im, Real.sin_pi]; norm_num

/-- **The phase is trivial iff the flux is a multiple of `2π`.** -/
theorem link_eq_one_iff (θ : ℝ) : link θ = 1 ↔ ∃ n : ℤ, θ = 2 * Real.pi * n := by
  unfold link
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h2 : (θ : ℂ) = (n : ℂ) * (2 * (Real.pi : ℂ)) :=
      mul_right_cancel₀ Complex.I_ne_zero (by rw [hn]; ring)
    have : (θ : ℂ) = ((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) := by rw [h2]; push_cast; ring
    exact_mod_cast this
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [hn]; push_cast; ring⟩

/-! ## Abelian Wilson loop: holonomy carries a flux phase -/

/-- **Net flux** through a plaquette: `Φ = θ₁ + θ₂ − θ₃ − θ₄` (oriented edge phases). -/
def u1Flux (θ₁ θ₂ θ₃ θ₄ : ℝ) : ℝ := θ₁ + θ₂ - θ₃ - θ₄

/-- **U(1) plaquette holonomy:** the ordered product of (conjugated, for reversed edges) links. -/
noncomputable def u1Holonomy (θ₁ θ₂ θ₃ θ₄ : ℝ) : ℂ :=
  link θ₁ * link θ₂ * conj (link θ₃) * conj (link θ₄)

/-- **Holonomy = phase of the flux:** `e^{iΦ}` with `Φ` the net flux. -/
theorem u1Holonomy_eq_link_flux (θ₁ θ₂ θ₃ θ₄ : ℝ) :
    u1Holonomy θ₁ θ₂ θ₃ θ₄ = link (u1Flux θ₁ θ₂ θ₃ θ₄) := by
  unfold u1Holonomy u1Flux
  rw [conj_link, conj_link, link_mul, link_mul, link_mul]
  congr 1

/-- A **flux-free** plaquette is flat (trivial holonomy). -/
theorem u1Holonomy_trivial_of_flux_zero (θ₁ θ₂ θ₃ θ₄ : ℝ) (h : u1Flux θ₁ θ₂ θ₃ θ₄ = 0) :
    u1Holonomy θ₁ θ₂ θ₃ θ₄ = 1 := by rw [u1Holonomy_eq_link_flux, h, link_zero]

/-- A **half-flux** plaquette has non-trivial holonomy `−1`: curvature is a genuine phase. -/
theorem u1Holonomy_nontrivial (θ₁ θ₂ θ₃ θ₄ : ℝ) (h : u1Flux θ₁ θ₂ θ₃ θ₄ = Real.pi) :
    u1Holonomy θ₁ θ₂ θ₃ θ₄ = -1 := by rw [u1Holonomy_eq_link_flux, h, link_pi]

/-- **Flat iff quantized flux:** the abelian Wilson loop is trivial exactly when the flux is `2πℤ`. -/
theorem u1Holonomy_eq_one_iff (θ₁ θ₂ θ₃ θ₄ : ℝ) :
    u1Holonomy θ₁ θ₂ θ₃ θ₄ = 1 ↔ ∃ n : ℤ, u1Flux θ₁ θ₂ θ₃ θ₄ = 2 * Real.pi * n := by
  rw [u1Holonomy_eq_link_flux, link_eq_one_iff]

/-! ## The Jarlskog invariant: CP violation as a flavour-space holonomy -/

/-- **Jarlskog invariant** `J = Im(V_us V_cb V*_ub V*_cs)` — the imaginary part of the closed quartet
loop in flavour space. The unique (up to sign) rephasing-invariant measure of CP violation. -/
noncomputable def jarlskog (Vus Vcb Vub Vcs : ℂ) : ℝ :=
  (Vus * Vcb * conj Vub * conj Vcs).im

/-- **A real CKM matrix conserves CP:** all-real entries give `J = 0`. -/
theorem jarlskog_real (a b c d : ℝ) : jarlskog (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) = 0 := by
  unfold jarlskog
  simp only [Complex.conj_ofReal]
  rw [show (a : ℂ) * b * c * d = ((a * b * c * d : ℝ) : ℂ) by push_cast; ring]
  exact Complex.ofReal_im _

/-- **The CP phase is physical (rephasing-invariant).** Multiplying the up rows by phases
`αᵤ, α_c` and the down columns by `β_s, β_b` leaves `J` unchanged: the phase cannot be rotated
away — this is gauge (rephasing) invariance of the flavour-space Wilson loop. -/
theorem jarlskog_rephasing (Vus Vcb Vub Vcs : ℂ) (αu αc βs βb : ℝ) :
    jarlskog (link αu * link βs * Vus) (link αc * link βb * Vcb)
      (link αu * link βb * Vub) (link αc * link βs * Vcs) = jarlskog Vus Vcb Vub Vcs := by
  unfold jarlskog
  congr 1
  have cb : conj (link αu * link βb * Vub) = link (-αu) * link (-βb) * conj Vub := by
    rw [map_mul, map_mul, conj_link, conj_link]
  have cs : conj (link αc * link βs * Vcs) = link (-αc) * link (-βs) * conj Vcs := by
    rw [map_mul, map_mul, conj_link, conj_link]
  rw [cb, cs]
  have collect :
      (link αu * link βs * Vus) * (link αc * link βb * Vcb) *
          (link (-αu) * link (-βb) * conj Vub) * (link (-αc) * link (-βs) * conj Vcs)
        = (link αu * link (-αu)) * (link βs * link (-βs)) * (link αc * link (-αc)) *
            (link βb * link (-βb)) * (Vus * Vcb * conj Vub * conj Vcs) := by ring
  rw [collect, link_mul_neg, link_mul_neg, link_mul_neg, link_mul_neg]
  ring

/-- **One holonomy phase `δ` makes `J = (∏|V|)·sin δ`:** with three real entries and one carrying the
fibre-holonomy phase `e^{−iδ}`, the Jarlskog invariant is the product of magnitudes times `sin δ`. -/
theorem jarlskog_phase (a b d r δ : ℝ) :
    jarlskog (a : ℂ) (b : ℂ) ((r : ℂ) * link (-δ)) (d : ℂ) = a * b * d * r * Real.sin δ := by
  unfold jarlskog
  rw [Complex.conj_ofReal, map_mul, Complex.conj_ofReal, conj_link, neg_neg]
  rw [show (a : ℂ) * b * ((r : ℂ) * link δ) * d = ((a * b * r * d : ℝ) : ℂ) * link δ by
        push_cast; ring]
  rw [Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, link_im, link_re, zero_mul, add_zero]
  ring

/-- **CP violation `⟺` non-trivial holonomy phase:** with non-degenerate magnitudes, `J ≠ 0` exactly
when the holonomy phase is genuine (`sin δ ≠ 0`). -/
theorem jarlskog_phase_ne_zero {a b d r δ : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) (hr : r ≠ 0)
    (hδ : Real.sin δ ≠ 0) : jarlskog (a : ℂ) (b : ℂ) ((r : ℂ) * link (-δ)) (d : ℂ) ≠ 0 := by
  rw [jarlskog_phase]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ha hb) hd) hr) hδ

/-- **No phase, no CP violation:** `δ = 0` (a trivial holonomy) gives `J = 0`. -/
theorem jarlskog_no_phase (a b d r : ℝ) :
    jarlskog (a : ℂ) (b : ℂ) ((r : ℂ) * link (-0)) (d : ℂ) = 0 := by
  rw [jarlskog_phase, Real.sin_zero]; ring

/-! ## Closure -/

/-- **CP-holonomy discharge bundle.** -/
structure CPHolonomyDischarged : Prop where
  holonomy_is_flux :
    ∀ θ₁ θ₂ θ₃ θ₄ : ℝ, u1Holonomy θ₁ θ₂ θ₃ θ₄ = link (u1Flux θ₁ θ₂ θ₃ θ₄)
  flat_iff_quantized :
    ∀ θ₁ θ₂ θ₃ θ₄ : ℝ,
      u1Holonomy θ₁ θ₂ θ₃ θ₄ = 1 ↔ ∃ n : ℤ, u1Flux θ₁ θ₂ θ₃ θ₄ = 2 * Real.pi * n
  cp_rephasing_invariant :
    ∀ (Vus Vcb Vub Vcs : ℂ) (αu αc βs βb : ℝ),
      jarlskog (link αu * link βs * Vus) (link αc * link βb * Vcb)
        (link αu * link βb * Vub) (link αc * link βs * Vcs) = jarlskog Vus Vcb Vub Vcs
  real_conserves_cp : ∀ a b c d : ℝ, jarlskog (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) = 0
  cp_from_phase :
    ∀ a b d r δ : ℝ, jarlskog (a : ℂ) (b : ℂ) ((r : ℂ) * link (-δ)) (d : ℂ) = a * b * d * r * Real.sin δ

/-- **CP violation is a holonomy phase:** the abelian Wilson loop's holonomy is its flux phase (flat
iff quantized), and the rephasing-invariant Jarlskog invariant vanishes for real (CP-conserving)
mixing while a single fibre-holonomy phase `δ` produces `J ∝ sin δ`. -/
theorem cpHolonomyDischarged_holds : CPHolonomyDischarged where
  holonomy_is_flux := u1Holonomy_eq_link_flux
  flat_iff_quantized := u1Holonomy_eq_one_iff
  cp_rephasing_invariant := jarlskog_rephasing
  real_conserves_cp := jarlskog_real
  cp_from_phase := jarlskog_phase

end HqivSpine.Physics.CPHolonomyPhase

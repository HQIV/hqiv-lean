import Hqiv.Story.S3OctonionS7TorsionCancellation

/-!
# The log edge: phases, Diophantine independence, and the Goldbach circle

Every locator so far has been a *modulus* readout, and the carrier
factorizes: `n^{−s} = n^{−σ}·exp(−i t log n)`.  The modulus channel knows
only `σ` (hence: locators ⟺ RH), and the phase channel knows only
`t = Im s`.  This module formalizes the phase (log) channel — the edge
where the additive (Goldbach) and multiplicative (Euler) structures
actually touch.

## Proved here

* **Polar decomposition / decoupling** (`so4SpectralLine_polar`,
  `log_edge_decoupling`): the spectral line splits exactly as
  σ-modulus × t-phase, with the phase unimodular.  This is the formal
  reason every norm readout produced an RH-equivalence and nothing more:
  the modulus erases `t`, the phase erases `σ`.
* **The log edge itself** (`linePhase_mul`): multiplication becomes
  addition in the phase channel — `phase(pq) = phase(p)·phase(q)` via
  `log(pq) = log p + log q`.
* **Diophantine phase independence** (`prime_log_nat_rel`,
  `prime_log_int_rel`): for distinct primes, `k·log p = m·log q` forces
  `k = m = 0` — proved from unique factorization (`p^k = q^m` is
  impossible).  The prime phase speeds are incommensurable.
* **Two prime phases pin the height** (`two_prime_phases_pin_height`):
  if the phases of two distinct primes agree at heights `t₁, t₂`, then
  `t₁ = t₂` — the joint `2π`-ambiguity of two incommensurable channels is
  *zero*.  One prime leaves a lattice of ghost heights; two primes leave
  none.
* **The Goldbach circle — additive curvature**
  (`goldbach_pair_circle`): for a midpoint pair `p + q = 2N`,
  \[ pq + (q-N)^2 = N^2. \]
  The additive channel literally supplies curvature: Goldbach pairs are
  points on a circle of radius `N` in the (geometric-mean, deviation)
  plane.  The multiplicative phase speed `log(pq)` is capped by the
  additive constraint: `log(pq) ≤ 2 log N` with equality iff the pair is
  the diagonal `p = q = N` (`pair_phase_speed_max`).
* **Zeros are addressed by two prime phases under RH**
  (`RH_zero_determined_by_two_prime_phases`): given RH, a nontrivial
  zero is *completely determined* by the phases of any two distinct
  primes at its height — σ comes from RH, t from phase independence.
  This is the "transformer that locates a zero" in its honest form.

## Honest scope

The curvature is real, but it lives entirely in the `t`/additive channel,
and the decoupling theorem says the geometry cleanly separates it from
`σ`.  That is precisely why the modulus program produced reformulations:
no norm readout can import phase curvature into a σ-constraint.  Any
genuine forcing attack must couple the two channels — e.g. through the
zero set itself (where `ζ` ties σ and t together analytically), which is
exactly what the classical explicit formula does and what remains open
here.  We name that coupling as the frontier rather than claim it.
-/

namespace Hqiv.Story

open Complex Hqiv.Geometry

noncomputable section

/-! ## Polar decomposition: the carrier factorizes -/

/-- **The phase factor of a spectral line**: the unimodular part
`exp(−i t log n)`, carrying all the `t`-dependence and none of the
σ-dependence. -/
noncomputable def linePhase (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (-(t * Real.log n) * Complex.I)

/-- **Polar decomposition of the spectral line**:
`n^{−s} = n^{−σ} · exp(−i t log n)`. -/
theorem so4SpectralLine_polar {n : ℕ} (hn : 0 < n) (s : ℂ) :
    so4SpectralLine n s =
      (((n : ℝ) ^ (-s.re) : ℝ) : ℂ) * linePhase n s.im := by
  unfold so4SpectralLine linePhase
  have hne : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Complex.cpow_def_of_ne_zero hne]
  have hL : Complex.log ((n : ℕ) : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg n)]
  rw [hL]
  have hsplit : ((Real.log n : ℝ) : ℂ) * (-s) =
      ((-(s.re * Real.log n) : ℝ) : ℂ) +
        ((-(s.im * Real.log n) : ℝ) : ℂ) * Complex.I := by
    nth_rewrite 1 [← Complex.re_add_im s]
    push_cast
    ring
  rw [hsplit, Complex.exp_add]
  congr 1
  · rw [← Complex.ofReal_exp]
    congr 1
    rw [Real.rpow_def_of_pos (by exact_mod_cast hn)]
    ring_nf
  · congr 1
    push_cast
    ring

/-- **The decoupling theorem**: the carrier splits as σ-modulus times
unimodular t-phase.  Every norm readout erases `t`; the phase erases `σ`.
This is the formal reason the modulus program yields RH-equivalences and
cannot import additive curvature into a σ-constraint. -/
theorem log_edge_decoupling {n : ℕ} (hn : 0 < n) (s : ℂ) :
    so4SpectralLine n s =
      (((n : ℝ) ^ (-s.re) : ℝ) : ℂ) * linePhase n s.im ∧
    ‖(((n : ℝ) ^ (-s.re) : ℝ) : ℂ)‖ = (n : ℝ) ^ (-s.re) ∧
    ‖linePhase n s.im‖ = 1 := by
  refine ⟨so4SpectralLine_polar hn s, ?_, ?_⟩
  · rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · unfold linePhase
    rw [Complex.norm_exp, Complex.mul_I_re]
    simp [Complex.log_im, Complex.natCast_arg]

/-- **The log edge**: multiplication becomes addition in the phase
channel — the joint phase of `pq` is the product of the prime phases. -/
theorem linePhase_mul {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (t : ℝ) :
    linePhase (p * q) t = linePhase p t * linePhase q t := by
  unfold linePhase
  rw [← Complex.exp_add]
  congr 1
  have hlog : Real.log ((p * q : ℕ) : ℝ) = Real.log p + Real.log q := by
    push_cast
    exact Real.log_mul (by positivity) (by positivity)
  rw [hlog]
  push_cast
  ring

/-! ## Diophantine phase independence -/

/-- **Natural incommensurability**: `k·log p = m·log q` for distinct
primes forces `k = m = 0`, by unique factorization. -/
theorem prime_log_nat_rel {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) {k m : ℕ}
    (h : (k : ℝ) * Real.log p = (m : ℝ) * Real.log q) :
    k = 0 ∧ m = 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  by_cases hk : k = 0
  · subst hk
    simp only [Nat.cast_zero, zero_mul] at h
    have hlq : 0 < Real.log q := Real.log_pos hq1
    have hm : (m : ℝ) = 0 := by
      by_contra hm
      have : (m : ℝ) * Real.log q ≠ 0 :=
        mul_ne_zero hm (ne_of_gt hlq)
      exact this h.symm
    exact ⟨rfl, by exact_mod_cast hm⟩
  · exfalso
    have hexp : ((p : ℝ)) ^ k = ((q : ℝ)) ^ m := by
      have h' : Real.log ((p : ℝ) ^ k) = Real.log ((q : ℝ) ^ m) := by
        rw [Real.log_pow, Real.log_pow]
        exact_mod_cast h
      have hpk : (0 : ℝ) < (p : ℝ) ^ k := by positivity
      have hqm : (0 : ℝ) < (q : ℝ) ^ m := by positivity
      calc ((p : ℝ)) ^ k = Real.exp (Real.log ((p : ℝ) ^ k)) :=
            (Real.exp_log hpk).symm
        _ = Real.exp (Real.log ((q : ℝ) ^ m)) := by rw [h']
        _ = ((q : ℝ)) ^ m := Real.exp_log hqm
    have hnat : p ^ k = q ^ m := by exact_mod_cast hexp
    have hm : m ≠ 0 := by
      intro hm0
      subst hm0
      rw [pow_zero] at hnat
      have := Nat.pow_eq_one.mp hnat
      rcases this with h1 | h0
      · exact hp.one_lt.ne' h1
      · exact hk h0
    have hdvd : p ∣ q ^ m := by
      rw [← hnat]
      exact dvd_pow_self p hk
    have : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp
      (hp.dvd_of_dvd_pow hdvd)
    exact hne this

/-- **Integer incommensurability**: the same with integer coefficients. -/
theorem prime_log_int_rel {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) {k m : ℤ}
    (h : (k : ℝ) * Real.log p = (m : ℝ) * Real.log q) :
    k = 0 ∧ m = 0 := by
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  by_cases hk0 : 0 ≤ k
  · have hm0 : 0 ≤ m := by
      by_contra hneg
      push_neg at hneg
      have h1 : (m : ℝ) * Real.log q < 0 :=
        mul_neg_of_neg_of_pos (by exact_mod_cast hneg) hlq
      have h2 : (0 : ℝ) ≤ (k : ℝ) * Real.log p :=
        mul_nonneg (by exact_mod_cast hk0) hlp.le
      linarith
    lift k to ℕ using hk0
    lift m to ℕ using hm0
    have := prime_log_nat_rel hp hq hne (by exact_mod_cast h)
    exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
  · push_neg at hk0
    have hm0 : m < 0 := by
      by_contra hpos
      push_neg at hpos
      have h1 : (k : ℝ) * Real.log p < 0 :=
        mul_neg_of_neg_of_pos (by exact_mod_cast hk0) hlp
      have h2 : (0 : ℝ) ≤ (m : ℝ) * Real.log q :=
        mul_nonneg (by exact_mod_cast hpos) hlq.le
      linarith
    have h' : ((-k : ℤ) : ℝ) * Real.log p = ((-m : ℤ) : ℝ) * Real.log q := by
      push_cast
      linarith
    obtain ⟨k', hk'⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ -k)
    obtain ⟨m', hm'⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ -m)
    rw [hk', hm'] at h'
    obtain ⟨hk1, hm1⟩ := prime_log_nat_rel hp hq hne
      (k := k') (m := m') (by exact_mod_cast h')
    omega

/-- Phase equality at one prime extracts an integer `2π` relation. -/
theorem linePhase_eq_iff_int {n : ℕ} {t₁ t₂ : ℝ}
    (h : linePhase n t₁ = linePhase n t₂) :
    ∃ k : ℤ, (t₂ - t₁) * Real.log n = 2 * Real.pi * k := by
  unfold linePhase at h
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨k, ?_⟩
  have him := congrArg Complex.im hk
  simp only [Complex.ofReal_re, Complex.add_im,
    Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
    Complex.ofReal_im, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.re_ofNat, Complex.im_ofNat, Complex.neg_re,
    Complex.neg_im, mul_zero, zero_mul, sub_zero, mul_one,
    add_zero] at him
  ring_nf at him ⊢
  linarith

/-- **Two prime phases pin the height**: if the phases of two *distinct*
primes agree at heights `t₁` and `t₂`, then `t₁ = t₂`.  One prime leaves
a `2π/log p` lattice of ghost heights; two incommensurable primes leave
none. -/
theorem two_prime_phases_pin_height {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hne : p ≠ q) {t₁ t₂ : ℝ}
    (h1 : linePhase p t₁ = linePhase p t₂)
    (h2 : linePhase q t₁ = linePhase q t₂) :
    t₁ = t₂ := by
  obtain ⟨k, hk⟩ := linePhase_eq_iff_int h1
  obtain ⟨m, hm⟩ := linePhase_eq_iff_int h2
  by_contra hne'
  have hΔ : t₂ - t₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne')
  have key : (t₂ - t₁) * ((m : ℝ) * Real.log p) =
      (t₂ - t₁) * ((k : ℝ) * Real.log q) := by
    have e1 : (m : ℝ) * ((t₂ - t₁) * Real.log p) =
        (m : ℝ) * (2 * Real.pi * k) := by rw [hk]
    have e2 : (k : ℝ) * ((t₂ - t₁) * Real.log q) =
        (k : ℝ) * (2 * Real.pi * m) := by rw [hm]
    linear_combination e1 - e2
  have hrel := mul_left_cancel₀ hΔ key
  obtain ⟨hm0, hk0⟩ := prime_log_int_rel hp hq hne hrel
  rw [hk0, Int.cast_zero, mul_zero] at hk
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  exact hΔ ((mul_eq_zero.mp hk).resolve_right (ne_of_gt hlp))

/-! ## The Goldbach circle: additive curvature -/

/-- **The Goldbach circle**: a midpoint pair `p + q = 2N` satisfies
\[ pq + (q-N)^2 = N^2. \]
The additive prime channel supplies literal curvature — every pair is a
point on the circle of radius `N` in the (geometric-mean, deviation)
plane. -/
theorem goldbach_pair_circle {N p q : ℕ}
    (h : GoldbachMidpointPair N p q) :
    p * q + (q - N) ^ 2 = N ^ 2 := by
  obtain ⟨_, _, hpN, hNq, hsum⟩ := h
  zify [hNq]
  have hs : (p : ℤ) + q = 2 * N := by exact_mod_cast hsum
  linear_combination (q : ℤ) * hs

/-- **Phase speed is capped by the additive constraint**: on the
Goldbach circle the multiplicative phase speed `log(pq)` never exceeds
`2 log N`, with equality exactly at the diagonal pair `p = q = N`. -/
theorem pair_phase_speed_max {N p q : ℕ} (hN : 0 < N)
    (h : GoldbachMidpointPair N p q) :
    Real.log ((p * q : ℕ) : ℝ) ≤ 2 * Real.log N ∧
      (Real.log ((p * q : ℕ) : ℝ) = 2 * Real.log N ↔ p = N ∧ q = N) := by
  have hp0 : 0 < p := h.1.pos
  have hq0 : 0 < q := h.2.1.pos
  obtain ⟨hprime_p, hprime_q, hpN, hNq, hsum⟩ := h
  have hcirc : p * q + (q - N) ^ 2 = N ^ 2 :=
    goldbach_pair_circle ⟨hprime_p, hprime_q, hpN, hNq, hsum⟩
  have hpq : p * q ≤ N ^ 2 := Nat.le.intro hcirc
  have hpq0 : (0 : ℝ) < ((p * q : ℕ) : ℝ) := by positivity
  have hN2 : ((N ^ 2 : ℕ) : ℝ) = ((N : ℝ)) ^ 2 := by push_cast; ring
  have hlogN2 : Real.log (((N : ℝ)) ^ 2) = 2 * Real.log N := by
    rw [Real.log_pow]
    norm_num
  have hle : Real.log ((p * q : ℕ) : ℝ) ≤ 2 * Real.log N := by
    have h1 : ((p * q : ℕ) : ℝ) ≤ ((N : ℝ)) ^ 2 := by
      rw [← hN2]; exact_mod_cast hpq
    have h2 := (Real.log_le_log_iff hpq0 (by positivity)).mpr h1
    rwa [hlogN2] at h2
  refine ⟨hle, ?_, ?_⟩
  · intro heq
    have hpqN : p * q = N ^ 2 := by
      by_contra hne2
      have hlt : p * q < N ^ 2 := lt_of_le_of_ne hpq hne2
      have hltR : ((p * q : ℕ) : ℝ) < ((N : ℝ)) ^ 2 := by
        rw [← hN2]; exact_mod_cast hlt
      have hlog := Real.log_lt_log hpq0 hltR
      rw [hlogN2] at hlog
      linarith
    rw [hpqN] at hcirc
    have hd : (q - N) ^ 2 = 0 :=
      Nat.add_left_cancel (by rw [Nat.add_zero]; exact hcirc)
    have hqN : q = N := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hd
      omega
    exact ⟨by omega, hqN⟩
  · rintro ⟨hpN', hqN'⟩
    rw [hpN', hqN']
    have hNN : ((N * N : ℕ) : ℝ) = ((N : ℝ)) ^ 2 := by push_cast; ring
    rw [hNN, hlogN2]

/-! ## Zeros are addressed by two prime phases -/

/-- **Under RH, two prime phases are a complete address for a zero**:
σ is pinned by RH, the height by Diophantine phase independence.  This is
the honest form of the "transformer that locates a zero for a given
input": feed it the phases of two distinct primes, receive the zero. -/
theorem RH_zero_determined_by_two_prime_phases
    (hRH : RiemannHypothesis) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) {ρ₁ ρ₂ : ℂ}
    (h₁ : IsNontrivialZetaZero ρ₁) (h₂ : IsNontrivialZetaZero ρ₂)
    (hph_p : linePhase p ρ₁.im = linePhase p ρ₂.im)
    (hph_q : linePhase q ρ₁.im = linePhase q ρ₂.im) :
    ρ₁ = ρ₂ := by
  have him := two_prime_phases_pin_height hp hq hne hph_p hph_q
  have hre₁ := hRH ρ₁ h₁.1 h₁.2.1 h₁.2.2
  have hre₂ := hRH ρ₂ h₂.1 h₂.2.1 h₂.2.2
  exact Complex.ext (by rw [hre₁, hre₂]) him

end

end Hqiv.Story

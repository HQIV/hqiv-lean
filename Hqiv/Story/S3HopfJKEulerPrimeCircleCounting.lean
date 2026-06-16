import Hqiv.Story.S3HopfJKUnitCircleZeroReadout
import Hqiv.Story.S3HarmonicShellZeroCounting
import Hqiv.Story.S3LogPhaseEdge
import Hqiv.Story.S3LogExpTrigReadoutBridge
import Hqiv.Story.S3EulerSpectralCancellation
import Hqiv.Story.S3HarmonicPrimeZetaPath
import Hqiv.Story.S3SpectralResonanceChanneling
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# Euler prime product on the Hopf `j`–`k` circle: natural zero counting

The critical line lifts to a **compact** unit circle in the `j`/`k` plane.
Scanning a non-compact height `t ∈ ℝ` is the universal cover; the Euler prime
product supplies the **discrete** spectrum that locates points on that circle.

## Polar decomposition on the line

For `s = ½ + it` and `n > 0`,

`n^{−s} = n^{−½} · exp(−it log n)` (`critical_line_prime_power_polar`).

Each prime contributes a **unit phase** `linePhase p t` on the circle; the
modulus `p^{−½}` is independent of the angle (`critical_line_modulus_no_angle`).

Multiplication in `ℕ` becomes phase multiplication on the circle
(`linePhase_mul`).

## Counting axis (not a height scan)

Zeros are spectral cancellations of the continued Euler product
(`S3EulerSpectralCancellation`).  On the circle the natural indices are:

* **arc slot** `(n, k)` at angle `2πk/n` (`shellSweepAngle`);
* **prime label** `p` with phase `linePhase p θ` at circle angle `θ`;
* **`j`–`k` coordinates** `(j, k) = (cos θ, sin θ)` with amplitude
  `j/√2 + k/√2` and phase `exp(π i j k)`.

Two distinct prime phases **pin** the circle point (`two_prime_phases_pin_height`):
one prime leaves a `2π/log p` ghost lattice; two incommensurable primes fix
the angle.  That is the Euler-product reason height is overdetermined as a
scan and underdetermined as a **prime-phase coincidence problem** on `S¹`.

**Honesty.**  Identifying `ζ(s)=0` with amplitude balance on the rolled lift
still requires `RollingZetaIdentificationAtCriticalLine`.  The Euler polar
split, prime-phase multiplicativity, shell-slot indexing, and two-prime pinning
are unconditional.
-/

namespace Hqiv.Story

noncomputable section

open Complex Real ArithmeticFunction
open scoped LSeries.notation zeta

/-! ## Critical-line Euler factors as modulus × circle phase -/

/-- Modulus factor `n^{−½}` on the critical line (no angle dependence). -/
noncomputable def criticalLineModulus (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-(1 / 2 : ℝ))

theorem critical_line_modulus_no_angle (n : ℕ) (t₁ t₂ : ℝ) :
    criticalLineModulus n = criticalLineModulus n :=
  rfl

theorem critical_line_prime_power_polar {n : ℕ} (hn : 0 < n) (t : ℝ) :
    so4SpectralLine n (criticalLinePointAtHeight t) =
      (criticalLineModulus n : ℂ) * linePhase n t := by
  dsimp [so4SpectralLine, criticalLineModulus]
  simpa [criticalLinePointAtHeight_im] using
    so4SpectralLine_polar hn (criticalLinePointAtHeight t)

theorem critical_line_modulus_pos {n : ℕ} (hn : 0 < n) :
    0 < criticalLineModulus n := by
  dsimp [criticalLineModulus]
  exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _

/-! ## Prime phases on shell slots and the `j`–`k` circle -/

/-- Euler prime phase at circle angle `θ`. -/
noncomputable def primePhaseAtCircleAngle (p : ℕ) (θ : ℝ) : ℂ :=
  linePhase p θ

/-- Prime phase at harmonic-shell slot `(n, k)`. -/
noncomputable def primePhaseAtShellSlot {n : ℕ} (hn : 0 < n) (p : ℕ) (k : Fin n) : ℂ :=
  linePhase p (shellSweepAngle hn k)

theorem prime_phase_at_slot_eq_angle {n : ℕ} (hn : 0 < n) (p : ℕ) (k : Fin n) :
    primePhaseAtShellSlot hn p k =
      primePhaseAtCircleAngle p (shellSweepAngle hn k) := rfl

theorem prime_phase_shell_slot_on_unit_circle {n : ℕ} (hn : 0 < n) (p : ℕ) (k : Fin n) :
    ‖primePhaseAtShellSlot hn p k‖ = 1 := by
  dsimp [primePhaseAtShellSlot, primePhaseAtCircleAngle, linePhase]
  rw [Complex.norm_exp, Complex.mul_I_re]
  simp [Complex.log_im, Complex.natCast_arg]

theorem euler_phase_multiplicative_at_slot {n : ℕ} (hn : 0 < n) (p q : ℕ)
    (hp : 0 < p) (hq : 0 < q) (k : Fin n) :
    primePhaseAtShellSlot hn (p * q) k =
      primePhaseAtShellSlot hn p k * primePhaseAtShellSlot hn q k := by
  dsimp [primePhaseAtShellSlot]
  exact linePhase_mul hp hq (shellSweepAngle hn k)

lemma hopf_amp_zero_iff_critical_proj_zero (t : ℝ) :
    hopfJKCriticalAmplitude t = 0 ↔ criticalProj (stripRollingMap t) = 0 := by
  rw [← hopf_jk_amplitude_eq_critical_proj]

/-! ## `j`–`k` amplitude + prime log twiddle at a slot -/

/--
Prime-side explicit term paired with the `j`–`k` amplitude at shell angle
`θ = 2πk/n` — the Euler/log channel against the rolled survivor amplitude.
-/
noncomputable def primeLogTwiddleAtAngle (θ : ℝ) : PrimeLogTrigRollingSlot θ :=
  primeLogTrigRollingSlot θ

theorem prime_log_twiddle_at_slot {n : ℕ} (hn : 0 < n) (k : Fin n) :
    (primeLogTwiddleAtAngle (shellSweepAngle hn k)).twiddle =
      rollingFourierTwiddle (shellSweepAngle hn k) := rfl

theorem shell_slot_prime_log_term_eq_vonMangoldt_amp {n : ℕ} (hn : 0 < n) (k : Fin n) :
    (primeLogTwiddleAtAngle (shellSweepAngle hn k)).prime_log_term =
      vonMangoldt 2 * hopfJKCriticalAmplitude (shellSweepAngle hn k) := by
  have h := prime_log_term_eq_vonMangoldt_times_amp (shellSweepAngle hn k)
  dsimp [primeLogTwiddleAtAngle, primeLogTrigRollingSlot] at h ⊢
  rw [h, hopf_jk_amplitude_eq_critical_proj]

/-! ## Two primes locate a circle point -/

/--
If two distinct prime phases agree at two circle angles, the angles coincide.
This is the Euler-product mechanism for **locating** a point on `S¹` by prime
data rather than scanning `t`.
-/
theorem two_prime_phases_pin_circle_angle {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) {θ₁ θ₂ : ℝ}
    (h1 : linePhase p θ₁ = linePhase p θ₂)
    (h2 : linePhase q θ₁ = linePhase q θ₂) :
    θ₁ = θ₂ :=
  two_prime_phases_pin_height hp hq hne h1 h2

/-! ## Spectral cancellation ↔ circle balance (conditional) -/

theorem zeta_zero_iff_shell_slot_balance
    (hId : RollingZetaIdentificationAtCriticalLine) {n : ℕ} (hn : 0 < n) (k : Fin n) :
    riemannZeta (criticalLinePointAtHeight (shellSweepAngle hn k)) = 0 ↔
      HarmonicShellBalanceEvent hn k := by
  dsimp [HarmonicShellBalanceEvent, stripRollingAtSlot]
  rw [zeta_zero_iff_hopf_jk_amplitude hId, hopf_jk_amplitude_eq_critical_proj]

theorem zeta_zero_iff_shell_prime_twiddle
    (hId : RollingZetaIdentificationAtCriticalLine) {n : ℕ} (hn : 0 < n) (k : Fin n) :
    riemannZeta (criticalLinePointAtHeight (shellSweepAngle hn k)) = 0 ↔
      (primeLogTwiddleAtAngle (shellSweepAngle hn k)).twiddle = 0 := by
  rw [zeta_zero_iff_hopf_jk_amplitude hId]
  dsimp [primeLogTwiddleAtAngle, primeLogTrigRollingSlot]
  rw [hopf_amp_zero_iff_critical_proj_zero, criticalProj_eq_zero_iff_balanced,
    rolling_twiddle_vanishes_iff_balanced]

theorem nontrivial_zero_forces_breakdown_locus (s : ℂ) (h : IsNontrivialZetaZero s) :
    0 < s.re ∧ s.re < 1 :=
  spectral_cancellation_in_breakdown_locus s h

/--
Counting axis: discrete shell arcs × discrete prime phases × `j`–`k` amplitude,
not a monotone scan of `t ∈ ℝ`.
-/
structure EulerPrimeCircleCountingAxis where
  /-- Arc partition at shell depth. -/
  slot_angle : ∀ {n : ℕ}, 0 < n → Fin n → ℝ
  /-- Prime phase at each slot lies on `S¹`. -/
  prime_phase_on_circle :
    ∀ {n : ℕ} (hn : 0 < n) (p : ℕ) (k : Fin n),
      ‖primePhaseAtShellSlot hn p k‖ = 1
  /-- Euler multiplicativity of phases at a fixed slot. -/
  prime_phase_multiplicative :
    ∀ {n : ℕ} (hn : 0 < n) (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (k : Fin n),
      primePhaseAtShellSlot hn (p * q) k =
        primePhaseAtShellSlot hn p k * primePhaseAtShellSlot hn q k
  /-- `j`–`k` balance at slot equals prime-log twiddle vanishing (bridge layer). -/
  slot_balance_twiddle :
    ∀ {n : ℕ} (hn : 0 < n) (k : Fin n),
      hopfJKTwiddleReadout (shellSweepAngle hn k) = 0 ↔
        (primeLogTwiddleAtAngle (shellSweepAngle hn k)).twiddle = 0
  /-- Two distinct primes pin the circle angle. -/
  two_primes_pin : ∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) {θ₁ θ₂ : ℝ},
    linePhase p θ₁ = linePhase p θ₂ → linePhase q θ₁ = linePhase q θ₂ → θ₁ = θ₂

noncomputable def eulerPrimeCircleCountingAxis : EulerPrimeCircleCountingAxis where
  slot_angle := @shellSweepAngle
  prime_phase_on_circle := prime_phase_shell_slot_on_unit_circle
  prime_phase_multiplicative := euler_phase_multiplicative_at_slot
  slot_balance_twiddle := fun {n} hn k => by
    dsimp [primeLogTwiddleAtAngle, primeLogTrigRollingSlot]
    rw [hopf_jk_twiddle_vanishes_iff_amplitude, hopf_amp_zero_iff_critical_proj_zero,
      criticalProj_eq_zero_iff_balanced, rolling_twiddle_vanishes_iff_balanced]
  two_primes_pin := @two_prime_phases_pin_circle_angle

/-!
## Status

* **Unconditional:** critical-line polar split; prime phases on shell slots;
  Euler phase multiplicativity; two-prime circle pinning; shell-slot `j`–`k`
  balance dictionary; nontrivial zeros live on the Euler breakdown locus.
* **Conditional:** `ζ=0` at slot angle ↔ harmonic-shell balance ↔ prime twiddle
  vanishes under `RollingZetaIdentificationAtCriticalLine`.
* **Not claimed:** that known ζ-zeros sit at rational shell angles `2πk/n`; the
  axis is the **indexing infrastructure** the Euler product supplies for circle
  counting, not a closed-form zero locator.
-/

end

end Hqiv.Story

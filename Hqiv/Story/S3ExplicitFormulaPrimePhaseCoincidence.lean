import Hqiv.Story.S3CountableCircleFill
import Hqiv.Story.S3LogExpTrigReadoutBridge
import Hqiv.Story.S3ExplicitFormulaDualitySlot
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Explicit-formula zero oscillations ↔ Euler prime phases on the filled circle

The explicit formula pairs

* **prime side:** `ψ(x) = ∑_{n≤x} Λ(n)` with von Mangoldt weights and Euler
  phases `linePhase p θ = exp(−i θ log p)` on the Hopf circle;
* **zero side:** `∑_ρ x^ρ/ρ` with oscillations `exp(i γ log x)` at each
  nontrivial zero height `γ`.

On the countably filled circle (`S3CountableCircleFill`), every arc slot carries
prime phases; this module proves the **log→trig coincidence law** linking the
two carriers:

`conj (linePhase p θ) = exp(i θ log p)`  (prime Euler phase ↔ zero oscillation)

At encoded slot `(p, n, k)` the prime phase and the explicit-formula oscillation
at scale `x = p` and height `γ = θ = 2πk/n` are conjugate unit-circle partners.
Two distinct primes **pin** `θ`; ζ-zero identification at the slot remains
conditional on `RollingZetaIdentificationAtCriticalLine`.

**Honesty.**  Conjugate duality, countable coincidence grid, and two-prime
pinning are unconditional.  Reading a ζ-zero as a balance / coincidence event on
the grid requires the rolling bridge.
-/

namespace Hqiv.Story

noncomputable section

open Complex Real ArithmeticFunction
open scoped ComplexConjugate LSeries.notation zeta

/-! ## Conjugate duality: Euler phase ↔ zero oscillation -/

/--
Prime Euler phase uses **negative** chirality in the log carrier;
explicit-formula zero oscillation uses **positive** chirality.  They are
complex conjugates on the unit circle.
-/
theorem linePhase_conj_is_zero_oscillation {p : ℕ} (_hp : 0 < p) (θ : ℝ) :
    conj (linePhase p θ) = zeroOscillationUnitPhase θ (p : ℝ) := by
  dsimp [linePhase, zeroOscillationUnitPhase, zeroOscillationPhase]
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, map_neg, Complex.conj_ofReal, mul_neg, neg_neg]
  simp [mul_comm, mul_assoc]

theorem zero_oscillation_conj_is_linePhase {p : ℕ} (hp : 0 < p) (θ : ℝ) :
    conj (zeroOscillationUnitPhase θ (p : ℝ)) = linePhase p θ := by
  rw [← linePhase_conj_is_zero_oscillation hp θ]
  simp [conj_conj]

/--
Explicit-formula power at prime scale: `p^{1/2+iγ}` factors into `√p` times
the conjugate Euler phase at angle `γ`.
-/
theorem cpow_at_prime_eq_sqrt_times_conj_linePhase {p : ℕ} (hp : 0 < p) (γ : ℝ) :
    (p : ℂ) ^ criticalLineExponent γ =
      (Real.sqrt p : ℂ) * conj (linePhase p γ) := by
  convert cpow_critical_line_trig_decomposition (Nat.cast_pos.mpr hp) using 2
  exact linePhase_conj_is_zero_oscillation hp γ

/-! ## Coincidence at harmonic-shell slots -/

/--
At shell slot angle `θ = 2πk/n`, the prime Euler phase is conjugate to the
zero oscillation at height `γ = θ` and scale `x = p`.
-/
theorem shell_slot_prime_conj_zero_oscillation {n : ℕ} (hn : 0 < n) (p : ℕ) (hp : 0 < p)
    (k : Fin n) :
    conj (primePhaseAtShellSlot hn p k) =
      zeroOscillationUnitPhase (shellSweepAngle hn k) (p : ℝ) := by
  dsimp [primePhaseAtShellSlot, primePhaseAtCircleAngle]
  exact linePhase_conj_is_zero_oscillation hp _

/--
Explicit-formula power at prime scale evaluated at the slot height `γ = 2πk/n`.
-/
theorem cpow_at_prime_slot_eq_sqrt_times_prime_phase_conj {n : ℕ} (hn : 0 < n)
    (p : ℕ) (hp : 0 < p) (k : Fin n) :
    (p : ℂ) ^ criticalLineExponent (shellSweepAngle hn k) =
      (Real.sqrt p : ℂ) * conj (primePhaseAtShellSlot hn p k) := by
  rw [cpow_at_prime_eq_sqrt_times_conj_linePhase hp]
  dsimp [primePhaseAtShellSlot, primePhaseAtCircleAngle]

/-! ## Encoded `(prime, slot)` coincidence cells -/

/--
A **coincidence cell** on the countably filled circle: prime label `p`, harmonic
slot, circle angle `θ`, and the conjugate pair (Euler phase, zero oscillation).
-/
structure PrimePhaseCoincidenceCell where
  prime : ℕ
  slot : HarmonicShellSlot
  hn : 0 < slot.1
  angle : ℝ
  angle_eq : angle = shellSweepAngle hn slot.2
  prime_phase : ℂ
  prime_phase_eq : prime_phase = primePhaseAtEncodedSlot prime slot
  zero_oscillation : ℂ
  zero_oscillation_eq :
    zero_oscillation = zeroOscillationUnitPhase angle (prime : ℝ)
  conj_duality : conj prime_phase = zero_oscillation

noncomputable def coincidenceCell (p : ℕ) (hp : 0 < p) (slot : HarmonicShellSlot)
    (hslot : 0 < slot.1) : PrimePhaseCoincidenceCell where
  prime := p
  slot := slot
  hn := hslot
  angle := shellSweepAngle hslot slot.2
  angle_eq := rfl
  prime_phase := primePhaseAtEncodedSlot p slot
  prime_phase_eq := rfl
  zero_oscillation := zeroOscillationUnitPhase (shellSweepAngle hslot slot.2) (p : ℝ)
  zero_oscillation_eq := rfl
  conj_duality := by
    rcases slot with ⟨n, k⟩
    rcases n with _ | n
    · exact absurd hslot (Nat.not_lt_zero 0)
    · dsimp [primePhaseAtEncodedSlot]
      exact shell_slot_prime_conj_zero_oscillation (Nat.succ_pos n) p hp k

theorem coincidence_cell_prime_phase_on_circle (c : PrimePhaseCoincidenceCell) :
    ‖c.prime_phase‖ = 1 := by
  rcases c with ⟨p, ⟨n, k⟩, hn, θ, hθ, φ, hφ, ψ, hψ, _⟩
  subst hθ hφ hψ
  rcases n with _ | n
  · exact absurd hn (Nat.not_lt_zero _)
  · dsimp [primePhaseAtEncodedSlot]
    exact prime_phase_shell_slot_on_unit_circle (Nat.succ_pos n) p k

theorem coincidence_cell_zero_oscillation_on_circle (c : PrimePhaseCoincidenceCell) :
    ‖c.zero_oscillation‖ = 1 := by
  rw [c.zero_oscillation_eq]
  exact zeroOscillationUnitPhase_on_circle c.angle (c.prime : ℝ)

theorem coincidence_cell_cpow_factorization (c : PrimePhaseCoincidenceCell)
    (hp : 0 < c.prime) :
    (c.prime : ℂ) ^ criticalLineExponent c.angle =
      (Real.sqrt c.prime : ℂ) * conj c.prime_phase := by
  rcases c with ⟨p, ⟨n, k⟩, hn, angle, hangle, φ, hφ, ψ, hψ, hconj⟩
  subst hangle hφ hψ
  rcases n with _ | n
  · exact absurd hn (Nat.not_lt_zero _)
  · dsimp [primePhaseAtEncodedSlot]
    simpa [hconj] using
      cpow_at_prime_slot_eq_sqrt_times_prime_phase_conj (Nat.succ_pos n) p hp k

/-! ## Prime log twiddle meets zero oscillation at a slot -/

/--
At slot angle `θ`, the rolling prime twiddle `e^{iθ}·amp` and the zero
oscillation `e^{iγ log x}` share the same `exp(i·)` trig carrier; the prime
log term pairs von Mangoldt weight with the survivor amplitude.
-/
structure SlotExplicitFormulaPair where
  slot : HarmonicShellSlot
  hn : 0 < slot.1
  angle : ℝ
  angle_eq : angle = shellSweepAngle hn slot.2
  prime_channel : PrimeLogTrigRollingSlot angle
  prime_channel_eq : prime_channel = primeLogTrigRollingSlot angle
  zero_oscillation : ℝ → ℂ
  zero_oscillation_eq :
    ∀ (x : ℝ), 0 < x → zero_oscillation x = zeroOscillationUnitPhase angle x

noncomputable def slotExplicitFormulaPair (slot : HarmonicShellSlot) (hn : 0 < slot.1) :
    SlotExplicitFormulaPair where
  slot := slot
  hn := hn
  angle := shellSweepAngle hn slot.2
  angle_eq := rfl
  prime_channel := primeLogTrigRollingSlot (shellSweepAngle hn slot.2)
  prime_channel_eq := rfl
  zero_oscillation := fun x => zeroOscillationUnitPhase (shellSweepAngle hn slot.2) x
  zero_oscillation_eq := fun _ _ => rfl

theorem slot_prime_twiddle_eq_rolling (P : SlotExplicitFormulaPair) :
    P.prime_channel.twiddle = rollingFourierTwiddle P.angle := by
  rw [P.prime_channel_eq]
  dsimp [primeLogTrigRollingSlot]

theorem slot_prime_conj_at_prime_scale (P : SlotExplicitFormulaPair) (p : ℕ) (hp : 0 < p) :
    conj (primePhaseAtShellSlot P.hn p P.slot.2) =
      P.zero_oscillation (p : ℝ) := by
  have hx : 0 < (p : ℝ) := Nat.cast_pos.mpr hp
  rw [shell_slot_prime_conj_zero_oscillation P.hn p hp P.slot.2, ← P.angle_eq]
  exact Eq.symm (P.zero_oscillation_eq (p : ℝ) hx)

/-! ## Two primes pin the coincidence locus -/

theorem coincidence_cell_angle_pinned_by_two_primes
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    {θ₁ θ₂ : ℝ}
    (h1 : linePhase p θ₁ = linePhase p θ₂)
    (h2 : linePhase q θ₁ = linePhase q θ₂) :
    θ₁ = θ₂ :=
  two_prime_phases_pin_circle_angle hp hq hne h1 h2

/-! ## Conditional: ζ-zero as coincidence balance on the grid -/

theorem zeta_zero_iff_slot_coincidence_balance
    (hId : RollingZetaIdentificationAtCriticalLine) {n : ℕ} (hn : 0 < n) (k : Fin n) :
    riemannZeta (criticalLinePointAtHeight (shellSweepAngle hn k)) = 0 ↔
      HarmonicShellBalanceEvent hn k :=
  zeta_zero_iff_shell_slot_balance hId hn k

theorem zeta_zero_iff_slot_prime_twiddle_vanishes
    (hId : RollingZetaIdentificationAtCriticalLine) {n : ℕ} (hn : 0 < n) (k : Fin n) :
    riemannZeta (criticalLinePointAtHeight (shellSweepAngle hn k)) = 0 ↔
      (primeLogTwiddleAtAngle (shellSweepAngle hn k)).twiddle = 0 :=
  zeta_zero_iff_shell_prime_twiddle hId hn k

/-! ## Master coincidence bundle -/

/--
Bundle: countably filled circle + log/exp bridge + conjugate prime/zero phase
duality + two-prime pinning + conditional ζ-zero ↔ slot balance.
-/
structure ExplicitFormulaPrimePhaseCoincidenceBundle where
  circle_fill : CountableCircleFillBundle
  log_exp_bridge : LogExpTrigReadoutBridge
  coincidence_grid_injective :
    Function.Injective (fun x : ℕ × HarmonicShellSlot => encodePrimeShellSlot x.1 x.2)
  conj_duality :
    ∀ {p : ℕ}, 0 < p → ∀ θ : ℝ,
      conj (linePhase p θ) = zeroOscillationUnitPhase θ (p : ℝ)
  cpow_prime_factor :
    ∀ {p : ℕ} (hp : 0 < p) (γ : ℝ),
      (p : ℂ) ^ criticalLineExponent γ =
        (Real.sqrt p : ℂ) * conj (linePhase p γ)
  slot_conj_duality :
    ∀ {n : ℕ} (hn : 0 < n) (p : ℕ) (hp : 0 < p) (k : Fin n),
      conj (primePhaseAtShellSlot hn p k) =
        zeroOscillationUnitPhase (shellSweepAngle hn k) (p : ℝ)
  two_primes_pin :
    ∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) {θ₁ θ₂ : ℝ},
      linePhase p θ₁ = linePhase p θ₂ → linePhase q θ₁ = linePhase q θ₂ → θ₁ = θ₂
  euler_axis : EulerPrimeCircleCountingAxis

noncomputable def explicitFormulaPrimePhaseCoincidenceBundle :
    ExplicitFormulaPrimePhaseCoincidenceBundle where
  circle_fill := countableCircleFillBundle
  log_exp_bridge := logExpTrigReadoutBridge
  coincidence_grid_injective := encode_prime_shell_slot_injective
  conj_duality := linePhase_conj_is_zero_oscillation
  cpow_prime_factor := cpow_at_prime_eq_sqrt_times_conj_linePhase
  slot_conj_duality := shell_slot_prime_conj_zero_oscillation
  two_primes_pin := coincidence_cell_angle_pinned_by_two_primes
  euler_axis := eulerPrimeCircleCountingAxis

/-!
## Status

* **Unconditional:** `conj (linePhase p θ) = exp(i θ log p)`; same law at every
  shell slot and encoded `(prime, slot)` cell; explicit-formula power at prime
  scale factors through the conjugate phase; countable coincidence grid; two
  primes pin the circle angle; prime log twiddle / zero oscillation share the
  `exp(i·)` carrier via `LogExpTrigReadoutBridge`.
* **Conditional:** `ζ(s)=0` at slot angle ↔ harmonic-shell balance ↔ prime
  twiddle vanishes under `RollingZetaIdentificationAtCriticalLine`.
* **Not claimed:** that known ζ-zeros occur at rational shell angles, or that
  phase coincidence alone locates zeros without the rolling bridge.
-/

end

end Hqiv.Story

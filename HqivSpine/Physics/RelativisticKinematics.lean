import HqivSpine.Physics.HadronDecayWidths
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# `HqivSpine.Physics.RelativisticKinematics` — two-body decay kinematics and the Breit–Wigner resonance

The HEP working toolkit, upgrading `HadronDecayWidths`'s crude non-relativistic release
`Q = M − ∑mᵢ` to the **relativistic invariants** every collider physicist computes, and adding the
**Breit–Wigner resonance lineshape**. Purely algebraic; no PDG number, no external coupling.

* **Källén triangle function.** `λ(a,b,c) = a²+b²+c² − 2(ab+bc+ca)` factorises on the physical
  masses as `λ(M²,m₁²,m₂²) = (M²−(m₁+m₂)²)(M²−(m₁−m₂)²)` (`kallen_factor`), so it is `≥ 0` exactly at
  and above the two-body threshold (`kallen_nonneg_of_threshold`).
* **Centre-of-mass momentum.** `p* = √λ(M²,m₁²,m₂²)/(2M)` is real and strictly positive once the
  channel is open (`pStar_pos`), and reduces to `√(M²−4m²)/2` for equal masses (`pStar_equal_masses`)
  and `M/2` for massless daughters (`pStar_massless`).
* **Daughter energies.** `E₁* = (M²+m₁²−m₂²)/2M`, `E₂* = (M²+m₂²−m₁²)/2M` conserve energy in the
  rest frame, `E₁*+E₂* = M` (`energy_conservation`), and satisfy the on-shell relation
  `E₁*² − p*² = m₁²` (`daughter1_onShell`) — relativistic four-momentum conservation, derived.
* **Breit–Wigner.** The relativistic lineshape `BW(s) = 1/((s−M²)²+M²Γ²)` peaks at the resonance
  `s = M²` with height `1/(M²Γ²)` (`breitWigner_peak`, `breitWigner_le_peak`) and drops to half-maximum
  at `s = M² ± MΓ` (`breitWigner_halfMax`) — i.e. a full width `MΓ` in `s`.
* **Bridge.** An open crude channel (`HadronDecayWidths.decayQ > 0`) gives a positive relativistic
  momentum (`pStar_pos_of_decayAllowed`).

Bundled in `RelativisticKinematicsClosure` / `relativistic_kinematics_closure`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.RelativisticKinematics

open HqivSpine.Physics

/-! ## Källén triangle function -/

/-- **Källén triangle function** `λ(a,b,c) = a²+b²+c² − 2(ab+bc+ca)`. -/
def kallen (a b c : ℝ) : ℝ := a ^ 2 + b ^ 2 + c ^ 2 - 2 * (a * b + b * c + c * a)

/-- **Källén factorisation** on physical masses:
`λ(M²,m₁²,m₂²) = (M²−(m₁+m₂)²)(M²−(m₁−m₂)²)`. -/
theorem kallen_factor (M m1 m2 : ℝ) :
    kallen (M ^ 2) (m1 ^ 2) (m2 ^ 2) = (M ^ 2 - (m1 + m2) ^ 2) * (M ^ 2 - (m1 - m2) ^ 2) := by
  unfold kallen; ring

/-- The Källén function is symmetric in its first two physical masses. -/
theorem kallen_symm_masses (M m1 m2 : ℝ) :
    kallen (M ^ 2) (m1 ^ 2) (m2 ^ 2) = kallen (M ^ 2) (m2 ^ 2) (m1 ^ 2) := by
  unfold kallen; ring

/-- **At/above threshold the Källén function is non-negative.** -/
theorem kallen_nonneg_of_threshold {M m1 m2 : ℝ} (hM : 0 ≤ M) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    (hthr : m1 + m2 ≤ M) : 0 ≤ kallen (M ^ 2) (m1 ^ 2) (m2 ^ 2) := by
  rw [kallen_factor]
  have h1 : 0 ≤ M ^ 2 - (m1 + m2) ^ 2 := by nlinarith [hthr, hm1, hm2, hM]
  have h2 : 0 ≤ M ^ 2 - (m1 - m2) ^ 2 := by nlinarith [hthr, hm1, hm2, hM, mul_nonneg hm1 hm2]
  exact mul_nonneg h1 h2

/-! ## Centre-of-mass momentum -/

/-- **Daughter centre-of-mass momentum** `p* = √λ(M²,m₁²,m₂²)/(2M)`. -/
noncomputable def pStar (M m1 m2 : ℝ) : ℝ := Real.sqrt (kallen (M ^ 2) (m1 ^ 2) (m2 ^ 2)) / (2 * M)

/-- **An open channel has a positive momentum.** -/
theorem pStar_pos {M m1 m2 : ℝ} (hM : 0 < M) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2) (hthr : m1 + m2 < M) :
    0 < pStar M m1 m2 := by
  unfold pStar
  apply div_pos _ (by linarith : (0 : ℝ) < 2 * M)
  rw [Real.sqrt_pos, kallen_factor]
  have h1 : 0 < M ^ 2 - (m1 + m2) ^ 2 := by nlinarith [hthr, hm1, hm2, hM]
  have h2 : 0 < M ^ 2 - (m1 - m2) ^ 2 := by nlinarith [hthr, hm1, hm2, hM, mul_nonneg hm1 hm2]
  exact mul_pos h1 h2

/-- **Equal-mass daughters:** `p* = √(M²−4m²)/2`. -/
theorem pStar_equal_masses {M m : ℝ} (hM : 0 < M) :
    pStar M m m = Real.sqrt (M ^ 2 - 4 * m ^ 2) / 2 := by
  unfold pStar
  rw [show kallen (M ^ 2) (m ^ 2) (m ^ 2) = M ^ 2 * (M ^ 2 - 4 * m ^ 2) by unfold kallen; ring,
    Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM.le, mul_comm (2 : ℝ) M,
    mul_div_mul_left _ _ hM.ne']

/-- **Massless daughters** (e.g. a two-photon decay): `p* = M/2`. -/
theorem pStar_massless {M : ℝ} (hM : 0 < M) : pStar M 0 0 = M / 2 := by
  unfold pStar
  rw [show kallen (M ^ 2) ((0 : ℝ) ^ 2) ((0 : ℝ) ^ 2) = (M ^ 2) ^ 2 by unfold kallen; ring,
    Real.sqrt_sq (by positivity), pow_two, mul_comm (2 : ℝ) M, mul_div_mul_left _ _ hM.ne']

/-! ## Daughter energies and on-shell relation -/

/-- **First daughter rest-frame energy** `E₁* = (M²+m₁²−m₂²)/2M`. -/
noncomputable def daughterEnergy1 (M m1 m2 : ℝ) : ℝ := (M ^ 2 + m1 ^ 2 - m2 ^ 2) / (2 * M)

/-- **Second daughter rest-frame energy** `E₂* = (M²+m₂²−m₁²)/2M`. -/
noncomputable def daughterEnergy2 (M m1 m2 : ℝ) : ℝ := (M ^ 2 + m2 ^ 2 - m1 ^ 2) / (2 * M)

/-- **Energy conservation in the rest frame:** `E₁* + E₂* = M`. -/
theorem energy_conservation {M : ℝ} (m1 m2 : ℝ) (hM : M ≠ 0) :
    daughterEnergy1 M m1 m2 + daughterEnergy2 M m1 m2 = M := by
  unfold daughterEnergy1 daughterEnergy2
  field_simp
  ring

/-- **On-shell relation** for the first daughter: `E₁*² − p*² = m₁²`, i.e. relativistic
four-momentum conservation holds with the derived energy and momentum. -/
theorem daughter1_onShell {M m1 m2 : ℝ} (hM : 0 < M) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    (hthr : m1 + m2 ≤ M) :
    daughterEnergy1 M m1 m2 ^ 2 - pStar M m1 m2 ^ 2 = m1 ^ 2 := by
  have hk : 0 ≤ kallen (M ^ 2) (m1 ^ 2) (m2 ^ 2) := kallen_nonneg_of_threshold hM.le hm1 hm2 hthr
  have h2M : (0 : ℝ) < 2 * M := by linarith
  unfold daughterEnergy1 pStar
  rw [div_pow, div_pow, Real.sq_sqrt hk, div_sub_div_same,
    div_eq_iff (pow_ne_zero 2 h2M.ne')]
  unfold kallen; ring

/-- **On-shell relation** for the second daughter: `E₂*² − p*² = m₂²`. -/
theorem daughter2_onShell {M m1 m2 : ℝ} (hM : 0 < M) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    (hthr : m1 + m2 ≤ M) :
    daughterEnergy2 M m1 m2 ^ 2 - pStar M m1 m2 ^ 2 = m2 ^ 2 := by
  have hk : 0 ≤ kallen (M ^ 2) (m1 ^ 2) (m2 ^ 2) := kallen_nonneg_of_threshold hM.le hm1 hm2 hthr
  have h2M : (0 : ℝ) < 2 * M := by linarith
  unfold daughterEnergy2 pStar
  rw [div_pow, div_pow, Real.sq_sqrt hk, div_sub_div_same,
    div_eq_iff (pow_ne_zero 2 h2M.ne')]
  unfold kallen; ring

/-! ## Breit–Wigner resonance lineshape -/

/-- **Relativistic Breit–Wigner lineshape** `BW(s) = 1/((s−M²)²+M²Γ²)` (up to the overall constant). -/
noncomputable def breitWigner (s M Γ : ℝ) : ℝ := 1 / ((s - M ^ 2) ^ 2 + M ^ 2 * Γ ^ 2)

/-- The denominator is strictly positive away from a zero-width, zero-mass degenerate case. -/
theorem breitWigner_denom_pos {M Γ : ℝ} (hM : M ≠ 0) (hΓ : Γ ≠ 0) (s : ℝ) :
    0 < (s - M ^ 2) ^ 2 + M ^ 2 * Γ ^ 2 := by
  have hMΓ : 0 < M ^ 2 * Γ ^ 2 := by
    rw [sq, sq]; exact mul_pos (mul_self_pos.mpr hM) (mul_self_pos.mpr hΓ)
  nlinarith [sq_nonneg (s - M ^ 2), hMΓ]

theorem breitWigner_pos {M Γ : ℝ} (hM : M ≠ 0) (hΓ : Γ ≠ 0) (s : ℝ) : 0 < breitWigner s M Γ := by
  unfold breitWigner
  exact one_div_pos.mpr (breitWigner_denom_pos hM hΓ s)

/-- **Resonance peak value** at `s = M²` is `1/(M²Γ²)`. -/
theorem breitWigner_peak (M Γ : ℝ) : breitWigner (M ^ 2) M Γ = 1 / (M ^ 2 * Γ ^ 2) := by
  unfold breitWigner; congr 1; ring

/-- **The lineshape is maximised at the resonance** `s = M²`. -/
theorem breitWigner_le_peak {M Γ : ℝ} (hM : M ≠ 0) (hΓ : Γ ≠ 0) (s : ℝ) :
    breitWigner s M Γ ≤ breitWigner (M ^ 2) M Γ := by
  unfold breitWigner
  have hMΓ : 0 < M ^ 2 * Γ ^ 2 := by
    rw [sq, sq]; exact mul_pos (mul_self_pos.mpr hM) (mul_self_pos.mpr hΓ)
  rw [show (M ^ 2 - M ^ 2) ^ 2 + M ^ 2 * Γ ^ 2 = M ^ 2 * Γ ^ 2 by ring]
  exact one_div_le_one_div_of_le hMΓ (by nlinarith [sq_nonneg (s - M ^ 2)])

/-- **Off resonance is strictly below the peak.** -/
theorem breitWigner_lt_peak_of_ne {M Γ : ℝ} (hM : M ≠ 0) (hΓ : Γ ≠ 0) {s : ℝ} (hs : s ≠ M ^ 2) :
    breitWigner s M Γ < breitWigner (M ^ 2) M Γ := by
  unfold breitWigner
  have hMΓ : 0 < M ^ 2 * Γ ^ 2 := by
    rw [sq, sq]; exact mul_pos (mul_self_pos.mpr hM) (mul_self_pos.mpr hΓ)
  have hsq : 0 < (s - M ^ 2) ^ 2 := by
    rw [pow_two]; exact mul_self_pos.mpr (sub_ne_zero.mpr hs)
  rw [show (M ^ 2 - M ^ 2) ^ 2 + M ^ 2 * Γ ^ 2 = M ^ 2 * Γ ^ 2 by ring]
  exact one_div_lt_one_div_of_lt hMΓ (by nlinarith [hsq])

/-- **Half-maximum at `s = M² + MΓ`** — the full width is `MΓ` in `s`. -/
theorem breitWigner_halfMax (M Γ : ℝ) :
    breitWigner (M ^ 2 + M * Γ) M Γ = breitWigner (M ^ 2) M Γ / 2 := by
  unfold breitWigner
  rw [show ((M ^ 2 + M * Γ) - M ^ 2) ^ 2 + M ^ 2 * Γ ^ 2 = 2 * (M ^ 2 * Γ ^ 2) by ring,
    show (M ^ 2 - M ^ 2) ^ 2 + M ^ 2 * Γ ^ 2 = M ^ 2 * Γ ^ 2 by ring, div_div]
  congr 1
  ring

/-- **Half-maximum at `s = M² − MΓ`** (the lower half-power point). -/
theorem breitWigner_halfMax_lower (M Γ : ℝ) :
    breitWigner (M ^ 2 - M * Γ) M Γ = breitWigner (M ^ 2) M Γ / 2 := by
  unfold breitWigner
  rw [show ((M ^ 2 - M * Γ) - M ^ 2) ^ 2 + M ^ 2 * Γ ^ 2 = 2 * (M ^ 2 * Γ ^ 2) by ring,
    show (M ^ 2 - M ^ 2) ^ 2 + M ^ 2 * Γ ^ 2 = M ^ 2 * Γ ^ 2 by ring, div_div]
  congr 1
  ring

/-! ## Bridge to the crude phase-space threshold -/

/-- **An open crude channel implies a positive relativistic momentum:** if the `HadronDecayWidths`
`Q`-value is positive, the relativistic centre-of-mass momentum is real and strictly positive. -/
theorem pStar_pos_of_decayAllowed {M m1 m2 : ℝ} (hM : 0 < M) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    (h : 0 < HadronDecayWidths.decayQ M (m1 + m2)) : 0 < pStar M m1 m2 :=
  pStar_pos hM hm1 hm2 ((HadronDecayWidths.decayAllowed_iff M (m1 + m2)).mp h)

/-! ## Closure -/

/-- **Relativistic-kinematics discharge bundle.** -/
structure RelativisticKinematicsClosure : Prop where
  kallen_factored : ∀ M m1 m2 : ℝ,
    kallen (M ^ 2) (m1 ^ 2) (m2 ^ 2) = (M ^ 2 - (m1 + m2) ^ 2) * (M ^ 2 - (m1 - m2) ^ 2)
  threshold_nonneg : ∀ {M m1 m2 : ℝ}, 0 ≤ M → 0 ≤ m1 → 0 ≤ m2 → m1 + m2 ≤ M →
    0 ≤ kallen (M ^ 2) (m1 ^ 2) (m2 ^ 2)
  momentum_pos : ∀ {M m1 m2 : ℝ}, 0 < M → 0 ≤ m1 → 0 ≤ m2 → m1 + m2 < M → 0 < pStar M m1 m2
  energy_conservation : ∀ {M : ℝ} (m1 m2 : ℝ), M ≠ 0 →
    daughterEnergy1 M m1 m2 + daughterEnergy2 M m1 m2 = M
  on_shell : ∀ {M m1 m2 : ℝ}, 0 < M → 0 ≤ m1 → 0 ≤ m2 → m1 + m2 ≤ M →
    daughterEnergy1 M m1 m2 ^ 2 - pStar M m1 m2 ^ 2 = m1 ^ 2
  resonance_peak : ∀ M Γ : ℝ, breitWigner (M ^ 2) M Γ = 1 / (M ^ 2 * Γ ^ 2)
  resonance_max : ∀ {M Γ : ℝ}, M ≠ 0 → Γ ≠ 0 → ∀ s : ℝ,
    breitWigner s M Γ ≤ breitWigner (M ^ 2) M Γ
  resonance_halfMax : ∀ M Γ : ℝ, breitWigner (M ^ 2 + M * Γ) M Γ = breitWigner (M ^ 2) M Γ / 2

/-- **The relativistic-kinematics story is discharged:** the Källén function factorises and is
non-negative at threshold, the centre-of-mass momentum is positive on an open channel, the daughter
energies conserve energy and are on-shell, and the Breit–Wigner lineshape peaks at the resonance with
a half-power full width `MΓ` — all PDG-free. -/
theorem relativistic_kinematics_closure : RelativisticKinematicsClosure where
  kallen_factored := kallen_factor
  threshold_nonneg := kallen_nonneg_of_threshold
  momentum_pos := pStar_pos
  energy_conservation := energy_conservation
  on_shell := daughter1_onShell
  resonance_peak := breitWigner_peak
  resonance_max := breitWigner_le_peak
  resonance_halfMax := breitWigner_halfMax

end HqivSpine.Physics.RelativisticKinematics

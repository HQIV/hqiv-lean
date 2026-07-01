import HqivSpine.Physics.GravitationalLensing

/-!
# `HqivSpine.Physics.EinsteinRing` — the Einstein radius from the deflection

When source, lens and observer align, the bent rays close into a ring of angular radius `θ_E`. With
the lattice coupling `G_eff(φ) = φ^α` and the lens geometry factor `κ = D_ls/(D_l·D_s)`, the squared
ring radius is `θ_E² = 4·G_eff(φ)·M·κ` — the lensing deflection folded with the geometric baseline.

* **Deflection bridge.** `θ_E² = δ(φ,M,b)·(b·κ)` for any `b ≠ 0` (`einsteinRadiusSq_eq_deflection`):
  the ring is the deflection times the baseline, no new coupling.
* **Positive, `√M` law.** The radius is positive (`einsteinRadius_pos`), squares back to `θ_E²`
  (`einsteinRadius_sq`), and grows with the lens mass (`einsteinRadius_strictMono_in_M`) — the
  characteristic `θ_E ∝ √M` scaling.

Bundled in `EinsteinRingClosure` / `einstein_ring_closure`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.EinsteinRing

open HqivSpine.Physics HqivSpine.Physics.GravitationalLensing

/-- **Squared Einstein radius** `θ_E² = 4·G_eff(φ)·M·κ` (`κ = D_ls/(D_l·D_s)` the lens geometry). -/
noncomputable def einsteinRadiusSq (φ M κ : ℝ) : ℝ := 4 * gEff φ * M * κ

/-- **Einstein radius** `θ_E = √(θ_E²)`. -/
noncomputable def einsteinRadius (φ M κ : ℝ) : ℝ := Real.sqrt (einsteinRadiusSq φ M κ)

theorem einsteinRadiusSq_pos {φ M κ : ℝ} (hφ : 0 < φ) (hM : 0 < M) (hκ : 0 < κ) :
    0 < einsteinRadiusSq φ M κ := by
  unfold einsteinRadiusSq
  have hG : 0 < gEff φ := gEff_pos hφ
  positivity

/-- **The ring is the deflection folded with the geometric baseline.** -/
theorem einsteinRadiusSq_eq_deflection (φ M κ b : ℝ) (hb : b ≠ 0) :
    einsteinRadiusSq φ M κ = einsteinDeflection φ M b * (b * κ) := by
  unfold einsteinRadiusSq einsteinDeflection
  field_simp

theorem einsteinRadius_pos {φ M κ : ℝ} (hφ : 0 < φ) (hM : 0 < M) (hκ : 0 < κ) :
    0 < einsteinRadius φ M κ :=
  Real.sqrt_pos.mpr (einsteinRadiusSq_pos hφ hM hκ)

/-- The radius squares back to `θ_E²`. -/
theorem einsteinRadius_sq {φ M κ : ℝ} (hφ : 0 < φ) (hM : 0 < M) (hκ : 0 < κ) :
    (einsteinRadius φ M κ) ^ 2 = einsteinRadiusSq φ M κ := by
  unfold einsteinRadius
  rw [Real.sq_sqrt (le_of_lt (einsteinRadiusSq_pos hφ hM hκ))]

/-- **The `θ_E ∝ √M` law:** the ring grows strictly with the lens mass. -/
theorem einsteinRadius_strictMono_in_M {φ κ : ℝ} (hφ : 0 < φ) (hκ : 0 < κ) {M M' : ℝ}
    (hM : 0 < M) (h : M < M') : einsteinRadius φ M κ < einsteinRadius φ M' κ := by
  unfold einsteinRadius
  apply Real.sqrt_lt_sqrt (le_of_lt (einsteinRadiusSq_pos hφ hM hκ))
  unfold einsteinRadiusSq
  have hG : 0 < gEff φ := gEff_pos hφ
  have hc : 0 < 4 * gEff φ * κ := by positivity
  rw [show 4 * gEff φ * M * κ = (4 * gEff φ * κ) * M from by ring,
      show 4 * gEff φ * M' * κ = (4 * gEff φ * κ) * M' from by ring]
  exact mul_lt_mul_of_pos_left h hc

/-! ## Closure -/

/-- **Einstein-ring discharge bundle.** -/
structure EinsteinRingClosure : Prop where
  deflection_bridge : ∀ (φ M κ b : ℝ), b ≠ 0 →
    einsteinRadiusSq φ M κ = einsteinDeflection φ M b * (b * κ)
  radius_sq : ∀ {φ M κ : ℝ}, 0 < φ → 0 < M → 0 < κ →
    (einsteinRadius φ M κ) ^ 2 = einsteinRadiusSq φ M κ
  mass_increasing : ∀ {φ κ : ℝ}, 0 < φ → 0 < κ → ∀ {M M' : ℝ}, 0 < M → M < M' →
    einsteinRadius φ M κ < einsteinRadius φ M' κ

/-- **The Einstein ring is discharged:** a positive `√M`-scaling ring radius that is the lensing
deflection folded with the lens geometry, off the same lattice coupling `G_eff`. -/
theorem einstein_ring_closure : EinsteinRingClosure where
  deflection_bridge := einsteinRadiusSq_eq_deflection
  radius_sq := einsteinRadius_sq
  mass_increasing := einsteinRadius_strictMono_in_M

end HqivSpine.Physics.EinsteinRing

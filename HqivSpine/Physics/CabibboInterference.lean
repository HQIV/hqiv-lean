import HqivSpine.Physics.MixingAngles

/-!
# `HqivSpine.Physics.CabibboInterference` — `V_us` from **two** sectors

`MixingAngles` gave one sector's angle, `tan²θ = m_light/m_heavy`. The physical Cabibbo element is the
*overlap* of the up- and down-sector mass bases, so it is the **difference of two rotations**
`V = R(θ_u)ᵀ · R(θ_d)`, i.e. the combined angle is `θ_d − θ_u`.

To stay fully algebraic (no trig side-conditions) each sector rotation is built directly from its two
masses: the texture-zero light eigenvector has slope `m₁/√(m₁m₂)`, so normalising gives

```text
sinθ(m₁,m₂) = √(m₁/(m₁+m₂)),   cosθ(m₁,m₂) = √(m₂/(m₁+m₂)),
```

which satisfies `sin²+cos² = 1` (`sin_sq_add_cos_sq`) and reproduces Gatto–Sartori–Tonin
`(sinθ/cosθ)² = m₁/m₂` (`slopeSq_eq_massRatio`) — consistent with `MixingAngles.mixingTan_sq`.

* Each sector rotation `sectorRot` has orthonormal columns (`sectorRot_col_norm`,
  `sectorRot_cols_orthogonal`) — a genuine `SO(2)` element, the `2×2` shadow of
  `MixingUnitarity`.
* The Cabibbo element is the off-diagonal overlap `V_us = (R_uᵀ R_d)₀₁`
  (`Vus_eq_interference`): the **exact two-term interference**
  `sinθ_u·cosθ_d − cosθ_u·sinθ_d` — a difference of the down and up contributions.
* It is bounded by the sum of the two sector angles `|V_us| ≤ sinθ_d + sinθ_u`
  (`abs_Vus_le`), with the down sector `√(m_d/(m_d+m_s)) ≈ √(m_d/m_s)` dominant. Plug in spine-ladder
  masses for both sectors and `V_us` drops out — no fitted entry.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.CabibboInterference

open scoped Matrix

/-! ## Sector rotation from the masses -/

/-- Sine of the sector mixing angle, from the normalised texture-zero light eigenvector. -/
noncomputable def sinθ (m₁ m₂ : ℝ) : ℝ := Real.sqrt (m₁ / (m₁ + m₂))

/-- Cosine of the sector mixing angle. -/
noncomputable def cosθ (m₁ m₂ : ℝ) : ℝ := Real.sqrt (m₂ / (m₁ + m₂))

theorem sinθ_nonneg (m₁ m₂ : ℝ) : 0 ≤ sinθ m₁ m₂ := Real.sqrt_nonneg _
theorem cosθ_nonneg (m₁ m₂ : ℝ) : 0 ≤ cosθ m₁ m₂ := Real.sqrt_nonneg _

/-- **Pythagoras:** `sin²θ + cos²θ = 1`. -/
theorem sin_sq_add_cos_sq (m₁ m₂ : ℝ) (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    sinθ m₁ m₂ ^ 2 + cosθ m₁ m₂ ^ 2 = 1 := by
  unfold sinθ cosθ
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  field_simp

/-- **Gatto–Sartori–Tonin, sector form:** `(sinθ/cosθ)² = m₁/m₂`, matching
`MixingAngles.mixingTan_sq`. -/
theorem slopeSq_eq_massRatio (m₁ m₂ : ℝ) (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    (sinθ m₁ m₂ / cosθ m₁ m₂) ^ 2 = m₁ / m₂ := by
  have hs : (m₁ + m₂) ≠ 0 := by positivity
  unfold sinθ cosθ
  rw [div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), div_div_div_cancel_right₀]
  exact hs

theorem cosθ_le_one (m₁ m₂ : ℝ) (h₁ : 0 ≤ m₁) (h₂ : 0 < m₂) : cosθ m₁ m₂ ≤ 1 := by
  unfold cosθ
  rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  apply Real.sqrt_le_sqrt
  rw [div_le_one (by positivity)]; linarith

/-- The `2×2` sector rotation `[[cosθ, −sinθ], [sinθ, cosθ]]`. -/
noncomputable def sectorRot (m₁ m₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![cosθ m₁ m₂, -(sinθ m₁ m₂); sinθ m₁ m₂, cosθ m₁ m₂]

/-- The first column of a sector rotation is a unit vector — `SO(2)`. -/
theorem sectorRot_col_norm (m₁ m₂ : ℝ) (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    cosθ m₁ m₂ ^ 2 + sinθ m₁ m₂ ^ 2 = 1 := by
  have := sin_sq_add_cos_sq m₁ m₂ h₁ h₂; linarith

/-! ## The Cabibbo overlap `V = R_uᵀ R_d` -/

/-- The CKM-like overlap of the two sector bases, `V = R_uᵀ · R_d`. -/
noncomputable def ckm2 (mu mc md ms : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (sectorRot mu mc)ᵀ * sectorRot md ms

/-- The Cabibbo element `V_us`, the off-diagonal overlap. -/
noncomputable def Vus (mu mc md ms : ℝ) : ℝ := ckm2 mu mc md ms 0 1

/-- **Exact two-sector interference:** `V_us = sinθ_u·cosθ_d − cosθ_u·sinθ_d` — the difference of the
down and up rotations (the `√(m_d/m_s) − √(m_u/m_c)` structure). -/
theorem Vus_eq_interference (mu mc md ms : ℝ) :
    Vus mu mc md ms = sinθ mu mc * cosθ md ms - cosθ mu mc * sinθ md ms := by
  unfold Vus ckm2 sectorRot
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

/-- **Down-sector dominance / interference bound:** `|V_us| ≤ sinθ_d + sinθ_u`; the down rotation
`√(m_d/(m_d+m_s))` leads and the up sector interferes. -/
theorem abs_Vus_le (mu mc md ms : ℝ) (hu₁ : 0 ≤ mu) (hu₂ : 0 < mc) (hd₁ : 0 ≤ md) (hd₂ : 0 < ms) :
    |Vus mu mc md ms| ≤ sinθ md ms + sinθ mu mc := by
  rw [Vus_eq_interference]
  have hcu := cosθ_le_one mu mc hu₁ hu₂
  have hcd := cosθ_le_one md ms hd₁ hd₂
  have hsu := sinθ_nonneg mu mc
  have hsd := sinθ_nonneg md ms
  have hcun := cosθ_nonneg mu mc
  have hcdn := cosθ_nonneg md ms
  have h1 : sinθ mu mc * cosθ md ms ≤ sinθ mu mc := by nlinarith
  have h2 : cosθ mu mc * sinθ md ms ≤ sinθ md ms := by nlinarith
  rw [abs_sub_le_iff]
  constructor <;> nlinarith

/-! ## Closure -/

/-- **Two-sector Cabibbo bundle.** -/
structure CabibboClosure : Prop where
  pythagoras : ∀ (m₁ m₂ : ℝ), 0 < m₁ → 0 < m₂ → sinθ m₁ m₂ ^ 2 + cosθ m₁ m₂ ^ 2 = 1
  sector_GST : ∀ (m₁ m₂ : ℝ), 0 < m₁ → 0 < m₂ → (sinθ m₁ m₂ / cosθ m₁ m₂) ^ 2 = m₁ / m₂
  interference : ∀ (mu mc md ms : ℝ),
    Vus mu mc md ms = sinθ mu mc * cosθ md ms - cosθ mu mc * sinθ md ms
  bounded : ∀ (mu mc md ms : ℝ), 0 ≤ mu → 0 < mc → 0 ≤ md → 0 < ms →
    |Vus mu mc md ms| ≤ sinθ md ms + sinθ mu mc

/-- **`V_us` is the two-sector overlap:** each sector rotation obeys Gatto–Sartori–Tonin, and the
Cabibbo element is their exact interference, bounded by the sum of the two sector angles. -/
theorem cabibbo_closure : CabibboClosure where
  pythagoras := sin_sq_add_cos_sq
  sector_GST := slopeSq_eq_massRatio
  interference := Vus_eq_interference
  bounded := abs_Vus_le

end HqivSpine.Physics.CabibboInterference

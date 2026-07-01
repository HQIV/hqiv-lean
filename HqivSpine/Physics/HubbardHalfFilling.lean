import HqivSpine.Physics.Shell
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.HubbardHalfFilling` — the half-filled Hubbard dimer and superexchange

The canonical two-site Hubbard model at half filling (one electron per site), the **charge-sector**
companion of `Physics.HubbardDimer`'s spin toy. Mined from the legacy
`Hqiv.QuantumMechanics.HubbardDimerHalfFilledObservables` and disentangled to a single explicit
Hermitian `4×4`, Mathlib-only.

In the four-state basis `(|↑↓,0⟩, |0,↑↓⟩, |↑,↓⟩, |↓,↑⟩)` the Hamiltonian couples the two
doubly-occupied (charge) states to the two singly-occupied (spin) states by hopping `t`, with on-site
Hubbard repulsion `U` on the doubly-occupied states:

```
H(t,U) = ⎡  U   0  −t   t ⎤
         ⎢  0   U  −t   t ⎥
         ⎢ −t  −t   0   0 ⎥
         ⎣  t   t   0   0 ⎦
```

It is **exactly solvable**, with the textbook spectrum `{0, U, (U ± √(U²+16t²))/2}`:

* the **spin triplet** `|↑,↓⟩ + |↓,↑⟩` is a zero mode (`eigen_triplet`, `S = 1`, energy `0`);
* the **antisymmetric charge** state `|↑↓,0⟩ − |0,↑↓⟩` has energy `U` (`eigen_chargeAsym`);
* the two **singlets** `(E,E,−2t,2t)` with `E = (U ± √(U²+16t²))/2` (`eigen_ground`, `eigen_excited`
  via the secular lemma `eigen_secular`, `E² = UE + 4t²`).

The ground state is the lower singlet `E₀ = (U − √(U²+16t²))/2 ≤ 0`, below every level
(`groundEnergy_le_zero/_U/_excited`). The **singlet–triplet gap** `J = −E₀ = (√(U²+16t²) − U)/2`
(`exchangeJ`) is the antiferromagnetic **superexchange**: it equals `8t²/(U + √(U²+16t²))`
(`exchangeJ_eq`) and, in the Mott regime `U > 0`, obeys the Anderson scaling
`J ≤ 4t²/U` (`superexchange_le`) — virtual hopping through the doubly-occupied state lowers the
singlet. The repulsion is **shell-anchored** `U(m) = U₀·φ(m)/φ(referenceM)` (`Ushell_referenceM`).

Honest scope: a finite four-state model — the dimer spectrum, gap, and superexchange bound, not the
thermodynamic-limit Hubbard model or the Mott transition. Mathlib + spine `Physics.Shell` only;
no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Physics.HubbardHalfFilling

open Matrix

/-- Half-filled Hubbard dimer Hamiltonian on `ℂ⁴` in the basis `(|↑↓,0⟩,|0,↑↓⟩,|↑,↓⟩,|↓,↑⟩)`. -/
noncomputable def H (t U : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(U : ℂ), 0, -(t : ℂ), (t : ℂ);
     0, (U : ℂ), -(t : ℂ), (t : ℂ);
     -(t : ℂ), -(t : ℂ), 0, 0;
     (t : ℂ), (t : ℂ), 0, 0]

/-- The half-filled Hamiltonian is Hermitian. -/
theorem H_isHermitian (t U : ℝ) : (H t U).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H, Matrix.conjTranspose_apply, Complex.conj_ofReal]

/-! ## Shell-anchored Hubbard repulsion -/

/-- Shell-coupled on-site repulsion, normalised at the lock-in shell `referenceM = 4`:
`U(m) = U₀·φ(m)/φ(referenceM)`. -/
noncomputable def Ushell (m : ℕ) (U0 : ℝ := 1) : ℝ :=
  U0 * ((phi m : ℝ) / (phi referenceM : ℝ))

theorem Ushell_eq (m : ℕ) (U0 : ℝ) : Ushell m U0 = U0 * ((m + 1) / 5) := by
  unfold Ushell phi referenceM; push_cast; ring

theorem Ushell_referenceM (U0 : ℝ) : Ushell referenceM U0 = U0 := by
  rw [Ushell_eq]; norm_num [referenceM]

/-! ## Hopping- and U-independent eigenpairs (triplet and antisymmetric charge) -/

/-- The **spin triplet** `|↑,↓⟩ + |↓,↑⟩` is a zero-energy eigenstate. -/
theorem eigen_triplet (t U : ℝ) :
    (H t U).mulVec ![0, 0, 1, 1] = (0 : ℂ) • ![0, 0, 1, 1] := by
  funext i
  fin_cases i <;>
    simp [H, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- The **antisymmetric charge** state `|↑↓,0⟩ − |0,↑↓⟩` has energy `U`. -/
theorem eigen_chargeAsym (t U : ℝ) :
    (H t U).mulVec ![1, -1, 0, 0] = (U : ℂ) • ![1, -1, 0, 0] := by
  funext i
  fin_cases i <;>
    simp [H, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-! ## The two singlets via the secular equation `E² = UE + 4t²` -/

/-- **Secular eigenpair.** For any `E` with `E² = U·E + 4t²`, the singlet `(E, E, −2t, 2t)` is an
eigenvector of `H` with eigenvalue `E`. Specialising `E = (U ± √(U²+16t²))/2` gives both singlets. -/
theorem eigen_secular {t U E : ℝ} (hE : (E : ℂ) ^ 2 = (U : ℂ) * (E : ℂ) + 4 * (t : ℂ) ^ 2) :
    (H t U).mulVec ![(E : ℂ), (E : ℂ), -2 * (t : ℂ), 2 * (t : ℂ)]
      = (E : ℂ) • ![(E : ℂ), (E : ℂ), -2 * (t : ℂ), 2 * (t : ℂ)] := by
  funext i
  fin_cases i
  · simp [H, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul]
    linear_combination -hE
  · simp [H, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul]
    linear_combination -hE
  · simp [H, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul]; ring
  · simp [H, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul]; ring

/-! ## Ground-state energy, spectrum ordering, and the gap -/

/-- Ground-state energy `E₀ = (U − √(U²+16t²))/2`. -/
noncomputable def groundEnergy (t U : ℝ) : ℝ := (U - Real.sqrt (U ^ 2 + 16 * t ^ 2)) / 2

/-- Upper singlet energy `E₊ = (U + √(U²+16t²))/2`. -/
noncomputable def excitedEnergy (t U : ℝ) : ℝ := (U + Real.sqrt (U ^ 2 + 16 * t ^ 2)) / 2

/-- Both singlet energies solve the secular equation `E² = U·E + 4t²`. -/
theorem groundEnergy_secular (t U : ℝ) :
    (groundEnergy t U) ^ 2 = U * groundEnergy t U + 4 * t ^ 2 := by
  have hD : Real.sqrt (U ^ 2 + 16 * t ^ 2) ^ 2 = U ^ 2 + 16 * t ^ 2 :=
    Real.sq_sqrt (by positivity)
  unfold groundEnergy; linear_combination (1 / 4) * hD

theorem excitedEnergy_secular (t U : ℝ) :
    (excitedEnergy t U) ^ 2 = U * excitedEnergy t U + 4 * t ^ 2 := by
  have hD : Real.sqrt (U ^ 2 + 16 * t ^ 2) ^ 2 = U ^ 2 + 16 * t ^ 2 :=
    Real.sq_sqrt (by positivity)
  unfold excitedEnergy; linear_combination (1 / 4) * hD

/-- **Ground singlet eigenpair** at `E₀ = (U − √(U²+16t²))/2`. -/
theorem eigen_ground (t U : ℝ) :
    (H t U).mulVec ![(groundEnergy t U : ℂ), (groundEnergy t U : ℂ), -2 * (t : ℂ), 2 * (t : ℂ)]
      = (groundEnergy t U : ℂ) •
          ![(groundEnergy t U : ℂ), (groundEnergy t U : ℂ), -2 * (t : ℂ), 2 * (t : ℂ)] :=
  eigen_secular (by exact_mod_cast groundEnergy_secular t U)

/-- **Excited singlet eigenpair** at `E₊ = (U + √(U²+16t²))/2`. -/
theorem eigen_excited (t U : ℝ) :
    (H t U).mulVec ![(excitedEnergy t U : ℂ), (excitedEnergy t U : ℂ), -2 * (t : ℂ), 2 * (t : ℂ)]
      = (excitedEnergy t U : ℂ) •
          ![(excitedEnergy t U : ℂ), (excitedEnergy t U : ℂ), -2 * (t : ℂ), 2 * (t : ℂ)] :=
  eigen_secular (by exact_mod_cast excitedEnergy_secular t U)

/-- `√(U²+16t²) ≥ |U|`: the discriminant dominates the bare repulsion. -/
theorem abs_U_le_sqrt (t U : ℝ) : |U| ≤ Real.sqrt (U ^ 2 + 16 * t ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t])

/-- In particular `U ≤ √(U²+16t²)`. -/
theorem U_le_sqrt (t U : ℝ) : U ≤ Real.sqrt (U ^ 2 + 16 * t ^ 2) :=
  le_trans (le_abs_self U) (abs_U_le_sqrt t U)

/-- The ground singlet sits at or below the triplet zero mode (`E₀ ≤ 0`). -/
theorem groundEnergy_le_zero (t U : ℝ) : groundEnergy t U ≤ 0 := by
  rw [groundEnergy]; have := U_le_sqrt t U; linarith

/-- The ground singlet sits at or below the antisymmetric-charge level `U`. -/
theorem groundEnergy_le_U (t U : ℝ) : groundEnergy t U ≤ U := by
  rw [groundEnergy]
  have h := abs_U_le_sqrt t U
  have h2 := neg_le_abs U
  linarith

/-- The ground singlet sits at or below the upper singlet. -/
theorem groundEnergy_le_excited (t U : ℝ) : groundEnergy t U ≤ excitedEnergy t U := by
  rw [groundEnergy, excitedEnergy]
  have h : 0 ≤ Real.sqrt (U ^ 2 + 16 * t ^ 2) := Real.sqrt_nonneg _
  linarith

/-! ## Superexchange (antiferromagnetic spin coupling) -/

/-- **Singlet–triplet gap** `J = −E₀ = (√(U²+16t²) − U)/2`, the antiferromagnetic superexchange. -/
noncomputable def exchangeJ (t U : ℝ) : ℝ := (Real.sqrt (U ^ 2 + 16 * t ^ 2) - U) / 2

/-- The gap is exactly the negative of the ground energy (triplet at `0`). -/
theorem exchangeJ_eq_neg_ground (t U : ℝ) : exchangeJ t U = -groundEnergy t U := by
  rw [exchangeJ, groundEnergy]; ring

/-- The superexchange is nonnegative (antiferromagnetic: the singlet is favoured). -/
theorem exchangeJ_nonneg (t U : ℝ) : 0 ≤ exchangeJ t U := by
  rw [exchangeJ]; have := U_le_sqrt t U; linarith

/-- **Closed form** `J = 8t²/(U + √(U²+16t²))` (rationalised), valid when `U + √(U²+16t²) > 0`. -/
theorem exchangeJ_eq (t U : ℝ) (hpos : 0 < U + Real.sqrt (U ^ 2 + 16 * t ^ 2)) :
    exchangeJ t U = 8 * t ^ 2 / (U + Real.sqrt (U ^ 2 + 16 * t ^ 2)) := by
  have hD : Real.sqrt (U ^ 2 + 16 * t ^ 2) ^ 2 = U ^ 2 + 16 * t ^ 2 :=
    Real.sq_sqrt (by positivity)
  rw [exchangeJ, eq_div_iff (ne_of_gt hpos)]
  linear_combination (1 / 2) * hD

/-- **Anderson superexchange scaling:** in the Mott regime `U > 0`, the antiferromagnetic coupling
obeys `J ≤ 4t²/U` — the textbook `J = 4t²/U` second-order virtual hopping, as a rigorous bound. -/
theorem superexchange_le {t U : ℝ} (hU : 0 < U) : exchangeJ t U ≤ 4 * t ^ 2 / U := by
  have hD : Real.sqrt (U ^ 2 + 16 * t ^ 2) ^ 2 = U ^ 2 + 16 * t ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hDnn : 0 ≤ Real.sqrt (U ^ 2 + 16 * t ^ 2) := Real.sqrt_nonneg _
  have key : (U * Real.sqrt (U ^ 2 + 16 * t ^ 2)) ^ 2 ≤ (U ^ 2 + 8 * t ^ 2) ^ 2 := by
    nlinarith [hD, sq_nonneg U, sq_nonneg (t ^ 2)]
  have hUD : U * Real.sqrt (U ^ 2 + 16 * t ^ 2) ≤ U ^ 2 + 8 * t ^ 2 := by
    have h := Real.sqrt_le_sqrt key
    rwa [Real.sqrt_sq (mul_nonneg hU.le hDnn), Real.sqrt_sq (by positivity)] at h
  rw [exchangeJ, le_div_iff₀ hU]
  nlinarith [hUD]

end HqivSpine.Physics.HubbardHalfFilling

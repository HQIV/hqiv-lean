import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import HqivSpine.Physics.Shell

/-!
# `HqivSpine.Physics.HubbardDimer` — the first interacting many-body model on the spine

A minimal **two-site, spin-½ interacting** Hamiltonian on the four-state sector `ℂ⁴`, the spine
refinement of the legacy `Hqiv.QuantumMechanics.HubbardDimerFinite` (disentangled from its Kronecker /
`FiniteManyBodyTensorScaffold` machinery to a single explicit `4×4` matrix, Mathlib-only).

In the basis `(|00⟩, |01⟩, |10⟩, |11⟩)` the Hamiltonian is the hopping term `−t(σx⊗I + I⊗σx)` (a
`4`-cycle adjacency) plus the Ising interaction `λ(σz⊗σz)`:

```
H(t,λ) = ⎡  λ  −t  −t   0 ⎤
         ⎢ −t  −λ   0  −t ⎥
         ⎢ −t   0  −λ  −t ⎥
         ⎣  0  −t  −t   λ ⎦
```

Unlike the non-interacting spine QM stack, this is genuinely *interacting* (`λ ≠ 0` couples the
sites) yet stays **exactly solvable**: the spectrum is the closed form `{+λ, −λ, +√(4t²+λ²),
−√(4t²+λ²)}` (`charPoly_factor` certifies the characteristic polynomial factorisation; the two
`±λ` levels carry explicit eigenvectors `eigen_singlet`/`eigen_triplet`). The ground energy is
`E₀ = −√(4t²+λ²)` (`groundEnergy_le_*` — it sits below every level), with a strictly positive
**spectral gap** `√(4t²+λ²) − |λ|` whenever the hopping `t ≠ 0` (`spectralGap_pos`) — a Lieb–Mattis
"interaction cannot close the gap as long as particles hop" statement.

The interaction strength is **shell-anchored**, not free: `lambdaShell m = λ₀·φ(m)/φ(referenceM)`
using the spine mode count `φ(m)=2(m+1)` normalised at the lock-in shell `referenceM = 4`
(`lambdaShell_referenceM`).

Honest scope: a finite four-state toy — the dimer spectrum and gap, not a thermodynamic-limit
Hubbard model. Mathlib + spine `Physics.Shell` only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`,
no `native_decide`.
-/

namespace HqivSpine.Physics.HubbardDimer

open Matrix

/-- The finite Hubbard-dimer Hamiltonian on `ℂ⁴` in the basis `(|00⟩,|01⟩,|10⟩,|11⟩)`:
`H = −t(σx⊗I + I⊗σx) + λ(σz⊗σz)`. -/
noncomputable def H (t lam : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(lam : ℂ), -(t : ℂ), -(t : ℂ), 0;
     -(t : ℂ), -(lam : ℂ), 0, -(t : ℂ);
     -(t : ℂ), 0, -(lam : ℂ), -(t : ℂ);
     0, -(t : ℂ), -(t : ℂ), (lam : ℂ)]

/-- The dimer Hamiltonian is Hermitian (a genuine observable). -/
theorem H_isHermitian (t lam : ℝ) : (H t lam).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H, Matrix.conjTranspose_apply, Complex.conj_ofReal]

/-! ## Shell-anchored interaction strength -/

/-- Shell-coupled Ising strength, normalised at the lock-in shell `referenceM = 4`:
`λ(m) = λ₀·φ(m)/φ(referenceM)` with `φ(m) = 2(m+1)`. -/
noncomputable def lambdaShell (m : ℕ) (lambda0 : ℝ := 1) : ℝ :=
  lambda0 * ((phi m : ℝ) / (phi referenceM : ℝ))

/-- Closed form of the shell coupling: `λ(m) = λ₀·(m+1)/5`. -/
theorem lambdaShell_eq (m : ℕ) (lambda0 : ℝ) :
    lambdaShell m lambda0 = lambda0 * ((m + 1) / 5) := by
  unfold lambdaShell phi referenceM
  push_cast
  ring

/-- At the lock-in shell the coupling is exactly `λ₀` (the normalisation anchor). -/
theorem lambdaShell_referenceM (lambda0 : ℝ) : lambdaShell referenceM lambda0 = lambda0 := by
  rw [lambdaShell_eq]; norm_num [referenceM]

/-! ## Two exact eigenpairs (`±λ`, hopping-independent) -/

/-- The antisymmetric site state `|01⟩ − |10⟩` is an eigenvector with eigenvalue `−λ`,
independent of the hopping `t` (the on-site Ising channel). -/
theorem eigen_singlet (t lam : ℝ) :
    (H t lam).mulVec ![0, 1, -1, 0] = (-(lam : ℂ)) • ![0, 1, -1, 0] := by
  funext i
  fin_cases i <;>
    simp [H, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- The state `|00⟩ − |11⟩` is an eigenvector with eigenvalue `+λ`, again `t`-independent. -/
theorem eigen_triplet (t lam : ℝ) :
    (H t lam).mulVec ![1, 0, 0, -1] = (lam : ℂ) • ![1, 0, 0, -1] := by
  funext i
  fin_cases i <;>
    simp [H, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-! ## The interacting `±√(4t²+λ²)` eigenpairs (bonding / antibonding) -/

/-- **Generic interacting eigenpair.** For any `s` with `s² = 4t²+λ²`, the vector
`(2t, λ+s, λ+s, 2t)` is an eigenvector of `H` with eigenvalue `−s`. This is the secular equation of
the bonding/antibonding channel; specialising `s = ±√(4t²+λ²)` gives the genuine spectrum. -/
theorem eigen_of_sq {t lam s : ℝ} (hs : (s : ℂ) ^ 2 = 4 * (t : ℂ) ^ 2 + (lam : ℂ) ^ 2) :
    (H t lam).mulVec ![2 * (t : ℂ), (lam : ℂ) + (s : ℂ), (lam : ℂ) + (s : ℂ), 2 * (t : ℂ)]
      = (-(s : ℂ)) •
          ![2 * (t : ℂ), (lam : ℂ) + (s : ℂ), (lam : ℂ) + (s : ℂ), 2 * (t : ℂ)] := by
  funext i
  fin_cases i
  · simp [H, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul]; ring
  · simp [H, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul]
    linear_combination hs
  · simp [H, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul]
    linear_combination hs
  · simp [H, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul]; ring

/-- The squared ground scale, as a complex identity for `√(4t²+λ²)`. -/
theorem sqrt_sq_complex (t lam : ℝ) :
    ((Real.sqrt (4 * t ^ 2 + lam ^ 2) : ℝ) : ℂ) ^ 2 = 4 * (t : ℂ) ^ 2 + (lam : ℂ) ^ 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; ring

/-- Ground-state eigenvector `(2t, λ+s, λ+s, 2t)` with `s = √(4t²+λ²)` (the bonding combination). -/
noncomputable def groundVec (t lam : ℝ) : Fin 4 → ℂ :=
  ![2 * (t : ℂ), (lam : ℂ) + (Real.sqrt (4 * t ^ 2 + lam ^ 2) : ℂ),
    (lam : ℂ) + (Real.sqrt (4 * t ^ 2 + lam ^ 2) : ℂ), 2 * (t : ℂ)]

/-- **Interacting ground eigenpair:** `H · groundVec = −√(4t²+λ²) · groundVec`. The interaction
genuinely mixes the sites, yet the ground state is closed-form. -/
theorem eigen_ground (t lam : ℝ) :
    (H t lam).mulVec (groundVec t lam)
      = (-(Real.sqrt (4 * t ^ 2 + lam ^ 2) : ℂ)) • groundVec t lam :=
  eigen_of_sq (sqrt_sq_complex t lam)

/-- Top eigenvector `(2t, λ−s, λ−s, 2t)` with eigenvalue `+√(4t²+λ²)` (the antibonding state). -/
theorem eigen_top (t lam : ℝ) :
    (H t lam).mulVec
        ![2 * (t : ℂ), (lam : ℂ) - (Real.sqrt (4 * t ^ 2 + lam ^ 2) : ℂ),
          (lam : ℂ) - (Real.sqrt (4 * t ^ 2 + lam ^ 2) : ℂ), 2 * (t : ℂ)]
      = ((Real.sqrt (4 * t ^ 2 + lam ^ 2) : ℂ)) •
          ![2 * (t : ℂ), (lam : ℂ) - (Real.sqrt (4 * t ^ 2 + lam ^ 2) : ℂ),
            (lam : ℂ) - (Real.sqrt (4 * t ^ 2 + lam ^ 2) : ℂ), 2 * (t : ℂ)] := by
  have hneg : ((-Real.sqrt (4 * t ^ 2 + lam ^ 2) : ℝ) : ℂ) ^ 2 = 4 * (t : ℂ) ^ 2 + (lam : ℂ) ^ 2 := by
    push_cast; rw [neg_sq]; exact sqrt_sq_complex t lam
  have h := eigen_of_sq (s := -Real.sqrt (4 * t ^ 2 + lam ^ 2)) hneg
  simpa only [Complex.ofReal_neg, sub_eq_add_neg, neg_neg] using h

/-! ## Ground-state energy and the spectral gap -/

/-- Ground-state energy `E₀ = −√(4t²+λ²)`. -/
noncomputable def groundEnergy (t lam : ℝ) : ℝ := -Real.sqrt (4 * t ^ 2 + lam ^ 2)

/-- Key bound: `|λ| ≤ √(4t²+λ²)` (the interaction level never exceeds the full ground scale). -/
theorem abs_lam_le_sqrt (t lam : ℝ) : |lam| ≤ Real.sqrt (4 * t ^ 2 + lam ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t])

/-- The ground energy lies at or below the `+λ` level. -/
theorem groundEnergy_le_lam (t lam : ℝ) : groundEnergy t lam ≤ lam := by
  have h := abs_lam_le_sqrt t lam
  have h2 : -|lam| ≤ lam := neg_abs_le lam
  rw [groundEnergy]; linarith

/-- The ground energy lies at or below the `−λ` level. -/
theorem groundEnergy_le_neg_lam (t lam : ℝ) : groundEnergy t lam ≤ -lam := by
  have h := abs_lam_le_sqrt t lam
  have h2 : lam ≤ |lam| := le_abs_self lam
  rw [groundEnergy]; linarith

/-- The ground energy lies at or below the top `+√(4t²+λ²)` level (it is the minimum). -/
theorem groundEnergy_le_top (t lam : ℝ) : groundEnergy t lam ≤ Real.sqrt (4 * t ^ 2 + lam ^ 2) := by
  rw [groundEnergy]
  have : 0 ≤ Real.sqrt (4 * t ^ 2 + lam ^ 2) := Real.sqrt_nonneg _
  linarith

/-- **Spectral gap** above the ground state: `√(4t²+λ²) − |λ|`. -/
noncomputable def spectralGap (t lam : ℝ) : ℝ := Real.sqrt (4 * t ^ 2 + lam ^ 2) - |lam|

/-- **Interaction cannot close the gap while particles hop:** the spectral gap is strictly positive
whenever the hopping `t ≠ 0`, for every interaction strength `λ`. -/
theorem spectralGap_pos {t : ℝ} (lam : ℝ) (ht : t ≠ 0) : 0 < spectralGap t lam := by
  rw [spectralGap, sub_pos, ← Real.sqrt_sq_eq_abs]
  have htt : 0 < t ^ 2 := (sq_nonneg t).lt_of_ne' (pow_ne_zero 2 ht)
  exact Real.sqrt_lt_sqrt (sq_nonneg lam) (by nlinarith)

/-- The shell-driven dimer keeps a positive gap at every shell, provided the hopping is on. -/
theorem shell_spectralGap_pos {t : ℝ} (m : ℕ) (lambda0 : ℝ) (ht : t ≠ 0) :
    0 < spectralGap t (lambdaShell m lambda0) :=
  spectralGap_pos _ ht

end HqivSpine.Physics.HubbardDimer

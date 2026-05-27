import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# `S⁷` metahorizon: Laplace–Beltrami spectrum and non-interacting fermion sums

This module packages **standard** hyperspherical data on the unit `7`-sphere (embedded in
`ℝ⁸`): eigenvalues of the **scalar** Laplace–Beltrami operator `−Δ_{S⁷}` on degree-`ℓ`
spherical harmonics,
`λ_ℓ = ℓ(ℓ+6)`, and dimensions `dim(ℋ_ℓ)`.

It then defines **Pauli filling** of the lowest single-particle modes (non-interacting
fermions) and proves the small-`N` cumulative **λ-sums** used for the electron-shell
Casimir ladder narrative.

**Convention (documented explicitly):**

* `noninteractingFermionLambdaSum N` is `∑ λ_ℓ` over occupied modes (one `λ_ℓ` per
  fermion). This matches the “total Casimir” column in the sandbox table; it is **twice**
  the strict per-mode zero-point `½ λ_ℓ` sum.
* `noninteractingFermionHalfLambdaSum N` casts that sum to `ℝ` and divides by `2` for the
  `ℏω/2` bookkeeping aligned with `HQIVNuclei.CasimirEnergySurface`.

**Physical scaling** (one real-world anchor) is recorded as definitions over `ℝ`; no claim
is made that this replaces Hartree–Fock—only that the **dimensionless** ladder is fixed by
`S⁷` geometry.

This file is independent of the discrete null-lattice axiom stack (`OctonionicLightCone`);
it is pure spectral geometry + combinatorics.
-/

namespace Hqiv.Geometry

open Nat List

/-- Scalar Laplace–Beltrami eigenvalue on unit `S⁷`, degree `ℓ`: `λ_ℓ = ℓ(ℓ+6)`. -/
def laplaceBeltramiEigenvalueS7 (ℓ : ℕ) : ℝ :=
  (ℓ : ℝ) * ((ℓ : ℝ) + 6)

/-- Same eigenvalue as a natural number (for exact arithmetic in small lemmas). -/
def laplaceBeltramiEigenvalueS7Nat (ℓ : ℕ) : ℕ :=
  ℓ * (ℓ + 6)

theorem laplaceBeltramiEigenvalueS7Nat_cast (ℓ : ℕ) :
    (laplaceBeltramiEigenvalueS7Nat ℓ : ℝ) = laplaceBeltramiEigenvalueS7 ℓ := by
  simp [laplaceBeltramiEigenvalueS7Nat, laplaceBeltramiEigenvalueS7, Nat.cast_mul, Nat.cast_add,
    Nat.cast_ofNat]

/--
Dimension of degree-`ℓ` spherical harmonics on `S⁷`:
`dim = (2ℓ+6) · binom(ℓ+5,5) / 6`
(standard formula `(2ℓ+d-1)(ℓ+d-2)!/(ℓ!(d-1)!)` with `d = 7`).
-/
def sphericalHarmonicDimS7 (ℓ : ℕ) : ℕ :=
  (2 * ℓ + 6) * choose (ℓ + 5) 5 / 6

theorem sphericalHarmonicDimS7_zero : sphericalHarmonicDimS7 0 = 1 := by
  rfl

theorem sphericalHarmonicDimS7_one : sphericalHarmonicDimS7 1 = 8 := by
  rfl

theorem sphericalHarmonicDimS7_two : sphericalHarmonicDimS7 2 = 35 := by
  rfl

theorem sphericalHarmonicDimS7_three : sphericalHarmonicDimS7 3 = 112 := by
  rfl

theorem sphericalHarmonicDimS7_four : sphericalHarmonicDimS7 4 = 294 := by
  rfl

private lemma six_le_sphericalHarmonicNumer (ℓ : ℕ) :
    6 ≤ (2 * ℓ + 6) * choose (ℓ + 5) 5 := by
  have h0 : 0 < choose (ℓ + 5) 5 := Nat.choose_pos (by omega : 5 ≤ ℓ + 5)
  have hone : 1 ≤ choose (ℓ + 5) 5 := Nat.succ_le_iff.mpr h0
  calc
    6 ≤ 2 * ℓ + 6 := by omega
    _ = (2 * ℓ + 6) * 1 := by rw [Nat.mul_one]
    _ ≤ (2 * ℓ + 6) * choose (ℓ + 5) 5 := Nat.mul_le_mul_left _ hone

private lemma sphericalHarmonicDimS7_pos (ℓ : ℕ) : 0 < sphericalHarmonicDimS7 ℓ := by
  unfold sphericalHarmonicDimS7
  refine Nat.div_pos (six_le_sphericalHarmonicNumer ℓ) (by decide : 0 < 6)

/-- Accumulate `λ_ℓ` for `remaining` fermions, filling shells `ℓ, ℓ+1, …` with `acc` running sum. -/
def fillLambdaSum (remaining ℓ acc : ℕ) : ℕ :=
  match remaining with
  | 0 => acc
  | rem + 1 =>
      let d := sphericalHarmonicDimS7 ℓ
      if hle : rem + 1 ≤ d then
        acc + (rem + 1) * laplaceBeltramiEigenvalueS7Nat ℓ
      else
        have hdpos : 0 < d := sphericalHarmonicDimS7_pos ℓ
        have hdle : d ≤ rem + 1 := Nat.le_of_lt (Nat.lt_of_not_ge hle)
        have _hlt : rem + 1 - d < rem + 1 := Nat.sub_lt_of_pos_le hdpos hdle
        fillLambdaSum (rem + 1 - d) (ℓ + 1) (acc + d * laplaceBeltramiEigenvalueS7Nat ℓ)
  termination_by remaining

/--
Greedy lowest-`ℓ`-first occupation: shell indices for each fermion (list order matches energy ordering).
`match` structure is parallel to `fillLambdaSum`.
-/
def fillOccupation (remaining ℓ : ℕ) (acc : List ℕ) : List ℕ :=
  match remaining with
  | 0 => acc.reverse
  | rem + 1 =>
      let d := sphericalHarmonicDimS7 ℓ
      if hle : rem + 1 ≤ d then
        (replicate (rem + 1) ℓ ++ acc).reverse
      else
        have hdpos : 0 < d := sphericalHarmonicDimS7_pos ℓ
        have hdle : d ≤ rem + 1 := Nat.le_of_lt (Nat.lt_of_not_ge hle)
        have _hlt : rem + 1 - d < rem + 1 := Nat.sub_lt_of_pos_le hdpos hdle
        fillOccupation (rem + 1 - d) (ℓ + 1) (replicate d ℓ ++ acc)
  termination_by remaining

@[simp] lemma fillOccupation_zero (ℓ : ℕ) (acc : List ℕ) : fillOccupation 0 ℓ acc = acc.reverse := by
  conv_lhs => simp [fillOccupation]

lemma fillOccupation_succ_of_le {rem ℓ : ℕ} (acc : List ℕ) (hle : rem + 1 ≤ sphericalHarmonicDimS7 ℓ) :
    fillOccupation (rem + 1) ℓ acc = (replicate (rem + 1) ℓ ++ acc).reverse := by
  conv_lhs => simp [fillOccupation, hle]
  rw [reverse_append, reverse_replicate]

lemma fillOccupation_succ_of_not_le {rem ℓ : ℕ} (acc : List ℕ) (hle : ¬ rem + 1 ≤ sphericalHarmonicDimS7 ℓ) :
    fillOccupation (rem + 1) ℓ acc =
      fillOccupation (rem + 1 - sphericalHarmonicDimS7 ℓ) (ℓ + 1)
        (replicate (sphericalHarmonicDimS7 ℓ) ℓ ++ acc) := by
  conv_lhs => simp [fillOccupation, hle]

@[simp] lemma fillLambdaSum_zero (ℓ acc : ℕ) : fillLambdaSum 0 ℓ acc = acc := by
  conv_lhs => simp [fillLambdaSum]

lemma fillLambdaSum_succ_of_le {rem ℓ acc : ℕ} (hle : rem + 1 ≤ sphericalHarmonicDimS7 ℓ) :
    fillLambdaSum (rem + 1) ℓ acc = acc + (rem + 1) * laplaceBeltramiEigenvalueS7Nat ℓ := by
  conv_lhs => simp [fillLambdaSum, hle]

lemma fillLambdaSum_succ_of_not_le {rem ℓ acc : ℕ} (hle : ¬ rem + 1 ≤ sphericalHarmonicDimS7 ℓ) :
    fillLambdaSum (rem + 1) ℓ acc =
      fillLambdaSum (rem + 1 - sphericalHarmonicDimS7 ℓ) (ℓ + 1)
        (acc + sphericalHarmonicDimS7 ℓ * laplaceBeltramiEigenvalueS7Nat ℓ) := by
  conv_lhs => simp [fillLambdaSum, hle]

/-- Shell indices for the lowest-`N` modes (Pauli filling), `ℓ` increasing. -/
def occupationList (N : ℕ) : List ℕ :=
  fillOccupation N 0 []

/--
Sum of `λ_ℓ` over the lowest `N` single-particle modes (non-interacting fermions).
Equal to **twice** the strict `½ λ_ℓ` Casimir sum at unit radius (`ℏ = 1`).
-/
def noninteractingFermionLambdaSum (N : ℕ) : ℕ :=
  fillLambdaSum N 0 0

private lemma fillOccupation_map_sum_eq :
    ∀ (rem ℓ : ℕ) (pref : List ℕ),
      ((fillOccupation rem ℓ pref).map laplaceBeltramiEigenvalueS7Nat).sum =
        (pref.map laplaceBeltramiEigenvalueS7Nat).sum +
          ((fillOccupation rem ℓ []).map laplaceBeltramiEigenvalueS7Nat).sum := by
  intro rem
  refine Nat.strong_induction_on rem ?_
  intro rem ih ℓ pref
  cases rem with
  | zero =>
    simp [fillOccupation_zero, map_nil, sum_nil, map_reverse, sum_reverse]
  | succ rem' =>
    by_cases hle : rem' + 1 ≤ sphericalHarmonicDimS7 ℓ
    · rw [fillOccupation_succ_of_le pref hle, fillOccupation_succ_of_le [] hle]
      simp [map_append, map_replicate, sum_replicate, laplaceBeltramiEigenvalueS7Nat, reverse_append,
        reverse_replicate]
    · have hnotle := hle
      let d := sphericalHarmonicDimS7 ℓ
      have hlt : rem' + 1 - d < rem' + 1 := by
        have hdpos := sphericalHarmonicDimS7_pos ℓ
        have hdl : d ≤ rem' + 1 := Nat.le_of_lt (Nat.lt_of_not_ge hnotle)
        exact Nat.sub_lt_of_pos_le hdpos hdl
      have h₁ := ih (rem' + 1 - d) hlt (ℓ + 1) (replicate d ℓ ++ pref)
      have h₂ := ih (rem' + 1 - d) hlt (ℓ + 1) (replicate d ℓ)
      dsimp [d] at h₁ h₂ ⊢
      rw [fillOccupation_succ_of_not_le pref hnotle, h₁]
      have hroot' := fillOccupation_succ_of_not_le ([] : List ℕ) hnotle
      simp only [append_nil] at hroot'
      simp only [map_append, List.sum_append_nat]
      conv_rhs => rw [hroot']
      rw [h₂]
      simp [laplaceBeltramiEigenvalueS7Nat, Nat.mul_comm, Nat.add_assoc, Nat.add_comm]

private lemma fillLambdaSum_eq_acc_add_listSum :
    ∀ (rem ℓ acc : ℕ),
      fillLambdaSum rem ℓ acc =
        acc + ((fillOccupation rem ℓ []).map laplaceBeltramiEigenvalueS7Nat).sum := by
  intro rem
  refine Nat.strong_induction_on rem ?_
  intro rem ih ℓ acc
  cases rem with
  | zero =>
    simp [fillLambdaSum_zero, fillOccupation_zero, map_nil, sum_nil]
  | succ rem' =>
    by_cases hle : rem' + 1 ≤ sphericalHarmonicDimS7 ℓ
    · rw [fillLambdaSum_succ_of_le hle, fillOccupation_succ_of_le [] hle]
      simp [map_replicate, sum_replicate, laplaceBeltramiEigenvalueS7Nat, reverse_replicate]
    · have hnotle := hle
      let d := sphericalHarmonicDimS7 ℓ
      have hlt : rem' + 1 - d < rem' + 1 := by
        have hdpos := sphericalHarmonicDimS7_pos ℓ
        have hdl : d ≤ rem' + 1 := Nat.le_of_lt (Nat.lt_of_not_ge hnotle)
        exact Nat.sub_lt_of_pos_le hdpos hdl
      rw [fillLambdaSum_succ_of_not_le hnotle]
      have hrec := ih (rem' + 1 - d) hlt (ℓ + 1) (acc + d * laplaceBeltramiEigenvalueS7Nat ℓ)
      have hsplit := fillOccupation_map_sum_eq (rem' + 1 - d) (ℓ + 1) (replicate d ℓ)
      have hroot := fillOccupation_succ_of_not_le ([] : List ℕ) hnotle
      dsimp [d] at hrec hsplit hroot ⊢
      rw [hrec]
      conv_rhs => rw [hroot]
      simp only [List.append_nil]
      rw [hsplit]
      simp [map_replicate, sum_replicate, laplaceBeltramiEigenvalueS7Nat, Nat.add_assoc]

theorem occupationList_spec (N : ℕ) :
    noninteractingFermionLambdaSum N =
      ((occupationList N).map laplaceBeltramiEigenvalueS7Nat).sum := by
  simp [noninteractingFermionLambdaSum, occupationList, fillLambdaSum_eq_acc_add_listSum]

private lemma cast_sum_map_laplaceNat (l : List ℕ) :
    ((l.map laplaceBeltramiEigenvalueS7Nat).sum : ℝ) =
      (l.map laplaceBeltramiEigenvalueS7).sum := by
  induction l with
  | nil => simp
  | cons a as ih => simp [laplaceBeltramiEigenvalueS7Nat_cast, ih, Nat.cast_add]

theorem occupationList_spec_real (N : ℕ) :
    (noninteractingFermionLambdaSum N : ℝ) =
      ((occupationList N).map (fun ℓ => laplaceBeltramiEigenvalueS7 ℓ)).sum := by
  rw [occupationList_spec, cast_sum_map_laplaceNat]

theorem occupationList_three : occupationList 3 = [0, 1, 1] := by native_decide

theorem occupationList_nine :
    occupationList 9 = 0 :: replicate 8 1 := by native_decide

/-- `ℏω/2` style total: half the λ-sum, as `ℝ`. -/
noncomputable def noninteractingFermionHalfLambdaSum (N : ℕ) : ℝ :=
  (noninteractingFermionLambdaSum N : ℝ) / 2

/-! ## Small-`N` identities (sandbox table) -/

theorem noninteractingFermionLambdaSum_three :
    noninteractingFermionLambdaSum 3 = 14 := by native_decide

theorem noninteractingFermionLambdaSum_four :
    noninteractingFermionLambdaSum 4 = 21 := by native_decide

theorem noninteractingFermionLambdaSum_five :
    noninteractingFermionLambdaSum 5 = 28 := by native_decide

theorem noninteractingFermionLambdaSum_nine :
    noninteractingFermionLambdaSum 9 = 56 := by native_decide

theorem noninteractingFermionLambdaSum_ten :
    noninteractingFermionLambdaSum 10 = 72 := by native_decide

theorem noninteractingFermionLambdaSum_eleven :
    noninteractingFermionLambdaSum 11 = 88 := by native_decide

theorem ionizationIncrement_four_minus_three :
    noninteractingFermionLambdaSum 4 - noninteractingFermionLambdaSum 3 = 7 := by native_decide

/-- While filling the `ℓ = 1` multiplet after the first three modes, each added fermion costs `λ₁ = 7`. -/
theorem ionizationIncrement_constant_in_ell1_shell {k : ℕ} (hk : 0 < k) (hk' : k ≤ 6) :
    noninteractingFermionLambdaSum (3 + k) - noninteractingFermionLambdaSum (3 + (k - 1)) = 7 := by
  interval_cases k <;> native_decide

theorem ionizationIncrement_ten_minus_nine :
    noninteractingFermionLambdaSum 10 - noninteractingFermionLambdaSum 9 = 16 := by native_decide

/-- Strict `½ λ` Casimir-style total for `N = 3` modes: `14 / 2 = 7` (matches `λ₁` for the first excited shell). -/
theorem noninteractingFermionHalfLambdaSum_three :
    noninteractingFermionHalfLambdaSum 3 = 7 := by
  unfold noninteractingFermionHalfLambdaSum
  simp [noninteractingFermionLambdaSum_three]
  norm_num

/-! ## Hydrogen anchor (one-parameter scale to eV) -/

noncomputable def hydrogenGroundIP_eV : ℝ := 13.6

noncomputable def eVPerLambdaUnit_S7HydrogenAnchor : ℝ :=
  hydrogenGroundIP_eV / 7

theorem eVPerLambdaUnit_S7HydrogenAnchor_approx :
    eVPerLambdaUnit_S7HydrogenAnchor = 13.6 / 7 := by
  unfold eVPerLambdaUnit_S7HydrogenAnchor hydrogenGroundIP_eV
  ring

theorem predictedIP_secondElectron_eV :
    7 * eVPerLambdaUnit_S7HydrogenAnchor = hydrogenGroundIP_eV := by
  unfold eVPerLambdaUnit_S7HydrogenAnchor
  field_simp

theorem predictedIP_firstEll2_eV :
    16 * eVPerLambdaUnit_S7HydrogenAnchor = 13.6 * (16 / 7 : ℝ) := by
  unfold eVPerLambdaUnit_S7HydrogenAnchor hydrogenGroundIP_eV
  ring

end Hqiv.Geometry
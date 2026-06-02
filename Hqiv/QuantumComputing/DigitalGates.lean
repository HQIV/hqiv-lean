/-
Digital gates as bijections of `DiscreteState L` preserving the informational inner product from
`DiscreteQuantumState`, together with the ℝ octonion 8-plane (left multiplications from
`Hqiv.OctonionLeftMultiplication`) and a finite `Fin 4` controlled–swap model (CNOT analogue).
No continuum Hilbert space: only finite sums, rational weights on the angular ladder, and ℝ only
where the existing generator matrices are typed.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Hqiv.OctonionLeftMultiplication
import Hqiv.QuantumComputing.DiscreteQuantumState
import Hqiv.QuantumMechanics.MonogamyTanglesPhiConditions

namespace Hqiv.QuantumComputing

open scoped BigOperators
open Finset
open Hqiv.Algebra

variable {L : ℕ}
variable [DecidableEq (HarmonicIndex L)]

/-- Euclidean octonion inner product: sign flip on both arguments is invariant. -/
private theorem octonionInner_neg_neg (x y : OctonionVec) :
    octonionInner (-x) (-y) = octonionInner x y := by
  -- Unfold to the componentwise sum and finish by termwise negation cancellation.
  simp [octonionInner] at *
  -- Now the goal is a sum over `Fin 8`; use termwise equality.
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact neg_mul_neg (x i) (y i)

/-- Bijections of digital amplitudes preserving `discreteIp`. -/
structure HQIVGate (L : ℕ) where
  toEquiv : DiscreteState L ≃ DiscreteState L
  preserves_ip (f g : DiscreteState L) :
    discreteIp (toEquiv f) (toEquiv g) = discreteIp f g

omit [DecidableEq (HarmonicIndex L)] in
theorem HQIVGate.preserves_normSq (G : HQIVGate L) (f : DiscreteState L) :
    discreteNormSq (G.toEquiv f) = discreteNormSq f := by
  simpa [discreteNormSq] using G.preserves_ip f f

def HQIVGate.symm (G : HQIVGate L) : HQIVGate L where
  toEquiv := G.toEquiv.symm
  preserves_ip f g := by
    simpa [Equiv.apply_symm_apply] using
      (G.preserves_ip (G.toEquiv.symm f) (G.toEquiv.symm g)).symm

def HQIVGate.trans (G₁ G₂ : HQIVGate L) : HQIVGate L where
  toEquiv := G₁.toEquiv.trans G₂.toEquiv
  preserves_ip f g := by
    simp [Equiv.trans_apply, G₂.preserves_ip, G₁.preserves_ip]

def HQIVGate.id : HQIVGate L where
  toEquiv := Equiv.refl _
  preserves_ip _ _ := rfl

/-- π phase on one angular mode. -/
def phaseGate (ij : HarmonicIndex L) : HQIVGate L where
  toEquiv := {
    toFun := fun f k => if k = ij then -f k else f k
    invFun := fun f k => if k = ij then -f k else f k
    left_inv := fun f => funext fun k => by by_cases hk : k = ij <;> simp [hk]
    right_inv := fun f => funext fun k => by by_cases hk : k = ij <;> simp [hk]
  }
  preserves_ip f g := by
    classical
    -- Expand the informational inner product; only index `ij` is sign-flipped.
    simp [discreteIp, Equiv.coe_fn_mk]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : k = ij
    · subst h
      simp [octonionInner_neg_neg]
    · simp [h]

private theorem phiRat_eq_of_swap {ij₁ ij₂ : HarmonicIndex L} (hℓ : ij₁.fst = ij₂.fst)
    (k : HarmonicIndex L) :
    phiRat k.fst.val = phiRat ((Equiv.swap ij₁ ij₂) k).fst.val := by
  by_cases hk1 : k = ij₁
  · subst hk1
    simpa [Equiv.swap_apply_left, phiRat] using congr_arg (fun ℓ : Fin (L + 1) => phiRat ℓ.val) hℓ
  · by_cases hk2 : k = ij₂
    · subst hk2
      simpa [Equiv.swap_apply_right, phiRat] using
        congr_arg (fun ℓ : Fin (L + 1) => phiRat ℓ.val) hℓ.symm
    · have hk3 : Equiv.swap ij₁ ij₂ k = k := Equiv.swap_apply_of_ne_of_ne hk1 hk2
      simp [hk3]

/-- Swap two modes with the same `ℓ` (identical `phiRat` weight). -/
def swapGates (ij₁ ij₂ : HarmonicIndex L) (_hℓ : ij₁.fst = ij₂.fst) : HQIVGate L where
  toEquiv := (Equiv.swap ij₁ ij₂).arrowCongr (Equiv.refl (OctonionVec))
  preserves_ip f g := by
    let σ := Equiv.swap ij₁ ij₂
    -- With the unweighted `discreteIp`, any index permutation preserves the inner product.
    -- `arrowCongr` induces precomposition by `σ` on the basis-indexed amplitude function.
    simp [discreteIp, Equiv.arrowCongr, Equiv.coe_refl, octonionInner]
    simpa using Equiv.sum_comp σ (fun k => octonionInner (f k) (g k))

/-- Hadamard-style identity on a uniform `Fin 2` pair (no `√2`; doubling is explicit). -/
theorem hadamardShell_two_mul (v : Fin 2 → ℚ) :
    (v 0 + v 1) ^ 2 + (v 0 - v 1) ^ 2 = 2 * (v 0 ^ 2 + v 1 ^ 2) := by
  ring

/-! ### Octonion left multiplications on `Fin 8 → ℝ` (Euclidean sum of squares) -/

def octonionMulVec (M : Matrix (Fin 8) (Fin 8) ℝ) (v : Fin 8 → ℝ) : Fin 8 → ℝ :=
  fun i => ∑ j : Fin 8, M i j * v j

def euclideanNormSqEight (v : Fin 8 → ℝ) : ℝ :=
  ∑ i : Fin 8, v i * v i

theorem octonionLeftMul_N_preserves_euclidean (N : Fin 7) (v : Fin 8 → ℝ) :
    euclideanNormSqEight (octonionMulVec (octonionLeftMul_N N) v) = euclideanNormSqEight v := by
  set_option maxHeartbeats 0 in
  match N with
  | ⟨0, _⟩ =>
      simp [octonionLeftMul_N, octonionMulVec, euclideanNormSqEight, octonionLeftMul_1,
        Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]; ring
  | ⟨1, _⟩ =>
      simp [octonionLeftMul_N, octonionMulVec, euclideanNormSqEight, octonionLeftMul_2,
        Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]; ring
  | ⟨2, _⟩ =>
      simp [octonionLeftMul_N, octonionMulVec, euclideanNormSqEight, octonionLeftMul_3,
        Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]; ring
  | ⟨3, _⟩ =>
      simp [octonionLeftMul_N, octonionMulVec, euclideanNormSqEight, octonionLeftMul_4,
        Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]; ring
  | ⟨4, _⟩ =>
      simp [octonionLeftMul_N, octonionMulVec, euclideanNormSqEight, octonionLeftMul_5,
        Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]; ring
  | ⟨5, _⟩ =>
      simp [octonionLeftMul_N, octonionMulVec, euclideanNormSqEight, octonionLeftMul_6,
        Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]; ring
  | ⟨6, _⟩ =>
      simp [octonionLeftMul_N, octonionMulVec, euclideanNormSqEight, octonionLeftMul_7,
        Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]; ring

/-- The scalar unit `e₀ = 1` acts as identity on the octonion 8-vector. -/
def octonionScalarUnit : Matrix (Fin 8) (Fin 8) ℝ := 1

theorem octonionScalarUnit_preserves_euclidean (v : Fin 8 → ℝ) :
    euclideanNormSqEight (octonionMulVec octonionScalarUnit v) = euclideanNormSqEight v := by
  have hmul : octonionMulVec octonionScalarUnit v = v := by
    funext i
    simp only [octonionMulVec, octonionScalarUnit, Matrix.one_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hne; simp only [hne.symm, ite_false, zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  simp [hmul]

/-! ### Embedded two-level local mixes

The Python `EmbeddedQubitSpace` represents a qubit line by pairs of computational-basis slots.
The Lean state type is still real-valued (`OctonionVec` fibers), so the certified primitive below
is deliberately phrased as a real two-slot witness. Complex OpenQASM gates such as `u3` are admitted
by realifying their `2 × 2` unitary onto the active octonion components and supplying the same
pair-inner-product proof.
-/

/-- A local two-level gate witness on two octonion amplitudes. -/
structure TwoLevelOctonionUnitary where
  toPairEquiv : (OctonionVec × OctonionVec) ≃ (OctonionVec × OctonionVec)
  preserves_pair_ip (x y : OctonionVec × OctonionVec) :
    octonionInner (toPairEquiv x).1 (toPairEquiv y).1 +
      octonionInner (toPairEquiv x).2 (toPairEquiv y).2 =
    octonionInner x.1 y.1 + octonionInner x.2 y.2

/-- Apply a two-level unitary witness to two distinct harmonic slots, fixing all other slots. -/
def twoLevelUnitaryGate (ij₀ ij₁ : HarmonicIndex L) (hij : ij₀ ≠ ij₁)
    (U : TwoLevelOctonionUnitary) : HQIVGate L where
  toEquiv := {
    toFun := fun f k =>
      if k = ij₀ then (U.toPairEquiv (f ij₀, f ij₁)).1
      else if k = ij₁ then (U.toPairEquiv (f ij₀, f ij₁)).2
      else f k
    invFun := fun f k =>
      if k = ij₀ then (U.toPairEquiv.symm (f ij₀, f ij₁)).1
      else if k = ij₁ then (U.toPairEquiv.symm (f ij₀, f ij₁)).2
      else f k
    left_inv := by
      intro f
      funext k
      by_cases hk0 : k = ij₀
      · subst hk0
        have h10 : ij₁ ≠ k := hij.symm
        simp [h10]
      · by_cases hk1 : k = ij₁
        · subst hk1
          simp [hij.symm]
        · simp [hk0, hk1]
    right_inv := by
      intro f
      funext k
      by_cases hk0 : k = ij₀
      · subst hk0
        have h10 : ij₁ ≠ k := hij.symm
        simp [h10]
      · by_cases hk1 : k = ij₁
        · subst hk1
          simp [hij.symm]
        · simp [hk0, hk1]
  }
  preserves_ip f g := by
    classical
    let F : DiscreteState L :=
      fun k =>
        if k = ij₀ then (U.toPairEquiv (f ij₀, f ij₁)).1
        else if k = ij₁ then (U.toPairEquiv (f ij₀, f ij₁)).2
        else f k
    let G : DiscreteState L :=
      fun k =>
        if k = ij₀ then (U.toPairEquiv (g ij₀, g ij₁)).1
        else if k = ij₁ then (U.toPairEquiv (g ij₀, g ij₁)).2
        else g k
    change discreteIp F G = discreteIp f g
    unfold discreteIp
    let rest : Finset (HarmonicIndex L) := (Finset.univ \ {ij₀}) \ {ij₁}
    have hmem₁ : ij₁ ∈ (Finset.univ \ {ij₀} : Finset (HarmonicIndex L)) := by
      simp [hij.symm]
    have hF_rest : ∀ k ∈ rest, F k = f k := by
      intro k hk
      simp [rest] at hk
      simp [F, hk.1, hk.2]
    have hG_rest : ∀ k ∈ rest, G k = g k := by
      intro k hk
      simp [rest] at hk
      simp [G, hk.1, hk.2]
    calc
      (∑ k : HarmonicIndex L, octonionInner (F k) (G k))
          = octonionInner (F ij₀) (G ij₀) +
              (octonionInner (F ij₁) (G ij₁) +
                (Finset.sum rest fun k => octonionInner (F k) (G k))) := by
            rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ ij₀)]
            rw [Finset.sum_eq_add_sum_diff_singleton hmem₁]
      _ = (octonionInner (F ij₀) (G ij₀) + octonionInner (F ij₁) (G ij₁)) +
              (Finset.sum rest fun k => octonionInner (f k) (g k)) := by
            have hrest :
                (Finset.sum rest fun k => octonionInner (F k) (G k)) =
                  (Finset.sum rest fun k => octonionInner (f k) (g k)) := by
              exact Finset.sum_congr rfl fun k hk => by simp [hF_rest k hk, hG_rest k hk]
            rw [hrest]
            ring
      _ = (octonionInner (f ij₀) (g ij₀) + octonionInner (f ij₁) (g ij₁)) +
              (Finset.sum rest fun k => octonionInner (f k) (g k)) := by
            have hactive :
                octonionInner (F ij₀) (G ij₀) + octonionInner (F ij₁) (G ij₁) =
                  octonionInner (f ij₀) (g ij₀) + octonionInner (f ij₁) (g ij₁) := by
              simpa [F, G, hij, hij.symm] using
                U.preserves_pair_ip (f ij₀, f ij₁) (g ij₀, g ij₁)
            rw [hactive]
      _ = octonionInner (f ij₀) (g ij₀) +
              (octonionInner (f ij₁) (g ij₁) +
                (Finset.sum rest fun k => octonionInner (f k) (g k))) := by ring
      _ = ∑ k : HarmonicIndex L, octonionInner (f k) (g k) := by
            rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ ij₀)]
            rw [Finset.sum_eq_add_sum_diff_singleton hmem₁]

/-- Componentwise two-vector linear combination. -/
def octonionVecLin2 (a b : ℝ) (x y : OctonionVec) : OctonionVec :=
  fun i => a * x i + b * y i

/-- A real `SO(2)` local mix, the real shadow used for `rx`/`ry` slices and Hadamard checks. -/
def realPlaneRotationUnitary (c s : ℝ) (hcs : c * c + s * s = 1) :
    TwoLevelOctonionUnitary where
  toPairEquiv := {
    toFun := fun p =>
      (octonionVecLin2 c (-s) p.1 p.2, octonionVecLin2 s c p.1 p.2)
    invFun := fun p =>
      (octonionVecLin2 c s p.1 p.2, octonionVecLin2 (-s) c p.1 p.2)
    left_inv := by
      intro p
      have hcs' : c ^ 2 + s ^ 2 = 1 := by nlinarith [hcs]
      have hmul_left (a : ℝ) : c ^ 2 * a + s ^ 2 * a = a := by
        calc
          c ^ 2 * a + s ^ 2 * a = (c ^ 2 + s ^ 2) * a := by ring
          _ = a := by rw [hcs']; ring
      have hmul_right (a : ℝ) : s ^ 2 * a + c ^ 2 * a = a := by
        rw [add_comm]
        exact hmul_left a
      ext i
      · simp [octonionVecLin2]
        ring_nf
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul_left (p.1 i)
      · simp [octonionVecLin2]
        ring_nf
        exact hmul_right (p.2 i)
    right_inv := by
      intro p
      have hcs' : c ^ 2 + s ^ 2 = 1 := by nlinarith [hcs]
      have hmul_left (a : ℝ) : c ^ 2 * a + s ^ 2 * a = a := by
        calc
          c ^ 2 * a + s ^ 2 * a = (c ^ 2 + s ^ 2) * a := by ring
          _ = a := by rw [hcs']; ring
      have hmul_right (a : ℝ) : s ^ 2 * a + c ^ 2 * a = a := by
        rw [add_comm]
        exact hmul_left a
      ext i
      · simp [octonionVecLin2]
        ring_nf
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul_left (p.1 i)
      · simp [octonionVecLin2]
        ring_nf
        exact hmul_right (p.2 i)
  }
  preserves_pair_ip x y := by
    have hcs' : c ^ 2 + s ^ 2 = 1 := by nlinarith [hcs]
    have hbilin (a b : ℝ) : c ^ 2 * a * b + a * s ^ 2 * b = a * b := by
      calc
        c ^ 2 * a * b + a * s ^ 2 * b = (c ^ 2 + s ^ 2) * (a * b) := by ring
        _ = a * b := by rw [hcs']; ring
    simp [octonionInner, octonionVecLin2]
    rw [← Finset.sum_add_distrib]
    calc
      (∑ x_1,
          ((c * x.1 x_1 + -(s * x.2 x_1)) * (c * y.1 x_1 + -(s * y.2 x_1)) +
            (s * x.1 x_1 + c * x.2 x_1) * (s * y.1 x_1 + c * y.2 x_1))) =
          ∑ i, (x.1 i * y.1 i + x.2 i * y.2 i) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            ring_nf
            nlinarith [hbilin (x.1 i) (y.1 i), hbilin (x.2 i) (y.2 i)]
      _ = (∑ i, x.1 i * y.1 i) + ∑ i, x.2 i * y.2 i := by
            rw [Finset.sum_add_distrib]

/-- Certified one-qubit-line real local mix between two embedded basis slots. -/
def realPlaneRotationGate (ij₀ ij₁ : HarmonicIndex L) (hij : ij₀ ≠ ij₁)
    (c s : ℝ) (hcs : c * c + s * s = 1) : HQIVGate L :=
  twoLevelUnitaryGate ij₀ ij₁ hij (realPlaneRotationUnitary c s hcs)

/-! ### `Fin 4` controlled–swap (CNOT analogue) on `ℚ⁴`, unweighted `ℓ²` -/

def unweightedNormSqFour (v : Fin 4 → ℚ) : ℚ :=
  ∑ i : Fin 4, v i * v i

/-- Swap the `|10⟩` and `|11⟩` basis labels (`2` and `3` in little-endian two-bit order). -/
def cnotPerm : Fin 4 ≃ Fin 4 :=
  Equiv.swap 2 3

def applyPermFour (σ : Fin 4 ≃ Fin 4) (v : Fin 4 → ℚ) : Fin 4 → ℚ :=
  fun i => v (σ i)

theorem unweighted_norm_perm_four (σ : Fin 4 ≃ Fin 4) (v : Fin 4 → ℚ) :
    unweightedNormSqFour (applyPermFour σ v) = unweightedNormSqFour v := by
  simp [unweightedNormSqFour, applyPermFour]
  exact Equiv.sum_comp σ fun i => v i * v i

theorem cnot_preserves_unweighted_four (v : Fin 4 → ℚ) :
    unweightedNormSqFour (applyPermFour cnotPerm v) = unweightedNormSqFour v :=
  unweighted_norm_perm_four cnotPerm v

/-- CKW/monogamy budget compatibility: scaling nonnegative tangles by `etaModePhi` preserves CKW. -/
theorem digital_ckw_step (m : ℕ) {τAB τAC τA_BC : ℝ} (h : Hqiv.QM.ckwMonogamy τAB τAC τA_BC) :
    Hqiv.QM.correctedCkwMonogamyPhi m τAB τAC τA_BC :=
  Hqiv.QM.corrected_monogamy_of_ckw_phi m h

#print HQIVGate
#print swapGates
#print octonionLeftMul_N_preserves_euclidean
#print cnot_preserves_unweighted_four
#print digital_ckw_step

#check HQIVGate.preserves_normSq
#check hadamardShell_two_mul
#check octonionLeftMul_N_preserves_euclidean
#check cnot_preserves_unweighted_four
#check TwoLevelOctonionUnitary
#check twoLevelUnitaryGate
#check realPlaneRotationGate
#check digital_ckw_step

end Hqiv.QuantumComputing

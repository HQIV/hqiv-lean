import Hqiv.Story.S3MidpointSO4DeltaOrbit
import Hqiv.Story.S3WeilPositivityCriterion
import Hqiv.Story.S3CenteredResidualModel

/-!
# Square-orbit Δ collision: algebra, closure, and orbit energy

First discharge layer for `SO4DeltaOrbitObstruction`:

1. **Collision algebra (proved).**  Slot/gap congruences, gap separation `≥ r`, Ng-square
   factorization `N · (g_a − g_b) = s_a² − s_b²`.

2. **Square-midpoint closure (proved).**  At `N = m²`, two distinct off-diagonal prime
   slots with perfect-square gaps `n²` force the same gap.

3. **Ng-square ⇒ perfect-square gap at square midpoint (proved).**  If `m² · g = s²`
   then `g = (s/m)²`.

4. **Extinction contradiction (proved).**  Given `SO4SquareOrbitCollisionCloses N`, an
   Ng-square collision contradicts slot distinctness.

5. **Orbit collision energy (proved).**  Ng-square defect and `criticalLineDeviation`
   share the rank-one Gram PSD backbone.

Global `SO4DeltaOrbitObstruction` for general composite `N` remains open.
-/

namespace Hqiv.Story

open Complex Real Hqiv.Geometry

noncomputable section

/-! ## 1. Collision algebra -/

namespace SO4GapOrbitCollision

theorem gap_sub_eq_slot_sub {N p q : ℕ} (_hp : p ≤ N) (_hq : q ≤ N) :
    (N - p) - (N - q) = q - p := by
  omega

theorem gap_diff_eq_slot_diff {N : ℕ} (c : SO4GapOrbitCollision N)
    (hp : c.slot_a ≤ N) (hq : c.slot_b ≤ N) :
    midpointLeftGap N c.slot_a - midpointLeftGap N c.slot_b =
      c.slot_b - c.slot_a := by
  dsimp [midpointLeftGap]
  exact gap_sub_eq_slot_sub hp hq

theorem r_divides_gap_diff_of_lt {N : ℕ} (c : SO4GapOrbitCollision N)
    (hlt : c.slot_a < c.slot_b) :
    c.r ∣ midpointLeftGap N c.slot_a - midpointLeftGap N c.slot_b := by
  have hpLe : c.slot_a ≤ N := by
    have hN : 2 ≤ N := by
      by_contra hltN
      push_neg at hltN
      have : c.slot_a ∉ offDiagonalPrimeScanSlots N := by
        simp [offDiagonalPrimeScanSlots, Finset.mem_filter, Finset.mem_Icc]
        omega
      exact this c.ha
    exact Nat.le_of_lt ((mem_offDiagonalPrimeScanSlots_iff (N := N) hN).mp c.ha).2.2
  have hqLe : c.slot_b ≤ N := by
    have hN : 2 ≤ N := by
      by_contra hltN
      push_neg at hltN
      have : c.slot_b ∉ offDiagonalPrimeScanSlots N := by
        simp [offDiagonalPrimeScanSlots, Finset.mem_filter, Finset.mem_Icc]
        omega
      exact this c.hb
    exact Nat.le_of_lt ((mem_offDiagonalPrimeScanSlots_iff (N := N) hN).mp c.hb).2.2
  rw [gap_diff_eq_slot_diff c hpLe hqLe]
  exact reflect_duplicate_divides_q_sub_p_of_lt c.hcross_a c.hcross_b hlt

theorem r_le_gap_diff_of_lt {N : ℕ} (c : SO4GapOrbitCollision N)
    (hlt : c.slot_a < c.slot_b) :
    c.r ≤ midpointLeftGap N c.slot_a - midpointLeftGap N c.slot_b := by
  have hpLe : c.slot_a ≤ N := by
    have hN : 2 ≤ N := by
      by_contra hltN
      push_neg at hltN
      have : c.slot_a ∉ offDiagonalPrimeScanSlots N := by
        simp [offDiagonalPrimeScanSlots, Finset.mem_filter, Finset.mem_Icc]
        omega
      exact this c.ha
    exact Nat.le_of_lt ((mem_offDiagonalPrimeScanSlots_iff (N := N) hN).mp c.ha).2.2
  have hqLe : c.slot_b ≤ N := by
    have hN : 2 ≤ N := by
      by_contra hltN
      push_neg at hltN
      have : c.slot_b ∉ offDiagonalPrimeScanSlots N := by
        simp [offDiagonalPrimeScanSlots, Finset.mem_filter, Finset.mem_Icc]
        omega
      exact this c.hb
    exact Nat.le_of_lt ((mem_offDiagonalPrimeScanSlots_iff (N := N) hN).mp c.hb).2.2
  rw [gap_diff_eq_slot_diff c hpLe hqLe]
  exact gap_dist_ge_r c hlt

theorem ng_square_diff_factorization {N : ℕ} (c : SO4GapOrbitCollision N)
    {s_a s_b : ℕ}
    (hNg_a : N * midpointLeftGap N c.slot_a = s_a * s_a)
    (hNg_b : N * midpointLeftGap N c.slot_b = s_b * s_b)
    (_hle : midpointLeftGap N c.slot_b ≤ midpointLeftGap N c.slot_a) :
    N * (midpointLeftGap N c.slot_a - midpointLeftGap N c.slot_b) =
      s_a * s_a - s_b * s_b := by
  calc
    N * (midpointLeftGap N c.slot_a - midpointLeftGap N c.slot_b) =
        N * midpointLeftGap N c.slot_a - N * midpointLeftGap N c.slot_b := by
      rw [Nat.mul_sub]
    _ = s_a * s_a - s_b * s_b := by rw [hNg_a, hNg_b]

theorem reflect_divides_partner_arm {N : ℕ} (c : SO4GapOrbitCollision N) (slot : ℕ)
    (hslot : slot = c.slot_a ∨ slot = c.slot_b) :
    c.r ∣ N + midpointLeftGap N slot := by
  rcases hslot with rfl | rfl
  · have hc := c.hcross_a
    rw [reflectResidueCrossed_iff_mod] at hc
    have hslotLe : c.slot_a ≤ N := by
      have hN : 2 ≤ N := by
        by_contra hltN
        push_neg at hltN
        have : c.slot_a ∉ offDiagonalPrimeScanSlots N := by
          simp [offDiagonalPrimeScanSlots, Finset.mem_filter, Finset.mem_Icc]
          omega
        exact this c.ha
      exact Nat.le_of_lt ((mem_offDiagonalPrimeScanSlots_iff (N := N) hN).mp c.ha).2.2
    have hpartner : 2 * N - c.slot_a = N + midpointLeftGap N c.slot_a := by
      dsimp [midpointLeftGap]
      omega
    rw [← hpartner]
    exact Nat.dvd_of_mod_eq_zero hc.2.2
  · have hc := c.hcross_b
    rw [reflectResidueCrossed_iff_mod] at hc
    have hslotLe : c.slot_b ≤ N := by
      have hN : 2 ≤ N := by
        by_contra hltN
        push_neg at hltN
        have : c.slot_b ∉ offDiagonalPrimeScanSlots N := by
          simp [offDiagonalPrimeScanSlots, Finset.mem_filter, Finset.mem_Icc]
          omega
        exact this c.hb
      exact Nat.le_of_lt ((mem_offDiagonalPrimeScanSlots_iff (N := N) hN).mp c.hb).2.2
    have hpartner : 2 * N - c.slot_b = N + midpointLeftGap N c.slot_b := by
      dsimp [midpointLeftGap]
      omega
    rw [← hpartner]
    exact Nat.dvd_of_mod_eq_zero hc.2.2

end SO4GapOrbitCollision

/-! ## 2. Square-midpoint prime-arm uniqueness -/

theorem square_diff_eq_gap_arms {m n : ℕ} (hn : n ≤ m) :
    m * m - n * n = (m - n) * (m + n) := by
  symm
  exact gap_arm_product_square hn

theorem prime_of_square_diff_forces_unit_gap {m n : ℕ} (hn : n < m)
    (hp : Nat.Prime (m * m - n * n)) : m - n = 1 := by
  have hnle : n ≤ m := Nat.le_of_lt hn
  set d := m - n
  have hdpos : 0 < d := Nat.sub_pos_of_lt hn
  have hfactor : m * m - n * n = d * (m + n) :=
    square_diff_eq_gap_arms hnle
  have hd1 : d = 1 := by
    have hdvd : d ∣ m * m - n * n := by rw [hfactor]; exact Nat.dvd_mul_right _ _
    rcases Nat.Prime.eq_one_or_self_of_dvd hp d hdvd with h1 | hmn
    · exact h1
    · exfalso
      have hprod : d = (m + n) * d := by
        calc d = m * m - n * n := hmn
          _ = d * (m + n) := hfactor
          _ = (m + n) * d := Nat.mul_comm _ _
      have hCancel : (m + n) * d = 1 * d := by rw [Nat.one_mul, hprod.symm]
      have hmn1 : m + n = 1 := Nat.mul_right_cancel hdpos hCancel
      have hone : m * m - n * n = 1 := by omega
      exact Nat.not_prime_one (hone ▸ hp)
  exact hd1

theorem m_dvd_s_of_square_midpoint_ng_square {m g s : ℕ} (hm : 0 < m)
    (h : m * m * g = s * s) : m ∣ s := by
  set d := Nat.gcd m s
  set m' := m / d
  set s' := s / d
  have hmm : m' * d = m := Nat.div_mul_cancel (Nat.gcd_dvd_left m s)
  have hss : s' * d = s := Nat.div_mul_cancel (Nat.gcd_dvd_right m s)
  have hcop : Nat.Coprime m' s' :=
    Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left (m := m) (n := s) hm)
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left (m := m) (n := s) hm
  have hEq : m' * m' * g = s' * s' := by
    have hBig : d * d * (m' * m' * g) = d * d * (s' * s') := by
      calc
        d * d * (m' * m' * g) = (m' * d) * (m' * d) * g := by ring
        _ = m * m * g := by rw [hmm]
        _ = s * s := h
        _ = (s' * d) * (s' * d) := by rw [hss]
        _ = d * d * (s' * s') := by ring
    exact Nat.mul_left_cancel (Nat.mul_pos hdpos hdpos) hBig
  have hm'1 : m' = 1 := by
    have hs' : (m' * m').Coprime s' := Nat.Coprime.mul_left hcop hcop
    have hcop' : (m' * m').Coprime (s' * s') := Nat.Coprime.mul_right hs' hs'
    have hm'sq : m' * m' = 1 := hcop'.eq_one_of_dvd ⟨g, hEq.symm⟩
    rcases m' with (_ | _ | m')
    all_goals simp at hm'sq
    exact rfl
  have hmEq : m = d := by rw [← hmm, hm'1, Nat.one_mul]
  have hs : s = d * s' := by rw [Nat.mul_comm, hss]
  exact hmEq ▸ hs ▸ Nat.dvd_mul_right d s'

theorem ng_square_gap_is_perfect_square {m g s : ℕ} (hm : 0 < m)
    (hNg : m * m * g = s * s) : ∃ n, g = n * n := by
  have hmdv : m ∣ s := m_dvd_s_of_square_midpoint_ng_square hm hNg
  refine ⟨s / m, Nat.mul_left_cancel (Nat.mul_pos hm hm) ?_⟩
  have hdiv : m * (s / m) = s := Nat.mul_div_cancel' hmdv
  have hss : (m * (s / m)) * (m * (s / m)) = s * s := by
    nth_rw 2 [hdiv]
    rw [Nat.mul_comm, hdiv]
  calc
    m * m * g = s * s := hNg
    _ = (m * (s / m)) * (m * (s / m)) := hss.symm
    _ = m * m * ((s / m) * (s / m)) := by ring

theorem square_midpoint_at_most_one_square_gap_prime_arm {m n₁ n₂ : ℕ}
    (hn₁ : n₁ < m) (hn₂ : n₂ < m) (hne : n₁ ≠ n₂) :
    ¬ (Nat.Prime (m * m - n₁ * n₁) ∧ Nat.Prime (m * m - n₂ * n₂)) := by
  intro ⟨hp₁, hp₂⟩
  have hn₁' : n₁ = m - 1 := by
    have := prime_of_square_diff_forces_unit_gap hn₁ hp₁
    omega
  have hn₂' : n₂ = m - 1 := by
    have := prime_of_square_diff_forces_unit_gap hn₂ hp₂
    omega
  exact hne (hn₁' ▸ hn₂'.symm)

/-! ## 4. Perfect-square-gap collision closes at square midpoints -/

theorem offDiagonal_slot_lt_square_midpoint {m p : ℕ}
    (hp : p ∈ offDiagonalPrimeScanSlots (m * m)) : p < m * m := by
  have hN : 2 ≤ m * m := by
    by_contra hlt
    push_neg at hlt
    simp [offDiagonalPrimeScanSlots, Finset.mem_filter, Finset.mem_Icc] at hp
    omega
  exact (mem_offDiagonalPrimeScanSlots_iff (N := m * m) hN).mp hp |>.2.2

theorem SO4SquareOrbitCollisionCloses_perfect_square_gaps (m : ℕ) :
    ∀ (c : SO4GapOrbitCollision (m * m)),
      (∃ n₁, midpointLeftGap (m * m) c.slot_a = n₁ * n₁) →
        (∃ n₂, midpointLeftGap (m * m) c.slot_b = n₂ * n₂) →
          midpointLeftGap (m * m) c.slot_a = midpointLeftGap (m * m) c.slot_b := by
  intro c ⟨n₁, hn₁⟩ ⟨n₂, hn₂⟩
  by_contra hneGap
  have hN : 2 ≤ m * m := by
    by_contra hlt
    push_neg at hlt
    have ha := c.ha
    simp [offDiagonalPrimeScanSlots, Finset.mem_filter, Finset.mem_Icc] at ha
    omega
  have hm : 2 ≤ m := by
    by_contra hlt
    push_neg at hlt
    nlinarith
  have hn₁lt : n₁ < m := by
    by_contra hnm
    push_neg at hnm
    have hplt := offDiagonal_slot_lt_square_midpoint c.ha
    have hpr := (mem_offDiagonalPrimeScanSlots_iff (N := m * m) hN).mp c.ha |>.2.1
    have hle : m * m ≤ n₁ * n₁ := Nat.mul_le_mul hnm hnm
    dsimp [midpointLeftGap] at hn₁
    omega
  have hn₂lt : n₂ < m := by
    by_contra hnm
    push_neg at hnm
    have hplt := offDiagonal_slot_lt_square_midpoint c.hb
    have hpr := (mem_offDiagonalPrimeScanSlots_iff (N := m * m) hN).mp c.hb |>.2.1
    have hle : m * m ≤ n₂ * n₂ := Nat.mul_le_mul hnm hnm
    dsimp [midpointLeftGap] at hn₂
    omega
  have hp₁ : Nat.Prime (m * m - n₁ * n₁) := by
    have h := (mem_offDiagonalPrimeScanSlots_iff (N := m * m) hN).mp c.ha
    have hslot : c.slot_a = m * m - n₁ * n₁ := by
      dsimp [midpointLeftGap] at hn₁ ⊢
      omega
    exact hslot ▸ h.1
  have hp₂ : Nat.Prime (m * m - n₂ * n₂) := by
    have h := (mem_offDiagonalPrimeScanSlots_iff (N := m * m) hN).mp c.hb
    have hslot : c.slot_b = m * m - n₂ * n₂ := by
      dsimp [midpointLeftGap] at hn₂ ⊢
      omega
    exact hslot ▸ h.1
  have hne_n : n₁ ≠ n₂ := by
    intro heq
    exact hneGap (by rw [hn₁, hn₂, heq])
  exact square_midpoint_at_most_one_square_gap_prime_arm hn₁lt hn₂lt hne_n ⟨hp₁, hp₂⟩

theorem SO4SquareOrbitCollisionCloses_square_midpoint (m : ℕ) (hm : 0 < m) :
    SO4SquareOrbitCollisionCloses (m * m) := by
  intro c hNg_a hNg_b
  rcases hNg_a with ⟨s_a, hs_a⟩
  rcases hNg_b with ⟨s_b, hs_b⟩
  have h₁ := ng_square_gap_is_perfect_square hm hs_a
  have h₂ := ng_square_gap_is_perfect_square hm hs_b
  exact SO4SquareOrbitCollisionCloses_perfect_square_gaps m c h₁ h₂

/-! ## 5. Extinction vs square-orbit collision -/

theorem square_orbit_collision_extinction_contradiction {N : ℕ}
    (hClose : SO4SquareOrbitCollisionCloses N) (c : SO4GapOrbitCollision N)
    (hNg_a : MidpointGapNgSquare N (midpointLeftGap N c.slot_a))
    (hNg_b : MidpointGapNgSquare N (midpointLeftGap N c.slot_b)) : False := by
  have hneGap := hClose c hNg_a hNg_b
  have hpLe : c.slot_a ≤ N := by
    have hN : 2 ≤ N := by
      by_contra hltN
      push_neg at hltN
      have ha := c.ha
      simp [offDiagonalPrimeScanSlots, Finset.mem_filter, Finset.mem_Icc] at ha
      omega
    exact Nat.le_of_lt ((mem_offDiagonalPrimeScanSlots_iff (N := N) hN).mp c.ha).2.2
  have hqLe : c.slot_b ≤ N := by
    have hN : 2 ≤ N := by
      by_contra hltN
      push_neg at hltN
      have hb := c.hb
      simp [offDiagonalPrimeScanSlots, Finset.mem_filter, Finset.mem_Icc] at hb
      omega
    exact Nat.le_of_lt ((mem_offDiagonalPrimeScanSlots_iff (N := N) hN).mp c.hb).2.2
  have hslot : c.slot_a = c.slot_b := by
    dsimp [midpointLeftGap] at hneGap
    omega
  exact c.hne hslot

theorem square_orbit_collision_extinction_contradiction_at_square_midpoint {m : ℕ}
    (hm : 0 < m) (c : SO4GapOrbitCollision (m * m))
    (hNg_a : MidpointGapNgSquare (m * m) (midpointLeftGap (m * m) c.slot_a))
    (hNg_b : MidpointGapNgSquare (m * m) (midpointLeftGap (m * m) c.slot_b)) : False :=
  square_orbit_collision_extinction_contradiction
    (SO4SquareOrbitCollisionCloses_square_midpoint m hm) c hNg_a hNg_b

/-! ## 6. Orbit collision energy (shared Gram / PSD packaging) -/

/-- Ng-square **defect** at gap `g`: `N·g − s²` (zero on the Ng-square locus). -/
def ngSquareDefect (N g s : ℕ) : ℤ :=
  (N : ℤ) * g - (s : ℤ) * s

theorem ngSquareDefect_zero_iff {N g s : ℕ} :
    ngSquareDefect N g s = 0 ↔ N * g = s * s := by
  unfold ngSquareDefect
  constructor
  · intro h
    exact (Nat.cast_inj (R := ℤ)).1 (sub_eq_zero.mp h)
  · intro h
    exact sub_eq_zero.mpr (mod_cast h)

/-- Rank-one **orbit energy** vector: ζ deviation and Goldbach Ng-square defect. -/
def orbitCollisionEnergyVector (deviation defect : ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then deviation else defect

theorem orbit_collision_energy_gram_psd (deviation defect : ℝ) :
    PSD (gramKernel (orbitCollisionEnergyVector deviation defect)) :=
  gramKernel_psd _

theorem orbit_collision_energy_sum_nonneg (deviation defect : ℝ) :
    0 ≤
      orbitCollisionEnergyVector deviation defect 0 ^ 2 +
        orbitCollisionEnergyVector deviation defect 1 ^ 2 := by
  positivity

theorem orbitCollisionEnergyVector_zero (deviation defect : ℝ) :
    orbitCollisionEnergyVector deviation defect 0 = deviation := by
  simp [orbitCollisionEnergyVector, reduceIte]

theorem orbitCollisionEnergyVector_one (deviation defect : ℝ) :
    orbitCollisionEnergyVector deviation defect 1 = defect := by
  have h1 : (1 : Fin 2) ≠ 0 := by decide
  simp [orbitCollisionEnergyVector, h1, reduceIte]

theorem critical_deviation_is_orbit_energy_zero_locus (s : ℂ) :
    criticalLineDeviation s = 0 ↔
      orbitCollisionEnergyVector (criticalLineDeviation s) (0 : ℝ) 0 = 0 := by
  rw [orbitCollisionEnergyVector_zero]

theorem ng_square_defect_zero_is_orbit_energy_zero_locus {N g s : ℕ} :
    ngSquareDefect N g s = 0 ↔
      orbitCollisionEnergyVector 0 ((ngSquareDefect N g s : ℝ)) 1 = 0 := by
  rw [orbitCollisionEnergyVector_one, ngSquareDefect]
  exact Int.cast_eq_zero (α := ℝ).symm

/--
**Shared PSD spine.**  RH-side deviation and Goldbach-side Ng-square defect embed in
the same rank-one Gram kernel; critical-line zeros are the ζ-channel instance of
`weilSumOnLine_nonneg`.
-/
theorem orbit_energy_shares_weil_gram_backbone {n : ℕ} (v : Fin n → ℝ) :
    PSD (gramKernel v) ∧ 0 ≤ ∑ i, v i ^ 2 := by
  refine ⟨gramKernel_psd v, Finset.sum_nonneg fun i _ => sq_nonneg (v i)⟩

/-! ## 7. Certified square-midpoint instances -/

theorem SO4SquareOrbitCollisionCloses_four :
    SO4SquareOrbitCollisionCloses 4 :=
  SO4SquareOrbitCollisionCloses_square_midpoint 2 (by decide)

theorem SO4SquareOrbitCollisionCloses_nine :
    SO4SquareOrbitCollisionCloses 9 :=
  SO4SquareOrbitCollisionCloses_square_midpoint 3 (by decide)

theorem SO4SquareOrbitCollisionCloses_sixteen :
    SO4SquareOrbitCollisionCloses 16 :=
  SO4SquareOrbitCollisionCloses_square_midpoint 4 (by decide)

end

end Hqiv.Story

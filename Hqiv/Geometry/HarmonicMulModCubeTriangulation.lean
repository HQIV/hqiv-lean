import Hqiv.Geometry.HarmonicCascadeRegularization
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Mul-mod holonomy ↔ mod‑7 cube triangulation (regularization geometry)

The ζ / Goldbach bridge triangulates the discrete→continuous gap with a **square tail**
(`ζ(2)−1`) and a **cube tail** (`ζ(3)−1`); their band width `ζ(2)−ζ(3)` is the regularization
slack.

The same geometry on **`ℤ/nℤ`**:

* **Square / raw channel:** the finite harmonic cascade `6 → 5 → 11 → 7` picks one mul-mod
  multiplier; it saturates on the obstruction ideal `385·(2∪3)ℕ` (first at `770`).
* **Cube / Fano channel:** residues mod `7` split the shell; a **single** cube residue lives in
  `{0, ±1}`, but **three** cube slots triangulate every class of `ℤ/7ℤ`.
* **Regularized channel:** extend the cascade to an infinite prime tower (no blind `7` fallback) —
  packaged in `harmonicOrbitMulModMultiplierReg`.

Raw failure shells lie in the zero Fano fibre (`n ≡ 0 mod 7`) where single-cube data is
degenerate and the three-cube triangulation (plus prime tail) is required.
-/

namespace Hqiv.Geometry

open Nat ZMod

/-! ## Mod‑7 cube fibre -/

/-- Residue classes of **single** cubes in `ℤ/7ℤ` (the `{0, ±1}` fibre). -/
def cubeResidueClasses : Finset (ZMod 7) :=
  {0, 1, 6}

/-- Residues **not** represented by a single cube — the mod‑7 "forbidden body". -/
def forbiddenSingleCubeResidues : Finset (ZMod 7) :=
  {2, 3, 4, 5}

/--
**Cube triangulation of `ℤ/7ℤ`.**  Every residue is a sum of three cube residues; this is the
mul-mod analogue of filling the `ζ(2)−ζ(3)` band with a three-slot simplex over the Fano base.
-/
theorem triangulate_mod7 (r : ZMod 7) :
    ∃ a b c : ZMod 7, a ^ 3 + b ^ 3 + c ^ 3 = r := by
  fin_cases r
  · exact ⟨0, 0, 0, by native_decide⟩
  · exact ⟨0, 0, 1, by native_decide⟩
  · exact ⟨0, 1, 1, by native_decide⟩
  · exact ⟨1, 1, 1, by native_decide⟩
  · exact ⟨3, 3, 3, by native_decide⟩
  · exact ⟨0, 3, 3, by native_decide⟩
  · exact ⟨0, 0, 3, by native_decide⟩

theorem triangulate_mod7_of_nat (m : ℕ) :
    ∃ a b c : ℕ, (a ^ 3 + b ^ 3 + c ^ 3 : ZMod 7) = (m : ZMod 7) := by
  obtain ⟨a, b, c, hr⟩ := triangulate_mod7 (m : ZMod 7)
  exact ⟨a.val, b.val, c.val, by simpa using hr⟩

/-! ## Structured cascade (prefix + adelic tail) -/

/--
Finite harmonic prefix `[6,5,11,13,…,41]`; index `≥ 11` uses the canonical regularized prime
step (adelic tail matching `harmonicOrbitMulModMultiplierReg`).
-/
noncomputable def harmonicCascadeTrialAt (n : ℕ) (hn : 0 < n) : ℕ → ℕ
  | 0 => 6
  | 1 => 5
  | 2 => 11
  | 3 => 13
  | 4 => 17
  | 5 => 19
  | 6 => 23
  | 7 => 29
  | 8 => 31
  | 9 => 37
  | 10 => 41
  | _ => harmonicRegularizedPrimeStep n hn

def harmonicCascadeTrial : ℕ → ℕ
  | 0 => 6
  | 1 => 5
  | 2 => 11
  | 3 => 13
  | 4 => 17
  | 5 => 19
  | 6 => 23
  | 7 => 29
  | 8 => 31
  | 9 => 37
  | 10 => 41
  | _ => 43

theorem harmonicCascadeTrial_zero : harmonicCascadeTrial 0 = 6 := rfl

theorem harmonicCascadeTrial_one : harmonicCascadeTrial 1 = 5 := rfl

theorem harmonicCascadeTrial_two : harmonicCascadeTrial 2 = 11 := rfl

theorem harmonicCascadeTrial_three : harmonicCascadeTrial 3 = 13 := rfl

theorem harmonicCascadeTrialAt_prefix {n : ℕ} (hn : 0 < n) {i : ℕ} (hi : i ≤ 10) :
    harmonicCascadeTrialAt n hn i = harmonicCascadeTrial i := by
  interval_cases i <;> rfl

def harmonicCascadeTrialCoprime (n : ℕ) (i : ℕ) : Prop :=
  Nat.Coprime (harmonicCascadeTrial i) n

def harmonicCascadeTrialAtCoprime (n : ℕ) (hn : 0 < n) (i : ℕ) : Prop :=
  Nat.Coprime (harmonicCascadeTrialAt n hn i) n

/-! ## Raw obstruction ideal (770 semilattice) -/

/--
**Raw obstruction ideal:** prefix saturation forces multiplier `7` on a shell already divisible
by `7`.  Minimal witnesses: `770 = 2·5·7·11`, `1155 = 3·5·7·11`.
-/
def harmonicRawObstructionShell (n : ℕ) : Prop :=
  385 ∣ n ∧ (2 ∣ n ∨ 3 ∣ n)

theorem harmonic_raw_obstruction_shell_mod_seven {n : ℕ}
    (h : harmonicRawObstructionShell n) : 7 ∣ n := by
  rcases h with ⟨h385, _⟩
  exact dvd_trans (by decide : 7 ∣ 385) h385

theorem harmonic_raw_obstruction_shell_zero_residue {n : ℕ}
    (h : harmonicRawObstructionShell n) : (n : ZMod 7) = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  exact harmonic_raw_obstruction_shell_mod_seven h

theorem harmonic_raw_obstruction_shell_770 :
    harmonicRawObstructionShell 770 := by
  refine ⟨?_, Or.inl (by decide)⟩
  decide

theorem harmonic_raw_obstruction_shell_1155 :
    harmonicRawObstructionShell 1155 := by
  refine ⟨?_, Or.inr (by decide)⟩
  decide

private theorem not_coprime_prime_iff {p n : ℕ} (hp : Nat.Prime p) :
    ¬ Nat.Coprime p n ↔ p ∣ n := by
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  tauto

private theorem not_coprime_six_iff (n : ℕ) : ¬ Nat.Coprime 6 n ↔ 2 ∣ n ∨ 3 ∣ n := by
  constructor
  · intro h
    rw [Nat.coprime_iff_gcd_eq_one] at h
    by_cases h2 : 2 ∣ n
    · exact Or.inl h2
    · right
      by_contra h3
      have hg1 : Nat.gcd 6 n = 1 := by
        have hg : Nat.gcd 6 n ∣ 6 := Nat.gcd_dvd_left 6 n
        have hle : Nat.gcd 6 n ≤ 6 := Nat.le_of_dvd (by decide) hg
        have hne2 : ¬ 2 ∣ Nat.gcd 6 n := fun h => h2 (Nat.dvd_trans h (Nat.gcd_dvd_right 6 n))
        have hne3 : ¬ 3 ∣ Nat.gcd 6 n := fun h => h3 (Nat.dvd_trans h (Nat.gcd_dvd_right 6 n))
        interval_cases g : Nat.gcd 6 n
        · exfalso; exact hne2 (by decide)
        · rfl
        · exfalso; exact hne2 (by decide)
        · exfalso; exact hne3 (by decide)
        · exfalso; exact (by decide : ¬(4 : ℕ) ∣ 6) hg
        · exfalso; exact (by decide : ¬(5 : ℕ) ∣ 6) hg
        · exfalso; exact hne2 (by decide)
      exact h (Nat.coprime_iff_gcd_eq_one.mpr hg1)
  · rintro (h2 | h3)
    · intro hc
      rw [Nat.coprime_iff_gcd_eq_one] at hc
      have h2g : 2 ∣ Nat.gcd 6 n := Nat.dvd_gcd (by decide : 2 ∣ 6) h2
      omega
    · intro hc
      rw [Nat.coprime_iff_gcd_eq_one] at hc
      have h3g : 3 ∣ Nat.gcd 6 n := Nat.dvd_gcd (by decide : 3 ∣ 6) h3
      omega

private theorem dvd_385_of_not_coprime_prefix {n : ℕ}
    (h5 : ¬ Nat.Coprime 5 n) (h11 : ¬ Nat.Coprime 11 n) (h7 : 7 ∣ n) : 385 ∣ n := by
  have h5' : 5 ∣ n := (not_coprime_prime_iff Nat.prime_five).mp h5
  have h11' : 11 ∣ n := (not_coprime_prime_iff Nat.prime_eleven).mp h11
  have h35 : 35 ∣ n := by
    have h := Nat.lcm_dvd_iff.mpr ⟨h5', h7⟩
    rwa [show Nat.lcm 5 7 = 35 by decide] at h
  have h385 : 385 ∣ n := by
    have h := Nat.lcm_dvd_iff.mpr ⟨h35, h11'⟩
    rwa [show Nat.lcm 35 11 = 385 by decide] at h
  exact h385

/--
**Classification theorem.**  The raw `{6,5,11,7}` cascade fails exactly on the obstruction
ideal `385·(2∪3)ℕ`.
-/
theorem harmonic_raw_not_coprime_iff_obstruction_shell (n : ℕ) :
    ¬ HarmonicMulModMultiplierCoprimeObstruction n ↔ harmonicRawObstructionShell n := by
  constructor
  · intro hncop
    change ¬ Nat.Coprime (harmonicOrbitMulModMultiplier n) n at hncop
    have hm7 : harmonicOrbitMulModMultiplier n = 7 := by
      by_cases h6 : Nat.Coprime 6 n
      · exact (hncop (by rw [harmonicOrbitMulModMultiplier_eq_six h6]; exact h6)).elim
      · by_cases h5 : Nat.Coprime 5 n
        · exact (hncop (by rw [harmonicOrbitMulModMultiplier_eq_five h6 h5]; exact h5)).elim
        · by_cases h11 : Nat.Coprime 11 n
          · exact (hncop (by rw [harmonicOrbitMulModMultiplier_eq_eleven h6 h5 h11]; exact h11)).elim
          · exact harmonicOrbitMulModMultiplier_eq_seven h6 h5 h11
    have h7dvd : 7 ∣ n :=
      (not_coprime_prime_iff Nat.prime_seven).mp (by rw [← hm7]; exact hncop)
    have h6 : ¬ Nat.Coprime 6 n := by
      by_contra hc
      exact hncop (by rw [harmonicOrbitMulModMultiplier_eq_six hc]; exact hc)
    have h5 : ¬ Nat.Coprime 5 n := by
      intro hc
      exact hncop (by rw [harmonicOrbitMulModMultiplier_eq_five h6 hc]; exact hc)
    have h11 : ¬ Nat.Coprime 11 n := by
      intro hc
      exact hncop (by rw [harmonicOrbitMulModMultiplier_eq_eleven h6 h5 hc]; exact hc)
    exact ⟨dvd_385_of_not_coprime_prefix h5 h11 h7dvd, (not_coprime_six_iff n).mp h6⟩
  · intro hobs
    intro hcop
    have h7 := harmonic_raw_obstruction_shell_mod_seven hobs
    rcases hobs with ⟨h385, h23⟩
    have h6 : ¬ Nat.Coprime 6 n := (not_coprime_six_iff n).mpr h23
    have h5 : ¬ Nat.Coprime 5 n :=
      (not_coprime_prime_iff Nat.prime_five).mpr (dvd_trans (by decide : 5 ∣ 385) h385)
    have h11 : ¬ Nat.Coprime 11 n :=
      (not_coprime_prime_iff Nat.prime_eleven).mpr (dvd_trans (by decide : 11 ∣ 385) h385)
    have hm7 := harmonicOrbitMulModMultiplier_eq_seven h6 h5 h11
    dsimp [HarmonicMulModMultiplierCoprimeObstruction] at hcop
    rw [hm7] at hcop
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_seven).mp hcop) h7

theorem harmonic_raw_obstruction_iff_not_coprime (n : ℕ) :
    harmonicRawObstructionShell n ↔ ¬ HarmonicMulModMultiplierCoprimeObstruction n :=
  (harmonic_raw_not_coprime_iff_obstruction_shell n).symm

theorem harmonic_raw_not_coprime_770_obstruction :
    harmonicRawObstructionShell 770 ∧ ¬ HarmonicMulModMultiplierCoprimeObstruction 770 :=
  ⟨harmonic_raw_obstruction_shell_770,
    (harmonic_raw_obstruction_iff_not_coprime 770).mp harmonic_raw_obstruction_shell_770⟩

theorem harmonic_obstruction_shell_reg_ne_raw (n : ℕ) (hn : 0 < n)
    (h : harmonicRawObstructionShell n) :
    harmonicOrbitMulModMultiplierReg n hn ≠ harmonicOrbitMulModMultiplier n := by
  intro heq
  have hraw := (harmonic_raw_obstruction_iff_not_coprime n).mp h
  by_cases hrawcop : HarmonicMulModMultiplierCoprimeObstruction n
  · exact absurd hrawcop hraw
  · have hreg := harmonic_reg_multiplier_coprime n hn
    dsimp [HarmonicMulModMultiplierCoprimeObstructionReg, harmonicOrbitMulModMultiplierReg] at hreg
    simp [hrawcop] at hreg
    have hreg_eq : harmonicOrbitMulModMultiplierReg n hn = harmonicRegularizedPrimeStep n hn := by
      unfold harmonicOrbitMulModMultiplierReg
      simp [hrawcop]
    have hcop : Nat.Coprime (harmonicOrbitMulModMultiplier n) n := by
      rw [← heq, hreg_eq]
      exact hreg
    exact hraw (by simpa [HarmonicMulModMultiplierCoprimeObstruction] using hcop)

theorem harmonic_obstruction_shell_reg_discharge (n : ℕ) (hn : 0 < n)
    (h : harmonicRawObstructionShell n) :
    HarmonicMulModMultiplierCoprimeObstructionReg n hn ∧
      harmonicOrbitMulModMultiplierReg n hn ≠ harmonicOrbitMulModMultiplier n :=
  ⟨harmonic_reg_multiplier_coprime n hn, harmonic_obstruction_shell_reg_ne_raw n hn h⟩

/-! ## First coprime cascade index -/

theorem harmonic_cascade_trial_thirteen_coprime_770 :
    Nat.Coprime (harmonicCascadeTrial 3) 770 := by
  decide

/-- Prefix indices `0..10` admitting a coprime cascade trial (computable scan). -/
def harmonicPrefixCoprimeIndices (n : ℕ) : List ℕ :=
  (List.range 11).filter fun i => Nat.Coprime (harmonicCascadeTrial i) n

theorem mem_harmonicPrefixCoprimeIndices {n i : ℕ} :
    i ∈ harmonicPrefixCoprimeIndices n ↔
      i ≤ 10 ∧ Nat.Coprime (harmonicCascadeTrial i) n := by
  simp [harmonicPrefixCoprimeIndices, List.mem_filter, List.mem_range, Nat.lt_succ_iff]

/-- First coprime prefix index, or `11` for the adelic tail step. -/
def harmonicFirstCoprimeCascadeIndex (n : ℕ) (_hn : 0 < n) : ℕ :=
  match harmonicPrefixCoprimeIndices n with
  | i :: _ => i
  | [] => 11

private theorem harmonicFirstCoprimeCascadeIndex_prefix {n i : ℕ} (js : List ℕ) (hn : 0 < n)
    (hhead : harmonicPrefixCoprimeIndices n = i :: js) :
    harmonicFirstCoprimeCascadeIndex n hn = i := by
  unfold harmonicFirstCoprimeCascadeIndex
  rw [hhead]

private theorem harmonicPrefixCoprimeIndices_not_nil_of_mem {n i : ℕ}
    (hi : i ∈ harmonicPrefixCoprimeIndices n) :
    harmonicPrefixCoprimeIndices n ≠ [] := by
  intro h
  rw [h] at hi
  exact List.not_mem_nil hi

private theorem harmonicFirstCoprimeCascadeIndex_tail {n : ℕ} (hn : 0 < n)
    (h : harmonicPrefixCoprimeIndices n = []) :
    harmonicFirstCoprimeCascadeIndex n hn = 11 := by
  unfold harmonicFirstCoprimeCascadeIndex
  rw [h]

theorem harmonicFirstCoprimeCascadeIndex_spec (n : ℕ) (hn : 0 < n) :
    harmonicCascadeTrialAtCoprime n hn (harmonicFirstCoprimeCascadeIndex n hn) := by
  by_cases hnil : harmonicPrefixCoprimeIndices n = []
  · have htail := harmonicFirstCoprimeCascadeIndex_tail hn hnil
    rw [htail]
    simp [harmonicCascadeTrialAt, harmonicCascadeTrialAtCoprime]
    exact harmonicRegularizedPrimeStep_coprime n hn
  · have hne : harmonicPrefixCoprimeIndices n ≠ [] := by simpa using hnil
    obtain ⟨i, js, hhead⟩ := List.exists_cons_of_ne_nil hne
    have hidx := harmonicFirstCoprimeCascadeIndex_prefix js hn hhead
    rw [hidx]
    rcases mem_harmonicPrefixCoprimeIndices.mp
        (show i ∈ harmonicPrefixCoprimeIndices n by rw [hhead]; exact .head js) with
      ⟨hi10, hcop⟩
    dsimp [harmonicCascadeTrialAtCoprime]
    rw [harmonicCascadeTrialAt_prefix hn hi10]
    exact hcop

theorem harmonicFirstCoprimeCascadeIndex_coprime (n : ℕ) (hn : 0 < n) :
    Nat.Coprime (harmonicCascadeTrialAt n hn (harmonicFirstCoprimeCascadeIndex n hn)) n :=
  harmonicFirstCoprimeCascadeIndex_spec n hn

theorem harmonicFirstCoprimeCascadeIndex_discharges_770 (hn : 0 < 770 := by decide) :
    harmonicFirstCoprimeCascadeIndex 770 hn = 3 := by
  unfold harmonicFirstCoprimeCascadeIndex harmonicPrefixCoprimeIndices
  native_decide

private theorem harmonic_cascade_trial_at_coprime_of_not_obstruction {n : ℕ} (hn : 0 < n)
    (h : HarmonicMulModMultiplierCoprimeObstruction n) :
    ∃ i, harmonicCascadeTrialAtCoprime n hn i := by
  unfold HarmonicMulModMultiplierCoprimeObstruction at h
  by_cases h6 : Nat.Coprime 6 n
  · exact ⟨0, by simpa [harmonicCascadeTrialAt] using h6⟩
  · by_cases h5 : Nat.Coprime 5 n
    · exact ⟨1, by simpa [harmonicCascadeTrialAt] using h5⟩
    · by_cases h11 : Nat.Coprime 11 n
      · exact ⟨2, by simpa [harmonicCascadeTrialAt] using h11⟩
      · by_cases h13 : Nat.Coprime 13 n
        · exact ⟨3, by simpa [harmonicCascadeTrialAt] using h13⟩
        · exact ⟨11, by
            simp [harmonicCascadeTrialAt, harmonicCascadeTrialAtCoprime]
            exact harmonicRegularizedPrimeStep_coprime n hn⟩

theorem exists_harmonic_cascade_trial_at_coprime (n : ℕ) (hn : 0 < n) :
    ∃ i, harmonicCascadeTrialAtCoprime n hn i :=
  ⟨harmonicFirstCoprimeCascadeIndex n hn, harmonicFirstCoprimeCascadeIndex_spec n hn⟩

/--
Structured multiplier: on the raw-coprime locus use the finite cascade output; on
obstruction shells use the first coprime prefix / adelic tail scan.
-/
noncomputable def harmonicStructuredCascadeMultiplier (n : ℕ) (hn : 0 < n) : ℕ :=
  if HarmonicMulModMultiplierCoprimeObstruction n then
    harmonicOrbitMulModMultiplier n
  else
    harmonicCascadeTrialAt n hn (harmonicFirstCoprimeCascadeIndex n hn)

theorem harmonicStructuredCascadeMultiplier_coprime (n : ℕ) (hn : 0 < n) :
    Nat.Coprime (harmonicStructuredCascadeMultiplier n hn) n := by
  unfold harmonicStructuredCascadeMultiplier
  split_ifs with h
  · exact h
  · exact harmonicFirstCoprimeCascadeIndex_coprime n hn

/--
On the raw-coprime locus, the structured multiplier agrees with the finite cascade.
-/
theorem harmonicStructuredCascadeMultiplier_eq_raw {n : ℕ} (hn : 0 < n)
    (h : HarmonicMulModMultiplierCoprimeObstruction n) :
    harmonicStructuredCascadeMultiplier n hn = harmonicOrbitMulModMultiplier n := by
  simp [harmonicStructuredCascadeMultiplier, h]

theorem harmonicStructuredCascadeMultiplier_eq_reg_of_raw_coprime {n : ℕ} (hn : 0 < n)
    (h : HarmonicMulModMultiplierCoprimeObstruction n) :
    harmonicStructuredCascadeMultiplier n hn = harmonicOrbitMulModMultiplierReg n hn :=
  (harmonicStructuredCascadeMultiplier_eq_raw hn h).trans (harmonic_reg_extends_raw n hn h).symm

theorem harmonicStructuredCascadeMultiplier_ne_raw_on_obstruction {n : ℕ} (hn : 0 < n)
    (h : harmonicRawObstructionShell n) :
    harmonicStructuredCascadeMultiplier n hn ≠ harmonicOrbitMulModMultiplier n := by
  have hraw := (harmonic_raw_obstruction_iff_not_coprime n).mp h
  by_cases hcop : HarmonicMulModMultiplierCoprimeObstruction n
  · exact absurd hcop hraw
  · intro heq
    have hcop' := harmonicStructuredCascadeMultiplier_coprime n hn
    rw [heq] at hcop'
    exact hraw (by simpa [HarmonicMulModMultiplierCoprimeObstruction] using hcop')

theorem harmonicStructuredCascadeMultiplier_fixes_770 (hn : 0 < 770 := by decide) :
    harmonicStructuredCascadeMultiplier 770 hn = 13 := by
  have hraw := harmonic_raw_not_coprime_770
  simp [harmonicStructuredCascadeMultiplier, hraw, harmonicFirstCoprimeCascadeIndex_discharges_770 hn,
    harmonicCascadeTrialAt_prefix hn (by decide : 3 ≤ 10), harmonicCascadeTrial_three]

theorem harmonic_cascade_trial_discharges_raw_770 :
    harmonicRawObstructionShell 770 ∧
      Nat.Coprime (harmonicCascadeTrial 3) 770 ∧
        harmonicCascadeTrial 3 ≠ harmonicOrbitMulModMultiplier 770 :=
  ⟨harmonic_raw_obstruction_shell_770,
    harmonic_cascade_trial_thirteen_coprime_770,
    by rw [harmonicCascadeTrial_three, harmonic_raw_multiplier_770_eq_seven]; decide⟩

noncomputable def harmonic_mul_mod_sweep_structured (n : ℕ) (hn : 0 < n) :
    MulModScaleOrbitSweep n (harmonicStructuredCascadeMultiplier n hn) :=
  mulModScaleOrbitSweep n (harmonicStructuredCascadeMultiplier n hn) hn <|
    harmonicStructuredCascadeMultiplier_coprime n hn

end Hqiv.Geometry

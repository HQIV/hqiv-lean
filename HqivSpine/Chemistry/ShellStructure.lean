import HqivSpine.Foundation.Carrier
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic

/-!
# `HqivSpine.Chemistry.ShellStructure` — the octet and subshell capacities, derived

`Chemistry.LonePairs` took the closed shell `s = 4` (octet `8`) as input. Here it is *derived* from
two axiom-level multiplicities, closing that gap:

* **monogamy pairing** `g_pair = 2` — informational monogamy makes a shared phase channel a pair of
  two opposite-phase carriers (the same `2` as in `φ(m) = 2(m+1)` and the `1 − α/2` contraction);
* **angular degeneracy** `2ℓ+1` — the discrete light-cone shells are spheres, so an `ℓ`-mode carries
  the `S²` spherical-harmonic multiplicity.

Hence `cap(ℓ) = 2(2ℓ+1) = 4ℓ+2` and the octet is the s+p closure `cap(0)+cap(1) = 8` — which is
exactly the `carrierMultiplicity = 8` of the so(8) carrier (`octetCapacity_eq_carrierMultiplicity`).
The `2n²` principal-shell rule, the periodic doubling `2,2,8,8,18,18,…`, the triple-bond ceiling,
and a unified geometric-mean bond order all follow.

Mathlib + foundation only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Chemistry.ShellStructure

open HqivSpine.Foundation

/-- Informational-monogamy pairing multiplicity (two opposite-phase carriers per channel). -/
def monogamyPairMultiplicity : ℕ := 2

/-- `S²` spherical-harmonic multiplicity of orbital angular momentum `ℓ`: `2ℓ+1`. -/
def angularDegeneracy (l : ℕ) : ℕ := 2 * l + 1

/-- Subshell capacity = monogamy pair × angular degeneracy = `2(2ℓ+1)`. -/
def subshellCapacity (l : ℕ) : ℕ := monogamyPairMultiplicity * angularDegeneracy l

/-- Octet = closure of the valence s+p shells = `cap(0) + cap(1)`. -/
def octetCapacity : ℕ := subshellCapacity 0 + subshellCapacity 1

/-- Maximum covalent bond order = the p-shell angular degeneracy `2·1+1 = 3` (σ + 2π). -/
def maxBondOrder : ℕ := angularDegeneracy 1

theorem maxBondOrder_eq_three : maxBondOrder = 3 := rfl

/-- s,p,d,f capacities are `2,6,10,14` (`2(2ℓ+1)`). -/
theorem subshellCapacity_spdf :
    subshellCapacity 0 = 2 ∧ subshellCapacity 1 = 6 ∧
      subshellCapacity 2 = 10 ∧ subshellCapacity 3 = 14 := ⟨rfl, rfl, rfl, rfl⟩

/-- Closed form `cap(ℓ) = 4ℓ + 2`. -/
theorem subshellCapacity_closed (l : ℕ) : subshellCapacity l = 4 * l + 2 := by
  unfold subshellCapacity angularDegeneracy monogamyPairMultiplicity; ring

/-- **The octet is 8** — derived as the s+p closure `2·1 + 2·3`, not a literal. -/
theorem octetCapacity_eq_eight : octetCapacity = 8 := rfl

/-- **The chemical octet is the so(8) carrier multiplicity.** The `8` of the valence s+p closure is
the *same* `8` as `carrierMultiplicity` — chemistry's octet rule is the carrier dimension. -/
theorem octetCapacity_eq_carrierMultiplicity : octetCapacity = carrierMultiplicity := by
  rw [octetCapacity_eq_eight, carrierMultiplicity_eq_eight]

/-- A full principal shell holds `2n²` electrons: `Σ_{ℓ<n} 2(2ℓ+1) = 2n²`. -/
theorem principalShellCapacity (n : ℕ) :
    (Finset.range n).sum (fun l => subshellCapacity l) = 2 * n ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih, subshellCapacity_closed]; ring

/-! ## Madelung as network step-distance -/

/-- Network step-distance (BFS generation) of subshell `(n, ℓ)` from the 1s origin: `g = n + ℓ`. -/
def shellGeneration (n l : ℕ) : ℕ := n + l

/-- Electrons in a whole generation `g`: `2·⌈g/2⌉²` (Janet left-step period length). -/
def generationCapacity (g : ℕ) : ℕ := 2 * ((g + 1) / 2) ^ 2

/-- **Periodic-table doubling is a floor/ceil pairing.** Generations `2k−1` and `2k` share
`⌈g/2⌉ = k`, hence the same capacity `2k²` — the origin of `2,2,8,8,18,18,32,…`. -/
theorem generationCapacity_pair (k : ℕ) (hk : 1 ≤ k) :
    generationCapacity (2 * k - 1) = 2 * k ^ 2 ∧ generationCapacity (2 * k) = 2 * k ^ 2 := by
  unfold generationCapacity
  refine ⟨?_, ?_⟩
  · rw [show (2 * k - 1 + 1) / 2 = k by omega]
  · rw [show (2 * k + 1) / 2 = k by omega]

/-- Consecutive odd/even generations have equal capacity (the doubling, stated directly). -/
theorem generationCapacity_doubling (k : ℕ) (hk : 1 ≤ k) :
    generationCapacity (2 * k - 1) = generationCapacity (2 * k) := by
  obtain ⟨h1, h2⟩ := generationCapacity_pair k hk; rw [h1, h2]

/-! ## Unified geometric-mean bond order -/

/-- Covalent bonds an atom commits = bonds to the nearest closed shell, `min(v, target−v)`. -/
def bondingCapacityOfValence (v target : ℕ) : ℕ := min v (target - v)

/-- **Donate-or-accept symmetry**: valence `v` and its octet complement `8−v` commit the same
number of bonds (Li↔F, Be↔O, B↔N). -/
theorem bondingCapacity_mirror (v : ℕ) (hv : v ≤ 8) :
    bondingCapacityOfValence v 8 = bondingCapacityOfValence (8 - v) 8 := by
  unfold bondingCapacityOfValence; omega

/-- Geometric-mean bond order on one contact, capped at the p-shell triple ceiling. -/
noncomputable def geometricBondOrder (ci cj : ℝ) : ℝ :=
  min (maxBondOrder : ℝ) (Real.sqrt (ci * cj))

/-- **Homonuclear collapse**: `√(c·c) = c`, so a same-atom contact carries bond order `c` (within
the triple ceiling) — N₂→3, O₂→2, F₂→1 are this rule, not a separate formula. -/
theorem geometricBondOrder_homonuclear (c : ℝ) (hc : 0 ≤ c) (hcap : c ≤ (maxBondOrder : ℝ)) :
    geometricBondOrder c c = c := by
  unfold geometricBondOrder
  rw [Real.sqrt_mul_self hc]; exact min_eq_right hcap

/-- A heteronuclear contact interpolates: the geometric mean lies between the two capacities. -/
theorem geometricBondOrder_brackets (ci cj : ℝ) (hi : 0 ≤ ci) (hj : 0 ≤ cj)
    (hcap : Real.sqrt (ci * cj) ≤ (maxBondOrder : ℝ)) :
    min ci cj ≤ geometricBondOrder ci cj ∧ geometricBondOrder ci cj ≤ max ci cj := by
  unfold geometricBondOrder
  rw [min_eq_right hcap]
  refine ⟨?_, ?_⟩
  · rcases le_total ci cj with h | h
    · rw [min_eq_left h]
      calc ci = Real.sqrt (ci * ci) := (Real.sqrt_mul_self hi).symm
        _ ≤ Real.sqrt (ci * cj) := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h hi)
    · rw [min_eq_right h]
      calc cj = Real.sqrt (cj * cj) := (Real.sqrt_mul_self hj).symm
        _ ≤ Real.sqrt (ci * cj) := by
              rw [mul_comm ci cj]; exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h hj)
  · rcases le_total ci cj with h | h
    · rw [max_eq_right h]
      calc Real.sqrt (ci * cj) ≤ Real.sqrt (cj * cj) := by
              rw [mul_comm ci cj]; exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h hj)
        _ = cj := Real.sqrt_mul_self hj
    · rw [max_eq_left h]
      calc Real.sqrt (ci * cj) ≤ Real.sqrt (ci * ci) :=
              Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h hi)
        _ = ci := Real.sqrt_mul_self hi

end HqivSpine.Chemistry.ShellStructure

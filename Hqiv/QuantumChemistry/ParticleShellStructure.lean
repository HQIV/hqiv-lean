import Mathlib.Tactic

/-!
# Particle-first shell structure: the octet and subshell capacities from two multiplicities

Lean counterpart of `scripts/hqiv_particle_shell_structure.py`.

The chemistry engine no longer injects the octet `8` or the subshell capacities `{2,6,10,14}`
as literals.  They are reconstructed from two axiom-level multiplicities:

* **monogamy pairing** `g_pair = 2` — informational monogamy makes a shared phase channel a pair
  of two opposite-phase carriers (the same `2` in φ(m)=2(m+1) and the `1 − α/2` contraction);
* **angular degeneracy** `2ℓ+1` — the discrete light-cone shells are spheres, so an ℓ-mode carries
  the S² spherical-harmonic multiplicity `2ℓ+1`.

Hence `cap(ℓ) = g_pair·(2ℓ+1)` and the octet is the s+p closure `cap(0)+cap(1) = 8`.  This module
proves those identities; the noble-gas closures and the valence count follow computationally from
Madelung `(n+ℓ)` filling (see the Python layer).
-/

namespace Hqiv.QuantumChemistry.ParticleShellStructure

/-- Informational-monogamy pairing multiplicity (two opposite-phase carriers per channel). -/
def monogamyPairMultiplicity : ℕ := 2

/-- S² spherical-harmonic multiplicity of orbital angular momentum `ℓ`: `2ℓ+1`. -/
def angularDegeneracy (l : ℕ) : ℕ := 2 * l + 1

/-- Subshell capacity = monogamy pair × angular degeneracy = `2(2ℓ+1)`. -/
def subshellCapacity (l : ℕ) : ℕ := monogamyPairMultiplicity * angularDegeneracy l

/-- Octet = closure of the valence s+p shells = `cap(0) + cap(1)`. -/
def octetCapacity : ℕ := subshellCapacity 0 + subshellCapacity 1

/-- Maximum covalent bond order between two atoms = the p-shell angular degeneracy `2·1+1 = 3`
(σ + 2π).  The triple bond is the ceiling. -/
def maxBondOrder : ℕ := angularDegeneracy 1

/-- The triple bond is the ceiling: `maxBondOrder = 3`. -/
theorem maxBondOrder_eq_three : maxBondOrder = 3 := by
  unfold maxBondOrder angularDegeneracy; rfl

/-- s,p,d,f capacities are `2,6,10,14` (`2(2ℓ+1)`). -/
theorem subshellCapacity_spdf :
    subshellCapacity 0 = 2 ∧ subshellCapacity 1 = 6 ∧
      subshellCapacity 2 = 10 ∧ subshellCapacity 3 = 14 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (unfold subshellCapacity angularDegeneracy monogamyPairMultiplicity; rfl)

/-- **The octet is 8** — derived as the s+p closure `2·1 + 2·3`, not a literal. -/
theorem octetCapacity_eq_eight : octetCapacity = 8 := by
  unfold octetCapacity subshellCapacity angularDegeneracy monogamyPairMultiplicity
  rfl

/-- Equivalent closed form: `cap(ℓ) = 4ℓ + 2`. -/
theorem subshellCapacity_closed (l : ℕ) : subshellCapacity l = 4 * l + 2 := by
  unfold subshellCapacity angularDegeneracy monogamyPairMultiplicity
  ring

/-! ## Madelung as network step-distance (the "same shape" as the shell network)

A radial step `n→n+1` and an angular step `ℓ→ℓ+1` are the *same unit step* of the growing shell
network, so `g = n+ℓ` is the BFS generation at which a subshell appears.  Filling by generation is
the same growth order the network uses everywhere — Madelung is not a foreign chemistry rule. -/

/-- Network step-distance (BFS generation) of subshell `(n, ℓ)` from the 1s origin: `g = n + ℓ`. -/
def shellGeneration (n l : ℕ) : ℕ := n + l

/-- Electrons in a whole generation `g`: `2·⌈g/2⌉²` (Janet left-step period length). -/
def generationCapacity (g : ℕ) : ℕ := 2 * ((g + 1) / 2) ^ 2

/-- **The periodic-table doubling is a floor/ceil pairing.** Generations `2k−1` and `2k` share
`⌈g/2⌉ = k`, hence the *same* capacity `2k²` — this is the origin of `2,2,8,8,18,18,32,…`. -/
theorem generationCapacity_pair (k : ℕ) (hk : 1 ≤ k) :
    generationCapacity (2 * k - 1) = 2 * k ^ 2 ∧ generationCapacity (2 * k) = 2 * k ^ 2 := by
  unfold generationCapacity
  refine ⟨?_, ?_⟩
  · have h : (2 * k - 1 + 1) / 2 = k := by omega
    rw [h]
  · have h : (2 * k + 1) / 2 = k := by omega
    rw [h]

/-- The doubling, stated directly: consecutive odd/even generations have equal capacity. -/
theorem generationCapacity_doubling (k : ℕ) (hk : 1 ≤ k) :
    generationCapacity (2 * k - 1) = generationCapacity (2 * k) := by
  obtain ⟨h1, h2⟩ := generationCapacity_pair k hk
  rw [h1, h2]

/-- A full principal shell (all ℓ from 0 to n−1) holds `2n²` electrons:
`Σ_{ℓ<n} 2(2ℓ+1) = 2n²`.  This is the particle-level origin of the `2n²` rule. -/
theorem principalShellCapacity (n : ℕ) :
    (Finset.range n).sum (fun l => subshellCapacity l) = 2 * n ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, subshellCapacity_closed]
    ring

/-! ## Unified bond order: one geometric-mean rule for all covalent contacts

The chemistry engine no longer carries separate homonuclear/heteronuclear bond-order formulas with
`−6/+1` valence offsets.  Both are the single rule: an atom commits `cap = min(valence, target−valence)`
bonds (electrons to the *nearest* closed shell, either side of the table), and a contact's order is the
geometric mean of the two capacities, capped at the p-shell triple. -/

/-- Covalent bonds an atom commits = bonds to the nearest closed shell, `min(valence, target−valence)`. -/
def bondingCapacityOfValence (v target : ℕ) : ℕ := min v (target - v)

/-- **Donate-or-accept symmetry**: valence `v` and its octet complement `8−v` commit the same number
of bonds (Li↔F, Be↔O, B↔N). -/
theorem bondingCapacity_mirror (v : ℕ) (hv : v ≤ 8) :
    bondingCapacityOfValence v 8 = bondingCapacityOfValence (8 - v) 8 := by
  unfold bondingCapacityOfValence
  omega

/-- Geometric-mean bond order on one contact, capped at the p-shell triple ceiling. -/
noncomputable def geometricBondOrder (ci cj : ℝ) : ℝ :=
  min (maxBondOrder : ℝ) (Real.sqrt (ci * cj))

/-- **Homonuclear collapse**: `√(c·c) = c`, so a same-atom contact carries bond order `c`
(within the triple ceiling) — N₂→3, O₂→2, F₂→1 are this rule, not a separate formula. -/
theorem geometricBondOrder_homonuclear (c : ℝ) (hc : 0 ≤ c) (hcap : c ≤ (maxBondOrder : ℝ)) :
    geometricBondOrder c c = c := by
  unfold geometricBondOrder
  rw [Real.sqrt_mul_self hc]
  exact min_eq_right hcap

/-- The geometric mean of two distinct capacities lies between them (for the uncapped branch):
a heteronuclear contact interpolates, never exceeding the larger or undercutting the smaller end. -/
theorem geometricBondOrder_brackets (ci cj : ℝ) (hi : 0 ≤ ci) (hj : 0 ≤ cj)
    (hcap : Real.sqrt (ci * cj) ≤ (maxBondOrder : ℝ)) :
    min ci cj ≤ geometricBondOrder ci cj ∧ geometricBondOrder ci cj ≤ max ci cj := by
  unfold geometricBondOrder
  rw [min_eq_right hcap]
  constructor
  · rcases le_total ci cj with h | h
    · rw [min_eq_left h]
      calc ci = Real.sqrt (ci * ci) := (Real.sqrt_mul_self hi).symm
        _ ≤ Real.sqrt (ci * cj) := by
              apply Real.sqrt_le_sqrt; exact mul_le_mul_of_nonneg_left h hi
    · rw [min_eq_right h]
      calc cj = Real.sqrt (cj * cj) := (Real.sqrt_mul_self hj).symm
        _ ≤ Real.sqrt (ci * cj) := by
              apply Real.sqrt_le_sqrt
              rw [mul_comm ci cj]; exact mul_le_mul_of_nonneg_left h hj
  · rcases le_total ci cj with h | h
    · rw [max_eq_right h]
      calc Real.sqrt (ci * cj) ≤ Real.sqrt (cj * cj) := by
              apply Real.sqrt_le_sqrt
              rw [mul_comm ci cj]; exact mul_le_mul_of_nonneg_left h hj
        _ = cj := Real.sqrt_mul_self hj
    · rw [max_eq_left h]
      calc Real.sqrt (ci * cj) ≤ Real.sqrt (ci * ci) := by
              apply Real.sqrt_le_sqrt; exact mul_le_mul_of_nonneg_left h hi
        _ = ci := Real.sqrt_mul_self hi

end Hqiv.QuantumChemistry.ParticleShellStructure

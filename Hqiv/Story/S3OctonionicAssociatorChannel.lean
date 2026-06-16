import Hqiv.Story.S3DiophantineTransformer
import Hqiv.Algebra.OctonionBasics

/-!
# The octonionic associator channel: breaking the abelian obstruction

The Diophantine transformer family is *diagonal*, hence **commutative and
normal** — and that is exactly why every law it yields is a zero-slack
reformulation: a commuting normal family is simultaneously diagonalizable,
so every invariant it carries factors through the entries, and the entries
are the σ-blind/RH-equivalent readouts we already have.  This module first
records that obstruction, then moves to the one carrier in the stack that
escapes it: the **octonionic associator** — the same non-associative phase
channel that supplies CP-odd structure elsewhere in HQIV.

## Proved here

* **Commutative saturation** (`diophantineTransformer_mul_comm`,
  `diophantineTransformer_normal`): the transformer family is abelian and
  normal.  Diagonalization is complete; no new invariant lives inside this
  algebra.  This is the formal "good reason we can't go further" on the
  diagonal attack.
* **Trilinear scaling of the associator**
  (`octonionAssociator_smul`, `octonionAssociatorNormSq_smul`): the
  associator is trilinear in scalar weights, so spectral weights couple
  cleanly.
* **Concrete non-associativity witness**
  (`octonionAssociator_e1_e2_e4`, `octonionAssociatorNormSq_e1_e2_e4`):
  on the frozen HQIV Fano tables, `[e₁,e₂,e₄] = −e₃ − e₄` with squared
  norm `2` — the carrier genuinely refuses to associate.
* **The associator channel** (`octAssociatorChannel`): weight the units
  `e₁, e₂, e₄` by the spectral moduli `‖a^{−s}‖, ‖b^{−s}‖, ‖c^{−s}‖`.
  Closed form: channel `= 2·(abc)^{−2σ}`
  (`octAssociatorChannel_eq`).
* **The channel never shuts off** (`octAssociatorChannel_pos`,
  `zero_keeps_associator_torsion`): the non-associative torsion is
  strictly positive at every point of the strip — in particular at every
  nontrivial zero.  Zeros cancel the *abelian* assembly; they cannot
  cancel the associator.
* **Asymmetry locator** (`octAssociatorChannel_eq_iff`): channel
  `= 2/(abc) ⟺ Re s = 1/2`.  A new locator, now read out of a
  non-associative 3-slot invariant that no commuting diagonal family can
  produce.
* **FE pairing in the channel** (`octAssociatorChannel_fe_product`):
  channel(s)·channel(1−s) `= 4/(abc)²` for *every* `s` — the FE composite
  is again a fixed rational, the associator-channel analogue of
  `D_N(s)D_N(1−s) = diag(1/n)`.
* **RH in associator language** (`RH_iff_zero_associator_channel`).
* **Goldbach floor** (`midpoint_triple_channel_floor`): for a Goldbach
  midpoint pair `p + q = 2N`, the triple `(p, q, 2N)` keeps the channel
  `≥ 1/N³` on the line — the AM–GM cap pushed into the associator
  channel.

## Honest scope

The associator channel structurally breaks the abelian obstruction: it is
an orientation-sensitive 3-slot invariant living in a non-associative
algebra, and it is *active at every zero* (positivity), unlike the abelian
assembly which the zero kills.  But the modulus coupling is still driven
by `Re s` alone, so the locator collapses to the same single bit: the RH
statement here is an exact reformulation, not a discharge.  What is new is
the *shape* of the invariant (alternating-type 3-form vs. abelian
diagonal) and the unconditional positivity at zeros.
-/

namespace Hqiv.Story

open Complex Matrix Hqiv.Algebra Hqiv.Geometry

noncomputable section

/-! ## Commutative saturation: why the diagonal attack ends -/

/-- **The transformer family is abelian**: any two levels of the
Diophantine transformer commute, at any pair of spectral parameters.
Every invariant of a commuting diagonal family factors through entries —
hence every law in the diagonal attack is a reformulation. -/
theorem diophantineTransformer_mul_comm (N : ℕ) (s s' : ℂ) :
    diophantineTransformer N s * diophantineTransformer N s' =
      diophantineTransformer N s' * diophantineTransformer N s := by
  unfold diophantineTransformer
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

/-- **The transformer is normal**: it commutes with its own adjoint.
Together with commutativity this exhausts the algebra — diagonalization
is already complete, and no further forcing lives inside it. -/
theorem diophantineTransformer_normal (N : ℕ) (s : ℂ) :
    diophantineTransformer N s * (diophantineTransformer N s)ᴴ =
      (diophantineTransformer N s)ᴴ * diophantineTransformer N s := by
  unfold diophantineTransformer
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

/-! ## Trilinearity of the carrier multiplication and associator -/

/-- Left multiplication is linear in the left slot (scalar weights). -/
theorem leftMulVec_smul_left (a : ℝ) (x y : OctonionVec) :
    leftMulVec (a • x) y = a • leftMulVec x y := by
  funext i
  show (∑ j, (∑ k, leftMulMatrix k i j * (a • x) k) * y j) =
    a * ∑ j, (∑ k, leftMulMatrix k i j * x k) * y j
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : (∑ k, leftMulMatrix k i j * (a • x) k) =
      a * ∑ k, leftMulMatrix k i j * x k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show leftMulMatrix k i j * (a * x k) = a * (leftMulMatrix k i j * x k)
    ring
  rw [h]
  ring

/-- Left multiplication is linear in the right slot (scalar weights). -/
theorem leftMulVec_smul_right (a : ℝ) (x y : OctonionVec) :
    leftMulVec x (a • y) = a • leftMulVec x y := by
  funext i
  show (∑ j, (∑ k, leftMulMatrix k i j * x k) * (a • y) j) =
    a * ∑ j, (∑ k, leftMulMatrix k i j * x k) * y j
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show (∑ k, leftMulMatrix k i j * x k) * (a * y j) =
    a * ((∑ k, leftMulMatrix k i j * x k) * y j)
  ring

/-- Right-slot negation passes through left multiplication. -/
theorem leftMulVec_neg_right (x y : OctonionVec) :
    leftMulVec x (-y) = -(leftMulVec x y) := by
  have h1 : (-1 : ℝ) • y = -y := neg_one_smul ℝ y
  have h2 : (-1 : ℝ) • leftMulVec x y = -(leftMulVec x y) :=
    neg_one_smul ℝ (leftMulVec x y)
  rw [← h1, ← h2]
  exact leftMulVec_smul_right (-1 : ℝ) x y

/-- **Trilinear scaling of the associator**: scalar weights multiply out.
This is the coupling law that lets spectral moduli ride the
non-associative channel. -/
theorem octonionAssociator_smul (a b c : ℝ) (x y z : OctonionVec) :
    octonionAssociator (a • x) (b • y) (c • z) =
      (a * b * c) • octonionAssociator x y z := by
  unfold octonionAssociator
  have h1 : leftMulVec (a • x) (b • y) = (a * b) • leftMulVec x y := by
    rw [leftMulVec_smul_left, leftMulVec_smul_right, smul_smul]
  have h2 : leftMulVec (b • y) (c • z) = (b * c) • leftMulVec y z := by
    rw [leftMulVec_smul_left, leftMulVec_smul_right, smul_smul]
  rw [h1, h2, leftMulVec_smul_left, leftMulVec_smul_right, smul_smul,
    leftMulVec_smul_left, leftMulVec_smul_right, smul_smul, smul_sub,
    ← mul_assoc]

/-- Squared-norm version of trilinear scaling. -/
theorem octonionAssociatorNormSq_smul (a b c : ℝ) (x y z : OctonionVec) :
    octonionAssociatorNormSq (a • x) (b • y) (c • z) =
      (a * b * c) ^ 2 * octonionAssociatorNormSq x y z := by
  unfold octonionAssociatorNormSq
  rw [octonionAssociator_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ((a * b * c) * octonionAssociator x y z i) ^ 2 =
    (a * b * c) ^ 2 * (octonionAssociator x y z i) ^ 2
  ring

/-! ## Concrete non-associativity witness on the frozen Fano tables -/

/-- Column 4 of `L(e₇)`: the product `e₇e₄ = −e₃`. -/
theorem octonionLeftMul_7_k_4 (k : Fin 8) :
    Hqiv.octonionLeftMul_7 k 4 = if k = 3 then (-1 : ℝ) else 0 := by
  fin_cases k <;> simp [Hqiv.octonionLeftMul_7, Matrix.of_apply]

/-- Column 4 of `L(e₂)`: the product `e₂e₄ = −e₅`. -/
theorem octonionLeftMul_2_k_4 (k : Fin 8) :
    Hqiv.octonionLeftMul_2 k 4 = if k = 5 then (-1 : ℝ) else 0 := by
  fin_cases k <;> simp [Hqiv.octonionLeftMul_2, Matrix.of_apply]

/-- Column 5 of `L(e₁)`: the product `e₁e₅ = −e₄`. -/
theorem octonionLeftMul_1_k_5 (k : Fin 8) :
    Hqiv.octonionLeftMul_1 k 5 = if k = 4 then (-1 : ℝ) else 0 := by
  fin_cases k <;> simp [Hqiv.octonionLeftMul_1, Matrix.of_apply]

/-- Multiplying two basis units reads off a column of the left-mul table. -/
theorem leftMulVec_basis_basis (i j : Fin 8) :
    leftMulVec (octonionBasis i) (octonionBasis j) =
      fun k => leftMulMatrix i k j := by
  rw [leftMulVec_octonionBasis]
  funext k
  show (∑ j', leftMulMatrix i k j' * octonionBasis j j') = leftMulMatrix i k j
  rw [Finset.sum_eq_single j]
  · show leftMulMatrix i k j * (if j = j then 1 else 0) = leftMulMatrix i k j
    rw [if_pos rfl, mul_one]
  · intro b _ hb
    show leftMulMatrix i k b * (if b = j then 1 else 0) = 0
    rw [if_neg hb, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- `e₁e₂ = e₇` on the frozen tables. -/
theorem e1_mul_e2 : leftMulVec e1 e2 = e7 := by
  unfold e1 e2 e7
  rw [leftMulVec_basis_basis]
  funext k
  rw [show leftMulMatrix 1 = Hqiv.octonionLeftMul_1 from rfl,
    Hqiv.octonionLeftMul_1_k_2 k]
  unfold octonionBasis
  rfl

/-- `e₇e₄ = −e₃` on the frozen tables. -/
theorem e7_mul_e4 : leftMulVec e7 e4 = -e3 := by
  unfold e7 e4 e3
  rw [leftMulVec_basis_basis]
  funext k
  rw [show leftMulMatrix 7 = Hqiv.octonionLeftMul_7 from rfl,
    octonionLeftMul_7_k_4 k]
  show (if k = 3 then (-1 : ℝ) else 0) = -(if k = 3 then (1 : ℝ) else 0)
  by_cases h : k = 3 <;> simp [h]

/-- `e₂e₄ = −e₅` on the frozen tables. -/
theorem e2_mul_e4 : leftMulVec e2 e4 = -e5 := by
  unfold e2 e4 e5
  rw [leftMulVec_basis_basis]
  funext k
  rw [show leftMulMatrix 2 = Hqiv.octonionLeftMul_2 from rfl,
    octonionLeftMul_2_k_4 k]
  show (if k = 5 then (-1 : ℝ) else 0) = -(if k = 5 then (1 : ℝ) else 0)
  by_cases h : k = 5 <;> simp [h]

/-- `e₁e₅ = −e₄` on the frozen tables. -/
theorem e1_mul_e5 : leftMulVec e1 e5 = -e4 := by
  unfold e1 e5 e4
  rw [leftMulVec_basis_basis]
  funext k
  rw [show leftMulMatrix 1 = Hqiv.octonionLeftMul_1 from rfl,
    octonionLeftMul_1_k_5 k]
  show (if k = 4 then (-1 : ℝ) else 0) = -(if k = 4 then (1 : ℝ) else 0)
  by_cases h : k = 4 <;> simp [h]

/-- **The carrier refuses to associate**: on the frozen HQIV tables,
`[e₁,e₂,e₄] = (e₁e₂)e₄ − e₁(e₂e₄) = −e₃ − e₄ ≠ 0`. -/
theorem octonionAssociator_e1_e2_e4 :
    octonionAssociator e1 e2 e4 = -e3 - e4 := by
  unfold octonionAssociator
  rw [e1_mul_e2, e7_mul_e4, e2_mul_e4, leftMulVec_neg_right, e1_mul_e5,
    neg_neg]

/-- The non-associativity witness carries squared norm `2`. -/
theorem octonionAssociatorNormSq_e1_e2_e4 :
    octonionAssociatorNormSq e1 e2 e4 = 2 := by
  unfold octonionAssociatorNormSq
  rw [octonionAssociator_e1_e2_e4]
  have hval : ∀ k : Fin 8, ((-e3 - e4 : OctonionVec) k) ^ 2 =
      (if k = 3 then (1 : ℝ) else 0) + (if k = 4 then (1 : ℝ) else 0) := by
    intro k
    show (-(if k = 3 then (1 : ℝ) else 0) -
      (if k = 4 then (1 : ℝ) else 0)) ^ 2 = _
    by_cases h3 : k = 3
    · subst h3
      rw [if_neg (by decide : ¬(3 : Fin 8) = 4)]
      norm_num
    · by_cases h4 : k = 4
      · subst h4
        rw [if_neg h3]
        norm_num
      · simp [h3, h4]
  rw [Finset.sum_congr rfl fun k _ => hval k, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (3 : Fin 8) (fun _ => (1 : ℝ)),
    Finset.sum_ite_eq' Finset.univ (4 : Fin 8) (fun _ => (1 : ℝ))]
  norm_num

/-! ## The associator channel: spectral weights on the torsion triple -/

/-- **The octonionic associator channel**: weight the non-associative
triple `(e₁, e₂, e₄)` by the spectral moduli of `a^{−s}, b^{−s}, c^{−s}`
and read the associator's squared norm. -/
noncomputable def octAssociatorChannel (a b c : ℕ) (s : ℂ) : ℝ :=
  octonionAssociatorNormSq
    (‖so4SpectralLine a s‖ • e1)
    (‖so4SpectralLine b s‖ • e2)
    (‖so4SpectralLine c s‖ • e4)

/-- **Closed form of the channel**: `2·(abc)^{−2σ}` — the torsion constant
of the triple times the joint spectral weight. -/
theorem octAssociatorChannel_eq {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (s : ℂ) :
    octAssociatorChannel a b c s =
      2 * ((a * b * c : ℕ) : ℝ) ^ (-(2 * s.re)) := by
  unfold octAssociatorChannel
  rw [octonionAssociatorNormSq_smul, octonionAssociatorNormSq_e1_e2_e4,
    so4SpectralLine_norm ha, so4SpectralLine_norm hb,
    so4SpectralLine_norm hc]
  have h1 : ((a : ℝ)) ^ (-s.re) * ((b : ℝ)) ^ (-s.re) * ((c : ℝ)) ^ (-s.re) =
      ((a * b * c : ℕ) : ℝ) ^ (-s.re) := by
    push_cast
    rw [← Real.mul_rpow (by positivity) (by positivity),
      ← Real.mul_rpow (by positivity) (by positivity)]
  have habc : (0 : ℝ) < ((a * b * c : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos ha hb) hc
  rw [h1, pow_two, ← Real.rpow_add habc,
    show -s.re + -s.re = -(2 * s.re) by ring]
  ring

/-- **The channel never shuts off**: the non-associative torsion is
strictly positive at every spectral parameter. -/
theorem octAssociatorChannel_pos {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (s : ℂ) :
    0 < octAssociatorChannel a b c s := by
  rw [octAssociatorChannel_eq ha hb hc]
  have habc : (0 : ℝ) < ((a * b * c : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos ha hb) hc
  have := Real.rpow_pos_of_pos habc (-(2 * s.re))
  linarith

/-- **Zeros cannot cancel the associator**: at every nontrivial zeta zero
the channel stays strictly positive.  The zero kills the abelian assembly;
the non-associative torsion survives untouched. -/
theorem zero_keeps_associator_torsion {ρ : ℂ}
    (_ : IsNontrivialZetaZero ρ) {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < octAssociatorChannel a b c ρ :=
  octAssociatorChannel_pos ha hb hc ρ

/-- **The asymmetry locator**: the channel carries the square-root weight
`2/(abc)` exactly on the critical line. -/
theorem octAssociatorChannel_eq_iff {a b c : ℕ}
    (ha : 2 ≤ a) (hb : 0 < b) (hc : 0 < c) {s : ℂ} :
    octAssociatorChannel a b c s = 2 / ((a * b * c : ℕ) : ℝ) ↔
      s.re = (1 / 2 : ℝ) := by
  have ha0 : 0 < a := by omega
  have habcN : 2 ≤ a * b * c := by
    have h1 : a ≤ a * b := Nat.le_mul_of_pos_right a hb
    have h2 : a * b ≤ a * b * c := Nat.le_mul_of_pos_right (a * b) hc
    omega
  have hX : (1 : ℝ) < ((a * b * c : ℕ) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le one_lt_two (by exact_mod_cast habcN)
  rw [octAssociatorChannel_eq ha0 hb hc, div_eq_mul_inv,
    ← Real.rpow_neg_one ((a * b * c : ℕ) : ℝ)]
  constructor
  · intro h
    have h' := mul_left_cancel₀ (two_ne_zero (α := ℝ)) h
    have := rpow_left_inj_of_one_lt hX h'
    linarith
  · intro h
    rw [h]
    norm_num

/-- **FE pairing in the associator channel**: for every `s`, the product
of the channel with its FE reflection is the fixed rational `4/(abc)²` —
the associator analogue of `D_N(s)·D_N(1−s) = diag(1/n)`. -/
theorem octAssociatorChannel_fe_product {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (s : ℂ) :
    octAssociatorChannel a b c s * octAssociatorChannel a b c (1 - s) =
      4 / ((a * b * c : ℕ) : ℝ) ^ (2 : ℕ) := by
  have habc : (0 : ℝ) < ((a * b * c : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos ha hb) hc
  have hre : (1 - s).re = 1 - s.re := by
    simp [Complex.sub_re, Complex.one_re]
  rw [octAssociatorChannel_eq ha hb hc, octAssociatorChannel_eq ha hb hc,
    hre, mul_mul_mul_comm, ← Real.rpow_add habc,
    show -(2 * s.re) + -(2 * (1 - s.re)) = -(2 : ℝ) by ring,
    Real.rpow_neg (le_of_lt habc),
    show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  rw [div_eq_mul_inv]
  norm_num

/-- **RH in associator language**: RH ⟺ at every nontrivial zero the
non-associative channel carries exact square-root weight for every triple.
The asymmetry channel names the line; pinning the zeros to it is still
exactly RH. -/
theorem RH_iff_zero_associator_channel :
    RiemannHypothesis ↔
      ∀ ρ : ℂ, IsNontrivialZetaZero ρ → ∀ a b c : ℕ, 2 ≤ a → 0 < b → 0 < c →
        octAssociatorChannel a b c ρ = 2 / ((a * b * c : ℕ) : ℝ) := by
  constructor
  · intro hRH ρ hz a b c ha hb hc
    exact (octAssociatorChannel_eq_iff ha hb hc).mpr
      (hRH ρ hz.1 hz.2.1 hz.2.2)
  · intro hW ρ hz hnt h1
    exact (octAssociatorChannel_eq_iff (le_refl 2) one_pos one_pos).mp
      (hW ρ ⟨hz, hnt, h1⟩ 2 1 1 (le_refl 2) one_pos one_pos)

/-- **Goldbach floor in the associator channel**: a Goldbach midpoint pair
`p + q = 2N` keeps the triple `(p, q, 2N)` torsion above `1/N³` on the
critical line — the AM–GM cap pushed into the non-associative channel. -/
theorem midpoint_triple_channel_floor {N p q : ℕ} (hN : 0 < N)
    (hPair : GoldbachMidpointPair N p q) {s : ℂ}
    (hs : s.re = (1 / 2 : ℝ)) :
    1 / ((N ^ 3 : ℕ) : ℝ) ≤ octAssociatorChannel p q (2 * N) s := by
  have hp2 : 2 ≤ p := hPair.1.two_le
  have hq : 0 < q := hPair.2.1.pos
  have h2N : 0 < 2 * N := by omega
  rw [(octAssociatorChannel_eq_iff hp2 hq h2N).mpr hs]
  have hpq : p * q ≤ N ^ 2 := midpoint_pair_product_le hPair
  have hineq : p * q * (2 * N) ≤ 2 * N ^ 3 := by nlinarith
  have hposN : 0 < p * q * (2 * N) := by positivity
  have hcast : ((p * q * (2 * N) : ℕ) : ℝ) ≤ 2 * ((N ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast hineq
  have hpos : (0 : ℝ) < ((p * q * (2 * N) : ℕ) : ℝ) := by
    exact_mod_cast hposN
  have hN3 : (0 : ℝ) < ((N ^ 3 : ℕ) : ℝ) := by positivity
  rw [div_le_div_iff₀ hN3 hpos, one_mul]
  exact hcast

end

end Hqiv.Story

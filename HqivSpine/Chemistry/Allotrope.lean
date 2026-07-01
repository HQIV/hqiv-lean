import HqivSpine.Chemistry.ShellStructure
import HqivSpine.Chemistry.VSEPR
import Mathlib.Tactic

/-!
# `HqivSpine.Chemistry.Allotrope` — allotrope networks as one geometric law

Same atoms, different bond graph (diamond vs graphite vs carbyne; the benzene ring; ozone) are
**not** new chemistry — they are one law applied to different coordinations. An atom commits its
octet shared-pair budget `cap = octetCapacity − valence` and an allotrope **partitions** it across
its `k` bonded neighbours: each atom offers `cap/k` to each bond, and a bond's order is the
**geometric mean** of its two endpoints' offers (`Chemistry.ShellStructure.geometricBondOrder`, the
saturated Cauchy–Schwarz combiner). The σ-framework angle is the derived VSEPR equilibrium cosine
`−1/(d−1)` (`Chemistry.VSEPR.balanced_unit_contacts_cos`), and the bond contracts on the carrier
contact by `1/(1 + (p−1)·strong/4)` with `strong` the monogamy half.

Everything is re-anchored to spine pieces: the octet is `ShellStructure.octetCapacity`
(= `carrierMultiplicity = 8`), the combiner is `ShellStructure.geometricBondOrder`, the angle is the
`VSEPR` equilibrium result, and `strong = 1/monogamyPairMultiplicity = 1/2`. No fitted coefficients,
no empirical bond tables.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Chemistry.Allotrope

open HqivSpine.Chemistry
open HqivSpine.Chemistry.ShellStructure (octetCapacity geometricBondOrder maxBondOrder
  monogamyPairMultiplicity)
open scoped RealInnerProductSpace

noncomputable section

/-- `(octetCapacity : ℝ) = 8` — the carrier-anchored octet as a real. -/
theorem octetCapacity_real : (octetCapacity : ℝ) = 8 := by
  rw [ShellStructure.octetCapacity_eq_eight]; norm_num

/-- `(maxBondOrder : ℝ) = 3` — the triple-bond ceiling (p-shell degeneracy) as a real. -/
theorem maxBondOrder_real : (maxBondOrder : ℝ) = 3 := by
  rw [ShellStructure.maxBondOrder_eq_three]; norm_num

/-! ## Capacity partition over the coordination -/

/-- Octet shared-pair capacity to partition: `cap = octetCapacity − valence`, the octet being the
derived so(8) carrier multiplicity (`ShellStructure.octetCapacity = carrierMultiplicity = 8`). -/
def octetSharedPairCapacity (valence : ℝ) : ℝ := (octetCapacity : ℝ) - valence

/-- Carbon (valence 4) has shared-pair capacity 4 — read off the carrier octet, not a literal. -/
theorem octetSharedPairCapacity_carbon : octetSharedPairCapacity 4 = 4 := by
  unfold octetSharedPairCapacity; rw [octetCapacity_real]; norm_num

/-- What one atom commits to each of its bonds: `cap / k` on its own coordination. -/
def atomPerBondOffer (cap k : ℝ) : ℝ := cap / k

/-- Symmetric (homonuclear, uniform-coordination) bond order `p = cap / k`. -/
def networkBondOrder (cap k : ℝ) : ℝ := cap / k

/-- **Partition identity**: the per-bond orders sum back to the octet capacity, `p·k = cap`. The
conservation that makes the coordination split lossless. -/
theorem bondOrder_partition (cap k : ℝ) (hk : k ≠ 0) :
    networkBondOrder cap k * k = cap := by
  unfold networkBondOrder; field_simp

/-- **More neighbours ⇒ lower per-bond order**: at fixed positive capacity the bond order is
strictly antitone in the coordination (diamond k=4 single < graphite k=3 < carbyne k=2). -/
theorem bondOrder_antitone_in_coordination
    (cap k₁ k₂ : ℝ) (hcap : 0 < cap) (hk₁ : 0 < k₁) (hlt : k₁ < k₂) :
    networkBondOrder cap k₂ < networkBondOrder cap k₁ := by
  unfold networkBondOrder; exact div_lt_div_of_pos_left hcap hk₁ hlt

/-- Carbon's allotrope orders: diamond (k=4) single, graphite (k=3) `4/3`, carbyne (k=2) double. -/
theorem carbon_allotrope_orders :
    networkBondOrder (octetSharedPairCapacity 4) 4 = 1 ∧
      networkBondOrder (octetSharedPairCapacity 4) 3 = 4 / 3 ∧
        networkBondOrder (octetSharedPairCapacity 4) 2 = 2 := by
  rw [octetSharedPairCapacity_carbon]
  refine ⟨by norm_num [networkBondOrder], by norm_num [networkBondOrder],
    by norm_num [networkBondOrder]⟩

/-- **The triple-bond ceiling forbids one-coordinate carbon.** A single carbon neighbour (`k = 1`)
would demand bond order `4`, above the `maxBondOrder = 3` ceiling — so C≣C-terminated carbyne caps
at the triple bond, never a quadruple. -/
theorem carbon_k_one_exceeds_ceiling :
    (maxBondOrder : ℝ) < networkBondOrder (octetSharedPairCapacity 4) 1 := by
  rw [octetSharedPairCapacity_carbon, maxBondOrder_real]; norm_num [networkBondOrder]

/-! ## Heavy-bond offer and the aromatic 3/2 -/

/-- **Capacity-conserving heavy-bond offer**: each X–H contact pins one shared pair, leaving the
budget first, and the residual splits over the heavy neighbours: `(cap − n_H)/k_heavy`. -/
def heavyBondOffer (cap nH kHeavy : ℝ) : ℝ := (cap - nH) / kHeavy

/-- With no hydrogen neighbours the heavy-bond offer is the plain `cap/k` offer (O₂/O₃/CO₂/diamond
untouched). -/
theorem heavyBondOffer_no_hydrogen (cap k : ℝ) :
    heavyBondOffer cap 0 k = atomPerBondOffer cap k := by
  unfold heavyBondOffer atomPerBondOffer; ring_nf

/-- **Aromatic ring order is 3/2.** A benzene-ring carbon (cap 4, one C–H, two ring bonds) offers
`(4−1)/2 = 3/2`, so each symmetric ring bond is `√(3/2·3/2) = 3/2` — the Kekulé average — using the
spine bond-order combiner (below the triple ceiling). -/
theorem aromaticRingOrder_three_halves :
    geometricBondOrder (heavyBondOffer 4 1 2) (heavyBondOffer 4 1 2) = 3 / 2 := by
  have h : heavyBondOffer 4 1 2 = 3 / 2 := by unfold heavyBondOffer; norm_num
  rw [h]
  exact ShellStructure.geometricBondOrder_homonuclear (3 / 2) (by norm_num)
    (by rw [maxBondOrder_real]; norm_num)

/-- **Ozone's asymmetric bond lands strictly between single and double.** Terminal offer `2`,
central offer `1` give a ring order bracketed by `1 ≤ √2 ≤ 2`. -/
theorem ozone_bond_brackets :
    1 ≤ geometricBondOrder 1 2 ∧ geometricBondOrder 1 2 ≤ 2 := by
  have hcap : Real.sqrt (1 * 2) ≤ (maxBondOrder : ℝ) := by
    rw [maxBondOrder_real, show (1 : ℝ) * 2 = 2 by norm_num]
    calc Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
      _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      _ ≤ 3 := by norm_num
  have h := ShellStructure.geometricBondOrder_brackets 1 2 (by norm_num) (by norm_num) hcap
  rwa [min_eq_left (by norm_num : (1 : ℝ) ≤ 2), max_eq_right (by norm_num : (1 : ℝ) ≤ 2)] at h

/-! ## Ring strain: VSEPR angle vs regular-polygon interior angle -/

/-- Interior angle (degrees) of a regular planar `n`-gon. -/
def polygonInteriorAngleDeg (n : ℝ) : ℝ := (n - 2) * 180 / n

/-- **Benzene closes strain-free.** The regular hexagon interior angle equals the sp² trigonal
angle `120°` exactly, so an aromatic six-ring has zero angular strain. -/
theorem hexagon_matches_sp2 : polygonInteriorAngleDeg 6 = 120 := by
  unfold polygonInteriorAngleDeg; norm_num

/-- The regular pentagon interior angle is `108°` — within ~1.5° of tetrahedral `109.47°`, so the
sp³ furanose five-ring is the strain-minimal saturated ring. -/
theorem pentagon_interior : polygonInteriorAngleDeg 5 = 108 := by
  unfold polygonInteriorAngleDeg; norm_num

/-- The three-membered ring is acutely strained for sp³ centres: interior `60°` vs `109.47°`. -/
theorem triangle_interior : polygonInteriorAngleDeg 3 = 60 := by
  unfold polygonInteriorAngleDeg; norm_num

/-- **Larger rings open their interior angle** (strictly monotone in `n`), so the polygon angle
sweeps up to meet each hybridization's preferred angle exactly once. -/
theorem polygonInteriorAngle_strictMono :
    StrictMonoOn polygonInteriorAngleDeg (Set.Ici 1) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  have ha0 : 0 < a := by linarith
  unfold polygonInteriorAngleDeg
  have h1 : (a - 2) * 180 / a = 180 - 360 / a := by field_simp; ring
  have h2 : (b - 2) * 180 / b = 180 - 360 / b := by field_simp; ring
  rw [h1, h2]
  have hlt : 360 / b < 360 / a := div_lt_div_of_pos_left (by norm_num) ha0 hab
  linarith

/-! ## σ-framework angle (anchored to the VSEPR equilibrium) -/

/-- VSEPR bond-angle cosine `cos θ = −1/(d−1)` for `d` steric domains. -/
def bondAngleCos (d : ℝ) : ℝ := -1 / (d - 1)

/-- **The allotrope σ-angle is the derived VSEPR equilibrium cosine**, not a posited value: for `d`
balanced symmetric unit contacts the forced common cosine is exactly `bondAngleCos d`. -/
theorem bondAngleCos_eq_vsepr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d : ℕ) (hd : 2 ≤ d) (v : Fin d → E)
    (hunit : ∀ i, ⟪v i, v i⟫ = (1 : ℝ)) (hsum : ∑ i, v i = 0)
    (c : ℝ) (hsym : ∀ i j, i ≠ j → ⟪v i, v j⟫ = c) :
    c = bondAngleCos (d : ℝ) :=
  VSEPR.balanced_unit_contacts_cos d hd v hunit hsum c hsym

/-- The tetrahedral (sp³, diamond) angle: `d = 4 ⇒ cos θ = −1/3`. -/
theorem bondAngleCos_tetrahedral : bondAngleCos 4 = -1 / 3 := by
  unfold bondAngleCos; norm_num

/-- The trigonal (sp², graphite) angle: `d = 3 ⇒ cos θ = −1/2` (θ = 120°). -/
theorem bondAngleCos_trigonal : bondAngleCos 3 = -1 / 2 := by
  unfold bondAngleCos; norm_num

/-- The linear (sp, carbyne) angle: `d = 2 ⇒ cos θ = −1` (θ = 180°). -/
theorem bondAngleCos_linear : bondAngleCos 2 = -1 := by
  unfold bondAngleCos; norm_num

/-! ## Bond-order length contraction (strong = monogamy half) -/

/-- The carrier-contact strength `strong = 1/monogamyPairMultiplicity = 1/2`, the monogamy half. -/
def monogamyHalf : ℝ := 1 / (monogamyPairMultiplicity : ℝ)

theorem monogamyHalf_eq : monogamyHalf = 1 / 2 := by
  unfold monogamyHalf; rw [show (monogamyPairMultiplicity : ℝ) = 2 from by
    rw [show monogamyPairMultiplicity = 2 from rfl]; norm_num]

/-- Bond-order contraction factor `1/(1 + (p−1)·strong/4)`. -/
def fractionalLengthScale (p strong : ℝ) : ℝ := 1 / (1 + (p - 1) * strong / 4)

/-- Per-bond length = single-bond carrier `r₁` times the fractional-order contraction. -/
def networkBondLength (r1 p strong : ℝ) : ℝ := r1 * fractionalLengthScale p strong

/-- At bond order 1 (all-single network) there is no contraction: scale = 1. -/
theorem fractionalLengthScale_at_one (strong : ℝ) : fractionalLengthScale 1 strong = 1 := by
  unfold fractionalLengthScale; norm_num

/-- **Higher order ⇒ shorter bond**: for `p ≥ 1` and `strong > 0` the contraction factor is
antitone in the bond order, so a higher-order network has a shorter bond. -/
theorem lengthScale_antitone_in_order
    (p₁ p₂ strong : ℝ) (hstrong : 0 < strong) (hp₁ : 1 ≤ p₁) (hle : p₁ ≤ p₂) :
    fractionalLengthScale p₂ strong ≤ fractionalLengthScale p₁ strong := by
  unfold fractionalLengthScale
  have hd₁ : 0 < 1 + (p₁ - 1) * strong / 4 := by nlinarith
  exact one_div_le_one_div_of_le hd₁ (by nlinarith)

end

end HqivSpine.Chemistry.Allotrope

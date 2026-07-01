import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic

/-!
# Intramolecular network allotropes from first principles

Lean counterpart of `scripts/hqiv_allotrope_network.py`.

Same atoms, different bond graph (diamond vs graphite vs carbyne; the S₈ ring) are not new
chemistry — they are one geometric law applied to different coordinations.  An atom commits a
fixed octet shared-pair budget

  `cap(Z) = 8 − valence`

and an allotrope *partitions* that budget across its `k` bonded neighbours (the coordination
number — the allotrope label).  Each atom commits `cap/k` to each of its bonds, and a bond's order
is the **geometric mean** of its two endpoints' offers (`√(oᵢ oⱼ)`) — the same combiner the
heteronuclear bond geometry and the nuclear binding use, so the two ends of an asymmetric bond can
differ (O₃: terminal offer 2, central offer 1 → √2).  A symmetric bond reduces to `p = cap/k`, so
diamond/graphite/O₂ are unchanged.  The σ-framework angle is
the VSEPR steric-domain angle `θ = arccos(−1/(d−1))` with `d = k + lone pairs`, and the bond
length contracts on the single-bond carrier contact by `1/(1 + (p−1)·strong/4)`.  The allowed
coordination spectrum (which allotropes exist) is forced by `1 ≤ p ≤ 3`.

This module records those maps and proves the structural identities the Python readout relies on:
the partition identity `p·k = cap`, monotonicity of order in coordination, the exact tetrahedral/
trigonal/linear angle cosines, and the length-contraction bracket.  No fitted coefficients and no
empirical bond tables appear here.
-/

namespace Hqiv.QuantumChemistry.AllotropeNetwork

noncomputable section

open Real

/-- Octet shared-pair capacity `cap = 8 − valence` (the bond-order budget to partition). -/
def octetSharedPairCapacity (valence : ℝ) : ℝ := 8 - valence

/-- What one atom commits to each of its bonds: `cap / k` on its own coordination. -/
def atomPerBondOffer (cap k : ℝ) : ℝ := cap / k

/-- **Bond-resolved order**: a bond is one shared contact between two atoms, so its order is the
geometric mean of the two endpoints' per-bond offers — the same `√(·)` combiner the heteronuclear
bond geometry and the nuclear binding use.  This is what lets the two ends of an asymmetric
network bond differ (the O₃ insight). -/
def geometricBondOrder (offerI offerJ : ℝ) : ℝ := Real.sqrt (offerI * offerJ)

/-- Symmetric (homonuclear, uniform-coordination) bond order `p = cap / k` is the special case
of the geometric-mean combiner with equal endpoint offers. -/
def networkBondOrder (cap k : ℝ) : ℝ := cap / k

/-- A symmetric bond reduces the geometric mean to the common offer: `√(o·o) = o` for `o ≥ 0`.
Diamond/graphite/O₂ are therefore left exactly at `cap/k`. -/
theorem geometricBondOrder_symmetric (o : ℝ) (ho : 0 ≤ o) :
    geometricBondOrder o o = o := by
  unfold geometricBondOrder
  rw [← pow_two, Real.sqrt_sq ho]

/-- **Geometric mean brackets the two offers**: `min ≤ order ≤ max`.  An asymmetric bond can be
neither stiffer than its strongest end nor weaker than its weakest — O₃ lands strictly between
the single-bond (1) and double-bond (2) ends. -/
theorem geometricBondOrder_brackets
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    a ≤ geometricBondOrder a b ∧ geometricBondOrder a b ≤ b := by
  have hb : 0 ≤ b := le_trans ha hab
  unfold geometricBondOrder
  constructor
  · calc a = Real.sqrt (a * a) := (geometricBondOrder_symmetric a ha).symm
      _ ≤ Real.sqrt (a * b) := by
          apply Real.sqrt_le_sqrt; nlinarith
  · calc Real.sqrt (a * b) ≤ Real.sqrt (b * b) := by
          apply Real.sqrt_le_sqrt; nlinarith
      _ = b := geometricBondOrder_symmetric b hb

/-- **Capacity-conserving heavy-bond offer**: each X–H contact pins one shared pair (hydrogen has
one electron), so those pinned pairs leave the budget first and the *residual* splits over the
heavy neighbours: `(cap − n_H) / k_heavy`.  This is what makes aromatic rings come out right. -/
def heavyBondOffer (cap nH kHeavy : ℝ) : ℝ := (cap - nH) / kHeavy

/-- **Aromatic ring order is 3/2.** A benzene ring carbon (cap 4, one C–H, two ring bonds) offers
`(4−1)/2 = 3/2`, so each symmetric ring bond is `√(3/2·3/2) = 3/2` — the Kekulé average — not the
`4/3` a naïve `cap/k` over all three bonds would give. -/
theorem aromaticRingOrder_three_halves :
    geometricBondOrder (heavyBondOffer 4 1 2) (heavyBondOffer 4 1 2) = 3 / 2 := by
  have h : heavyBondOffer 4 1 2 = 3 / 2 := by unfold heavyBondOffer; norm_num
  rw [h, geometricBondOrder_symmetric (3 / 2) (by norm_num)]

/-- With no hydrogen neighbours the heavy-bond offer is exactly the symmetric `cap/k` offer:
the H-pinning refinement leaves O₂/O₃/CO₂/diamond untouched. -/
theorem heavyBondOffer_no_hydrogen (cap k : ℝ) :
    heavyBondOffer cap 0 k = atomPerBondOffer cap k := by
  unfold heavyBondOffer atomPerBondOffer; ring_nf

/-! ## Ring strain: VSEPR angle vs regular-polygon interior angle

A flat ring is unstrained exactly when its atoms' preferred VSEPR angle equals the polygon interior
angle `(n−2)·180/n`.  sp² closes perfectly at the hexagon (benzene), sp³ is nearly perfect at the
pentagon (the furanose sugar) — the angular reason five- and six-membered rings dominate biology. -/

/-- Interior angle (degrees) of a regular planar `n`-gon. -/
def polygonInteriorAngleDeg (n : ℝ) : ℝ := (n - 2) * 180 / n

/-- The trigonal (sp²) VSEPR angle in degrees: `arccos(−1/2) = 120°`. -/
def trigonalAngleDeg : ℝ := 120

/-- **Benzene closes strain-free.** The regular hexagon interior angle equals the sp² trigonal
angle exactly, so an aromatic six-ring has zero angular strain. -/
theorem hexagon_matches_sp2 : polygonInteriorAngleDeg 6 = trigonalAngleDeg := by
  unfold polygonInteriorAngleDeg trigonalAngleDeg; norm_num

/-- The regular pentagon interior angle is `108°` — within ~1.5° of the tetrahedral `109.47°`, so
the sp³ furanose five-ring is the strain-minimal saturated ring. -/
theorem pentagon_interior : polygonInteriorAngleDeg 5 = 108 := by
  unfold polygonInteriorAngleDeg; norm_num

/-- The three-membered ring is acutely strained for sp³ centres: interior `60°` vs `109.47°`. -/
theorem triangle_interior : polygonInteriorAngleDeg 3 = 60 := by
  unfold polygonInteriorAngleDeg; norm_num

/-- **Larger rings open their interior angle** (monotone in `n`), so the polygon angle sweeps up to
meet each hybridization's preferred angle exactly once — a single crossing fixes the favoured size. -/
theorem polygonInteriorAngle_strictMono :
    StrictMonoOn polygonInteriorAngleDeg (Set.Ici 1) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  unfold polygonInteriorAngleDeg
  have h1 : (a - 2) * 180 / a = 180 - 360 / a := by field_simp; ring
  have h2 : (b - 2) * 180 / b = 180 - 360 / b := by field_simp; ring
  rw [h1, h2]
  have hlt : 360 / b < 360 / a := div_lt_div_of_pos_left (by norm_num) ha0 hab
  linarith

/-- σ-framework steric domains `d = k + lonePairs`. -/
def stericDomains (k lonePairs : ℝ) : ℝ := k + lonePairs

/-- VSEPR bond-angle cosine `cos θ = −1/(d−1)`. -/
def bondAngleCos (d : ℝ) : ℝ := -1 / (d - 1)

/-- Bond-order contraction factor `1/(1 + (p−1)·strong/4)` (strong = ½). -/
def fractionalLengthScale (p strong : ℝ) : ℝ := 1 / (1 + (p - 1) * strong / 4)

/-- Per-bond length = single-bond carrier `r₁` times the fractional-order contraction. -/
def networkBondLength (r1 p strong : ℝ) : ℝ := r1 * fractionalLengthScale p strong

/-- **Partition identity**: the per-bond orders sum back to the octet capacity, `p·k = cap`.
This is the conservation that makes the coordination split lossless. -/
theorem bondOrder_partition (cap k : ℝ) (hk : k ≠ 0) :
    networkBondOrder cap k * k = cap := by
  unfold networkBondOrder
  field_simp

/-- **More neighbours ⇒ lower per-bond order**: at fixed positive capacity the bond order is
strictly antitone in the coordination number (diamond k=4 single < graphite k=3 < carbyne k=2). -/
theorem bondOrder_antitone_in_coordination
    (cap k₁ k₂ : ℝ) (hcap : 0 < cap) (hk₁ : 0 < k₁) (hlt : k₁ < k₂) :
    networkBondOrder cap k₂ < networkBondOrder cap k₁ := by
  unfold networkBondOrder
  exact div_lt_div_of_pos_left hcap hk₁ hlt

/-- The tetrahedral (sp³, diamond) angle: `d = 4 ⇒ cos θ = −1/3`. -/
theorem bondAngleCos_tetrahedral : bondAngleCos 4 = -1 / 3 := by
  unfold bondAngleCos; norm_num

/-- The trigonal (sp², graphite) angle: `d = 3 ⇒ cos θ = −1/2` (θ = 120°). -/
theorem bondAngleCos_trigonal : bondAngleCos 3 = -1 / 2 := by
  unfold bondAngleCos; norm_num

/-- The linear (sp, carbyne) angle: `d = 2 ⇒ cos θ = −1` (θ = 180°). -/
theorem bondAngleCos_linear : bondAngleCos 2 = -1 := by
  unfold bondAngleCos; norm_num

/-- At bond order 1 (all-single network) there is no contraction: scale = 1. -/
theorem fractionalLengthScale_at_one (strong : ℝ) : fractionalLengthScale 1 strong = 1 := by
  unfold fractionalLengthScale; norm_num

/-- **Higher order ⇒ shorter bond**: for `p ≥ 1` and `strong > 0` the contraction factor is
antitone in the bond order, so a network with higher fractional order has a shorter bond. -/
theorem lengthScale_antitone_in_order
    (p₁ p₂ strong : ℝ) (hstrong : 0 < strong) (hp₁ : 1 ≤ p₁) (hle : p₁ ≤ p₂) :
    fractionalLengthScale p₂ strong ≤ fractionalLengthScale p₁ strong := by
  unfold fractionalLengthScale
  have hd₁ : 0 < 1 + (p₁ - 1) * strong / 4 := by nlinarith
  have hd₂ : 0 < 1 + (p₂ - 1) * strong / 4 := by nlinarith
  apply div_le_div_of_nonneg_left (by norm_num) hd₁
  nlinarith

end

end Hqiv.QuantumChemistry.AllotropeNetwork

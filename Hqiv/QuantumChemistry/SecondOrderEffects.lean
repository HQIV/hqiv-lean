import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.HQIVNuclei
import Hqiv.QuantumChemistry.CoupledRelaxation
import HqivSpine.Physics.GeneratorDependentCoupling

/-!
# Second-order chemistry effect slots (n-body ready)

The chemistry-extent paper (`papers/lightcone_chemistry_extent`) promises that every
"second-order" treatment used by the Python witnesses has a *formal target* before it
is turned into a number: a new finite object built from the already-proved slots, kept
algebraic in the foundation-anchored quantities `α = 3/5`, `γ = 2/5`, carrier
multiplicity `8` (so `strongChannelFraction = 4/8`), and `referenceM = 4`.

`scripts/hqiv_second_order_effect_audit.py` evaluates four derived-but-optional
second-order multipliers on the active binding chart, *without fitting any
coefficient*:

* `c2_lapse`               — lapse-concentration feedback `C₂(ξ) / C₂(ξ_lock)`;
* `outside_geff`           — `1 + (4/8)·(Σ G_eff / surplus)`;
* `vev_cluster_taylor`     — `(networked_vev / bare_vev)^α`;
* `graph_hyperclosure_weak`— `1 + (4/8)·(1 − 1/√n_bonds)` for `n_bonds ≥ 2`.

The **n-body second-order envelope** (`nBodySecondOrderEnvelope`) multiplies those
slots by the preferred-axis spectral-gap dress
(`preferredAxisPlaneLocalDressOfSpectrum`), so the same algebra covers diatomics and
polyatomics: bond-summed outside `G_eff`, bond-polarity spectral gap, and optional
scalar toggles.  No molecule-type case statement.

Each factor collapses to `1` at its trivial / lock-in argument, so promoting a
second-order term can never silently move the base readout.

No comparison residual, no fitted coefficient, and no new axiom enters here; the two
foundation constants are re-used from the proved spine
(`Hqiv.alpha`, `Hqiv.Physics.strongChannelFraction`).
-/

namespace Hqiv.QuantumChemistry

open Hqiv
open Hqiv.Physics
open HqivSpine.Physics.GeneratorDependentCoupling

noncomputable section

/-- A second-order treatment is a single multiplier applied to a proved base readout. -/
def secondOrderReadout (base factor : ℝ) : ℝ := base * factor

/-- A unit multiplier leaves the base readout untouched (this is what "no second-order
term" means in the audit). -/
theorem secondOrderReadout_unit (base : ℝ) : secondOrderReadout base 1 = base := by
  unfold secondOrderReadout; ring

/-! ## 1. Lapse-concentration feedback `C₂(ξ)/C₂(ξ_lock)` -/

/-- Ratio of the Rindler-dressed lapse concentration at epoch `ξ` to its value at the
lock-in shell.  Inputs are supplied by the proved `tuftLapseConcentrationAtXi` layer. -/
def c2LapseFeedback (c2Xi c2Lock : ℝ) : ℝ := c2Xi / c2Lock

/-- At lock-in the feedback is exactly `1`: the base readout is recovered. -/
theorem c2LapseFeedback_lockin (c2Lock : ℝ) (h : c2Lock ≠ 0) :
    c2LapseFeedback c2Lock c2Lock = 1 :=
  div_self h

/-- The feedback is positive whenever both concentrations are positive. -/
theorem c2LapseFeedback_pos (c2Xi c2Lock : ℝ) (hx : 0 < c2Xi) (hl : 0 < c2Lock) :
    0 < c2LapseFeedback c2Xi c2Lock :=
  div_pos hx hl

/-! ## 2. Outside `G_eff` contact surplus -/

/-- Outside closure surplus `1 + (4/8)·(Σ G_eff / surplus)`.  `geffSum` is the summed
outside `G_eff(θ)` over the covalent bonds; `surplus` is the network binding surplus. -/
def outsideGeffSurplus (geffSum surplus : ℝ) : ℝ :=
  1 + strongChannelFraction * (geffSum / surplus)

/-- With no outside contact contribution the surplus factor is exactly `1`. -/
theorem outsideGeffSurplus_base (surplus : ℝ) :
    outsideGeffSurplus 0 surplus = 1 := by
  unfold outsideGeffSurplus; simp

/-- The surplus factor is at least `1` for a nonnegative contact sum over a positive
surplus (the physical regime), since `strongChannelFraction = 4/8 ≥ 0`. -/
theorem outsideGeffSurplus_ge_one (geffSum surplus : ℝ)
    (hg : 0 ≤ geffSum) (hs : 0 < surplus) :
    1 ≤ outsideGeffSurplus geffSum surplus := by
  unfold outsideGeffSurplus
  have hscf : (0:ℝ) ≤ strongChannelFraction := by
    unfold strongChannelFraction; norm_num
  have hdiv : (0:ℝ) ≤ geffSum / surplus := div_nonneg hg hs.le
  nlinarith [mul_nonneg hscf hdiv]

/-! ## 3. Vev cluster Taylor factor `(vev/vev_bare)^α` -/

/-- The networked/bare vev ratio raised to the lattice imprint exponent `α = 3/5`. -/
def vevClusterTaylor (vev vevBare : ℝ) : ℝ := (vev / vevBare) ^ alpha

/-- When the networked vev equals its bare value the Taylor factor is exactly `1`. -/
theorem vevClusterTaylor_base (vevBare : ℝ) (h : vevBare ≠ 0) :
    vevClusterTaylor vevBare vevBare = 1 := by
  unfold vevClusterTaylor
  rw [div_self h, Real.one_rpow]

/-- The Taylor factor is positive for positive vevs. -/
theorem vevClusterTaylor_pos (vev vevBare : ℝ) (hv : 0 < vev) (hb : 0 < vevBare) :
    0 < vevClusterTaylor vev vevBare :=
  Real.rpow_pos_of_pos (div_pos hv hb) alpha

/-- A networked vev at least as large as the bare vev gives a factor `≥ 1` (because
`α ≥ 0` and the base ratio is `≥ 1`). -/
theorem vevClusterTaylor_ge_one (vev vevBare : ℝ)
    (hb : 0 < vevBare) (hvb : vevBare ≤ vev) :
    1 ≤ vevClusterTaylor vev vevBare := by
  unfold vevClusterTaylor
  have hratio : (1:ℝ) ≤ vev / vevBare := by
    rw [le_div_iff₀ hb]; linarith
  have halpha : (0:ℝ) ≤ alpha := by rw [alpha_eq_3_5]; norm_num
  calc (1:ℝ) = (1:ℝ) ^ alpha := (Real.one_rpow alpha).symm
    _ ≤ (vev / vevBare) ^ alpha := Real.rpow_le_rpow (by norm_num) hratio halpha

/-! ## 4. Graph hyperclosure weak lift -/

/-- Graph-level weak hyperclosure lift `1 + (4/8)·(1 − 1/√n)` for `n ≥ 2` bonds, and
`1` for a single bond (nothing to close). -/
def graphHyperclosureWeak (nBonds : ℕ) : ℝ :=
  if nBonds < 2 then 1
  else 1 + strongChannelFraction * (1 - 1 / Real.sqrt (nBonds : ℝ))

/-- Fewer than two bonds means no hyperclosure lift. -/
theorem graphHyperclosureWeak_trivial (nBonds : ℕ) (h : nBonds < 2) :
    graphHyperclosureWeak nBonds = 1 := by
  unfold graphHyperclosureWeak; rw [if_pos h]

/-- The weak hyperclosure lift is always at least `1`. -/
theorem graphHyperclosureWeak_ge_one (nBonds : ℕ) :
    1 ≤ graphHyperclosureWeak nBonds := by
  unfold graphHyperclosureWeak
  split
  · exact le_refl 1
  · rename_i h
    push_neg at h
    have hn1 : (1:ℝ) ≤ (nBonds : ℝ) := by
      have : (1:ℕ) ≤ nBonds := le_trans (by norm_num) h
      exact_mod_cast this
    have hsqrt : (1:ℝ) ≤ Real.sqrt (nBonds : ℝ) := by
      have := Real.sqrt_le_sqrt hn1
      rwa [Real.sqrt_one] at this
    have hpos : (0:ℝ) < Real.sqrt (nBonds : ℝ) := lt_of_lt_of_le one_pos hsqrt
    have hle1 : 1 / Real.sqrt (nBonds : ℝ) ≤ 1 := (div_le_one hpos).mpr hsqrt
    have hscf : (0:ℝ) ≤ strongChannelFraction := by
      unfold strongChannelFraction; norm_num
    nlinarith [mul_nonneg hscf (by linarith : (0:ℝ) ≤ 1 - 1 / Real.sqrt (nBonds : ℝ))]

/-! ## Combined second-order multiplier -/

/-- The product of the four derived second-order factors. -/
def secondOrderMultiplier
    (c2Xi c2Lock geffSum surplus vev vevBare : ℝ) (nBonds : ℕ) : ℝ :=
  c2LapseFeedback c2Xi c2Lock * outsideGeffSurplus geffSum surplus *
    vevClusterTaylor vev vevBare * graphHyperclosureWeak nBonds

/-- At every factor's trivial / lock-in argument the combined multiplier is exactly
`1`.  This is the formal statement of the audit's "base" column: with all derived
toggles at their neutral value the second-order treatment reproduces the proved base
readout. -/
theorem secondOrderMultiplier_trivial
    (c2Lock vevBare surplus : ℝ) (hc : c2Lock ≠ 0) (hv : vevBare ≠ 0) :
    secondOrderMultiplier c2Lock c2Lock 0 surplus vevBare vevBare 0 = 1 := by
  unfold secondOrderMultiplier
  rw [c2LapseFeedback_lockin c2Lock hc, outsideGeffSurplus_base surplus,
    vevClusterTaylor_base vevBare hv, graphHyperclosureWeak_trivial 0 (by norm_num)]
  ring

/-- Consequently, the second-order readout at neutral toggles equals the base readout. -/
theorem secondOrderReadout_trivial
    (base c2Lock vevBare surplus : ℝ) (hc : c2Lock ≠ 0) (hv : vevBare ≠ 0) :
    secondOrderReadout base
        (secondOrderMultiplier c2Lock c2Lock 0 surplus vevBare vevBare 0) = base := by
  rw [secondOrderMultiplier_trivial c2Lock vevBare surplus hc hv, secondOrderReadout_unit]

/-- In the fully physical regime (positive concentrations, nonnegative outside contact
over a positive surplus, networked vev not below bare) the combined multiplier is
positive: a second-order treatment never flips the sign of a proved readout. -/
theorem secondOrderMultiplier_pos
    (c2Xi c2Lock geffSum surplus vev vevBare : ℝ) (nBonds : ℕ)
    (hx : 0 < c2Xi) (hl : 0 < c2Lock)
    (hg : 0 ≤ geffSum) (hs : 0 < surplus)
    (hv : 0 < vev) (hb : 0 < vevBare) :
    0 < secondOrderMultiplier c2Xi c2Lock geffSum surplus vev vevBare nBonds := by
  unfold secondOrderMultiplier
  have h1 : 0 < c2LapseFeedback c2Xi c2Lock := c2LapseFeedback_pos c2Xi c2Lock hx hl
  have h2 : 0 < outsideGeffSurplus geffSum surplus :=
    lt_of_lt_of_le one_pos (outsideGeffSurplus_ge_one geffSum surplus hg hs)
  have h3 : 0 < vevClusterTaylor vev vevBare := vevClusterTaylor_pos vev vevBare hv hb
  have h4 : 0 < graphHyperclosureWeak nBonds :=
    lt_of_lt_of_le one_pos (graphHyperclosureWeak_ge_one nBonds)
  exact mul_pos (mul_pos (mul_pos h1 h2) h3) h4

/-! ## N-body second-order envelope (promoted + optional slots) -/

/-- **Promoted n-body second-order factor** (live chart):

`outsideGeffSurplus · preferredAxisPlaneLocalDress η g`

with `g` the preferred-axis spectral gap of the bond-polarity spectrum.
This is the molecule-type-free second-order dress already in
`scripts/hqiv_dynamic_binding_chart.py`. -/
noncomputable def nBodyPromotedSecondOrderFactor
    (geffSum surplus eta g : ℝ) : ℝ :=
  outsideGeffSurplus geffSum surplus * preferredAxisPlaneLocalDress eta g

/-- **Full n-body second-order envelope**: scalar audit slots × preferred-axis dress.

```
factor = c2 · outside_geff · vev_taylor · hyperclosure · preferredAxisDress(η, g)
```

At neutral toggles (`c2` lock-in, `geffSum = 0`, `vev = vevBare`, `nBonds < 2`,
`g = 0`) the factor is exactly `1`. -/
noncomputable def nBodySecondOrderEnvelope
    (c2Xi c2Lock geffSum surplus vev vevBare eta g : ℝ) (nBonds : ℕ) : ℝ :=
  secondOrderMultiplier c2Xi c2Lock geffSum surplus vev vevBare nBonds *
    preferredAxisPlaneLocalDress eta g

/-- Promoted factor is the envelope with optional slots at identity. -/
theorem nBodyPromoted_eq_envelope_neutral_optional
    (c2Lock geffSum surplus vevBare eta g : ℝ) (hc : c2Lock ≠ 0) (hv : vevBare ≠ 0) :
    nBodyPromotedSecondOrderFactor geffSum surplus eta g =
      nBodySecondOrderEnvelope c2Lock c2Lock geffSum surplus vevBare vevBare eta g 0 := by
  unfold nBodyPromotedSecondOrderFactor nBodySecondOrderEnvelope secondOrderMultiplier
  rw [c2LapseFeedback_lockin c2Lock hc, vevClusterTaylor_base vevBare hv,
    graphHyperclosureWeak_trivial 0 (by norm_num)]
  ring

theorem nBodySecondOrderEnvelope_trivial
    (c2Lock vevBare surplus eta : ℝ) (hc : c2Lock ≠ 0) (hv : vevBare ≠ 0) :
    nBodySecondOrderEnvelope c2Lock c2Lock 0 surplus vevBare vevBare eta 0 0 = 1 := by
  unfold nBodySecondOrderEnvelope
  rw [secondOrderMultiplier_trivial c2Lock vevBare surplus hc hv,
    preferredAxisPlaneLocalDress_zero_axis]
  ring

/-- N-body second-order readout: `base × envelope`. -/
noncomputable def nBodySecondOrderReadout
    (base c2Xi c2Lock geffSum surplus vev vevBare eta g : ℝ) (nBonds : ℕ) : ℝ :=
  secondOrderReadout base
    (nBodySecondOrderEnvelope c2Xi c2Lock geffSum surplus vev vevBare eta g nBonds)

theorem nBodySecondOrderReadout_trivial
    (base c2Lock vevBare surplus eta : ℝ) (hc : c2Lock ≠ 0) (hv : vevBare ≠ 0) :
    nBodySecondOrderReadout base c2Lock c2Lock 0 surplus vevBare vevBare eta 0 0 = base := by
  unfold nBodySecondOrderReadout
  rw [nBodySecondOrderEnvelope_trivial c2Lock vevBare surplus eta hc hv,
    secondOrderReadout_unit]

end

end Hqiv.QuantumChemistry

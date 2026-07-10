import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import HqivSpine.Physics.Binding
import HqivSpine.Physics.ColorCasimir
import HqivSpine.Physics.Forces
import HqivSpine.Physics.NonAbelianMatrixElement
import HqivSpine.Physics.SystemMatrixFunctors
import HqivSpine.Algebra.So8

/-!
# `HqivSpine.Physics.GeneratorDependentCoupling` — plane-local / colour-filtered cells

`SystemMatrixFunctors.shellProject_eq_of_weight_sum` proved that continuous SO(8)
weight redistribution is a **no-op** on `E_bind_from_network` while
`bindingCouplingAtShell` is generator-independent.  This module supplies the missing
generator dependence:

* each `So8Index` is identified with an ordered carrier plane `(i,j)` via the
  standard `𝔰𝔬(8)` skew basis;
* a plane is **strong** when both endpoints lie in `strongComponents` `{4,5,6,7}`;
* strong planes receive the derived colour-chart filter `C_A/C_F = 9/4`;
  all other planes keep filter `1`;
* the plane-local binding energy is `∑_k w_k · coupling(m) · filter(k)`.

With this cell, moving weight onto (or off) strong planes **changes** the readout.
The identity / zero-promotion limits recover the abelian network binding, so the
upgrade is still knob-free.

Foundation anchors: `α = 3/5`, carrier `8`, `C_A/C_F = 9/4`, strong-channel fraction
`4/8`.  No PDG masses, no fitted coefficients, no `sorry`.
-/

namespace HqivSpine.Physics.GeneratorDependentCoupling

open BigOperators
open HqivSpine.Physics
open HqivSpine.Physics.NonAbelianMatrixElement
open HqivSpine.Physics.SystemMatrixFunctors
open HqivSpine.Algebra

/-! ## So(8) index ↔ ordered carrier plane -/

/-- Canonical enumeration of the 28 ordered pairs `i < j` in `Fin 8`. -/
noncomputable def so8PlaneEquiv : So8Index ≃ OrderedPair 8 :=
  (Fintype.equivFin (OrderedPair 8)).symm

/-- The ordered carrier plane attached to generator index `k`. -/
noncomputable def planeOfIndex (k : So8Index) : OrderedPair 8 :=
  so8PlaneEquiv k

/-- Lower / upper carrier indices of generator `k`. -/
noncomputable def planeLow (k : So8Index) : Fin 8 := (planeOfIndex k).1.1
noncomputable def planeHigh (k : So8Index) : Fin 8 := (planeOfIndex k).1.2

theorem planeLow_lt_planeHigh (k : So8Index) : planeLow k < planeHigh k :=
  (planeOfIndex k).2

/-! ## Strong-plane predicate -/

/-- A plane is strong when both endpoints sit in the strong octonion mask. -/
noncomputable def planeIsStrong (k : So8Index) : Prop :=
  planeLow k ∈ strongComponents ∧ planeHigh k ∈ strongComponents

noncomputable instance planeIsStrong.decidable (k : So8Index) : Decidable (planeIsStrong k) := by
  unfold planeIsStrong; infer_instance

/-- Boolean strong-plane mask (for Python / readout mirrors). -/
noncomputable def planeIsStrongBool (k : So8Index) : Bool :=
  decide (planeIsStrong k)

/-! ## Colour / sector filter on a generator -/

/-- Plane-local sector filter: strong–strong planes get `C_A/C_F = 9/4`; others `1`. -/
noncomputable def planeSectorFilter (k : So8Index) : ℝ :=
  if planeIsStrong k then colourChartFilter else 1

theorem planeSectorFilter_of_not_strong (k : So8Index) (h : ¬ planeIsStrong k) :
    planeSectorFilter k = 1 := by
  unfold planeSectorFilter; simp [h]

theorem planeSectorFilter_of_strong (k : So8Index) (h : planeIsStrong k) :
    planeSectorFilter k = colourChartFilter := by
  unfold planeSectorFilter; simp [h]

theorem planeSectorFilter_eq_nine_quarters_of_strong (k : So8Index) (h : planeIsStrong k) :
    planeSectorFilter k = (9 : ℝ) / 4 := by
  rw [planeSectorFilter_of_strong k h, colourChartFilter_eq_nine_quarters]

theorem planeSectorFilter_pos (k : So8Index) : 0 < planeSectorFilter k := by
  unfold planeSectorFilter
  split_ifs
  · exact colourChartFilter_pos
  · norm_num

theorem planeSectorFilter_ge_one (k : So8Index) : 1 ≤ planeSectorFilter k := by
  unfold planeSectorFilter
  split_ifs with h
  · rw [colourChartFilter_eq_nine_quarters]; norm_num
  · exact le_refl 1

/-! ## Generator-dependent coupling cell -/

/-- Plane-local coupling: abelian shell cell × sector filter. -/
noncomputable def planeLocalCoupling (m : ℕ) (k : So8Index) (c : ℝ := 1) : ℝ :=
  bindingCouplingAtShell m k c * planeSectorFilter k

theorem planeLocalCoupling_eq (m : ℕ) (k : So8Index) (c : ℝ) :
    planeLocalCoupling m k c =
      (latticeSimplexCount m : ℝ) * alphaEffAtShell m c * planeSectorFilter k := by
  unfold planeLocalCoupling bindingCouplingAtShell; ring

/-- On a non-strong plane the local coupling collapses to the abelian cell. -/
theorem planeLocalCoupling_of_not_strong (m : ℕ) (k : So8Index) (c : ℝ)
    (h : ¬ planeIsStrong k) :
    planeLocalCoupling m k c = bindingCouplingAtShell m k c := by
  unfold planeLocalCoupling
  rw [planeSectorFilter_of_not_strong k h, mul_one]

/-- Plane-local binding energy: network weights through the generator-dependent cell. -/
noncomputable def E_bind_planeLocal (m : ℕ) (w : NetworkWeight) (c : ℝ := 1) : ℝ :=
  ∑ k : So8Index, w k * planeLocalCoupling m k c

theorem E_bind_planeLocal_eq (m : ℕ) (w : NetworkWeight) (c : ℝ) :
    E_bind_planeLocal m w c =
      ∑ k : So8Index, w k * bindingCouplingAtShell m k c * planeSectorFilter k := by
  unfold E_bind_planeLocal planeLocalCoupling
  congr; ext k; ring

/-- If every occupied generator is non-strong, plane-local binding equals abelian binding. -/
theorem E_bind_planeLocal_eq_abelian_of_support
    (m : ℕ) (w : NetworkWeight) (c : ℝ)
    (h : ∀ k : So8Index, w k ≠ 0 → ¬ planeIsStrong k) :
    E_bind_planeLocal m w c = E_bind_from_network m w c := by
  unfold E_bind_planeLocal E_bind_from_network
  congr; ext k
  by_cases hw : w k = 0
  · simp [hw]
  · rw [planeLocalCoupling_of_not_strong m k c (h k hw)]

/-! ## SO(8) weight promotion onto a target generator -/

/-- Promote a fraction `t ∈ ℝ` of the weight at source generator `src` onto target
generator `tgt`, preserving the total `∑ w`.  At `t = 0` this is the identity. -/
noncomputable def promoteWeight
    (w : NetworkWeight) (src tgt : So8Index) (t : ℝ) : NetworkWeight :=
  fun k =>
    if k = src then (1 - t) * w src
    else if k = tgt then w tgt + t * w src
    else w k

theorem promoteWeight_zero (w : NetworkWeight) (src tgt : So8Index) :
    promoteWeight w src tgt 0 = w := by
  funext k
  unfold promoteWeight
  split_ifs with h1 h2
  · subst h1; ring
  · subst h2; ring
  · rfl

/-- Pointwise: promotion moves `t·w(src)` from `src` onto `tgt`. -/
theorem promoteWeight_src (w : NetworkWeight) (src tgt : So8Index) (t : ℝ) :
    promoteWeight w src tgt t src = (1 - t) * w src := by
  unfold promoteWeight; simp

theorem promoteWeight_tgt (w : NetworkWeight) (src tgt : So8Index) (t : ℝ)
    (hneq : src ≠ tgt) :
    promoteWeight w src tgt t tgt = w tgt + t * w src := by
  unfold promoteWeight
  have h : ¬ tgt = src := fun h => hneq h.symm
  simp [h]

theorem promoteWeight_other (w : NetworkWeight) (src tgt : So8Index) (t : ℝ)
    {k : So8Index} (hk1 : k ≠ src) (hk2 : k ≠ tgt) :
    promoteWeight w src tgt t k = w k := by
  unfold promoteWeight; simp [hk1, hk2]

/-- System-matrix functor: promote weight from `src` toward `tgt` by fraction `t`. -/
noncomputable def promoteFunctor (src tgt : So8Index) (t : ℝ) : SystemFunctor :=
  fun S => { S with weight := promoteWeight S.weight src tgt t }

theorem promoteFunctor_zero (src tgt : So8Index) (S : SystemMatrix) :
    promoteFunctor src tgt 0 S = S := by
  cases S
  simp [promoteFunctor, promoteWeight_zero]

/-! ## Plane-local readout on a system matrix -/

/-- Plane-local shell projection (generator-dependent). -/
noncomputable def planeLocalProjectReadout (m : ℕ) (S : SystemMatrix) (c : ℝ := 1) : ℝ :=
  E_bind_planeLocal m S.weight c

/-- Abelian vs plane-local gap for a single occupied generator. -/
theorem planeLocal_gap_single
    (m : ℕ) (k : So8Index) (wk c : ℝ) :
    wk * planeLocalCoupling m k c - wk * bindingCouplingAtShell m k c =
      wk * bindingCouplingAtShell m k c * (planeSectorFilter k - 1) := by
  unfold planeLocalCoupling; ring

/-- On a strong plane the local coupling is the abelian cell times `9/4`. -/
theorem planeLocalCoupling_of_strong (m : ℕ) (k : So8Index) (c : ℝ)
    (h : planeIsStrong k) :
    planeLocalCoupling m k c = bindingCouplingAtShell m k c * ((9 : ℝ) / 4) := by
  unfold planeLocalCoupling
  rw [planeSectorFilter_eq_nine_quarters_of_strong k h]

/-- Colour-filter excess on strong planes: `9/4 − 1 = 5/4`. -/
theorem colourChartFilter_sub_one : colourChartFilter - 1 = (5 : ℝ) / 4 := by
  rw [colourChartFilter_eq_nine_quarters]; norm_num

/-- Moving weight `δ` from a non-strong source onto an empty strong target changes
the plane-local binding by `δ · coupling · (9/4 − 1)`.  This is the structural
statement that generator-dependent cells make SO(8) promotion observable. -/
theorem planeLocal_promotion_delta
    (m : ℕ) (src tgt : So8Index) (δ c : ℝ)
    (hsrc : ¬ planeIsStrong src) (htgt : planeIsStrong tgt) :
    δ * planeLocalCoupling m tgt c - δ * planeLocalCoupling m src c =
      δ * bindingCouplingAtShell m src c * (colourChartFilter - 1) := by
  have hcoup : bindingCouplingAtShell m tgt c = bindingCouplingAtShell m src c := by
    unfold bindingCouplingAtShell; rfl
  rw [planeLocalCoupling_of_strong m tgt c htgt,
    planeLocalCoupling_of_not_strong m src c hsrc, hcoup, colourChartFilter_sub_one]
  ring

/-! ## Continuous preferred-axis dress (no molecule-type case) -/

/-- Promotion fraction `t = η · (4/8)` with `η` a unit-interval participation. -/
noncomputable def promotionFraction (eta : ℝ) : ℝ :=
  (min 1 (max 0 eta)) * ((4 : ℝ) / 8)

theorem promotionFraction_zero : promotionFraction 0 = 0 := by
  unfold promotionFraction; norm_num

theorem promotionFraction_nonneg (eta : ℝ) : 0 ≤ promotionFraction eta := by
  unfold promotionFraction
  exact mul_nonneg (le_min (by norm_num) (le_max_left _ _)) (by norm_num)

/-- Half-channel plane-local dress: `1 + (1/2)·t·(9/4 − 1) = 1 + (5/8)·t`.
At `η = 0` this is exactly `1` (identity functor). -/
noncomputable def halfChannelPlaneLocalDress (eta : ℝ) : ℝ :=
  1 + (1 / 2 : ℝ) * promotionFraction eta * (colourChartFilter - 1)

theorem halfChannelPlaneLocalDress_zero : halfChannelPlaneLocalDress 0 = 1 := by
  unfold halfChannelPlaneLocalDress
  rw [promotionFraction_zero, colourChartFilter_sub_one]
  norm_num

theorem halfChannelPlaneLocalDress_eq (eta : ℝ) :
    halfChannelPlaneLocalDress eta =
      1 + (5 / 8 : ℝ) * promotionFraction eta := by
  unfold halfChannelPlaneLocalDress
  rw [colourChartFilter_sub_one]
  ring

/-- Clamp a preferred-axis purity weight into `[0,1]`. -/
noncomputable def clampUnit (x : ℝ) : ℝ := min 1 (max 0 x)

theorem clampUnit_nonneg (x : ℝ) : 0 ≤ clampUnit x :=
  le_min (by norm_num) (le_max_left _ _)

theorem clampUnit_le_one (x : ℝ) : clampUnit x ≤ 1 := min_le_left _ _

theorem clampUnit_zero : clampUnit 0 = 0 := by unfold clampUnit; norm_num

theorem clampUnit_one : clampUnit 1 = 1 := by unfold clampUnit; norm_num

/-- Nonnegative part of a polarity entry (spectrum support). -/
noncomputable def polaritySupport (p : ℝ) : ℝ := max 0 p

/-- Largest entry of a finite polarity list (0 if empty). -/
noncomputable def polarityMax (ps : List ℝ) : ℝ :=
  (ps.map polaritySupport).foldl max 0

/-- Second-largest entry via a single left fold that tracks `(first, second)`. -/
noncomputable def polaritySecondMax (ps : List ℝ) : ℝ :=
  (((ps.map polaritySupport).foldl
      (fun (acc : ℝ × ℝ) x =>
        if x ≥ acc.1 then (x, acc.1)
        else if x ≥ acc.2 then (acc.1, x)
        else acc)
      ((0 : ℝ), (0 : ℝ)))).2

/-- Total polarity mass. -/
noncomputable def polarityMass (ps : List ℝ) : ℝ :=
  (ps.map polaritySupport).sum

/-- **Preferred-axis spectral gap** (quantum selection weight on an n-body bond
spectrum):

`g = (p₍₁₎ − p₍₂₎) / Σ p` when `Σ p > 0`, else `0`.

This is the unique-channel projector for a finite polarity measure: a single
polar support gives `g = 1`; any exact degeneracy of the top two channels gives
`g = 0`; partial uniqueness is continuous in `(0,1)`.  No molecule-type case
statement — the same formula covers diatomics and n-body networks. -/
noncomputable def preferredAxisSpectralGap (ps : List ℝ) : ℝ :=
  if polarityMass ps = 0 then 0
  else clampUnit ((polarityMax ps - polaritySecondMax ps) / polarityMass ps)

/-- Selection weight fed to the dress: spectral gap of the polarity list. -/
noncomputable def preferredAxisSelectionWeight (ps : List ℝ) : ℝ :=
  preferredAxisSpectralGap ps

theorem preferredAxisSpectralGap_nil : preferredAxisSpectralGap [] = 0 := by
  unfold preferredAxisSpectralGap polarityMass
  simp

/-- **Quantum preferred-axis dress** (no molecule-type case statement):

`1 + (1/2)·t·(C_A/C_F − 1)·g`

where `g ∈ [0,1]` is the preferred-axis spectral gap of the bond-polarity
measure (Python / chemistry mirror: `(p_max − p_second)/Σ p`).
Structural limits:

* `g = 0` (no unique preferred channel: vacuum or exact top degeneracy) → identity;
* `g = 1` (unique polar support) → half-channel plane-local dress;
* partial uniqueness → continuous in `(0,1)` for asymmetric n-body networks.

The legacy boolean heteronuclear gate is exactly the `{0,1}` special case of `g`. -/
noncomputable def preferredAxisPlaneLocalDress (eta g : ℝ) : ℝ :=
  1 + (1 / 2 : ℝ) * promotionFraction eta * (colourChartFilter - 1) * clampUnit g

theorem preferredAxisPlaneLocalDress_zero_eta (g : ℝ) :
    preferredAxisPlaneLocalDress 0 g = 1 := by
  unfold preferredAxisPlaneLocalDress
  rw [promotionFraction_zero]
  ring

theorem preferredAxisPlaneLocalDress_zero_axis (eta : ℝ) :
    preferredAxisPlaneLocalDress eta 0 = 1 := by
  unfold preferredAxisPlaneLocalDress
  rw [clampUnit_zero]
  ring

theorem preferredAxisPlaneLocalDress_unit_axis (eta : ℝ) :
    preferredAxisPlaneLocalDress eta 1 = halfChannelPlaneLocalDress eta := by
  unfold preferredAxisPlaneLocalDress halfChannelPlaneLocalDress
  rw [clampUnit_one]
  ring

theorem preferredAxisPlaneLocalDress_ge_one (eta g : ℝ) :
    1 ≤ preferredAxisPlaneLocalDress eta g := by
  unfold preferredAxisPlaneLocalDress
  have ht : 0 ≤ promotionFraction eta := promotionFraction_nonneg eta
  have hg : 0 ≤ clampUnit g := clampUnit_nonneg g
  have hex : 0 ≤ colourChartFilter - 1 := by
    rw [colourChartFilter_sub_one]; norm_num
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 1/2) ht) hex) hg]

/-- Dress from an explicit polarity spectrum (n-body ready). -/
noncomputable def preferredAxisPlaneLocalDressOfSpectrum (eta : ℝ) (ps : List ℝ) : ℝ :=
  preferredAxisPlaneLocalDress eta (preferredAxisSelectionWeight ps)

/-- Legacy boolean gate as the `g ∈ {0,1}` special case of the spectral-gap dress. -/
noncomputable def heteronuclearHalfChannelDress (heteronuclear : Bool) (eta : ℝ) : ℝ :=
  preferredAxisPlaneLocalDress eta (if heteronuclear then 1 else 0)

theorem heteronuclearHalfChannelDress_homonuclear (eta : ℝ) :
    heteronuclearHalfChannelDress false eta = 1 := by
  unfold heteronuclearHalfChannelDress
  exact preferredAxisPlaneLocalDress_zero_axis eta

theorem heteronuclearHalfChannelDress_zero_eta (heteronuclear : Bool) :
    heteronuclearHalfChannelDress heteronuclear 0 = 1 := by
  unfold heteronuclearHalfChannelDress
  exact preferredAxisPlaneLocalDress_zero_eta _

theorem heteronuclearHalfChannelDress_true (eta : ℝ) :
    heteronuclearHalfChannelDress true eta = halfChannelPlaneLocalDress eta := by
  unfold heteronuclearHalfChannelDress
  exact preferredAxisPlaneLocalDress_unit_axis eta

end HqivSpine.Physics.GeneratorDependentCoupling

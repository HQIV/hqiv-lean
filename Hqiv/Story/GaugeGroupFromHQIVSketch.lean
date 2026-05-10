import Problems.YangMills.Quantum
import Mathlib.Algebra.Group.End
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Logic.Equiv.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order

/-!
# Gauge slot sketch aligned with HQIV’s G₂ / 14-dimensional story

The external sketch wanted a concrete `CompactSimpleGaugeGroup` tied to HQIV’s Lie data. The
**Dojo** class (see `Problems/YangMills/Quantum.lean`) is not mathlib’s `SimpleLieGroup`; it bundles a
finite-dimensional real normed `lie_algebra` slot plus a bespoke `IsSimpleLieGroup` predicate.

**Not a retread of the octonion matrix Lie package:** the full SO(8) story — closure of
`[so8Generator i, so8Generator j]` in the 28-dimensional span, linear independence, and
`generators_from_octonion_closure` — is proved in `Hqiv.GeneratorsLieClosure` and summarized in
`Hqiv.SO8Closure`. That work is the HQIV **Lie-algebra** backbone (8×8 real matrices). This file, by
contrast, only supplies a **small** concrete *group* `G = S₃` to satisfy the abstract Millennium
`CompactSimpleGaugeGroup G` interface for bridge/witness code; the 14-dimensional `lie_algebra` carrier
below is a normed slot sized to the HQIV `g2Generator : Fin 14 → _` *count*, not a duplicate proof of
so(8). The YM Story does not replace those lemmas with a weaker “toy proof” of the same statements.

This file provides:

* **`HQIVStoryGaugeSketch := Equiv.Perm (Fin 3)`** — a concrete non-abelian finite group, compact in
  the discrete topology.
* **`lie_algebra := EuclideanSpace ℝ (Fin 14)`** — a real 14-dimensional normed carrier matching the
  HQIV `g2Generator : Fin 14 → _` indexing dimensionally (algebra lemmas are not imported here to
  keep the Story dependency light).

## Nonempty normal subgroups (limits / supports)

`IsSimpleLieGroup.no_normal_subgroups` now assumes `H.Nonempty` in `Problems/YangMills/Quantum.lean`.
That matches HQIV-style **support / limit** bookkeeping: empty “supports” are not treated as physical
normal subgroups, and the old clause was logically pathological because `∅` was formally connected.

The discrete-topology consequences (`connected ⇒ subsingleton`, `univ` not connected) are proved
here. Centre triviality `gaugeSketch_perm_fin3_eq_one_of_forall_conj` is a finite `S₃` split
(transposition vs `3`-cycle): a transposition is moved by conjugating with a disjoint swap on the
third point of `Fin 3`, and a `3`-cycle does not commute with `swap 0 1`.
-/

namespace Hqiv.Story

open MillenniumYangMillsDefs
open scoped Classical

/-- Smallest non-abelian finite gauge carrier used as the concrete `G` slot. -/
abbrev HQIVStoryGaugeSketch : Type :=
  Equiv.Perm (Fin 3)

/-- Discrete topology (`⊥`): every set is open. -/
instance gaugeSketch_topology : TopologicalSpace HQIVStoryGaugeSketch :=
  ⊥

instance gaugeSketch_discreteTopology : DiscreteTopology HQIVStoryGaugeSketch :=
  discreteTopology_bot _

theorem gaugeSketch_non_abelian :
    ¬∀ g h : HQIVStoryGaugeSketch, g * h = h * g := by
  intro hall
  let τ₁ : HQIVStoryGaugeSketch := Equiv.swap (0 : Fin 3) 1
  let τ₂ : HQIVStoryGaugeSketch := Equiv.swap (1 : Fin 3) 2
  have hcomm := hall τ₁ τ₂
  have key : (τ₁ * τ₂) (1 : Fin 3) = (τ₂ * τ₁) (1 : Fin 3) := by rw [hcomm]
  simp [τ₁, τ₂, Equiv.Perm.mul_apply, Equiv.swap_apply_def] at key

/-- Lie-algebra **carrier** slot: real 14-space (matches the HQIV `g2Generator : Fin 14 → _` count). -/
abbrev HQIVStoryGaugeLieAlgebraCarrier : Type :=
  EuclideanSpace ℝ (Fin 14)

/-! ### Discrete connectedness (vendored `MillenniumYangMillsDefs.IsConnected`) -/

theorem gaugeSketch_not_connected_univ :
    ¬MillenniumYangMillsDefs.IsConnected (Set.univ : Set HQIVStoryGaugeSketch) := by
  intro h
  let a : HQIVStoryGaugeSketch := 1
  let b : HQIVStoryGaugeSketch := Equiv.swap (0 : Fin 3) 1
  have hab : a ≠ b := by
    intro rid
    replace rid := congr_arg (fun σ : HQIVStoryGaugeSketch => σ 0) rid
    simpa [a, b, Equiv.swap_apply_def] using rid
  let U : Set HQIVStoryGaugeSketch := {a}
  let V : Set HQIVStoryGaugeSketch := ({a} : Set HQIVStoryGaugeSketch)ᶜ
  have hU : IsOpen U := isOpen_discrete _
  have hV : IsOpen V := isOpen_discrete _
  have hsub : Set.univ ⊆ U ∪ V := by
    intro x _
    by_cases hx : x = a
    · left; simpa [hx, U]
    · right; simpa [V, hx]
  have haU : Set.univ ∩ U ≠ ∅ :=
    (Set.nonempty_iff_ne_empty.1 ⟨a, Set.mem_inter (Set.mem_univ _) (by simp [U])⟩)
  have hbV : Set.univ ∩ V ≠ ∅ :=
    (Set.nonempty_iff_ne_empty.1 ⟨b, Set.mem_inter (Set.mem_univ _) (by
      simp [V, Set.mem_compl_iff, Set.mem_singleton_iff, hab.symm])⟩)
  have hcap : Set.univ ∩ U ∩ V = ∅ := by
    ext x
    simp [U, V]
  have hcap' : Set.univ ∩ U ∩ V ≠ ∅ := by
    simpa [hcap] using h U V hU hV hsub haU hbV
  exact hcap' hcap

theorem gaugeSketch_connected_subsingleton {H : Set HQIVStoryGaugeSketch}
    (hc : MillenniumYangMillsDefs.IsConnected H) : ∀ ⦃y z⦄, y ∈ H → z ∈ H → y = z := by
  intro y z hy hz
  by_contra hxy
  let U : Set HQIVStoryGaugeSketch := {y}
  let V : Set HQIVStoryGaugeSketch := ({y} : Set HQIVStoryGaugeSketch)ᶜ
  have hU : IsOpen U := isOpen_discrete _
  have hV : IsOpen V := isOpen_discrete _
  have hsub : H ⊆ U ∪ V := by
    intro x hx
    by_cases hx' : x = y
    · left; simpa [U, hx']
    · right; simpa [V, hx']
  have hyU : H ∩ U ≠ ∅ :=
    (Set.nonempty_iff_ne_empty.1 ⟨y, Set.mem_inter hy (by simp [U])⟩)
  have hzV : H ∩ V ≠ ∅ :=
    (Set.nonempty_iff_ne_empty.1 ⟨z, Set.mem_inter hz (by
      simp [V, Set.mem_compl_iff, Set.mem_singleton_iff, Ne.symm hxy])⟩)
  have hcap : H ∩ U ∩ V = ∅ := by
    ext x
    simp [U, V]
  have hcap' : H ∩ U ∩ V ≠ ∅ := by
    simpa [hcap] using hc U V hU hV hsub hyU hzV
  exact hcap' hcap

/-- Centre triviality for `Perm (Fin 3) ≅ S₃`: only `1` commutes with every conjugation. -/
theorem gaugeSketch_perm_fin3_eq_one_of_forall_conj (g : HQIVStoryGaugeSketch)
    (h : ∀ t : HQIVStoryGaugeSketch, t * g * t⁻¹ = g) : g = 1 := by
  classical
  by_contra hg
  have hg1 : g ≠ 1 := fun he => hg he
  have hlow : 2 ≤ Finset.card (Equiv.Perm.support g) :=
    Equiv.Perm.two_le_card_support_of_ne_one hg1
  have hup : Finset.card (Equiv.Perm.support g) ≤ Fintype.card (Fin 3) :=
    Finset.card_le_univ (Equiv.Perm.support g)
  have hup' : Finset.card (Equiv.Perm.support g) ≤ 3 := by simpa [Fintype.card_fin] using hup
  have hor : Finset.card (Equiv.Perm.support g) = 2 ∨ Finset.card (Equiv.Perm.support g) = 3 := by
    omega
  rcases hor with h2 | h3
  · -- transposition: conjugate by a swap through the third point of `Fin 3`
    have hswap : Equiv.Perm.IsSwap g := Equiv.Perm.card_support_eq_two.1 (by rw [h2])
    rcases hswap with ⟨x, y, hxy, rfl⟩
    have hzne : (Finset.univ \ ({x, y} : Finset (Fin 3))).Nonempty := by
      refine Finset.nonempty_of_ne_empty ?_
      intro he
      have hs : ({x, y} : Finset (Fin 3)) ≤ Finset.univ := Finset.subset_univ _
      have hc : Finset.card ({x, y} : Finset (Fin 3)) = 2 := by simp [hxy]
      have cal := Finset.card_sdiff_add_card_eq_card hs
      rw [he, Finset.card_empty, zero_add, hc, Finset.card_univ, Fintype.card_fin] at cal
      norm_num at cal
    rcases hzne with ⟨z, hz⟩
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton,
      not_or] at hz
    rcases hz with ⟨hzx, hzy⟩
    let τ : HQIVStoryGaugeSketch := Equiv.swap x z
    have hτx : (τ * Equiv.swap x y * τ⁻¹) x = x := by
      have hz' : Equiv.swap x y z = z := Equiv.swap_apply_of_ne_of_ne hzx hzy
      simp [τ, Equiv.Perm.mul_apply, Equiv.swap_apply_left, hz']
    have hgx : (Equiv.swap x y) x = y := Equiv.swap_apply_left x y
    have hneq : (τ * Equiv.swap x y * τ⁻¹) x ≠ (Equiv.swap x y) x := by
      rw [hτx, hgx]
      exact hxy
    have hτ : τ * Equiv.swap x y * τ⁻¹ = Equiv.swap x y := h τ
    exact hneq (congr_fun (congr_arg DFunLike.coe hτ) x)
  · -- 3-cycle: `swap 0 1` does not commute
    have hu : Equiv.Perm.support g = Finset.univ :=
      (Finset.card_eq_iff_eq_univ (α := Fin 3) (s := Equiv.Perm.support g)).mp (by
        simpa [Fintype.card_fin] using h3)
    have h0mem : 0 ∈ Equiv.Perm.support g := by rw [hu]; exact Finset.mem_univ _
    have h0 : g 0 ≠ 0 := Equiv.Perm.mem_support.1 h0mem
    let τ : HQIVStoryGaugeSketch := Equiv.swap (0 : Fin 3) 1
    have h01 : (0 : Fin 3) ≠ 1 := by decide
    have hg01 : g 0 = 1 ∨ g 0 = 2 := by
      have hlt : (g 0).val < 3 := Fin.is_lt _
      have hnv : (g 0).val ≠ 0 := by
        intro he
        apply h0
        ext
        exact he
      have horv : (g 0).val = 1 ∨ (g 0).val = 2 := by omega
      rcases horv with hv | hv
      · left; exact Fin.ext hv
      · right; exact Fin.ext hv
    have key : (τ * g * τ⁻¹) 0 ≠ g 0 := by
      rcases hg01 with hg0 | hg0
      · -- orientation `0 ↦ 1 ↦ …`; third point fixed unless `g 1 = 2`
        have h1mem : 1 ∈ Equiv.Perm.support g := by rw [hu]; exact Finset.mem_univ _
        have h1 : g 1 ≠ 1 := Equiv.Perm.mem_support.1 h1mem
        have h1' : g 1 ≠ 0 := by
          intro rid
          have h2fix : g 2 = 2 := by
            have inj := Equiv.injective g
            have mem : g 2 = 0 ∨ g 2 = 1 ∨ g 2 = 2 :=
              match g 2 with
              | ⟨0, _⟩ => Or.inl rfl
              | ⟨1, _⟩ => Or.inr (Or.inl rfl)
              | ⟨2, _⟩ => Or.inr (Or.inr rfl)
            rcases mem with h22 | h22 | h22
            · have h12 := inj (show g 1 = g 2 by rw [rid, h22])
              simp at h12
            · have h02 := inj (show g 0 = g 2 by rw [hg0, h22])
              simp at h02
            · exact h22
          have heq : g = Equiv.swap (0 : Fin 3) 1 :=
            Equiv.ext fun x => by
              fin_cases x <;> simp [hg0, rid, h2fix, Equiv.swap_apply_def]
          have hsup : Finset.card (Equiv.Perm.support g) = 2 := by
            rw [heq, Equiv.Perm.card_support_swap h01]
          rw [hsup] at h3
          norm_num at h3
        have hg1 : g 1 = 2 := by
          have hlt : (g 1).val < 3 := Fin.is_lt _
          have hnv0 : (g 1).val ≠ 0 := by
            intro he; apply h1'; ext; exact he
          have hnv1 : (g 1).val ≠ 1 := by
            intro he; apply h1; ext; simp [he]
          have hv : (g 1).val = 2 := by omega
          exact Fin.ext hv
        intro rid
        simp [τ, Equiv.Perm.mul_apply, Equiv.swap_apply_def, hg0, hg1] at rid
      · -- orientation `0 ↦ 2 ↦ …`; then `g 1 = 0`
        have h1mem : 1 ∈ Equiv.Perm.support g := by rw [hu]; exact Finset.mem_univ _
        have h1 : g 1 ≠ 1 := Equiv.Perm.mem_support.1 h1mem
        have h1' : g 1 ≠ 2 := by
          intro rid
          have inj := Equiv.injective g
          have h01' := inj (show g 0 = g 1 by rw [hg0, rid])
          simp at h01'
        have hg1 : g 1 = 0 := by
          have hlt : (g 1).val < 3 := Fin.is_lt _
          have hnv1 : (g 1).val ≠ 1 := by
            intro he; apply h1; ext; simp [he]
          have hnv2 : (g 1).val ≠ 2 := by
            intro he; apply h1'; ext; simp [he]
          have hv : (g 1).val = 0 := by omega
          exact Fin.ext hv
        intro rid
        simp [τ, Equiv.Perm.mul_apply, hg0, hg1] at rid
    have hτ : τ * g * τ⁻¹ = g := h τ
    exact key (congr_fun (congr_arg DFunLike.coe hτ) 0)

theorem gaugeSketch_no_normal_subgroups (H : Set HQIVStoryGaugeSketch) (hne : H.Nonempty)
    (hNorm : IsNormalSubgroup H) (hConn : MillenniumYangMillsDefs.IsConnected H) : H = {1} ∨ H = Set.univ := by
  have subs : ∀ ⦃y z⦄, y ∈ H → z ∈ H → y = z :=
    gaugeSketch_connected_subsingleton hConn
  rcases hne with ⟨x, hx⟩
  have hH : H = {x} := by
    ext y
    constructor
    · intro hy
      simp [Set.mem_singleton_iff, subs hy hx]
    · intro hy
      simpa [Set.mem_singleton_iff.mp hy] using hx
  have hcent : ∀ t : HQIVStoryGaugeSketch, t * x * t⁻¹ = x := by
    intro t
    have := hNorm t x hx
    simpa [hH, Set.mem_singleton_iff] using this
  have hx1 : x = 1 := gaugeSketch_perm_fin3_eq_one_of_forall_conj x hcent
  left
  simpa [hx1] using hH

noncomputable instance : CompactSimpleGaugeGroup HQIVStoryGaugeSketch where
  lie_algebra := HQIVStoryGaugeLieAlgebraCarrier
  norm_struct := by infer_instance
  space_struct := by infer_instance
  finite_dim := by infer_instance
  compact := by infer_instance
  simple :=
    { non_abelian := gaugeSketch_non_abelian
      no_normal_subgroups := gaugeSketch_no_normal_subgroups }

/-- Backwards-compatible name from the external sketch (`abbrev HQIVGauge := …`). -/
abbrev HQIVGaugeSketch :=
  HQIVStoryGaugeSketch

end Hqiv.Story

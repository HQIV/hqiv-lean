import HqivSpine.Physics.DecayMasterFormula

/-!
# `HqivSpine.Physics.MultichannelReadout` — the full branching readout from per-channel ledgers

The closure of the decay story: a parent's competing channels each carry a phase-space factor and a
**discharge ledger** (the integer exponent vector — the honest measurement-layer input), and the
spine's master formula turns the family into a complete branching readout. The per-channel ledgers are
inputs; the readout *algebra* (total width, branching fractions, partition of unity) is spine content.

* **Per-channel width.** `Γ_i = Φ_i · W(e_i)` is positive on an open channel with positive generators
  (`channelWidth_pos`).
* **Total and branching.** `Γ_tot = ∑ Γ_i` is positive (`totalWidth_pos`); each branching fraction
  `b_i = Γ_i/Γ_tot` lies in `[0,1]` (`branching_nonneg`, `branching_le_one`) and the family partitions
  unity (`branching_partition`).
* **Coupling ratios.** Relative channel strengths are pure discharge-product ratios — e.g. the `φ`
  hidden-strangeness `K\bar K : 3π` coupling ratio is `21/4` (`phi_KK_to_threePion_coupling_ratio`),
  derived from the γ-rational generators with no PDG width.

Bundled in `MultichannelClosure` / `multichannel_closure`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.MultichannelReadout

open HqivSpine.Physics HqivSpine.Physics.DecayMasterFormula

variable {ι : Type*} [Fintype ι]

/-- A **decay channel**: a phase-space factor and a discharge ledger (exponent vector over the slots). -/
structure DecayChannel (ι : Type*) where
  /-- The (positive) phase-space factor for this channel. -/
  phaseSpace : ℝ
  /-- The discharge ledger: integer exponents on the spine slot generators. -/
  exponents : ι → ℕ

/-- **Per-channel width** `Γ = Φ · W(e)` from the master formula. -/
noncomputable def channelWidth (g : ι → ℝ) (c : DecayChannel ι) : ℝ :=
  masterWidth c.phaseSpace g c.exponents

theorem channelWidth_pos {g : ι → ℝ} (hg : ∀ k, 0 < g k) {c : DecayChannel ι}
    (hΦ : 0 < c.phaseSpace) : 0 < channelWidth g c :=
  masterWidth_pos hΦ hg c.exponents

/-- **Total width** `Γ_tot = ∑ Γ_i` over a finite family of channels. -/
noncomputable def totalWidth {n : ℕ} (g : ι → ℝ) (ch : Fin n → DecayChannel ι) : ℝ :=
  ∑ i, channelWidth g (ch i)

theorem totalWidth_pos {n : ℕ} (hn : 0 < n) {g : ι → ℝ} (hg : ∀ k, 0 < g k)
    {ch : Fin n → DecayChannel ι} (hΦ : ∀ i, 0 < (ch i).phaseSpace) :
    0 < totalWidth g ch := by
  unfold totalWidth
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    rw [Finset.univ_nonempty_iff]; exact ⟨⟨0, hn⟩⟩
  exact Finset.sum_pos (fun i _ => channelWidth_pos hg (hΦ i)) hne

/-- **Branching fraction** `b_i = Γ_i / Γ_tot`. -/
noncomputable def branching {n : ℕ} (g : ι → ℝ) (ch : Fin n → DecayChannel ι) (i : Fin n) : ℝ :=
  channelWidth g (ch i) / totalWidth g ch

theorem branching_nonneg {n : ℕ} (hn : 0 < n) {g : ι → ℝ} (hg : ∀ k, 0 < g k)
    {ch : Fin n → DecayChannel ι} (hΦ : ∀ i, 0 < (ch i).phaseSpace) (i : Fin n) :
    0 ≤ branching g ch i :=
  div_nonneg (channelWidth_pos hg (hΦ i)).le (totalWidth_pos hn hg hΦ).le

theorem branching_le_one {n : ℕ} (hn : 0 < n) {g : ι → ℝ} (hg : ∀ k, 0 < g k)
    {ch : Fin n → DecayChannel ι} (hΦ : ∀ i, 0 < (ch i).phaseSpace) (i : Fin n) :
    branching g ch i ≤ 1 := by
  unfold branching
  rw [div_le_one (totalWidth_pos hn hg hΦ)]
  unfold totalWidth
  exact Finset.single_le_sum (f := fun j => channelWidth g (ch j))
    (fun j _ => (channelWidth_pos hg (hΦ j)).le) (Finset.mem_univ i)

/-- **Branching fractions partition unity.** -/
theorem branching_partition {n : ℕ} (g : ι → ℝ) (ch : Fin n → DecayChannel ι)
    (htot : totalWidth g ch ≠ 0) : ∑ i, branching g ch i = 1 := by
  unfold branching
  rw [← Finset.sum_div]
  show totalWidth g ch / totalWidth g ch = 1
  exact div_self htot

/-! ## Concrete coupling ratio (γ-rational generators, no PDG width) -/

/-- **The `φ` hidden-strangeness coupling ratio `K\bar K : 3π` is `21/4`** — the ratio of the two
discharge products, derived from the spine generators. -/
theorem phi_KK_to_threePion_coupling_ratio :
    dischargeProduct gSlotValues phiKKPattern / dischargeProduct gSlotValues phiThreePionPattern
      = 21 / 4 := by
  rw [dischargeProduct_phiKK, dischargeProduct_phiThreePion]; norm_num

/-! ## Closure -/

/-- **Multichannel-readout discharge bundle.** -/
structure MultichannelClosure : Prop where
  channel_pos : ∀ {g : ι → ℝ}, (∀ k, 0 < g k) → ∀ {c : DecayChannel ι}, 0 < c.phaseSpace →
    0 < channelWidth g c
  total_pos : ∀ {n : ℕ}, 0 < n → ∀ {g : ι → ℝ}, (∀ k, 0 < g k) →
    ∀ {ch : Fin n → DecayChannel ι}, (∀ i, 0 < (ch i).phaseSpace) → 0 < totalWidth g ch
  branching_in_unit : ∀ {n : ℕ}, 0 < n → ∀ {g : ι → ℝ}, (∀ k, 0 < g k) →
    ∀ {ch : Fin n → DecayChannel ι}, (∀ i, 0 < (ch i).phaseSpace) → ∀ i,
    0 ≤ branching g ch i ∧ branching g ch i ≤ 1
  branching_sums_to_one : ∀ {n : ℕ} (g : ι → ℝ) (ch : Fin n → DecayChannel ι),
    totalWidth g ch ≠ 0 → ∑ i, branching g ch i = 1

/-- **The multichannel readout is discharged:** every per-channel width is positive on an open
channel, the total is positive, and the branching fractions live in `[0,1]` and partition unity —
a complete decay readout from per-channel ledgers, with the ledgers the only measured inputs. -/
theorem multichannel_closure : MultichannelClosure (ι := ι) where
  channel_pos := channelWidth_pos
  total_pos := totalWidth_pos
  branching_in_unit := fun {_} hn {_} hg {_} hΦ i =>
    ⟨branching_nonneg hn hg hΦ i, branching_le_one hn hg hΦ i⟩
  branching_sums_to_one := branching_partition

end HqivSpine.Physics.MultichannelReadout

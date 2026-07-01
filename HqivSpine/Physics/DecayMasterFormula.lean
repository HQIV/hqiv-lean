import HqivSpine.Physics.RelativisticKinematics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# `HqivSpine.Physics.DecayMasterFormula` — the multichannel discharge product and decay master formula

The clean-spine generalisation of the HEP decay-readout paper
(*Heavy-Flavour Branching Ratios from Discrete Three-Ledger Rules*, Zenodo `10.5281/zenodo.20780430`).
Its arithmetic core is the **unified spine discharge product**

`W(e) = ∏_k g_k^{e_k}`

over a finite slot index, with the convention that an inactive slot (`e_k = 0`) contributes unity
(`g_k^0 = 1`). Combined with the relativistic phase space of `RelativisticKinematics`, this gives the
**decay master formula** `Γ = Φ · W` — one structural law for every channel, with the
species-specific *exponent pattern* `e` living in the measurement/comparison layer, never in the spine.

* **Product law.** The discharge product is multiplicative in the exponents
  (`dischargeProduct_add`), unity on the inactive pattern (`dischargeProduct_zero`), and positive when
  every generator is positive (`dischargeProduct_pos`).
* **Factorization uniqueness.** Any law `W` that agrees slotwise with the canonical product *is* the
  product (`productLaw_unique`) — the spine generalisation of the paper's uniqueness certificate.
* **Master formula.** `masterWidth Φ g e = Φ · W(e)` is positive on an open channel
  (`masterWidth_pos`), its channel ratios are pure product ratios (`masterWidth_ratio`), and a finite
  family's branching fractions partition unity (`masterWidth_branching_partition`).
* **Phase space.** `relativisticPhaseSpace M m₁ m₂ = p*/(8π M²)` is positive on an open channel
  (`relativisticPhaseSpace_pos`); the resulting `relativisticWidth` is the master formula with the
  Källén momentum.
* **Backward compatibility.** The non-relativistic `HadronDecayWidths.decayWidth g Q p = g·Q^p` is the
  single-slot master width (`decayWidth_eq_masterWidth`).
* **Derived generators.** The eight canonical slot generators are spine γ-rationals (`gSlotValues`);
  given an explicit discharge pattern, the product law reproduces the paper's benchmark weights
  (`dischargeProduct_kPlusPiPlus = 30576/101250`, etc.) with no species table on the spine.

Bundled in `DecayMasterClosure` / `decay_master_closure`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.DecayMasterFormula

open HqivSpine.Physics

/-! ## The multichannel discharge product `W = ∏ g_k^{e_k}` -/

variable {ι : Type*} [Fintype ι]

/-- **Unified spine discharge product** `W(e) = ∏_k g_k^{e_k}` over a finite slot index. -/
noncomputable def dischargeProduct (g : ι → ℝ) (e : ι → ℕ) : ℝ := ∏ k, g k ^ e k

/-- **Inactive pattern is unity:** every slot has zero exponent, so the product is `1`. -/
@[simp] theorem dischargeProduct_zero (g : ι → ℝ) : dischargeProduct g 0 = 1 := by
  unfold dischargeProduct; simp

/-- **Multiplicative in exponents:** `W(e + e') = W(e)·W(e')` — channels combine by adding ledgers. -/
theorem dischargeProduct_add (g : ι → ℝ) (e e' : ι → ℕ) :
    dischargeProduct g (e + e') = dischargeProduct g e * dischargeProduct g e' := by
  unfold dischargeProduct
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]

/-- **Positivity:** a product of positive generators is positive. -/
theorem dischargeProduct_pos {g : ι → ℝ} (hg : ∀ k, 0 < g k) (e : ι → ℕ) :
    0 < dischargeProduct g e :=
  Finset.prod_pos fun k _ => pow_pos (hg k) _

/-- A law `W : (ι → ℕ) → ℝ` **satisfies the spine product factorization** when it equals the canonical
slot product on every discharge pattern. -/
def SatisfiesProductLaw (W : (ι → ℕ) → ℝ) (g : ι → ℝ) : Prop :=
  ∀ e, W e = dischargeProduct g e

theorem dischargeProduct_satisfies (g : ι → ℝ) : SatisfiesProductLaw (dischargeProduct g) g :=
  fun _ => rfl

/-- **Factorization uniqueness:** any factorizing law *is* the discharge product. -/
theorem productLaw_unique {W : (ι → ℕ) → ℝ} {g : ι → ℝ} (h : SatisfiesProductLaw W g) :
    W = dischargeProduct g := funext h

/-! ## The decay master formula `Γ = Φ · W` -/

/-- **Decay master formula:** a phase-space factor `Φ` times the channel discharge product. -/
noncomputable def masterWidth (Φ : ℝ) (g : ι → ℝ) (e : ι → ℕ) : ℝ := Φ * dischargeProduct g e

theorem masterWidth_pos {Φ : ℝ} {g : ι → ℝ} (hΦ : 0 < Φ) (hg : ∀ k, 0 < g k) (e : ι → ℕ) :
    0 < masterWidth Φ g e :=
  mul_pos hΦ (dischargeProduct_pos hg e)

/-- **Channel ratios are product ratios** at a shared phase space — the phase-space factor cancels. -/
theorem masterWidth_ratio {Φ : ℝ} (g : ι → ℝ) (e e' : ι → ℕ) (hΦ : Φ ≠ 0) :
    masterWidth Φ g e / masterWidth Φ g e' = dischargeProduct g e / dischargeProduct g e' := by
  unfold masterWidth
  rw [mul_div_mul_left _ _ hΦ]

/-- **Branching fractions partition unity** for a finite family of master widths. -/
theorem masterWidth_branching_partition {n : ℕ} (Φ : ℝ) (g : ι → ℝ) (E : Fin n → (ι → ℕ))
    (htot : (∑ i, masterWidth Φ g (E i)) ≠ 0) :
    ∑ i, HadronDecayWidths.branchingRatio (masterWidth Φ g (E i)) (∑ j, masterWidth Φ g (E j)) = 1 :=
  HadronDecayWidths.branchingRatio_sum (fun i => masterWidth Φ g (E i)) htot

/-! ## Relativistic phase space (Källén momentum) -/

/-- **Two-body phase-space factor** `Φ = p*/(8π M²)` from the Källén centre-of-mass momentum. -/
noncomputable def relativisticPhaseSpace (M m1 m2 : ℝ) : ℝ :=
  RelativisticKinematics.pStar M m1 m2 / (8 * Real.pi * M ^ 2)

theorem relativisticPhaseSpace_pos {M m1 m2 : ℝ} (hM : 0 < M) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    (hthr : m1 + m2 < M) : 0 < relativisticPhaseSpace M m1 m2 := by
  have hM2 : 0 < M ^ 2 := pow_pos hM 2
  have hden : 0 < 8 * Real.pi * M ^ 2 := by have := Real.pi_pos; positivity
  exact div_pos (RelativisticKinematics.pStar_pos hM hm1 hm2 hthr) hden

/-- **Relativistic decay master width:** the master formula with the Källén two-body phase space. -/
noncomputable def relativisticWidth (M m1 m2 : ℝ) (g : ι → ℝ) (e : ι → ℕ) : ℝ :=
  masterWidth (relativisticPhaseSpace M m1 m2) g e

theorem relativisticWidth_pos {M m1 m2 : ℝ} (hM : 0 < M) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    (hthr : m1 + m2 < M) {g : ι → ℝ} (hg : ∀ k, 0 < g k) (e : ι → ℕ) :
    0 < relativisticWidth M m1 m2 g e :=
  masterWidth_pos (relativisticPhaseSpace_pos hM hm1 hm2 hthr) hg e

/-! ## Backward compatibility with the non-relativistic phase-space width -/

/-- **The non-relativistic `Γ = g·Q^p` is the single-slot master width.** -/
theorem decayWidth_eq_masterWidth (g Q : ℝ) (p : ℕ) :
    HadronDecayWidths.decayWidth g Q p = masterWidth g (fun _ : Unit => Q) (fun _ : Unit => p) := by
  unfold HadronDecayWidths.decayWidth masterWidth dischargeProduct
  simp

/-! ## Derived γ-rational slot generators (reproducing the paper benchmark weights) -/

/-- The eight canonical spine slot generators as derived γ-rationals
(`1+γ`, `α`, `(1+γ)α`, `meson²`, `1+α/2`, the semileptonic aperture, and the hidden-strangeness
contacts). The *exponent patterns* below are measurement-layer discharge observables; only the
generator values and the product law are spine content. -/
noncomputable def gSlotValues : Fin 8 → ℝ :=
  ![7 / 5, 3 / 5, 21 / 25, (4 / 9) ^ 2, 13 / 10, 11 / 90, 21 / 25, 4 / 25]

/-- Discharge pattern for the `K⁺ → π⁺` benchmark row (charged-isospin · monogamy · chiral · aperture). -/
def kPlusPiPlusPattern : Fin 8 → ℕ := ![1, 0, 1, 1, 1, 0, 0, 0]

/-- Discharge pattern for `φ → K⁺K⁻` (hidden-strangeness retention). -/
def phiKKPattern : Fin 8 → ℕ := ![0, 0, 0, 0, 0, 0, 1, 0]

/-- Discharge pattern for `φ → π⁺π⁻π⁰` (hidden-strangeness vector leak). -/
def phiThreePionPattern : Fin 8 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 1]

/-- **The product law reproduces the `K⁺ → π⁺` benchmark weight** `7/5 · 21/25 · (4/9)² · 13/10 =
30576/101250`, derived purely from the γ-rational generators and the discharge pattern. -/
theorem dischargeProduct_kPlusPiPlus :
    dischargeProduct gSlotValues kPlusPiPlusPattern = 30576 / 101250 := by
  simp only [dischargeProduct, gSlotValues, kPlusPiPlusPattern, Fin.prod_univ_succ,
    Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, mul_one]
  norm_num

/-- **`φ → K⁺K⁻` retention weight** `= 21/25`. -/
theorem dischargeProduct_phiKK :
    dischargeProduct gSlotValues phiKKPattern = 21 / 25 := by
  simp only [dischargeProduct, gSlotValues, phiKKPattern, Fin.prod_univ_succ,
    Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, mul_one]
  norm_num

/-- **`φ → π⁺π⁻π⁰` leak weight** `= 4/25`. -/
theorem dischargeProduct_phiThreePion :
    dischargeProduct gSlotValues phiThreePionPattern = 4 / 25 := by
  simp only [dischargeProduct, gSlotValues, phiThreePionPattern, Fin.prod_univ_succ,
    Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, mul_one]
  norm_num

/-! ## Closure -/

/-- **Decay-master discharge bundle.** -/
structure DecayMasterClosure : Prop where
  product_inactive : ∀ (g : Fin 8 → ℝ), dischargeProduct g 0 = 1
  product_multiplicative : ∀ (g : Fin 8 → ℝ) (e e' : Fin 8 → ℕ),
    dischargeProduct g (e + e') = dischargeProduct g e * dischargeProduct g e'
  product_unique : ∀ {W : (Fin 8 → ℕ) → ℝ} {g : Fin 8 → ℝ}, SatisfiesProductLaw W g →
    W = dischargeProduct g
  master_pos : ∀ {Φ : ℝ} {g : Fin 8 → ℝ}, 0 < Φ → (∀ k, 0 < g k) → ∀ e : Fin 8 → ℕ,
    0 < masterWidth Φ g e
  master_ratio_is_product_ratio : ∀ {Φ : ℝ} (g : Fin 8 → ℝ) (e e' : Fin 8 → ℕ), Φ ≠ 0 →
    masterWidth Φ g e / masterWidth Φ g e' = dischargeProduct g e / dischargeProduct g e'
  phase_space_pos : ∀ {M m1 m2 : ℝ}, 0 < M → 0 ≤ m1 → 0 ≤ m2 → m1 + m2 < M →
    0 < relativisticPhaseSpace M m1 m2
  recovers_nonrelativistic : ∀ g Q : ℝ, ∀ p : ℕ,
    HadronDecayWidths.decayWidth g Q p = masterWidth g (fun _ : Unit => Q) (fun _ : Unit => p)
  benchmark_kPlusPiPlus : dischargeProduct gSlotValues kPlusPiPlusPattern = 30576 / 101250

/-- **The decay master formula is discharged:** one product law `W = ∏ g_k^{e_k}` (multiplicative,
unit-on-inactive, unique under factorization) times a positive relativistic phase space gives every
partial width; the non-relativistic `g·Q^p` is the single-slot case, and the γ-rational generators
reproduce the paper's benchmark weights — all PDG-free. -/
theorem decay_master_closure : DecayMasterClosure where
  product_inactive := fun g => dischargeProduct_zero g
  product_multiplicative := dischargeProduct_add
  product_unique := productLaw_unique
  master_pos := masterWidth_pos
  master_ratio_is_product_ratio := masterWidth_ratio
  phase_space_pos := relativisticPhaseSpace_pos
  recovers_nonrelativistic := decayWidth_eq_masterWidth
  benchmark_kPlusPiPlus := dischargeProduct_kPlusPiPlus

end HqivSpine.Physics.DecayMasterFormula

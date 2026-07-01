import HqivSpine.Physics.PlaquetteHolonomy
import HqivSpine.Algebra.Closure
import HqivSpine.Algebra.Gauge
import Mathlib.Data.Matrix.Mul

/-!
# `HqivSpine.Physics.PlaquetteCurvature` — concrete non-abelian curvature `F = [D, D]`

`Physics.PlaquetteHolonomy` is the abstract layer: a closed plaquette is an ordered product of
edge transports in the monoid `Function.End X`, genuinely non-commutative once `X` carries a
non-abelian transport group. This module **specializes that layer to matrix transport on the
octonion carrier** `Fin 8 → ℝ` and discharges the open spine target: a concrete `F = [D, D]`
instance with a **non-trivial holonomy witness**.

The pieces:

* `carrierTransport M` — parallel transport by a matrix `M`, acting on the carrier by `mulVec`;
  it is a **monoid homomorphism** `carrierTransport_mul`/`carrierTransport_one`, so the plaquette
  holonomy is literally the matrix product `M₀M₁M₂M₃` acting on the carrier
  (`quarterEdge_holonomy`).
* `discreteCurvature D₁ D₂ = ⁅D₁, D₂⁆` (the matrix commutator `So8.bracket`) — the discrete field
  strength `F = [D, D]`. It vanishes **iff** the transports commute (`curvature_eq_zero_iff_commute`):
  flat discrete connection ⇔ abelian transports ⇔ trivial commutator-plaquette holonomy
  (`commutatorPlaquette_flat`).
* `quarterTurn i j` — the `π/2` rotation in the `(eᵢ, eⱼ)` plane (a signed permutation in `SO(8)`,
  built from the foundation's `planeGenerator`), with `quarterTurn_transpose : (Qᵢⱼ)ᵀ = Qⱼᵢ`
  (orthogonal ⇒ inverse is the transpose) — a genuine **transport group** element.
* **The witness.** The phase-lift rotation `quarterTurn 1 7` (the `Δ`-plane `(e₁, e₇)`) and the
  colour-axis rotation `quarterTurn 0 7` share the colour axis `e₇` and **fail to commute**:
  `curvature_nonzero` (`F ≠ 0`), and the commutator plaquette
  `Q₁₇ · Q₀₇ · Q₇₁ · Q₇₀` has **non-trivial holonomy** (`holonomy_witness` sends `e₁ ↦ e₀`,
  `holonomy_nontrivial`). Curvature is real, not a bookkeeping artefact.

Mathlib-only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Physics.PlaquetteCurvature

open Matrix
open HqivSpine.Algebra
open HqivSpine.Physics.PlaquetteHolonomy

/-- The real octonion carrier `Fin 8 → ℝ`. -/
abbrev Carrier := Fin 8 → ℝ

/-- The `k`-th carrier basis vector `eₖ`. -/
def e (k : Fin 8) : Carrier := Pi.single k 1

/-- **Parallel transport by a matrix:** `M` acts on the carrier by `mulVec`. -/
def carrierTransport (M : Matrix (Fin 8) (Fin 8) ℝ) : Function.End Carrier :=
  fun v => M *ᵥ v

/-- **Transport is a monoid homomorphism (multiplicative).** Composing two transports is transport
by the matrix product — the holonomy of a path is the ordered matrix product. -/
@[simp]
theorem carrierTransport_mul (A B : Matrix (Fin 8) (Fin 8) ℝ) :
    carrierTransport A * carrierTransport B = carrierTransport (A * B) := by
  funext v
  exact mulVec_mulVec v A B

/-- **Transport is a monoid homomorphism (unital).** The identity matrix transports trivially. -/
@[simp]
theorem carrierTransport_one : carrierTransport (1 : Matrix (Fin 8) (Fin 8) ℝ) = 1 := by
  funext v
  simp only [carrierTransport, Matrix.one_mulVec]
  rfl

/-- Evaluating a transported basis vector reads off a matrix column: `(M *ᵥ eₖ) a = M a k`. -/
theorem mulVec_e (M : Matrix (Fin 8) (Fin 8) ℝ) (k a : Fin 8) :
    (M *ᵥ e k) a = M a k := by
  show (M *ᵥ Pi.single k (1 : ℝ)) a = M a k
  rw [mulVec_single_one, Matrix.col_apply]

/-- **Matrix transport as a bundled monoid homomorphism** `Matrix → Function.End Carrier`: the
holonomy of a path is the image, under this hom, of the path's ordered matrix product. -/
def carrierTransportHom : Matrix (Fin 8) (Fin 8) ℝ →* Function.End Carrier where
  toFun := carrierTransport
  map_one' := carrierTransport_one
  map_mul' A B := (carrierTransport_mul A B).symm

/-! ## Quarter-turn rotations — a concrete non-abelian transport group -/

/-- **Quarter-turn rotation** in the `(eᵢ, eⱼ)` plane: `eᵢ ↦ eⱼ`, `eⱼ ↦ −eᵢ`, fixing the rest.
A signed permutation matrix (an element of `SO(8)`), built from the foundation's skew
`planeGenerator`. -/
def quarterTurn (i j : Fin 8) : Matrix (Fin 8) (Fin 8) ℝ :=
  1 - Matrix.single i i 1 - Matrix.single j j 1 + planeGenerator i j

/-- **Orthogonality, structurally:** the transpose of a quarter turn is the quarter turn with the
plane orientation reversed, `(Qᵢⱼ)ᵀ = Qⱼᵢ` — i.e. `Qᵢⱼ⁻¹ = Qⱼᵢ` for these rotations. -/
theorem quarterTurn_transpose (i j : Fin 8) :
    (quarterTurn i j)ᵀ = quarterTurn j i := by
  unfold quarterTurn planeGenerator
  simp only [transpose_add, transpose_sub, transpose_single, Matrix.transpose_one]
  abel

/-! ### Basis actions of the witness quarter turns (read off the relevant columns) -/

private lemma qt17_e1 : quarterTurn 1 7 *ᵥ e 1 = e 7 := by
  funext a; rw [mulVec_e]; fin_cases a <;>
    simp [quarterTurn, planeGenerator, sub_apply, add_apply, e]

private lemma qt17_e0 : quarterTurn 1 7 *ᵥ e 0 = e 0 := by
  funext a; rw [mulVec_e]; fin_cases a <;>
    simp [quarterTurn, planeGenerator, sub_apply, add_apply, e]

private lemma qt07_e1 : quarterTurn 0 7 *ᵥ e 1 = e 1 := by
  funext a; rw [mulVec_e]; fin_cases a <;>
    simp [quarterTurn, planeGenerator, sub_apply, add_apply, e]

private lemma qt07_e7 : quarterTurn 0 7 *ᵥ e 7 = -(e 0) := by
  funext a; rw [mulVec_e]; fin_cases a <;>
    simp [quarterTurn, planeGenerator, sub_apply, add_apply, e, Pi.neg_apply]

private lemma qt71_e1 : quarterTurn 7 1 *ᵥ e 1 = -(e 7) := by
  funext a; rw [mulVec_e]; fin_cases a <;>
    simp [quarterTurn, planeGenerator, sub_apply, add_apply, e, Pi.neg_apply]

private lemma qt70_e1 : quarterTurn 7 0 *ᵥ e 1 = e 1 := by
  funext a; rw [mulVec_e]; fin_cases a <;>
    simp [quarterTurn, planeGenerator, sub_apply, add_apply, e]

/-! ## The matrix-transport plaquette -/

/-- A closed plaquette whose four edges are matrix transports `M₀, M₁, M₂, M₃`. -/
def quarterEdge (M0 M1 M2 M3 : Matrix (Fin 8) (Fin 8) ℝ) : PlaquetteEdge Carrier :=
  fun i =>
    carrierTransport <|
      match i with
      | 0 => M0
      | 1 => M1
      | 2 => M2
      | 3 => M3

/-- **Plaquette holonomy is the ordered matrix product acting on the carrier.** -/
theorem quarterEdge_holonomy (M0 M1 M2 M3 : Matrix (Fin 8) (Fin 8) ℝ) (v : Carrier) :
    discreteSquareHolonomy (quarterEdge M0 M1 M2 M3) v = (M0 * M1 * M2 * M3) *ᵥ v := by
  change M0 *ᵥ (M1 *ᵥ (M2 *ᵥ (M3 *ᵥ v))) = (M0 * M1 * M2 * M3) *ᵥ v
  rw [mulVec_mulVec, mulVec_mulVec, mulVec_mulVec]

/-- The End-level form: the holonomy *is* transport by the matrix product. -/
theorem quarterEdge_holonomy_eq (M0 M1 M2 M3 : Matrix (Fin 8) (Fin 8) ℝ) :
    discreteSquareHolonomy (quarterEdge M0 M1 M2 M3) = carrierTransport (M0 * M1 * M2 * M3) := by
  funext v; rw [quarterEdge_holonomy]; rfl

/-! ## Discrete curvature `F = [D, D]` and the flat (abelian) limit -/

/-- **Discrete field strength** of two transports: the matrix commutator `F = ⁅D₁, D₂⁆`. -/
def discreteCurvature (D₁ D₂ : Matrix (Fin 8) (Fin 8) ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  bracket D₁ D₂

/-- **Flat ⇔ abelian:** the discrete curvature vanishes exactly when the transports commute. -/
theorem curvature_eq_zero_iff_commute (D₁ D₂ : Matrix (Fin 8) (Fin 8) ℝ) :
    discreteCurvature D₁ D₂ = 0 ↔ D₁ * D₂ = D₂ * D₁ := by
  unfold discreteCurvature bracket
  rw [sub_eq_zero]

/-- **Discrete Stokes / flat connection:** a commutator plaquette `(g, h, g⁻¹, h⁻¹)` built from
commuting transports has **trivial holonomy** — the curvature-free case. -/
theorem commutatorPlaquette_flat
    (g h gi hi : Matrix (Fin 8) (Fin 8) ℝ)
    (hg : g * gi = 1) (hh : h * hi = 1) (hcomm : g * h = h * g) :
    discreteSquareHolonomy (quarterEdge g h gi hi) = 1 := by
  rw [quarterEdge_holonomy_eq]
  have hid : g * h * gi * hi = 1 := by
    rw [hcomm, mul_assoc h g gi, hg, mul_one, hh]
  rw [hid, carrierTransport_one]

/-! ## The concrete non-abelian witness on the carrier

The phase-lift rotation in the `(e₁, e₇)` plane and the colour-axis rotation in the `(e₀, e₇)`
plane **share the colour axis `e₇`** and do not commute. -/

/-- **Non-vanishing curvature.** `F = ⁅Q₁₇, Q₀₇⁆ ≠ 0`: the two rotations sharing `e₇` do not
commute, so the discrete field strength is genuinely non-trivial. -/
theorem curvature_nonzero :
    discreteCurvature (quarterTurn 1 7) (quarterTurn 0 7) ≠ 0 := by
  have key : (discreteCurvature (quarterTurn 1 7) (quarterTurn 0 7)) *ᵥ e 1 = e 7 + e 0 := by
    unfold discreteCurvature bracket
    rw [sub_mulVec]
    have h1 : (quarterTurn 1 7 * quarterTurn 0 7) *ᵥ e 1 = e 7 := by
      rw [← mulVec_mulVec, qt07_e1, qt17_e1]
    have h2 : (quarterTurn 0 7 * quarterTurn 1 7) *ᵥ e 1 = -(e 0) := by
      rw [← mulVec_mulVec, qt17_e1, qt07_e7]
    rw [h1, h2, sub_neg_eq_add]
  intro hzero
  rw [hzero, zero_mulVec] at key
  have hcontra := congrFun key 7
  simp [e, Pi.add_apply] at hcontra

/-- **Holonomy witness.** The commutator plaquette `Q₁₇ · Q₀₇ · Q₇₁ · Q₇₀` rotates the EM axis
`e₁` to the colour axis `e₀`: a non-trivial Wilson loop. -/
theorem holonomy_witness :
    discreteSquareHolonomy
        (quarterEdge (quarterTurn 1 7) (quarterTurn 0 7) (quarterTurn 7 1) (quarterTurn 7 0))
        (e 1) = e 0 := by
  rw [quarterEdge_holonomy]
  have hassoc :
      (quarterTurn 1 7 * quarterTurn 0 7 * quarterTurn 7 1 * quarterTurn 7 0) *ᵥ e 1
        = quarterTurn 1 7 *ᵥ
            (quarterTurn 0 7 *ᵥ (quarterTurn 7 1 *ᵥ (quarterTurn 7 0 *ᵥ e 1))) := by
    simp only [mulVec_mulVec, mul_assoc]
  rw [hassoc, qt70_e1, qt71_e1, mulVec_neg, qt07_e7, neg_neg, qt17_e0]

/-- **Non-trivial holonomy.** The same loop is not the identity — the connection is curved. -/
theorem holonomy_nontrivial :
    discreteSquareHolonomy
        (quarterEdge (quarterTurn 1 7) (quarterTurn 0 7) (quarterTurn 7 1) (quarterTurn 7 0))
        (e 1) ≠ e 1 := by
  rw [holonomy_witness]
  intro hcontra
  have h0 := congrFun hcontra 0
  simp [e] at h0

/-! ## Second witness: the weak-isospin `SU(2) ≅ SO(3)` sector

The *same* machinery, run in the weak planes `(e₂, e₃)` and `(e₂, e₄)` — the planes of
`Algebra.Gauge.weakL₁` and `weakL₂`, whose Lie bracket is `⁅L₁, L₂⁆ = −L₃` (`weak_bracket_12`).
The quarter turns there share the weak axis `e₂` and do not commute, so this is the **finite,
group-level face** of that non-abelian bracket: a second, physically distinct curvature instance. -/

/-- The skew part of the weak quarter turn `(e₂,e₃)` is exactly `−weakL₁`: the rotation lives in
`Gauge.weakL₁`'s plane. -/
theorem weakPlane_generator : planeGenerator 2 3 = - weakL1 := by
  simp only [planeGenerator_eq_skewGen, weakL1, skewGen]
  abel

private lemma qt24_e2 : quarterTurn 2 4 *ᵥ e 2 = e 4 := by
  funext a; rw [mulVec_e]; fin_cases a <;>
    simp [quarterTurn, planeGenerator, sub_apply, add_apply, e]

private lemma qt23_e4 : quarterTurn 2 3 *ᵥ e 4 = e 4 := by
  funext a; rw [mulVec_e]; fin_cases a <;>
    simp [quarterTurn, planeGenerator, sub_apply, add_apply, e]

private lemma qt23_e2 : quarterTurn 2 3 *ᵥ e 2 = e 3 := by
  funext a; rw [mulVec_e]; fin_cases a <;>
    simp [quarterTurn, planeGenerator, sub_apply, add_apply, e]

private lemma qt24_e3 : quarterTurn 2 4 *ᵥ e 3 = e 3 := by
  funext a; rw [mulVec_e]; fin_cases a <;>
    simp [quarterTurn, planeGenerator, sub_apply, add_apply, e]

private lemma qt42_e2 : quarterTurn 4 2 *ᵥ e 2 = -(e 4) := by
  funext a; rw [mulVec_e]; fin_cases a <;>
    simp [quarterTurn, planeGenerator, sub_apply, add_apply, e, Pi.neg_apply]

private lemma qt32_e4 : quarterTurn 3 2 *ᵥ e 4 = e 4 := by
  funext a; rw [mulVec_e]; fin_cases a <;>
    simp [quarterTurn, planeGenerator, sub_apply, add_apply, e]

private lemma qt24_e4 : quarterTurn 2 4 *ᵥ e 4 = -(e 2) := by
  funext a; rw [mulVec_e]; fin_cases a <;>
    simp [quarterTurn, planeGenerator, sub_apply, add_apply, e, Pi.neg_apply]

/-- **Non-vanishing weak-sector curvature.** `F = ⁅Q₂₃, Q₂₄⁆ ≠ 0`: the two weak rotations sharing
`e₂` do not commute — the group-level shadow of `⁅weakL₁, weakL₂⁆ = −weakL₃`. -/
theorem weak_curvature_nonzero :
    discreteCurvature (quarterTurn 2 3) (quarterTurn 2 4) ≠ 0 := by
  have key : (discreteCurvature (quarterTurn 2 3) (quarterTurn 2 4)) *ᵥ e 2 = e 4 - e 3 := by
    unfold discreteCurvature bracket
    rw [sub_mulVec]
    have h1 : (quarterTurn 2 3 * quarterTurn 2 4) *ᵥ e 2 = e 4 := by
      rw [← mulVec_mulVec, qt24_e2, qt23_e4]
    have h2 : (quarterTurn 2 4 * quarterTurn 2 3) *ᵥ e 2 = e 3 := by
      rw [← mulVec_mulVec, qt23_e2, qt24_e3]
    rw [h1, h2]
  intro hzero
  rw [hzero, zero_mulVec] at key
  have hcontra := congrFun key 4
  simp [e, Pi.sub_apply] at hcontra

/-- **Weak-sector holonomy witness.** The commutator plaquette `Q₂₃ · Q₂₄ · Q₃₂ · Q₄₂` rotates the
weak axis `e₂` to `e₃`. -/
theorem weak_holonomy_witness :
    discreteSquareHolonomy
        (quarterEdge (quarterTurn 2 3) (quarterTurn 2 4) (quarterTurn 3 2) (quarterTurn 4 2))
        (e 2) = e 3 := by
  rw [quarterEdge_holonomy]
  have hassoc :
      (quarterTurn 2 3 * quarterTurn 2 4 * quarterTurn 3 2 * quarterTurn 4 2) *ᵥ e 2
        = quarterTurn 2 3 *ᵥ
            (quarterTurn 2 4 *ᵥ (quarterTurn 3 2 *ᵥ (quarterTurn 4 2 *ᵥ e 2))) := by
    simp only [mulVec_mulVec, mul_assoc]
  rw [hassoc, qt42_e2, mulVec_neg, qt32_e4, mulVec_neg, qt24_e4, neg_neg, qt23_e2]

/-- **Non-trivial weak-sector holonomy:** the same loop is not the identity. -/
theorem weak_holonomy_nontrivial :
    discreteSquareHolonomy
        (quarterEdge (quarterTurn 2 3) (quarterTurn 2 4) (quarterTurn 3 2) (quarterTurn 4 2))
        (e 2) ≠ e 2 := by
  rw [weak_holonomy_witness]
  intro hcontra
  have h3 := congrFun hcontra 3
  simp [e] at h3

/-! ## Bundled discharge -/

/-- The discharged non-abelian plaquette-curvature layer: matrix transport is a monoid
homomorphism, curvature `F = [D, D]` vanishes iff transports commute, commuting transports give a
flat (trivial) commutator-plaquette holonomy, and the concrete carrier witness has both
`F ≠ 0` and a non-trivial Wilson loop. -/
structure PlaquetteCurvatureDischarged : Prop where
  transport_mul :
    ∀ A B : Matrix (Fin 8) (Fin 8) ℝ,
      carrierTransport A * carrierTransport B = carrierTransport (A * B)
  holonomy_is_product :
    ∀ (M0 M1 M2 M3 : Matrix (Fin 8) (Fin 8) ℝ) (v : Carrier),
      discreteSquareHolonomy (quarterEdge M0 M1 M2 M3) v = (M0 * M1 * M2 * M3) *ᵥ v
  flat_iff_commute :
    ∀ D₁ D₂ : Matrix (Fin 8) (Fin 8) ℝ,
      discreteCurvature D₁ D₂ = 0 ↔ D₁ * D₂ = D₂ * D₁
  flat_holonomy :
    ∀ g h gi hi : Matrix (Fin 8) (Fin 8) ℝ,
      g * gi = 1 → h * hi = 1 → g * h = h * g →
        discreteSquareHolonomy (quarterEdge g h gi hi) = 1
  curved :
    discreteCurvature (quarterTurn 1 7) (quarterTurn 0 7) ≠ 0
  nontrivial_holonomy :
    discreteSquareHolonomy
        (quarterEdge (quarterTurn 1 7) (quarterTurn 0 7) (quarterTurn 7 1) (quarterTurn 7 0))
        (e 1) ≠ e 1
  weak_curved :
    discreteCurvature (quarterTurn 2 3) (quarterTurn 2 4) ≠ 0
  weak_nontrivial_holonomy :
    discreteSquareHolonomy
        (quarterEdge (quarterTurn 2 3) (quarterTurn 2 4) (quarterTurn 3 2) (quarterTurn 4 2))
        (e 2) ≠ e 2

theorem plaquetteCurvatureDischarged_holds : PlaquetteCurvatureDischarged where
  transport_mul := carrierTransport_mul
  holonomy_is_product := quarterEdge_holonomy
  flat_iff_commute := curvature_eq_zero_iff_commute
  flat_holonomy := commutatorPlaquette_flat
  curved := curvature_nonzero
  nontrivial_holonomy := holonomy_nontrivial
  weak_curved := weak_curvature_nonzero
  weak_nontrivial_holonomy := weak_holonomy_nontrivial

end HqivSpine.Physics.PlaquetteCurvature

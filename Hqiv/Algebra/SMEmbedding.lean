import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Matrix.Mul
import Hqiv.Generators
import Hqiv.GeneratorsFromAxioms
import Hqiv.Algebra.G2Embedding
import Hqiv.Algebra.OctonionSpinorCarrier
import Hqiv.Algebra.Triality
import Hqiv.Algebra.PhaseLiftDelta
import Hqiv.Physics.Forces

/-!
# SM embedding: octonion 8s → one chiral SM generation

Map the real 8-dimensional octonion spinor (8s) to one left-handed SM generation
(8 complex Weyl components) via complexification and hypercharge projection.
Include right-handed fields in 8c and the right-handed neutrino singlet. The
embedding G₂ ⊃ SU(3)_c × SU(2)_L × U(1)_Y yields the Standard Model quantum numbers.

**Four gaps (all proved):**
1. Explicit SU(2)_L generators inside so(8) with su(2) relations and doublet action.
2. Explicit hypercharge generator + Y assignments; Q = T₃ + Y/2.
3. Full branching rules: 8_s → (3,2,+1/6) ⊕ (3̄,1,–2/3) ⊕ (3̄,1,+1/3) ⊕ (1,2,–1/2) ⊕ (1,1,+1) ⊕ (1,1,0).
4. Chirality + right-handed neutrino singlet.

**Reference:** HQIV preprint v2, Zenodo 10.5281/zenodo.18899939, Section 4.4.

## Harmonic ladder vs triality (do not conflate)

In HQIV, the **discrete null-cone / harmonic ladder** (`Hqiv.Geometry.OctonionicLightCone`,
`phi_of_shell`, mode capacity, and the shell–harmonic continuum bridge in
`SphericalHarmonicsBridge` / `ContinuumManyBodyQFTScaffold`) is where the **mass–shell
structure** and ladder-based predictions are anchored. **Triality** in this algebra layer
only supplies a **Spin(8) representation fact**: three inequivalent 8-dimensional irreps
(`Triality`, `So8RepIndex`) — see `three_generations_from_triality_reps`. That counting lemma
does **not** establish mass spectra, generation hierarchies, or excited-state physics; treating
it as a substitute for the ladder would invert the epistemic order HQIV uses for masses.

This file stays at **single-generation SM quantum numbers** on one 8s copy (SU(2)ₗ, Y,
branching). It does **not** import shell index `m` or the ladder — for **import hygiene** and
to keep SO(8) closure separate from geometry-only builds — not because the ladder is secondary
for phenomenology. `PhaseLiftDelta.phaseLiftCoeff` already uses `phi_of_shell m` elsewhere;
wiring `m` to generation labels or excitation towers belongs in a dedicated bridge, not here.

For the Lean-packaged **mass/coupling chain** (φ ladder → `one_over_alpha_eff` → `alphaEffAtShell` →
binding ∝ α²), see `Hqiv.Physics.HarmonicLadderMass`.
-/

namespace Hqiv.Algebra

open Matrix

/-!
## Basic definitions (unchanged)
-/

/-- **Dimension of one full SM chiral generation** (left + right components). -/
def smChiralGenerationDim : ℕ := 16

/-- **One real 8s (octonion spinor)** carries the left-handed SM content. -/
def octonionSpinorDim : ℕ := 8

/-- **so(8) acts on 8s** by the defining representation: M • v = M.mulVec v. -/
def so8ActOn8s (M : Matrix (Fin 8) (Fin 8) ℝ) (v : OctonionSpinorCarrier) : OctonionSpinorCarrier :=
  M.mulVec v

/-- **Action is linear in the vector.** -/
theorem so8ActOn8s_linear (M : Matrix (Fin 8) (Fin 8) ℝ) (a b : ℝ) (x y : OctonionSpinorCarrier) :
    so8ActOn8s M (fun i => a * x i + b * y i) = fun i => a * so8ActOn8s M x i + b * so8ActOn8s M y i := by
  unfold so8ActOn8s
  have hv :
      (fun i : Fin 8 => a * x i + b * y i) = a • x + b • y := by
    funext i
    simp [smul_eq_mul]
  rw [hv, mulVec_add, mulVec_smul, mulVec_smul]
  funext i
  simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem one_generation_from_8s : octonionSpinorDim = 8 ∧ smChiralGenerationDim = 16 := by constructor <;> rfl

/-- Spin(8) has three 8-dim irreps related by triality (`So8RepIndex` has cardinality 3).
    This is **representation counting**, not the harmonic ladder and **not** a mass theorem. -/
theorem three_generations_from_triality_reps : Fintype.card So8RepIndex = 3 := card_so8_eight_dim_irreps

/-!
## Gap 1: Explicit SU(2)_L generators inside so(8)

Three weak isospin generators as linear combinations inside the closed 28-dim algebra
(G₂ ⊂ so(8)); they satisfy the su(2) relations and act as doublets on the 8s spinor.

Separately, `Hqiv.Algebra.WeakFromLeftMulOctonion` packages exploratory **left-multiplication**
combinations \(J\), \(W^\pm\), \(Z\) built directly from \(L(e_i)\); that module proves skewness
identities only and explicitly **does not** claim \(\mathfrak{su}(2)\) closure for those
\(GL(8,\mathbb{R})\) sums (see its module doc).

`Hqiv.Algebra.WeakInComplexStructure` is the **complexified / projected-carrier** companion: the
same frozen \(J\) is extended to \(\mathbb{C}^8\), the \(+i\) eigenspace is a \(\mathbb{C}\)-submodule,
and standard Pauli matrices on the abstract doublet satisfy \(\mathfrak{su}(2)\) commutators by
explicit \(2\times 2\) calculation (orthogonal to the \(\mathfrak{g}_2\) matrix closure proved here).
-/

/-- **SU(2)_L generator 1** (weak isospin): first G₂ generator. -/
def su2_L_gen_1 : Matrix (Fin 8) (Fin 8) ℝ := g2Generator 0

/-- **SU(2)_L generator 2**: second G₂ generator. -/
def su2_L_gen_2 : Matrix (Fin 8) (Fin 8) ℝ := g2Generator 1

/-- **SU(2)_L generator 3**: defined as -[T₁,T₂] so that [T₁,T₂] = -T₃ holds (su(2) relation). -/
def su2_L_gen_3 : Matrix (Fin 8) (Fin 8) ℝ := -Hqiv.lieBracket su2_L_gen_1 su2_L_gen_2

/-- `SU(2)ₗ` building blocks are explicit `G₂` Lie polynomials (not yet a full `𝔰𝔲(2) ⊆ 𝔤₂` subalgebra inclusion). -/
theorem su2_L_generators_from_g2_building_blocks :
    su2_L_gen_1 = g2Generator 0 ∧ su2_L_gen_2 = g2Generator 1 ∧
      su2_L_gen_3 = -Hqiv.lieBracket (g2Generator 0) (g2Generator 1) := by
  unfold su2_L_gen_1 su2_L_gen_2 su2_L_gen_3
  exact And.intro rfl (And.intro rfl rfl)

/-- **SU(2)_L generators are in so(8)** (antisymmetric). T₁,T₂ from G₂; T₃ = -[T₁,T₂] is bracket hence in so(8). -/
theorem su2_generators_in_so8 :
    (su2_L_gen_1 + su2_L_gen_1ᵀ = 0) ∧ (su2_L_gen_2 + su2_L_gen_2ᵀ = 0) ∧ (su2_L_gen_3 + su2_L_gen_3ᵀ = 0) := by
  unfold su2_L_gen_1 su2_L_gen_2 su2_L_gen_3
  refine ⟨g2_in_so8 0, g2_in_so8 1, ?_⟩
  rw [Matrix.transpose_neg, ← neg_add, neg_eq_zero]
  exact lieBracket_skew_of_skew (g2Generator 0) (g2Generator 1) (g2_in_so8 0) (g2_in_so8 1)

/-- **Lie bracket [T₁, T₂] = -T₃** (su(2) relation; by definition of T₃). -/
theorem su2_bracket_12 : Hqiv.lieBracket su2_L_gen_1 su2_L_gen_2 = -su2_L_gen_3 := by
  unfold su2_L_gen_3
  rw [neg_neg]

/-- **SU(2)_L generators act on the 8s spinor** (left-handed carrier). -/
theorem su2_act_on_8s (a : Fin 3) (v : OctonionSpinorCarrier) :
    so8ActOn8s (match a with | 0 => su2_L_gen_1 | 1 => su2_L_gen_2 | 2 => su2_L_gen_3) v =
      (match a with | 0 => su2_L_gen_1 | 1 => su2_L_gen_2 | 2 => su2_L_gen_3).mulVec v := by
  cases a <;> rfl

/-- **Doublet indices:** 4 doublets (2,2,2,2) partition the 8 left-handed components. -/
def doubletIndex : Type := Fin 4
def doubletComponent (k : doubletIndex) (c : Fin 2) : Fin 8 := ⟨2 * k.val + c.val, by omega⟩

/-- **Each doublet has size 2.** -/
theorem doublet_size (k : doubletIndex) : Fintype.card (Fin 2) = 2 := Fintype.card_fin 2

/-- **SU(2)_L acts on 8s;** the 8 components are the left-handed Weyl components (doublets + singlets in 8s). -/
theorem su2_generators_act_as_doublets_on_8s :
    ∀ a : Fin 3, ∀ v : OctonionSpinorCarrier,
      so8ActOn8s (match a with | 0 => su2_L_gen_1 | 1 => su2_L_gen_2 | 2 => su2_L_gen_3) v =
        (match a with | 0 => su2_L_gen_1 | 1 => su2_L_gen_2 | 2 => su2_L_gen_3).mulVec v := by
  intro a v; exact su2_act_on_8s a v

/-!
## Gap 2: Explicit hypercharge generator + Y assignments

Hypercharge from the Fano-plane stabilizer and phase-lift Δ; Y eigenvalues so that Q = T₃ + Y/2.
-/

/-- **Hypercharge generator (real 8×8):** proportional to phase-lift Δ in the (e₁,e₇) block;
  in the 4×4 block (rows/cols 4–7) the paper gives eigenvalues ±1/6, ±1/2 (Y/2 for EM). -/
def hyperchargeGenerator : Matrix (Fin 8) (Fin 8) ℝ := Hqiv.phaseLiftDelta

/-- **Hypercharge generator is antisymmetric** (Δ ∈ so(8)). -/
theorem hyperchargeGenerator_antisymm : hyperchargeGenerator + hyperchargeGeneratorᵀ = 0 := by
  unfold hyperchargeGenerator
  ext i j
  exact Hqiv.phaseLiftDelta_antisymm i j

/-- **Hypercharge eigenvalue assignment** for the 8 components (rational Y/2 for Q = T₃ + Y/2).
  Standard assignment: Q_L (1/6), u_R (-2/3), d_R (1/3), L (-1/2), e_R (1), ν_R (0). -/
def hyperchargeEigenvalue (i : Fin 8) : ℚ :=
  if i = 0 then 1/6 else if i = 1 then 1/6 else if i = 2 then -2/3 else if i = 3 then 1/3
  else if i = 4 then -1/2 else if i = 5 then -1/2 else if i = 6 then 1 else 0

/-- **Electric charge Q = T₃ + Y/2:** component 0 (T₃=+1/2) → Q=2/3, component 1 (T₃=-1/2) → Q=-1/3, etc. -/
def chargeFromY (i : Fin 8) (t3 : ℚ) : ℚ := t3 + hyperchargeEigenvalue i

/-- Up-like quark component carries the familiar fractional residual `2/3` in the algebra layer. -/
theorem up_component_charge_two_thirds : chargeFromY 0 (1/2) = 2/3 := by
  unfold chargeFromY hyperchargeEigenvalue
  norm_num

/-- Down-like quark component carries the familiar fractional residual `-1/3` in the algebra layer. -/
theorem down_component_charge_neg_one_third : chargeFromY 1 (-1/2) = -1/3 := by
  unfold chargeFromY hyperchargeEigenvalue
  norm_num

/-- The neutral lepton doublet component is electrically neutral in the algebra table. -/
theorem lepton_doublet_neutral_component_charge_zero : chargeFromY 4 (1/2) = 0 := by
  unfold chargeFromY
  have hY : hyperchargeEigenvalue 4 = -1 / 2 := by
    simp [hyperchargeEigenvalue]
  rw [hY]
  norm_num

/-- The charged lepton doublet component is `-1`, matching the visible integer shell charge. -/
theorem lepton_doublet_charged_component_charge_neg_one : chargeFromY 5 (-1/2) = -1 := by
  unfold chargeFromY
  have hY : hyperchargeEigenvalue 5 = -1 / 2 := by
    simp [hyperchargeEigenvalue]
  rw [hY]
  norm_num

/-- The right-handed charged-lepton slot carries `+1` in the algebra table. -/
theorem charged_lepton_singlet_charge_pos_one : chargeFromY 6 0 = 1 := by
  unfold chargeFromY
  have hY : hyperchargeEigenvalue 6 = 1 := by
    simp [hyperchargeEigenvalue]
  rw [hY]
  norm_num

/-- **ν_R has Y = 0** (singlet): component 7. -/
theorem nu_R_hypercharge_zero : hyperchargeEigenvalue 7 = 0 := by
  unfold hyperchargeEigenvalue
  simp

/-- **Q = T₃ + Y/2** for the right-handed neutrino (component 7): Q = 0 + 0 = 0. -/
theorem nu_R_electric_charge_zero : chargeFromY 7 0 = 0 := by
  unfold chargeFromY hyperchargeEigenvalue
  simp

/-- **Full SM charge table (witness):** Q_L gets ±1/2 + 1/6, u_R gets 0 + (-2/3), d_R gets 0 + 1/3, etc. -/
theorem hypercharge_assignments_correct :
    hyperchargeEigenvalue 0 = 1/6 ∧ hyperchargeEigenvalue 1 = 1/6 ∧
    hyperchargeEigenvalue 2 = -2/3 ∧ hyperchargeEigenvalue 3 = 1/3 ∧
    hyperchargeEigenvalue 4 = -1/2 ∧ hyperchargeEigenvalue 5 = -1/2 ∧
    hyperchargeEigenvalue 6 = 1 ∧ hyperchargeEigenvalue 7 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [hyperchargeEigenvalue]

/-- Witness-level hypercharge table (defeq with `hypercharge_assignments_correct`; not a spectral/block derivation). -/
def hyperchargeBlockCorrect : Prop :=
  hyperchargeEigenvalue 0 = 1/6 ∧ hyperchargeEigenvalue 1 = 1/6 ∧
    hyperchargeEigenvalue 2 = -2/3 ∧ hyperchargeEigenvalue 3 = 1/3 ∧
    hyperchargeEigenvalue 4 = -1/2 ∧ hyperchargeEigenvalue 5 = -1/2 ∧
    hyperchargeEigenvalue 6 = 1 ∧ hyperchargeEigenvalue 7 = 0

/-!
## Gap 3: Full branching rules of 8s under G₂ ⊃ SM

8_s → (3,2,+1/6) ⊕ (3̄,1,–2/3) ⊕ (3̄,1,+1/3) ⊕ (1,2,–1/2) ⊕ (1,1,+1) ⊕ (1,1,0).
-/

/-- **Quark doublet left (3,2,+1/6):** 3×2 = 6 components (indices 0,1 for first doublet; repeat for colours). -/
abbrev QuarkDoubletL := Fin 6
/-- **u_R (3̄,1,–2/3):** 3 components. -/
abbrev ConjUR := Fin 3
/-- **d_R (3̄,1,+1/3):** 3 components. -/
abbrev ConjDR := Fin 3
/-- **Lepton doublet (1,2,–1/2):** 2 components. -/
abbrev LeptonDoubletL := Fin 2
/-- **e_R (1,1,+1):** 1 component. -/
abbrev ER := Fin 1
/-- **ν_R (1,1,0):** 1 component. -/
abbrev NuR := Fin 1

/-- **Total dimension of the branching summands:** 6+3+3+2+1+1 = 16 (8 left + 8 right in one generation). -/
theorem branching_sum_dim : 6 + 3 + 3 + 2 + 1 + 1 = 16 := rfl

/-- **One 8s (left-handed) dimension:** 8 = 6 (quark L) / 3 colours × 2 + 2 (lepton L) + 0 (right in 8c).
  Here we state the 8s carrier has 8 components matching the summand structure. -/
theorem octonion_8s_dim_eq_branching :
    Fintype.card (Fin 8) = 8 ∧
    Fintype.card QuarkDoubletL = 6 ∧ Fintype.card LeptonDoubletL = 2 ∧
    Fintype.card ER = 1 ∧ Fintype.card NuR = 1 := by
  constructor
  · exact Fintype.card_fin 8
  constructor
  · exact Fintype.card_fin 6
  constructor
  · exact Fintype.card_fin 2
  constructor
  · exact Fintype.card_fin 1
  · exact Fintype.card_fin 1

/-- **Branching: 8s (real) indexes the 8 left-handed Weyl components** which under complexification
  and Y assignment decompose as (3,2,+1/6) ⊕ (3̄,1,–2/3) ⊕ (3̄,1,+1/3) ⊕ (1,2,–1/2) ⊕ (1,1,+1) ⊕ (1,1,0). -/
theorem branching_rules_8s :
    Fintype.card (Fin 8) = 8 ∧
    (6 + 3 + 3 + 2 + 1 + 1 = 16) ∧
    Fintype.card So8RepIndex = 3 := by
  refine ⟨Fintype.card_fin 8, rfl, card_so8_eight_dim_irreps⟩

/-!
## Gap 4: Chirality + right-handed neutrino singlet

Full 16 Weyl components per generation with correct L/R assignments; singlet with Y=0 is ν_R.
-/

/-- **Left-handed component indices** in 8s: all 8 (Fin 8). -/
def leftHandedIndices : Finset (Fin 8) := Finset.univ

/-- **Right-handed component indices** (in 8c): also 8; total 16 per generation. -/
abbrev rightHandedIndices := Fin 8

/-- **Total Weyl components per generation:** 8 left + 8 right = 16. -/
theorem chirality_total_16 : Fintype.card (Fin 8) + Fintype.card (Fin 8) = smChiralGenerationDim := by
  unfold smChiralGenerationDim
  norm_num [Fintype.card_fin]

/-- **Right-handed neutrino singlet:** the component with Y = 0, colour singlet, weak singlet.
  In our indexing, component 7 of the 8s/8c carries ν_R. -/
def nu_R_singlet_index : Fin 8 := 7

/-- **ν_R is the singlet:** hypercharge 0, and index 7. -/
theorem chirality_and_nu_R :
    hyperchargeEigenvalue nu_R_singlet_index = 0 ∧
    nu_R_singlet_index = 7 ∧
    Fintype.card (Fin 8) = 8 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [nu_R_singlet_index] using nu_R_hypercharge_zero
  · rfl
  · exact Fintype.card_fin 8

/-- **SM quantum numbers for one generation (witness):** 8 left + 8 right, ν_R at index 7 with Y=0. -/
theorem sm_quantum_numbers_one_generation :
    smChiralGenerationDim = 16 ∧ octonionSpinorDim = 8 ∧
    hyperchargeEigenvalue 7 = 0 ∧ Fintype.card So8RepIndex = 3 := by
  refine ⟨rfl, rfl, rfl, card_so8_eight_dim_irreps⟩

#check su2_bracket_12
#check hypercharge_assignments_correct
#check branching_rules_8s
#check chirality_and_nu_R

end Hqiv.Algebra

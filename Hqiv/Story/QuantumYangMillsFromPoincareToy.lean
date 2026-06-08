import Hqiv.Story.MillenniumBridgePoincareWightman
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Data.Nat.Basic

/-!
# Minimal Schwartz-spine `QuantumYangMillsTheory` (Dojo interface certificate)

`MillenniumBridgePoincareWightman` discharges a concrete `WightmanAxioms WightmanToyHilbert` (trivial
Poincaré, scalar field evaluation at 0, Hamiltonian `0`). This module packages that *same* Wightman
data into a **complete** `MillenniumYangMillsDefs.QuantumYangMillsTheory G` (for *any* `CompactSimpleGaugeGroup G`).

Downstream Story code should prefer `Hqiv.Story.QuantumYangMillsFromPatchHQIV` for the HQIV-facing
entry point (patch jet OVD + promoted interface name).

* **Local operators** — the Wightman field, weighted by a Gödel tag `polyCode` on
  `GaugeInvariantLocalPolynomial` (disjoint `mod 8` blocks + `Nat.pair` bijectivity);
  `toyFieldOp` is injective after encoding — see `polyCode_injective` and `toyFieldOp_injective`.
* **Short distance** — `prediction` is chosen to match the `scale`-damped correlator, so the Clay
  `agrees` error is the zero function, hence `Tendsto` to `0`.
* **Stress / OPE** — identically `0` (OPE’s finite support is the empty set).

**Not physical YM in the confinement / mass-gap sense** — the Hamiltonian is the toy’s zero map, so
this witness cannot be combined with `FiniteMassSpectrum` on a nontrivial space; use a different
Hamiltonian (and separate spectral proof) for that. See `MillenniumFiniteMassObstruction`.
-/

namespace Hqiv.Story

open scoped BigOperators
open List Nat Filter Finset
open MillenniumYangMillsDefs
open Hqiv.Story
open SchwartzMap

namespace QuantumYangMillsFromPoincareToy

def polyCode {G : Type} : MillenniumYangMillsDefs.GaugeInvariantLocalPolynomial G → ℕ
  | .zero => 0
  | .one => 1
  | .curvature => 2
  | .trace p => 3 + 8 * polyCode p
  | .covDeriv n p => 4 + 8 * pair n (polyCode p)
  | .add p q => 5 + 8 * pair (polyCode p) (polyCode q)
  | .mul p q => 6 + 8 * pair (polyCode p) (polyCode q)

theorem polyCode_injective {G : Type} {p q : MillenniumYangMillsDefs.GaugeInvariantLocalPolynomial G}
    (h : polyCode p = polyCode q) : p = q := by
  revert q
  induction p with
  | zero =>
    intro q h; match q with
    | .zero => rfl
    | .one | .curvature | .covDeriv _ _ | .add _ _ | .mul _ _ | .trace _ =>
      unfold polyCode at h; exfalso; omega
  | one =>
    intro q h; match q with
    | .one => rfl
    | .zero | .curvature | .covDeriv _ _ | .add _ _ | .mul _ _ | .trace _ =>
      unfold polyCode at h; exfalso; omega
  | curvature =>
    intro q h; match q with
    | .curvature => rfl
    | .zero | .one | .covDeriv _ _ | .add _ _ | .mul _ _ | .trace _ =>
      unfold polyCode at h; exfalso; omega
  | covDeriv n p ih =>
    intro q h; match q with
    | .covDeriv n' p' =>
        have h₂ : 8 * pair n (polyCode p) = 8 * pair n' (polyCode p') := Nat.add_left_cancel h
        have h₃ : pair n (polyCode p) = pair n' (polyCode p') := Nat.eq_of_mul_eq_mul_left (by decide) h₂
        obtain ⟨hn, hpc⟩ := pair_eq_pair.1 h₃
        rw [hn]
        exact
          (congrArg
            (fun t : GaugeInvariantLocalPolynomial G => GaugeInvariantLocalPolynomial.covDeriv n' t) (ih hpc))
    | .zero | .one | .curvature | .add _ _ | .mul _ _ | .trace _ =>
      unfold polyCode at h; exfalso; omega
  | add p₁ p₂ ih₁ ih₂ =>
    intro q h; match q with
    | .add p₁' p₂' =>
        have h₂ : 8 * pair (polyCode p₁) (polyCode p₂) = 8 * pair (polyCode p₁') (polyCode p₂') := Nat.add_left_cancel h
        have h₃ : pair (polyCode p₁) (polyCode p₂) = pair (polyCode p₁') (polyCode p₂') :=
          Nat.eq_of_mul_eq_mul_left (by decide) h₂
        obtain ⟨hpc₁, hpc₂⟩ := pair_eq_pair.1 h₃
        rw [ih₁ hpc₁, ih₂ hpc₂]
    | .zero | .one | .curvature | .covDeriv _ _ | .mul _ _ | .trace _ =>
      unfold polyCode at h; exfalso; omega
  | mul p₁ p₂ ih₁ ih₂ =>
    intro q h; match q with
    | .mul p₁' p₂' =>
        have h₂ : 8 * pair (polyCode p₁) (polyCode p₂) = 8 * pair (polyCode p₁') (polyCode p₂') := Nat.add_left_cancel h
        have h₃ : pair (polyCode p₁) (polyCode p₂) = pair (polyCode p₁') (polyCode p₂') :=
          Nat.eq_of_mul_eq_mul_left (by decide) h₂
        obtain ⟨hpc₁, hpc₂⟩ := pair_eq_pair.1 h₃
        rw [ih₁ hpc₁, ih₂ hpc₂]
    | .zero | .one | .curvature | .covDeriv _ _ | .add _ _ | .trace _ =>
      unfold polyCode at h; exfalso; omega
  | trace p ih =>
    intro q h; match q with
    | .trace p' =>
        have h₂ : 8 * polyCode p = 8 * polyCode p' := Nat.add_left_cancel h
        have h₃ : polyCode p = polyCode p' := Nat.eq_of_mul_eq_mul_left (by decide) h₂
        exact congrArg GaugeInvariantLocalPolynomial.trace (ih h₃)
    | .zero | .one | .curvature | .covDeriv _ _ | .add _ _ | .mul _ _ =>
      unfold polyCode at h; exfalso; omega

noncomputable def toyFieldOp {G : Type}
    (p : MillenniumYangMillsDefs.GaugeInvariantLocalPolynomial G) :
    OperatorValuedDistribution WightmanToyHilbert :=
  fun f => (Nat.cast (polyCode p) : ℝ) • wightmanToyScalarField f

theorem toyFieldOp_injective {G} : Function.Injective (@toyFieldOp G) := by
  intro p q h
  classical
  obtain ⟨f, hf⟩ := schwartzMap_real_eqAt_zero 1
  have hef : toyFieldOp p f = toyFieldOp q f := congrArg (fun (T : OperatorValuedDistribution WightmanToyHilbert) => T f) h
  have hΩ : toyFieldOp p f wightmanToyVacuum = toyFieldOp q f wightmanToyVacuum :=
    congrArg (fun (L : WightmanToyHilbert →L[ℝ] WightmanToyHilbert) => L wightmanToyVacuum) hef
  have hpq : polyCode p = polyCode q := by
    have h0 := congrArg (fun w : WightmanToyHilbert => w (0 : Fin 1)) hΩ
    simp [toyFieldOp, wightmanToyScalarField, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, hf, mul_one,
      wightmanToyVacuum, EuclideanSpace.single_apply] at h0
    exact h0
  exact polyCode_injective hpq

noncomputable def toyLocalOperators (G : Type) : LocalOperatorAssignment G WightmanToyHilbert where
  op := @toyFieldOp G
  injective _ _ h := toyFieldOp_injective h

/-- `MillenniumYangMillsDefs.SchwartzSpace` is a `def`, so it does not gain Mathlib's `•` on
`SchwartzMap` in typeclass search; we act on the underlying `SchwartzMap Spacetime ℝ` and
coerce back. -/
noncomputable def poincareToyScale (ε : ℝ) (f : SchwartzSpace) : SchwartzSpace :=
  (ε : ℝ) • (show SchwartzMap Spacetime ℝ from f)

/-- Short distance: the predicted correlator is exactly the one built from the scaled test functions. -/
noncomputable def poincareToyShortDistance :
    ShortDistanceAgreement wightmanToyScalarField wightmanToyVacuum := by
  let P : ℝ → List SchwartzSpace → ℝ := fun ε fs =>
    correlation wightmanToyScalarField wightmanToyVacuum (List.map (poincareToyScale ε) fs)
  exact
    { scale := poincareToyScale
      prediction := P
      agrees := by
        intro fs
        have h0 :
            (fun (ε : ℝ) =>
                correlation wightmanToyScalarField wightmanToyVacuum
                    (List.map (poincareToyScale ε) fs) - P ε fs) = fun (ε : ℝ) => (0 : ℝ) := by
          funext ε
          dsimp
          have : P ε fs = correlation wightmanToyScalarField wightmanToyVacuum
              (List.map (poincareToyScale ε) fs) := rfl
          rw [this, sub_self]
        rw [h0]
        exact tendsto_const_nhds
    }

-- Stress tensor: all components zero, identity test derivatives, conservation is `sum` of four zeros
noncomputable def poincareToyStress : StressEnergyTensor WightmanToyHilbert where
  testDeriv _ := id
  T _ _ := 0
  symmetric _ _ := rfl
  conserved := by
    intro _ f
    ext ψ
    simp

noncomputable def poincareToyOPE (G : Type) : OperatorProductExpansion G WightmanToyHilbert where
  coefficient _ _ _ := 0
  finite_support A B := by
    have hempty : ({C : GaugeInvariantLocalPolynomial G | (0 : ℝ) ≠ 0} : Set _) = ∅ := by ext C; simp
    have : Set.Finite {C : GaugeInvariantLocalPolynomial G | (0 : ℝ) ≠ 0} := by
      rw [hempty]
      exact Set.finite_empty
    -- `coefficient` is the constant 0, so the membership reduces to the left side of `hempty`
    exact this

/-- Full Dojo YM *interface* (not a physical mass-gap YM) built from the HQIV Wightman scalar toy. -/
noncomputable def poincareToyQuantumYangMills (G : Type) [CompactSimpleGaugeGroup G] : QuantumYangMillsTheory G where
  hilbertSpace := WightmanToyHilbert
  field_operators := wightmanToyScalarField
  wightman := wightmanToyWightmanAxioms
  localOperators := toyLocalOperators G
  shortDistance := poincareToyShortDistance
  stressTensor := poincareToyStress
  operatorProductExpansion := poincareToyOPE G
  localOperators_covariant := by
    intro g p f
    let c : ℝ := (Nat.cast (polyCode p) : ℝ)
    have hΦ : wightmanToyScalarField (millenniumPoincareTrivialTestAction g f) =
        conjugateOperator (millenniumPoincareTrivialUnitaryRep g) (wightmanToyScalarField f) :=
      wightmanToy_covariance g f
    have hsmul' (U : WightmanToyHilbert ≃ₗᵢ[ℝ] WightmanToyHilbert) (c : ℝ) (A : WightmanToyHilbert →L[ℝ] WightmanToyHilbert) :
        conjugateOperator U (c • A) = c • conjugateOperator U A := by
      ext x
      simp only [conjugateOperator, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, map_smul,
        LinearIsometryEquiv.toContinuousLinearEquiv]
    -- Rewrites through the *concrete* toy Wightman record; projections are not defeq to `hΦ`'s head symbol.
    have hact : wightmanToyWightmanAxioms.action_on_tests = millenniumPoincareTrivialTestAction := rfl
    have hU : wightmanToyWightmanAxioms.unitary_rep = millenniumPoincareTrivialUnitaryRep := rfl
    have :
        c • wightmanToyScalarField (wightmanToyWightmanAxioms.action_on_tests g f) =
          conjugateOperator (wightmanToyWightmanAxioms.unitary_rep g) (c • wightmanToyScalarField f) := by
      -- `c • F(g·f)` then `F(g·f)=U F(f)U*`; conjugation pulls out the real scalar
      simp only [hact, hU, hΦ]
      exact (hsmul' (millenniumPoincareTrivialUnitaryRep g) c (wightmanToyScalarField f)).symm
    exact this
  localOperators_locality := by
    intro p q f g hsp
    have _hΦ : wightmanToyScalarField f ∘L wightmanToyScalarField g =
        wightmanToyScalarField g ∘L wightmanToyScalarField f := wightmanToy_locality f g hsp
    change (toyFieldOp p f) ∘L (toyFieldOp q g) = (toyFieldOp q g) ∘L (toyFieldOp p f)
    ext v
    simp [toyFieldOp, wightmanToyScalarField, ContinuousLinearMap.smul_apply, smul_smul, ContinuousLinearMap.id_apply,
      mul_comm, mul_left_comm, mul_assoc]

end QuantumYangMillsFromPoincareToy
end Hqiv.Story

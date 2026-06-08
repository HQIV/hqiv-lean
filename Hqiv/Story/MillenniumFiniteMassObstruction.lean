import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Data.Set.Disjoint
import Mathlib.Logic.Nontrivial.Defs
import Problems.YangMills.Millennium

/-!
# `FiniteMassSpectrum` vs. unbounded “mass gap” parameters

`MillenniumYangMills.FiniteMassSpectrum` (`Problems.YangMills.Millennium`) requires a *global* upper
bound on every `Δ` for which `HasMassGapSpectrum` holds. If, instead, the Hamiltonian (as a
bounded real operator) is **zero** on a nontrivial Hilbert space, the spectrum is **only the point
`0`**, and `Set.Ioo 0 Δ` is then **disjoint** from the spectrum for *every* `Δ > 0` (the open
interval has no `0` and the spectrum has no *strictly positive* point). So `HasMassGapSpectrum`
holds for *arbitrarily large* `Δ`, and `FiniteMassSpectrum` is impossible
(`not_FiniteMassSpectrum_of_forall_pos_HasMassGapSpectrum`).

A **full** `Hqiv.Story.MassGapCompletion.ClayYangMillsCompletionData` (genuine `hFin`) therefore
cannot be the 1D zero-Hamiltonian Poincaré Wightman toy alone: that layer still discharges the
Schwartz/bump and Wightman bookkeeping in `Hqiv.Story.MillenniumBridgePoincareWightman`, but a
different (gapped) Hamiltonian layer is needed for a Dojo completion. The `MillenniumBridgeToyWitness`
**Clay** and **Hilbert-bridge** axioms remain the insertion point for a future
`QuantumYangMillsTheory` and chosen bridge/alignment.

*Related:* a **full** (but still zero-Hamiltonian) Dojo `QuantumYangMillsTheory` is explicitly built in
`Hqiv.Story.QuantumYangMillsFromPatchHQIV.hqivInterfaceQuantumYangMills` (minimal Schwartz spine); it cannot satisfy
`FiniteMassSpectrum` in the nontrivial one-dimensional case for the same spectral reason as this file
(`MillenniumBridgeToyWitness.not_FiniteMassSpectrum_of_wightman_hamiltonian_eq_zero` route).
-/

namespace Hqiv.Story.MillenniumDojoFiniteGapObstruction

open Set
open MillenniumYangMills
open scoped Classical
open MillenniumYangMillsDefs

namespace Aux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [hnt : Nontrivial H]

/-- The space of continuous linear self-maps of `H` is nontrivial (compare `0` and `1`). -/
theorem nontrivial_continuousLinearMap : Nontrivial (H →L[ℝ] H) := by
  refine' ⟨⟨(1 : H →L[ℝ] H), 0, ?_⟩⟩
  intro rid
  have := congr_arg (fun f : H →L[ℝ] H => ‖f‖) rid
  simp at this

end Aux

open Aux

theorem mem_spectrum_zero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [hnt : Nontrivial H] (E : ℝ) : E ∈ spectrum ℝ (0 : H →L[ℝ] H) ↔ E = 0 := by
  classical
  haveI := nontrivial_continuousLinearMap (H := H)
  rw [spectrum.mem_iff]
  simp only [sub_zero, Algebra.algebraMap_eq_smul_one]
  constructor
  · intro hE
    by_contra hE0
    apply hE
    exact IsUnit.smul (Units.mk0 E hE0) (isUnit_one : IsUnit (1 : H →L[ℝ] H))
  · intro hE
    rw [hE]
    -- `0 • 1` in the `ContinuousLinearMap` algebra rewrites to the zero map
    simp

theorem not_FiniteMassSpectrum_of_forall_pos_HasMassGapSpectrum
    (G : Type) [CompactSimpleGaugeGroup G] (qft : QuantumYangMillsTheory G)
    (h : ∀ Δ : ℝ, 0 < Δ → HasMassGapSpectrum G qft Δ) : ¬FiniteMassSpectrum G qft := by
  intro ⟨m, hm, hbound⟩
  have h2 : 0 < 2 * m := by nlinarith
  have hΔ : HasMassGapSpectrum G qft (2 * m) := h (2 * m) h2
  have := hbound (2 * m) hΔ
  linarith

theorem hasMassGapSpectrum_of_hamiltonian_eq_zero
    (G : Type) [CompactSimpleGaugeGroup G] (qft : QuantumYangMillsTheory G)
    [hnt : Nontrivial qft.hilbertSpace] (hH : qft.wightman.hamiltonian = 0) (Δ : ℝ) (hΔ : 0 < Δ) :
    HasMassGapSpectrum G qft Δ := by
  have hE : ∀ E, E ∈ spectrum ℝ qft.wightman.hamiltonian → E = 0 := by
    intro E hE'
    rw [hH] at hE'
    exact (mem_spectrum_zero (E := E)).1 hE'
  refine ⟨hΔ, ?_⟩
  -- `a ∈ spectrum → a ∉ (0, Δ)`: the only point of the zero-operator spectrum is `0`, and
  -- `0 ∉ Set.Ioo 0 Δ` when `0 < Δ`.
  rw [disjoint_left]
  intro a haS
  have ha0 := hE a haS
  rw [ha0]
  simp

theorem not_FiniteMassSpectrum_of_hamiltonian_eq_zero
    (G : Type) [CompactSimpleGaugeGroup G] (qft : QuantumYangMillsTheory G)
    [hnt : Nontrivial qft.hilbertSpace] (hH : qft.wightman.hamiltonian = 0) :
    ¬FiniteMassSpectrum G qft :=
  not_FiniteMassSpectrum_of_forall_pos_HasMassGapSpectrum G qft
    (fun _ hpos => hasMassGapSpectrum_of_hamiltonian_eq_zero G qft hH _ hpos)

end Hqiv.Story.MillenniumDojoFiniteGapObstruction
